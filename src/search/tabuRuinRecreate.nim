## Ruin-and-recreate (large neighbourhood) moves on a valid giant-tour circuit.
## Included from tabu.nim — not a standalone module.
##
## Pickup-and-delivery models with a successor circuit (vrplc): single
## successor changes always break the tour, and the tour/pair relocation moves
## (tabuCircuitMoves) shift one node or one linked pair at a time, so emptying
## a route (merging two routes) needs a chain of individually worsening moves.
## A round here removes a few requests (a linked node pair, or an unpaired
## movable node, is one request), then reinserts them one by one at their best
## position (cheapest insertion), the standard LNS for routing (Shaw 1998,
## Ropke & Pisinger 2006). Requests are chosen at random, by relatedness to a
## seed (distance and time window), or as every request of one route. Each
## candidate insertion is scored by lean simulate-and-restore, so time windows,
## loads, congestion and the objective are all the model's own. Candidates are
## compared on (hard violation, raw objective slack): the optimizer's bound is
## compressed by its cost scale far from the target, which would hide most
## objective differences in the plain cost.
##
## Removed nodes get their release (waiting) variables reset to the earliest
## value: the old waits were set for their old position. A round is kept when
## its key is not worse than before the ruin (sideways rounds diversify).

const RrMinRemove = 2
const RrMaxRemove = 8
const RrAhead = 40           # nodes after the first one where the second of a pair may go
const RrEmptyRoutes = 2      # empty routes tried per insertion (identical-looking slots)
const RrEvalAfterBest = 12   # candidates evaluated past the best one (detour order)
const RrBurstFails = 25      # consecutive rounds without improvement that end a burst
const RrBurstSecs = 1.0
proc buildRuinRecreate*[T](state: TabuState[T]) =
    state.rrBuilt = true
    if not state.tourPairsBuilt: state.buildTourPairs()
    if state.tourPairs.len == 0: return
    let circ = state.tourPairs[0][0]
    let cc = state.circuitConstraints[circ]
    let n = cc.n
    let off = cc.valueOffset
    state.rrCirc = circ
    # Movable nodes: own successor variable, and no fixed arc into them (route
    # anchors such as giant-tour start/end depots are reached by fixed arcs or
    # leave by one)
    var fixedInto = newSeq[bool](n)
    var movable = newSeq[bool](n)
    for i in 0..<n:
        let p = cc.positionArray[i]
        if p < 0: return
        let d = state.sharedDomain[][p]
        if d.len == 1:
            let s = int(d[0]) - off
            if s >= 0 and s < n: fixedInto[s] = true
    for i in 0..<n:
        movable[i] = state.sharedDomain[][cc.positionArray[i]].len > 1 and not fixedInto[i]
    var inPair = newSeq[bool](n)
    for (pc, na, nb) in state.tourPairs:
        if pc != circ: continue
        if not movable[na] or not movable[nb]: continue
        inPair[na] = true
        inPair[nb] = true
        state.rrUnits.add(@[na, nb])
    for i in 0..<n:
        if movable[i] and not inPair[i]: state.rrUnits.add(@[i])
    state.rrMovable = movable
    # Distances and time windows from a time chain on this circuit
    state.rrEarly = newSeq[int](n)
    state.rrRelPos = newSeq[seq[int]](n)
    for ctc in state.circuitTimePropConstraints:
        if ctc.n != n: continue
        var same = true
        for i in 0..<n:
            let lp = ctc.positionArray[i]
            if lp >= 0 and lp != cc.positionArray[i]:
                same = false
                break
        if not same: continue
        if ctc.hasRelease:
            for i in 0..<n:
                if i < ctc.releasePositions.len and ctc.releasePositions[i] >= 0:
                    state.rrRelPos[i].add(ctc.releasePositions[i])
        if not ctc.equalityChain and state.rrDist.len == 0:
            state.rrDist = newSeq[seq[int]](n)
            for a in 0..<n:
                state.rrDist[a] = newSeq[int](n)
                for b in 0..<n:
                    state.rrDist[a][b] = int(ctc.distanceMatrix[b][a])   # a -> b
            for i in 0..<n: state.rrEarly[i] = int(ctc.earlyTimes[i])
    if (state.verbose and state.id == 0) or existsEnv("CRUSHER_DEBUG_CIRCUIT"):
        echo "[Init] Ruin-recreate: " & $state.rrUnits.len & " requests"

proc rrKey*[T](state: TabuState[T]): (int, int) {.inline.} =
    ## (hard violation, raw objective slack); see the module comment
    if state.boundConstraint == nil: return (state.cost, 0)
    let bp = state.boundConstraint.penalty()
    (state.cost - bp, int(state.boundSlack()))

proc rrRelatedness[T](state: TabuState[T], u, v: int): int =
    ## Smaller = more related: closest node distance plus window offset
    result = high(int)
    for a in state.rrUnits[u]:
        for b in state.rrUnits[v]:
            var d = abs(state.rrEarly[a] - state.rrEarly[b])
            if state.rrDist.len > 0:
                d += min(state.rrDist[a][b], state.rrDist[b][a])
            result = min(result, d)

proc rrRound*[T](state: TabuState[T]): int =
    ## One ruin-and-recreate round. 1 = improved, 0 = kept sideways,
    ## -1 = rejected (state restored).
    let cc = state.circuitConstraints[state.rrCirc]
    if cc.cost != 0:
        inc state.rrBroken
        return -1
    let n = cc.n
    let off = cc.valueOffset
    let nu = state.rrUnits.len
    var log: seq[(int, T)]
    template succOf(v: int): int = int(state.assignment[cc.positionArray[v]]) - off
    template setPos(p: int, val: T) =
        log.add((p, state.assignment[p]))
        state.assignValueLean(p, val)
    template setSucc(v, w: int) = setPos(cc.positionArray[v], T(w + off))
    template canSucc(v, w: int): bool = state.domIdx(cc.positionArray[v], T(w + off)) >= 0
    template undoTo(mark: int) =
        for li in countdown(log.len - 1, mark):
            state.assignValueLean(log[li][0], log[li][1])
        log.setLen(mark)
    let before = state.rrKey()
    var pred = newSeq[int](n)
    for i in 0..<n: pred[succOf(i)] = i
    # 1) choose requests
    let k = min(nu, RrMinRemove + rand(RrMaxRemove - RrMinRemove))
    var chosen: seq[int]
    var isChosen = newSeq[bool](nu)
    var unitOf = newSeq[int](n)
    for i in 0..<n: unitOf[i] = -1
    for ui, u in state.rrUnits:
        for z in u: unitOf[z] = ui
    template choose(ui: int) =
        if not isChosen[ui]:
            isChosen[ui] = true
            chosen.add(ui)
    let mode = rand(2)
    let seed = rand(nu - 1)
    choose(seed)
    if mode == 2:
        # every request on the seed's route
        let z0 = state.rrUnits[seed][0]
        var z = succOf(z0)
        var guard = 0
        while z != z0 and state.rrMovable[z] and guard < n:
            if unitOf[z] >= 0: choose(unitOf[z])
            z = succOf(z)
            inc guard
        z = pred[z0]
        guard = 0
        while z != z0 and state.rrMovable[z] and guard < n:
            if unitOf[z] >= 0: choose(unitOf[z])
            z = pred[z]
            inc guard
    if chosen.len < k:
        if mode == 0:
            while chosen.len < k: choose(rand(nu - 1))
        else:
            var others: seq[(int, int)]
            for ui in 0..<nu:
                if not isChosen[ui]: others.add((state.rrRelatedness(seed, ui), ui))
            others.sort()
            while chosen.len < k and others.len > 0:
                # Shaw's randomized pick, biased to the most related
                let r = rand(1.0)
                let idx = min(others.len - 1, int(r * r * r * float(others.len)))
                choose(others[idx][1])
                others.delete(idx)
    # 2) detach (self loops) and reset releases
    var removed = newSeq[bool](n)
    var kept: seq[int]
    for ui in chosen:
        let mark = log.len
        var ok = true
        var nodes = state.rrUnits[ui]
        # adjacent pair: bypass both at once (the arc that skips only one of
        # them is often not in the domain, e.g. start depot -> delivery)
        if nodes.len == 2 and succOf(nodes[1]) == nodes[0]: nodes = @[nodes[1], nodes[0]]
        var zi = 0
        while zi < nodes.len:
            let z = nodes[zi]
            var last = z
            if zi + 1 < nodes.len and succOf(z) == nodes[zi + 1]: last = nodes[zi + 1]
            var p = 0
            while p < n and succOf(p) != z: inc p
            let s = succOf(last)
            if p >= n or p == z or p == last or not canSucc(p, s):
                ok = false
                break
            setSucc(p, s)
            setSucc(z, z)
            if last != z: setSucc(last, last)
            zi += (if last != z: 2 else: 1)
        if not ok:
            # the bypass arc is not in the domain: leave this request in place
            undoTo(mark)
            continue
        kept.add(ui)
        for z in state.rrUnits[ui]:
            removed[z] = true
            for rp in state.rrRelPos[z]:
                let lo = min(state.sharedDomain[][rp])
                if state.assignment[rp] != lo: setPos(rp, lo)
    chosen = kept
    if chosen.len == 0:
        inc state.rrAborted
        return -1
    # 3) reinsert, cheapest position first
    if rand(1) == 0: shuffle(chosen)
    else:
        chosen.sort(proc (a, b: int): int =
            cmp(state.rrEarly[state.rrUnits[a][0]], state.rrEarly[state.rrUnits[b][0]]))
    var us: seq[int]
    type Cand = tuple[est: int, u, w, order: int]
    var cands: seq[Cand]
    let haveDist = state.rrDist.len > 0
    template dd(a, b: int): int = (if haveDist: state.rrDist[a][b] else: 0)
    for ui in chosen:
        let nodes = state.rrUnits[ui]
        var orders: seq[(int, int)]
        if nodes.len == 2:
            let (a, b) = (nodes[0], nodes[1])
            if state.rrEarly[a] < state.rrEarly[b]: orders.add((a, b))
            elif state.rrEarly[b] < state.rrEarly[a]: orders.add((b, a))
            else: orders = @[(a, b), (b, a)]
        us.setLen(0)
        for u in 0..<n:
            if not removed[u]: us.add(u)
        shuffle(us)
        # Candidate positions with their travel detour (an estimate: the real
        # key decides), cheapest first
        cands.setLen(0)
        var emptySeen = 0
        for u in us:
            let su = succOf(u)
            if state.sharedDomain[][cc.positionArray[u]].len <= 1: continue   # fixed arc
            if not state.rrMovable[u] and not state.rrMovable[su]:
                if emptySeen >= RrEmptyRoutes: continue
                inc emptySeen
            if nodes.len == 1:
                let x = nodes[0]
                if canSucc(u, x) and canSucc(x, su):
                    cands.add((dd(u, x) + dd(x, su) - dd(u, su), u, -1, 0))
                continue
            for oi, (x, y) in orders:
                if not canSucc(u, x): continue
                # y right after x
                if canSucc(x, y) and canSucc(y, su):
                    cands.add((dd(u, x) + dd(x, y) + dd(y, su) - dd(u, su), u, x, oi))
                if not canSucc(x, su) or not state.rrMovable[su]: continue
                let dx = dd(u, x) + dd(x, su) - dd(u, su)
                var w = su
                for step in 1..<RrAhead:
                    let sw = succOf(w)
                    if canSucc(w, y) and canSucc(y, sw):
                        cands.add((dx + dd(w, y) + dd(y, sw) - dd(w, sw), u, w, oi))
                    if not state.rrMovable[sw]: break   # route end
                    w = sw
        if cands.len == 0:
            undoTo(0)
            inc state.rrAborted
            return -1
        if haveDist: cands.sort(proc (a, b: Cand): int = cmp(a.est, b.est))
        template applyCand(c: Cand) =
            let su = succOf(c.u)
            if nodes.len == 1:
                setSucc(c.u, nodes[0])
                setSucc(nodes[0], su)
            else:
                let (x, y) = orders[c.order]
                if c.w == x:
                    setSucc(c.u, x)
                    setSucc(x, y)
                    setSucc(y, su)
                else:
                    setSucc(c.u, x)
                    setSucc(x, su)
                    let sw = succOf(c.w)
                    setSucc(c.w, y)
                    setSucc(y, sw)
        var bestKey = (high(int), high(int))
        var best = -1
        var sinceBest = 0
        for ci, c in cands:
            if haveDist and best >= 0 and sinceBest >= RrEvalAfterBest: break
            let mark = log.len
            applyCand(c)
            let key = state.rrKey()
            inc state.rrEvals
            if key < bestKey:
                bestKey = key
                best = ci
                sinceBest = 0
            else:
                inc sinceBest
            undoTo(mark)
        applyCand(cands[best])
        for z in nodes: removed[z] = false
    let after = state.rrKey()
    inc state.rrRounds
    if cc.cost != 0 or before < after:
        undoTo(0)
        inc state.rrRejected
        return -1
    # Commit the final values (last write per position wins)
    var finalOf: Table[int, T]
    var posOrder: seq[int]
    for (p, _) in log:
        if p notin finalOf: posOrder.add(p)
        finalOf[p] = state.assignment[p]
    undoTo(0)
    for p in posOrder:
        if state.assignment[p] != finalOf[p]:
            state.commitValue(p, finalOf[p])
    if after < before:
        inc state.rrImproved
        return 1
    return 0
