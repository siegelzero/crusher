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
##
## The tour is a circuit constraint (preferring one with linked pairs), else a
## time chain that enforces its own circuit (CVRP / TSPTW translations, where
## links may be fixed literals or predecessors: a round only rewires links, so
## the orientation does not matter). Insertion candidates are tried cheapest
## travel detour first, from the time chain's matrix or else the objective's
## per-link cost; the "route" ruin takes the seed's route, or a string of the
## tour around it when the tour has no anchors.

const RrMinRemove = 2
const RrMaxRemove = 8
const RrAhead = 40           # nodes after the first one where the second of a pair may go
const RrEmptyRoutes = 2      # empty routes tried per insertion (identical-looking slots)
const RrEvalAfterBest = 12   # candidates evaluated past the best one (detour order)
const RrBurstFails = 25      # consecutive rounds without improvement that end a burst
const RrBurstSecs = 1.0
const RrMinNodes = 5          # smallest circuit worth a round
const RrDistMaxNodes = 2000   # objective-derived travel matrix up to this size
proc buildRuinRecreate*[T](state: TabuState[T]) =
    ## Pick the tour (a circuit constraint, else a time chain that enforces its
    ## own circuit), its requests, travel estimates and release positions.
    state.rrBuilt = true
    state.rrCirc = -1
    state.rrCtp = -1
    if not state.tourPairsBuilt: state.buildTourPairs()
    var n = 0
    var off = 0
    var linkPos: seq[int]
    var fixedLink: seq[int]
    if state.tourPairs.len > 0:
        state.rrCirc = state.tourPairs[0][0]
    else:
        # the circuit with the most free successors
        var bestFree = 0
        for ci, c in state.circuitConstraints:
            if c.n < RrMinNodes: continue
            var nFree = 0
            for p in c.positionArray:
                if p >= 0 and state.sharedDomain[][p].len > 1: inc nFree
            if nFree > bestFree:
                bestFree = nFree
                state.rrCirc = ci
    if state.rrCirc >= 0:
        let cc = state.circuitConstraints[state.rrCirc]
        n = cc.n
        off = cc.valueOffset
        linkPos = cc.positionArray
        fixedLink = newSeq[int](n)
        for i in 0..<n:
            if linkPos[i] < 0: return
    else:
        # no circuit constraint: a time chain carrying the circuit (CVRP, TSPTW)
        var bestFree = 0
        for ti, c in state.circuitTimePropConstraints:
            if c.n < RrMinNodes or c.equalityChain: continue
            var nFree = 0
            for p in c.positionArray:
                if p >= 0 and state.sharedDomain[][p].len > 1: inc nFree
            if nFree > bestFree:
                bestFree = nFree
                state.rrCtp = ti
        if state.rrCtp < 0: return
        let c = state.circuitTimePropConstraints[state.rrCtp]
        n = c.n
        off = c.valueOffset
        linkPos = c.positionArray
        fixedLink = newSeq[int](n)
        for i in 0..<n: fixedLink[i] = c.links[i]
    state.rrOff = off
    state.rrLinkPos = linkPos
    state.rrFixedLink = fixedLink
    # Movable nodes: own link variable, and no fixed link into them (route
    # anchors such as giant-tour start/end depots are reached by fixed links or
    # leave by one)
    var fixedInto = newSeq[bool](n)
    var movable = newSeq[bool](n)
    for i in 0..<n:
        let p = linkPos[i]
        var s = -1
        if p < 0: s = fixedLink[i]
        elif state.sharedDomain[][p].len == 1: s = int(state.sharedDomain[][p][0]) - off
        if s >= 0 and s < n: fixedInto[s] = true
    for i in 0..<n:
        movable[i] = linkPos[i] >= 0 and state.sharedDomain[][linkPos[i]].len > 1 and
                     not fixedInto[i]
    var inPair = newSeq[bool](n)
    for (pc, na, nb) in state.tourPairs:
        if pc != state.rrCirc: continue
        if not movable[na] or not movable[nb]: continue
        inPair[na] = true
        inPair[nb] = true
        state.rrUnits.add(@[na, nb])
    for i in 0..<n:
        if movable[i] and not inPair[i]: state.rrUnits.add(@[i])
    state.rrMovable = movable
    # Travel (in link orientation: the cost of link(a) = b) and time windows
    # from a time chain on this tour
    state.rrEarly = newSeq[int](n)
    state.rrRelPos = newSeq[seq[int]](n)
    for ctc in state.circuitTimePropConstraints:
        if ctc.n != n: continue
        var same = true
        for i in 0..<n:
            let lp = ctc.positionArray[i]
            if lp >= 0 and lp != linkPos[i]:
                same = false
                break
        if not same: continue
        if ctc.hasRelease:
            for i in 0..<n:
                if i < ctc.releasePositions.len and ctc.releasePositions[i] >= 0:
                    state.rrRelPos[i].add(ctc.releasePositions[i])
        if not ctc.equalityChain and state.rrDist.len == 0 and ctc.distanceMatrix.len == n:
            state.rrDist = newSeq[seq[int]](n)
            for a in 0..<n:
                state.rrDist[a] = newSeq[int](n)
                for b in 0..<n:
                    # distanceMatrix[to][from]; a backward link is a predecessor
                    state.rrDist[a][b] = int(if ctc.forward: ctc.distanceMatrix[b][a]
                                             else: ctc.distanceMatrix[a][b])
            for i in 0..<n: state.rrEarly[i] = int(ctc.earlyTimes[i])
    # No travel matrix from a time chain: the objective's per-link cost (direct
    # coefficient plus constant element lookups of the link), if any
    if state.rrDist.len == 0 and state.boundConstraint != nil and n <= RrDistMaxNodes and
       state.boundConstraint.stateType == RelationalType:
        if not state.polishEstBuilt: state.buildPolishEstimates()
        if state.polishElems.len > 0:
            var anyArc = false
            var dist = newSeq[seq[int]](n)
            for a in 0..<n:
                dist[a] = newSeq[int](n)
                let p = linkPos[a]
                if p < 0: continue
                let old = state.assignment[p]
                for b in 0..<n:
                    let v = T(b + off)
                    var d = int(state.polishDirect[p] * v)
                    for (bi, c) in state.polishElems[p]:
                        let bnd {.cursor.} = state.carray.channelBindings[bi]
                        state.assignment[p] = v
                        let i1 = int(bnd.evalIndex(state.assignment))
                        state.assignment[p] = old
                        if i1 >= 0 and i1 < bnd.arrayElements.len:
                            d += int(c * bnd.arrayElements[i1].constantValue)
                    dist[a][b] = d
                    if d != 0: anyArc = true
            if anyArc: state.rrDist = dist
    if (state.verbose and state.id == 0) or existsEnv("CRUSHER_DEBUG_CIRCUIT"):
        echo "[Init] Ruin-recreate: " & $state.rrUnits.len & " requests on a " &
             (if state.rrCirc >= 0: "circuit" else: "time chain") & " of " & $n & " nodes" &
             (if state.rrDist.len > 0: " (travel estimates)" else: "")

proc rrTourValid[T](state: TabuState[T]): bool {.inline.} =
    if state.rrCirc >= 0: state.circuitConstraints[state.rrCirc].cost == 0
    else: state.circuitTimePropConstraints[state.rrCtp].circuitPenalty == 0

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
    if not state.rrTourValid():
        inc state.rrBroken
        return -1
    let n = state.rrLinkPos.len
    let off = state.rrOff
    let nu = state.rrUnits.len
    var log: seq[(int, T)]
    # "successor" = the tour's link (a predecessor on a backward time chain)
    template succOf(v: int): int =
        (if state.rrLinkPos[v] >= 0: int(state.assignment[state.rrLinkPos[v]]) - off
         else: state.rrFixedLink[v])
    template setPos(p: int, val: T) =
        log.add((p, state.assignment[p]))
        state.assignValueLean(p, val)
    template setSucc(v, w: int) = setPos(state.rrLinkPos[v], T(w + off))
    template canSucc(v, w: int): bool =
        state.rrLinkPos[v] >= 0 and state.domIdx(state.rrLinkPos[v], T(w + off)) >= 0
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
        # the seed's route (anchor to anchor), or a string of the tour around
        # the seed when the route is long (single-tour circuits)
        let z0 = state.rrUnits[seed][0]
        var fwd = succOf(z0)
        var bwd = pred[z0]
        var fwdOpen = true
        var bwdOpen = true
        var guard = 0
        while (fwdOpen or bwdOpen) and chosen.len < RrMaxRemove and guard < n:
            inc guard
            if fwdOpen:
                if fwd == z0 or not state.rrMovable[fwd]: fwdOpen = false
                else:
                    if unitOf[fwd] >= 0: choose(unitOf[fwd])
                    fwd = succOf(fwd)
            if bwdOpen and chosen.len < RrMaxRemove:
                if bwd == z0 or not state.rrMovable[bwd]: bwdOpen = false
                else:
                    if unitOf[bwd] >= 0: choose(unitOf[bwd])
                    bwd = pred[bwd]
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
            if state.rrLinkPos[u] < 0 or state.sharedDomain[][state.rrLinkPos[u]].len <= 1:
                continue   # fixed link
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
    if not state.rrTourValid() or before < after:
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
