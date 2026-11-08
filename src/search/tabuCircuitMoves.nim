## Circuit cross-cycle merge moves.
## Included from tabu.nim — not a standalone module.
##
## When a `circuit` constraint is stuck with several disjoint subtours, no single
## successor reassignment can merge two of them: redirecting one node's successor
## into another cycle breaks the permutation (creates a duplicate value / tail),
## so the single-variable move delta is >= 0 and tabu search plateaus. The
## standard escape is a *2-opt cross-cycle swap*: exchange the successor values of
## a node `a` on cycle A and a node `b` on cycle B. Swapping the successors of two
## nodes that lie on different cycles of a permutation stitches those two cycles
## into one — reducing the circuit penalty term `max(0, numCycles - 1)` by exactly
## one — while preserving allDifferent (the two values are merely exchanged
## between the two positions).
##
## This is a general neighborhood for any model with a circuit / Hamiltonian
## constraint over *direct* search variables (TSP, sequencing, vehicle-routing
## successor encodings). Circuits whose variables are channel (derived) positions
## are excluded at collection time — their successors cannot be assigned directly.
##
## Candidate generation is O(n · domain), not O(n^2): for each node `a`, scanning
## its (typically small) domain for a value `w` identifies the unique node `b`
## currently holding `w` as `a`'s 2-opt partner. The swap is only feasible — and
## only considered — when `b` is on a different cycle and `a`'s current value lies
## in `b`'s domain, so domain-restricted models (e.g. the knight's tour) stay
## cheap. Each surviving candidate is scored by its true global cost delta (via
## assignValueLean simulate-and-restore), so coupling with other constraints and
## the objective is accounted for, not just the circuit term.

proc tryCircuitMoves[T](state: TabuState[T], allowPerturb: bool = false): bool =
    if state.circuitConstraints.len == 0: return false
    state.circuitMoveCalls += 1

    const MAX_CIRCUITS = 3      # violated multi-cycle circuits examined per call
    const MAX_PAIRS = 1500      # candidate swaps simulated per call (work bound)

    var bestDelta = 0           # strictly improving moves only
    var bestPa, bestPb = -1
    var bestValA, bestValB: T
    # Least-harmful non-improving move, used only under allowPerturb
    var perturbDelta = high(int)
    var perturbPa, perturbPb = -1
    var perturbValA, perturbValB: T

    # NB: iterate circuits in a fixed order — do NOT shuffle. This helper runs
    # purely as reads + simulate-and-restore, so when it finds nothing it must
    # leave the global RNG state untouched, or it would desync the rest of the
    # search's random stream and perturb the baseline trajectory for free.
    var examined = 0
    var pairsEvaluated = 0

    for cc in state.circuitConstraints:
        if examined >= MAX_CIRCUITS or pairsEvaluated >= MAX_PAIRS: break
        # Only multi-cycle circuits can be helped by a merge.
        if cc.cost == 0 or cc.distinctCycleCount < 2: continue
        examined += 1

        # Snapshot cycle membership and the value -> holder map for this circuit.
        # The partition is what matters (which nodes share a cycle); it is stable
        # under the relabeling that simulate-and-restore may apply to cycle ids.
        let members = cc.nodeCycleIds()
        var posCycle = initTable[int, int]()
        var whoPointsTo = initTable[T, int]()
        for (pos, cid) in members:
            posCycle[pos] = cid
            whoPointsTo[state.assignment[pos]] = pos

        block circuitPairs:
            for (pa, cycleA) in members:
                if cycleA < 0: continue           # tail node, not on a cycle
                let valA = state.assignment[pa]
                for w in state.sharedDomain[][pa]:
                    if w == valA: continue
                    let pb = whoPointsTo.getOrDefault(w, -1)
                    if pb < 0: continue
                    let cycleB = posCycle.getOrDefault(pb, -1)
                    if cycleB < 0 or cycleB == cycleA: continue   # need a different cycle
                    # Swap is pa <- w (== valB) and pb <- valA; check pb accepts valA.
                    if state.domIdx(pb, valA) < 0: continue
                    let valB = w

                    # Score the swap by its true global delta.
                    let origCost = state.cost
                    state.assignValueLean(pa, valB)
                    state.assignValueLean(pb, valA)
                    let delta = state.cost - origCost
                    state.assignValueLean(pb, valB)
                    state.assignValueLean(pa, valA)

                    if delta < bestDelta:
                        bestDelta = delta
                        bestPa = pa; bestPb = pb
                        bestValA = valA; bestValB = valB
                    elif allowPerturb and delta < perturbDelta:
                        perturbDelta = delta
                        perturbPa = pa; perturbPb = pb
                        perturbValA = valA; perturbValB = valB

                    pairsEvaluated += 1
                    if pairsEvaluated >= MAX_PAIRS: break circuitPairs

    # Prefer a strictly improving merge; fall back to the gentlest perturbation.
    var pa, pb: int
    var valA, valB: T
    if bestPa >= 0:
        pa = bestPa; pb = bestPb; valA = bestValA; valB = bestValB
    elif allowPerturb and perturbPa >= 0:
        pa = perturbPa; pb = perturbPb; valA = perturbValA; valB = perturbValB
    else:
        return false

    # Apply for real: tabu the displaced values, then commit both assignments.
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    let idxA = state.domIdx(pa, valA)
    if idxA >= 0 and not state.isLazy[pa]:
        state.tabu[pa][idxA] = tabuTenure
    let idxB = state.domIdx(pb, valB)
    if idxB >= 0 and not state.isLazy[pb]:
        state.tabu[pb][idxB] = tabuTenure
    state.commitValue(pa, valB)
    state.commitValue(pb, valA)
    state.circuitMergesApplied += 1
    return true


# ---------------------------------------------------------------------------
# Channel circuits: the successor array `c` is derived (c[i] = sources_i[index_i],
# an element channel), so `c` cannot be assigned directly. The same cross-cycle
# 2-opt merge still applies, but it is *realized* by flipping the index selectors:
# to swap c[a] and c[b] we set each one's index so the channel produces the other's
# current value. This only fires when the swap is realizable from the sources the
# selectors can currently reach — exactly the p1f case (each c[i] selects between
# the successor of node i in two matchings). Assigning the index variable
# propagates through the channel and updates the circuit penalty, so the global
# delta is measured the same way as the direct case.
# ---------------------------------------------------------------------------

proc channelIndexVarPos[T](state: TabuState[T], bi: int): int =
    ## The single index variable position selecting an element channel, or -1 if
    ## the index expression is not one searchable variable (can't realize a flip).
    let b = addr state.carray.channelBindings[bi]
    if b.indexExpression.positions.len != 1: return -1
    for p in b.indexExpression.positions.items:
        return p
    return -1

proc realizeChannelValue[T](state: TabuState[T], bi: int, target: T): (int, T) =
    ## Find (indexVarPos, indexVarValue) such that setting that index variable
    ## makes channel `bi` evaluate to `target` from the current source values.
    ## Returns (-1, _) when no single index value reaches `target`.
    result = (-1, T(0))
    let idxPos = state.channelIndexVarPos(bi)
    if idxPos < 0 or state.isLazy[idxPos]: return
    let b = addr state.carray.channelBindings[bi]
    let saved = state.assignment[idxPos]
    for v in state.sharedDomain[][idxPos]:
        state.assignment[idxPos] = v
        let iv = b[].evalIndex(state.assignment)
        if iv >= 0 and iv < b.arrayElements.len:
            let elem = b.arrayElements[iv]
            let cv = if elem.isConstant: elem.constantValue
                     else: state.assignment[elem.variablePosition] + elem.offset
            if cv == target:
                result = (idxPos, v)
                break
    state.assignment[idxPos] = saved

proc tryChannelCircuitMoves[T](state: TabuState[T], allowPerturb: bool = false): bool =
    if state.channelCircuitConstraints.len == 0: return false
    state.circuitMoveCalls += 1

    const MAX_CIRCUITS = 4
    const MAX_PAIRS = 1200

    var bestDelta = 0
    var bIpA, bIpB = -1
    var bIvA, bIvB: T
    var perturbDelta = high(int)
    var pIpA, pIpB = -1
    var pIvA, pIvB: T

    var examined = 0
    var pairsEvaluated = 0

    for cc in state.channelCircuitConstraints:
        if examined >= MAX_CIRCUITS or pairsEvaluated >= MAX_PAIRS: break
        if cc.cost == 0 or cc.distinctCycleCount < 2: continue
        examined += 1

        let members = cc.nodeCycleIds()
        var posCycle = initTable[int, int]()
        var whoPointsTo = initTable[T, int]()
        for (pos, cid) in members:
            posCycle[pos] = cid
            whoPointsTo[state.assignment[pos]] = pos

        block pairs:
            for (cPosA, cycleA) in members:
                if cycleA < 0: continue
                if cPosA notin state.cPosToBinding: continue
                let biA = state.cPosToBinding[cPosA]
                let valA = state.assignment[cPosA]
                # Candidate new successors for c[a] are the values its selector can
                # currently reach (its element sources).
                let bA = addr state.carray.channelBindings[biA]
                for elem in bA.arrayElements:
                    let w = if elem.isConstant: elem.constantValue
                            else: state.assignment[elem.variablePosition] + elem.offset
                    if w == valA: continue
                    let pb = whoPointsTo.getOrDefault(w, -1)
                    if pb < 0: continue
                    let cycleB = posCycle.getOrDefault(pb, -1)
                    if cycleB < 0 or cycleB == cycleA: continue
                    if pb notin state.cPosToBinding: continue
                    let biB = state.cPosToBinding[pb]
                    # Realize c[a] := w and c[b] := valA by flipping both selectors.
                    let (ipA, ivA) = state.realizeChannelValue(biA, w)
                    if ipA < 0: continue
                    let (ipB, ivB) = state.realizeChannelValue(biB, valA)
                    if ipB < 0 or ipB == ipA: continue

                    let origCost = state.cost
                    let savedA = state.assignment[ipA]
                    let savedB = state.assignment[ipB]
                    state.assignValueLean(ipA, ivA)
                    state.assignValueLean(ipB, ivB)
                    let delta = state.cost - origCost
                    state.assignValueLean(ipB, savedB)
                    state.assignValueLean(ipA, savedA)

                    if delta < bestDelta:
                        bestDelta = delta
                        bIpA = ipA; bIvA = ivA; bIpB = ipB; bIvB = ivB
                    elif allowPerturb and delta < perturbDelta:
                        perturbDelta = delta
                        pIpA = ipA; pIvA = ivA; pIpB = ipB; pIvB = ivB

                    pairsEvaluated += 1
                    if pairsEvaluated >= MAX_PAIRS: break pairs

    var ipA, ipB: int
    var ivA, ivB: T
    if bIpA >= 0:
        ipA = bIpA; ipB = bIpB; ivA = bIvA; ivB = bIvB
    elif allowPerturb and pIpA >= 0:
        ipA = pIpA; ipB = pIpB; ivA = pIvA; ivB = pIvB
    else:
        return false

    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    let oldA = state.assignment[ipA]
    let oldB = state.assignment[ipB]
    let idxA = state.domIdx(ipA, oldA)
    if idxA >= 0 and not state.isLazy[ipA]: state.tabu[ipA][idxA] = tabuTenure
    let idxB = state.domIdx(ipB, oldB)
    if idxB >= 0 and not state.isLazy[ipB]: state.tabu[ipB][idxB] = tabuTenure
    state.assignValue(ipA, ivA)
    state.assignValue(ipB, ivB)
    state.circuitMergesApplied += 1
    return true


proc tryTourMoves[T](state: TabuState[T], allowPerturb: bool = false): bool =
    ## Tour-preserving node relocation (or-opt) on a VALID circuit over direct
    ## successor variables: remove node x (p -> x -> s becomes p -> s) and
    ## reinsert it after u (u -> x -> v). Three successor changes that keep the
    ## permutation a single cycle — single-variable successor moves always break
    ## it, so without this the search can only optimize a tour through circuit
    ## violations (fatal when the circuit drives time/accumulator chains whose
    ## values are meaningless off the tour). Each candidate is scored by its true
    ## global delta (lean simulate-and-restore, including channels and CTP
    ## writebacks); the best strictly improving one is applied (or, under
    ## allowPerturb, the least-worsening one).
    if state.circuitConstraints.len == 0: return false
    const MAX_EVALS = 3000
    var bestDelta = if allowPerturb: high(int) else: 0
    var bestChanges: seq[(int, T)]
    var evals = 0
    for cc in state.circuitConstraints:
        if cc.cost != 0: continue
        let n = cc.n
        if n < 4: continue
        var succ = newSeq[int](n)
        var pred = newSeq[int](n)
        var ok = true
        for i in 0..<n:
            let p = cc.positionArray[i]
            if p < 0: ok = false; break
            let s = int(state.assignment[p]) - cc.valueOffset
            if s < 0 or s >= n: ok = false; break
            succ[i] = s
            pred[s] = i
        if not ok: continue
        template valOf(node: int): T = T(node + cc.valueOffset)
        var order = toSeq(0..<n)
        shuffle(order)
        for x in order:
            if evals >= MAX_EVALS: break
            # Segment x..b: follow fixed arcs (single-value successor domains),
            # so fixed chains (e.g. giant-tour depot connectors end_v -> start_v+1)
            # relocate as a unit; a single node is the segment x..x.
            var b = x
            var segLen = 1
            while state.sharedDomain[][cc.positionArray[b]].len == 1 and segLen < n - 2 and
                  not gNoSegmentRelocate:
                let nb = succ[b]
                if nb == x: break
                b = nb
                inc segLen
            if state.sharedDomain[][cc.positionArray[b]].len == 1: continue   # tail arc fixed
            let p = pred[x]
            let s = succ[b]
            var inSeg = initPackedSet[int]()
            if segLen > 1:
                var y = x
                while true:
                    inSeg.incl(y)
                    if y == b: break
                    y = succ[y]
            for u in 0..<n:
                if evals >= MAX_EVALS: break
                if u == x or u == p or u == b or (segLen > 1 and u in inSeg): continue
                let v = if u == s: succ[s] else: succ[u]
                if v == x: continue
                # Changes: succ[p] := s, succ[u] := x, succ[b] := v
                let pp = cc.positionArray[p]
                let pu = cc.positionArray[u]
                let px = cc.positionArray[b]
                if state.domIdx(pp, valOf(s)) < 0 or state.domIdx(pu, valOf(x)) < 0 or
                   state.domIdx(px, valOf(v)) < 0:
                    continue
                inc evals
                let before = state.cost
                let ovp = state.assignment[pp]
                let ovu = state.assignment[pu]
                let ovx = state.assignment[px]
                state.assignValueLean(pp, valOf(s))
                state.assignValueLean(pu, valOf(x))
                state.assignValueLean(px, valOf(v))
                let delta = state.cost - before
                state.assignValueLean(px, ovx)
                state.assignValueLean(pu, ovu)
                state.assignValueLean(pp, ovp)
                if delta < bestDelta:
                    bestDelta = delta
                    bestChanges = @[(pp, valOf(s)), (pu, valOf(x)), (px, valOf(v))]
                    if delta < 0 and not allowPerturb: break   # first improvement
            if bestDelta < 0 and not allowPerturb: break
    if bestChanges.len == 0: return false
    if bestDelta >= 0 and not allowPerturb: return false
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    for (pos, val) in bestChanges:
        let oldIdx = state.domIdx(pos, state.assignment[pos])
        if oldIdx >= 0 and not state.isLazy[pos]:
            state.tabu[pos][oldIdx] = tabuTenure
        state.commitValue(pos, val)
    return true


proc buildTourPairs[T](state: TabuState[T]) =
    ## Node pairs tied by a 2-position relational constraint over the written-back
    ## values of ONE accumulator chain (pickup/delivery on the same vehicle:
    ## veh[i] == veh[P+i]). Moving one of them alone always violates the relation.
    state.tourPairsBuilt = true
    if state.circuitConstraints.len == 0: return
    var circOfLink: Table[int, int]
    for ci, cc in state.circuitConstraints:
        for p in cc.positionArray:
            if p >= 0: circOfLink[p] = ci
    var seen: HashSet[(int, int, int)]
    for ctc in state.circuitTimePropConstraints:
        if not ctc.equalityChain: continue
        var nodeOfPos: Table[int, int]
        for i in 0..<ctc.n:
            if ctc.departurePositions[i] >= 0: nodeOfPos[ctc.departurePositions[i]] = i
        # circuit of this chain: via any link position
        var circ = -1
        for p in ctc.positionArray:
            if p >= 0 and p in circOfLink:
                circ = circOfLink[p]
                break
        if circ < 0: continue
        # Nodes sharing ONE value position (the flattener unified veh[i] and veh[j])
        var byPos: Table[int, seq[int]]
        for i in 0..<ctc.n:
            let dp = ctc.departurePositions[i]
            if dp >= 0: byPos.mgetOrPut(dp, @[]).add(i)
        for dp, ns in byPos.pairs:
            if ns.len != 2: continue
            let key = (circ, min(ns[0], ns[1]), max(ns[0], ns[1]))
            if key in seen: continue
            let cc = state.circuitConstraints[circ]
            if state.sharedDomain[][cc.positionArray[ns[0]]].len <= 1 or
               state.sharedDomain[][cc.positionArray[ns[1]]].len <= 1: continue
            seen.incl(key)
            state.tourPairs.add(key)
        for c in state.constraints:
            if c.stateType != RelationalType: continue
            if c.positions.len != 2: continue
            var ns: seq[int]
            for p in c.positions.items:
                if p in nodeOfPos: ns.add(nodeOfPos[p])
            if ns.len != 2 or ns[0] == ns[1]: continue
            let key = (circ, min(ns[0], ns[1]), max(ns[0], ns[1]))
            if key in seen: continue
            # both endpoints must be movable (variable successor arcs)
            let cc = state.circuitConstraints[circ]
            if state.sharedDomain[][cc.positionArray[ns[0]]].len <= 1 or
               state.sharedDomain[][cc.positionArray[ns[1]]].len <= 1: continue
            seen.incl(key)
            state.tourPairs.add(key)
    if (state.verbose and state.id == 0) or existsEnv("CRUSHER_DEBUG_CIRCUIT"):
        echo "[Init] Tour pair moves: " & $state.tourPairs.len & " linked node pairs"

proc tryPairTourMoves[T](state: TabuState[T]): bool =
    ## Relocate a linked node pair together on a valid circuit: move a after u,
    ## then b within the next few nodes after a (same route), both orders.
    ## Six successor changes scored by lean simulate-and-restore; the best
    ## strictly improving one is committed.
    if not state.tourPairsBuilt: state.buildTourPairs()
    if state.tourPairs.len == 0: return false
    const MAX_EVALS = 2500
    const AHEAD = 6
    var evals = 0
    var bestDelta = 0
    var bestChanges: seq[(int, T)]
    var order = toSeq(0..<state.tourPairs.len)
    shuffle(order)
    var changes: seq[(int, T)]     # (position, old value) for restore
    for pi in order:
        if evals >= MAX_EVALS: break
        let (circ, na, nb) = state.tourPairs[pi]
        let cc = state.circuitConstraints[circ]
        if cc.cost != 0: continue
        let n = cc.n
        let off = cc.valueOffset
        template succOf(v: int): int = int(state.assignment[cc.positionArray[v]]) - off
        template setSucc(v, w: int) =
            let pp = cc.positionArray[v]
            changes.add((pp, state.assignment[pp]))
            state.assignValueLean(pp, T(w + off))
        proc predOf(state: TabuState[T], cc: CircuitConstraint[T], v: int): int =
            for k in 0..<cc.n:
                if int(state.assignment[cc.positionArray[k]]) - cc.valueOffset == v: return k
            -1
        for (x, y) in [(na, nb), (nb, na)]:
            if evals >= MAX_EVALS: break
            var us = toSeq(0..<n)
            shuffle(us)
            for u in us:
                if evals >= MAX_EVALS: break
                if u == x or u == y: continue
                for k in 0..<AHEAD:
                    if evals >= MAX_EVALS: break
                    changes.setLen(0)
                    let before = state.cost
                    var ok = true
                    # 1) remove x and y from the tour (y first if adjacent handled by preds)
                    for z in [x, y]:
                        let pz = state.predOf(cc, z)
                        let sz = succOf(z)
                        if pz < 0 or state.domIdx(cc.positionArray[pz], T(sz + off)) < 0:
                            ok = false
                            break
                        setSucc(pz, sz)
                        setSucc(z, z)            # detached (self loop placeholder)
                    # 2) insert x after u, then y after the k-th node following x
                    if ok:
                        let su = succOf(u)
                        if state.domIdx(cc.positionArray[u], T(x + off)) < 0 or
                           state.domIdx(cc.positionArray[x], T(su + off)) < 0:
                            ok = false
                        else:
                            setSucc(u, x)
                            setSucc(x, su)
                            var w = x
                            for step in 0..<k:
                                w = succOf(w)
                                if w == x: break
                            let sw = succOf(w)
                            if state.domIdx(cc.positionArray[w], T(y + off)) < 0 or
                               state.domIdx(cc.positionArray[y], T(sw + off)) < 0:
                                ok = false
                            else:
                                setSucc(w, y)
                                setSucc(y, sw)
                    inc evals
                    let delta = state.cost - before
                    let valid = ok and cc.cost == 0
                    var finalVals: seq[(int, T)]
                    if valid and delta < bestDelta:
                        for (pp, _) in changes: finalVals.add((pp, state.assignment[pp]))
                    for ci in countdown(changes.len - 1, 0):
                        state.assignValueLean(changes[ci][0], changes[ci][1])
                    if valid and delta < bestDelta:
                        bestDelta = delta
                        bestChanges = finalVals
                if bestDelta < 0: break
            if bestDelta < 0: break
        if bestDelta < 0: break
    if bestChanges.len == 0: return false
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    # commit the final successor values (dedup: last write per position wins)
    var finalOf: Table[int, T]
    var posOrder: seq[int]
    for (pp, v) in bestChanges:
        if pp notin finalOf: posOrder.add(pp)
        finalOf[pp] = v
    for pp in posOrder:
        let oldIdx = state.domIdx(pp, state.assignment[pp])
        if oldIdx >= 0 and not state.isLazy[pp]:
            state.tabu[pp][oldIdx] = tabuTenure
    for pp in posOrder:
        if state.assignment[pp] != finalOf[pp]:
            state.commitValue(pp, finalOf[pp])
    return true
