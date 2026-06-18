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
                    if state.domainIndex[pb].getOrDefault(valA, -1) < 0: continue
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
    let idxA = state.domainIndex[pa].getOrDefault(valA, -1)
    if idxA >= 0 and not state.isLazy[pa]:
        state.tabu[pa][idxA] = tabuTenure
    let idxB = state.domainIndex[pb].getOrDefault(valB, -1)
    if idxB >= 0 and not state.isLazy[pb]:
        state.tabu[pb][idxB] = tabuTenure
    state.assignValue(pa, valB)
    state.assignValue(pb, valA)
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
        let iv = b.indexExpression.evaluate(state.assignment)
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
    let idxA = state.domainIndex[ipA].getOrDefault(oldA, -1)
    if idxA >= 0 and not state.isLazy[ipA]: state.tabu[ipA][idxA] = tabuTenure
    let idxB = state.domainIndex[ipB].getOrDefault(oldB, -1)
    if idxB >= 0 and not state.isLazy[ipB]: state.tabu[ipB][idxB] = tabuTenure
    state.assignValue(ipA, ivA)
    state.assignValue(ipB, ivB)
    state.circuitMergesApplied += 1
    return true
