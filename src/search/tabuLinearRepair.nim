## Linear equality repair via iterative relaxation (Gauss-Seidel style).
## Included from tabu.nim — not a standalone module.
##
## Provides two entry points:
## 1. repairLinearEqualities: for initialization, fixes flow conservation violations
## 2. tryLinearRepairMoves: for use during search stagnation, coordinates multi-variable
##    adjustments on violated EqualTo constraints

proc nearestDomainValue[T](dom: seq[T], target: T): T =
    ## Snap target to the nearest value in a sorted domain.
    if target <= dom[0]: return dom[0]
    if target >= dom[^1]: return dom[^1]
    let idx = algorithm.lowerBound(dom, target)
    # idx is the first position where dom[idx] >= target
    if dom[idx] == target: return target
    # Choose the closer of dom[idx-1] and dom[idx]
    if target - dom[idx - 1] <= dom[idx] - target:
        return dom[idx - 1]
    else:
        return dom[idx]

proc repairLinearEqualities*[T](state: TabuState[T], verbose: bool, id: int) =
    ## Initialization repair: iteratively fix violated EqualTo constraints.
    ## Skips if constraints are already satisfied.
    let carray = state.carray

    type
        EqTerm = tuple[pos: int, coeff: T]
        EqInfo = object
            searchTerms: seq[EqTerm]
            allTerms: seq[EqTerm]
            constant: T
            rhs: T

    var eqInfos: seq[EqInfo]

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo:
            continue
        if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue

        var info = EqInfo(
            constant: rc.leftExpr.sumExpr.constant,
            rhs: rc.rightExpr.constantValue
        )
        var hasSearch = false
        for pos, coeff in rc.leftExpr.sumExpr.coefficient.pairs:
            info.allTerms.add((pos: pos, coeff: coeff))
            if pos notin carray.channelPositions and pos notin carray.fixedPositions:
                info.searchTerms.add((pos: pos, coeff: coeff))
                hasSearch = true

        if hasSearch:
            eqInfos.add(info)

    if eqInfos.len == 0:
        return

    # Check initial total residual; skip if already near-feasible
    var initialResidual: T = 0
    for info in eqInfos:
        var r = info.constant - info.rhs
        for term in info.allTerms:
            r += term.coeff * state.assignment[term.pos]
        initialResidual += abs(r)

    if initialResidual == T(0):
        return

    # Gauss-Seidel passes
    const MaxPasses = 50
    var nAdjustments = 0
    var prevResidual = initialResidual

    for pass in 0..<MaxPasses:
        var passImproved = false

        for i in 0..<eqInfos.len:
            let info = eqInfos[i]

            var residual = info.constant - info.rhs
            for term in info.allTerms:
                residual += term.coeff * state.assignment[term.pos]

            if residual == T(0):
                continue

            var bestPos = -1
            var bestNewVal: T = 0
            var bestReduction: T = 0

            for term in info.searchTerms:
                let pos = term.pos
                let coeff = term.coeff
                if coeff == T(0): continue

                let dom = state.sharedDomain[][pos]
                if dom.len == 0: continue

                let oldVal = state.assignment[pos]
                let idealDelta = -(residual div coeff)
                let idealNewVal = oldVal + idealDelta
                let clampedVal = nearestDomainValue(dom, idealNewVal)
                let actualDelta = clampedVal - oldVal
                if actualDelta == T(0): continue

                let reduction = abs(coeff * actualDelta)
                if reduction > bestReduction:
                    bestReduction = reduction
                    bestPos = pos
                    bestNewVal = clampedVal

            if bestPos >= 0:
                state.assignment[bestPos] = bestNewVal
                inc nAdjustments
                passImproved = true

        if not passImproved:
            break

        if pass mod 10 == 9:
            var totalResidual: T = 0
            for info in eqInfos:
                var r = info.constant - info.rhs
                for term in info.allTerms:
                    r += term.coeff * state.assignment[term.pos]
                totalResidual += abs(r)
            if totalResidual >= prevResidual:
                break
            prevResidual = totalResidual

    if nAdjustments > 0 and verbose and id == 0:
        var totalResidual: T = 0
        for info in eqInfos:
            var r = info.constant - info.rhs
            for term in info.allTerms:
                r += term.coeff * state.assignment[term.pos]
            totalResidual += abs(r)
        echo "[Init] Linear equality repair: " & $eqInfos.len & " equations, " &
             $nAdjustments & " adjustments, residual " & $initialResidual &
             " -> " & $totalResidual


proc repairChannelInequalities*[T](state: TabuState[T], verbose: bool, id: int) =
    ## Initialization repair for graduated `≥`/`≤` inequalities whose SumExpr
    ## consists entirely of channel positions — the case the standard
    ## `repairLinearEqualities` skips because it has no search-position term to
    ## adjust. Comes up in bin-packing-style models where the bin-capacity
    ## bound is `available − Σ_p t_pg ≥ 0` and every t_pg is an indicator-product
    ## channel; the channel positions are not directly assignable, so we
    ## instead iterate every search position in the model and pick the move
    ## (search-position + new domain value) whose full cost delta best reduces
    ## the global cost.
    ##
    ## Three phases — single, pair, triple greedy descent — each run until
    ## exhaustion, with cap-bounded scans for the higher-arity phases. Cheap
    ## relative to the main tabu loop (no tabu-list bookkeeping) and only run
    ## at init, so it's not in the per-iteration hot path.
    let carray = state.carray

    # Inverse groups force changes at peer positions when one of their members
    # is reassigned. Pair/triple search captures `old2 = state.assignment[p2]`
    # *after* a lean assign of p1; if p1 is in an inverse group covering p2,
    # `old2` is the post-forced value, not the original, and the eventual
    # revert can't restore the true initial state. Bailing out is safer than
    # a partial fix — the standard tabu loop handles the inverse-group case.
    if state.inverseEnabled: return

    var hasChannelInequality = false
    for constraint in state.constraints:
        if constraint.stateType != RelationalType: continue
        let rc = constraint.relationalState
        if rc.relation notin {GreaterThanEq, LessThanEq}: continue
        if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased: continue
        if rc.rightExpr.kind != ConstantExpr: continue
        # Confirm the SumExpr's coefficient table is all-channel — the case
        # `repairLinearEqualities` already covered handles search-position slacks.
        var allChannel = true
        for pos, _ in rc.leftExpr.sumExpr.coefficient.pairs:
            if pos notin carray.channelPositions and pos notin carray.fixedPositions:
                allChannel = false; break
        if allChannel:
            hasChannelInequality = true
            break
    if not hasChannelInequality: return

    let initialCost = state.cost
    if initialCost == 0: return

    const MaxSingleScans = 30
    const MaxPairScans = 100
    const MaxPairCandidates = 200_000  # cap (positions × domain)² evaluations
    var nSingle = 0
    var nPair = 0

    # Phase 1: greedy single-flip pre-pass.
    for scan in 0..<MaxSingleScans:
        var bestPos = -1
        var bestNewVal: T = 0
        var bestDelta = 0

        for pos in carray.allSearchPositions():
            let dom = state.sharedDomain[][pos]
            if dom.len < 2: continue
            let oldVal = state.assignment[pos]
            for v in dom:
                if v == oldVal: continue
                let delta = state.costDelta(pos, v)
                if delta < bestDelta:
                    bestDelta = delta
                    bestPos = pos
                    bestNewVal = v

        if bestPos < 0: break
        state.assignValue(bestPos, bestNewVal)
        state.updateNeighborPenalties(bestPos)
        inc nSingle
        if state.cost == 0: break

    # Phase 2: greedy 2-flip pre-pass. Single flips give delta ≥ 0 at this
    # point (we'd have moved already otherwise) — typical of bin-packing
    # plateaus where moving one person from an overflowing bin requires
    # someone else to move too. A naive O(N²·D²) scan is bounded by
    # MaxPairCandidates so it stays tractable on larger instances.
    if state.cost > 0:
        for scan in 0..<MaxPairScans:
            let scanStartCost = state.cost
            var bestP1, bestP2 = -1
            var bestV1, bestV2: T = 0
            var bestPairDelta = 0
            var nEvals = 0
            block searchPair:
                var positions: seq[int]
                for p in carray.allSearchPositions():
                    positions.add(p)
                for i in 0..<positions.len:
                    let p1 = positions[i]
                    let dom1 = state.sharedDomain[][p1]
                    if dom1.len < 2: continue
                    let old1 = state.assignment[p1]
                    for v1 in dom1:
                        if v1 == old1: continue
                        # Apply p1 ← v1 tentatively (lean: no penalty bookkeeping).
                        # state.cost will reflect the cost after this move only;
                        # adding costDelta(p2, v2) from this transient state gives
                        # the cost after both moves, and subtracting scanStartCost
                        # yields the joint-move delta.
                        state.assignValueLean(p1, v1)
                        for j in (i+1)..<positions.len:
                            let p2 = positions[j]
                            let dom2 = state.sharedDomain[][p2]
                            if dom2.len < 2: continue
                            let old2 = state.assignment[p2]
                            for v2 in dom2:
                                if v2 == old2: continue
                                let pairDelta = state.cost + state.costDelta(p2, v2) - scanStartCost
                                if pairDelta < bestPairDelta:
                                    bestPairDelta = pairDelta
                                    bestP1 = p1; bestV1 = v1
                                    bestP2 = p2; bestV2 = v2
                                inc nEvals
                                if nEvals >= MaxPairCandidates:
                                    state.assignValueLean(p1, old1)
                                    break searchPair
                        # Revert p1.
                        state.assignValueLean(p1, old1)

            if bestP1 < 0: break
            # Apply the winning pair move.
            state.assignValue(bestP1, bestV1)
            state.updateNeighborPenalties(bestP1)
            state.assignValue(bestP2, bestV2)
            state.updateNeighborPenalties(bestP2)
            inc nPair
            if state.cost == 0: break

    # Phase 3: greedy 3-flip pre-pass when pair flips have plateaued. Covers
    # cases like "rotate three persons across three bins to absorb a residual
    # 1-unit overflow" that 1- and 2-flip moves can't reach. Capped tightly
    # because a full O(N³·D³) scan is expensive — for 20-position models with
    # domain ~10 it's ~10⁸ evaluations, so we sample triples and fall back as
    # soon as the cap is hit. Each scan rotates the position list by a stride
    # so high-index positions still anchor triples on later scans (without the
    # rotation, the cap always trips before they're reached).
    const MaxTripleScans = 5
    const MaxTripleCandidates = 5_000_000
    var nTriple = 0
    if state.cost > 0:
        var basePositions: seq[int]
        for p in carray.allSearchPositions():
            basePositions.add(p)
        let rotateStride = max(1, basePositions.len div MaxTripleScans)
        for scan in 0..<MaxTripleScans:
            let scanStartCost = state.cost
            var bestP1, bestP2, bestP3 = -1
            var bestV1, bestV2, bestV3: T = 0
            var bestTripleDelta = 0
            var nEvals = 0
            block searchTriple:
                var positions = newSeq[int](basePositions.len)
                if basePositions.len > 0:
                    let offset = (scan * rotateStride) mod basePositions.len
                    for ii in 0..<basePositions.len:
                        positions[ii] = basePositions[(ii + offset) mod basePositions.len]
                for i in 0..<positions.len:
                    let p1 = positions[i]
                    let dom1 = state.sharedDomain[][p1]
                    if dom1.len < 2: continue
                    let old1 = state.assignment[p1]
                    for v1 in dom1:
                        if v1 == old1: continue
                        state.assignValueLean(p1, v1)
                        for j in (i+1)..<positions.len:
                            let p2 = positions[j]
                            let dom2 = state.sharedDomain[][p2]
                            if dom2.len < 2: continue
                            let old2 = state.assignment[p2]
                            for v2 in dom2:
                                if v2 == old2: continue
                                state.assignValueLean(p2, v2)
                                for k in (j+1)..<positions.len:
                                    let p3 = positions[k]
                                    let dom3 = state.sharedDomain[][p3]
                                    if dom3.len < 2: continue
                                    let old3 = state.assignment[p3]
                                    for v3 in dom3:
                                        if v3 == old3: continue
                                        let tripleDelta = state.cost +
                                            state.costDelta(p3, v3) - scanStartCost
                                        if tripleDelta < bestTripleDelta:
                                            bestTripleDelta = tripleDelta
                                            bestP1 = p1; bestV1 = v1
                                            bestP2 = p2; bestV2 = v2
                                            bestP3 = p3; bestV3 = v3
                                        inc nEvals
                                        if nEvals >= MaxTripleCandidates:
                                            state.assignValueLean(p2, old2)
                                            state.assignValueLean(p1, old1)
                                            break searchTriple
                                state.assignValueLean(p2, old2)
                        state.assignValueLean(p1, old1)

            if bestP1 < 0: break
            state.assignValue(bestP1, bestV1)
            state.updateNeighborPenalties(bestP1)
            state.assignValue(bestP2, bestV2)
            state.updateNeighborPenalties(bestP2)
            state.assignValue(bestP3, bestV3)
            state.updateNeighborPenalties(bestP3)
            inc nTriple
            if state.cost == 0: break

    if (nSingle > 0 or nPair > 0 or nTriple > 0) and verbose and id == 0:
        echo "[Init] Channel-inequality repair: " & $nSingle &
             " single + " & $nPair & " pair + " & $nTriple &
             " triple adjustments, cost " & $initialCost & " -> " & $state.cost


proc tryLinearRepairMoves*[T](state: TabuState[T]): bool =
    ## During search: find violated EqualTo constraints and make coordinated
    ## single-position adjustments via assignValue to reduce violations.
    ## Returns true if any improvement was made.
    let carray = state.carray
    var improved = false

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo or not rc.graduated:
            continue
        if rc.computeCost(rc.leftValue, rc.rightValue) == 0:
            continue  # Already satisfied
        if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue

        let residual = rc.leftValue - rc.rightValue
        if residual == 0:
            continue

        # Find the best search position to adjust
        var bestPos = -1
        var bestNewVal: T = 0
        var bestCostDelta = 0  # Must be negative to improve

        for pos, coeff in rc.leftExpr.sumExpr.coefficient.pairs:
            if coeff == T(0): continue
            if pos in carray.channelPositions or pos in carray.fixedPositions:
                continue

            let dom = state.sharedDomain[][pos]
            if dom.len == 0: continue

            let oldVal = state.assignment[pos]
            let idealDelta = -(T(residual) div coeff)
            let idealNewVal = oldVal + idealDelta
            let clampedVal = nearestDomainValue(dom, idealNewVal)
            if clampedVal == oldVal: continue

            # Evaluate full cost delta for this move
            let delta = state.costDelta(pos, clampedVal)
            if delta < bestCostDelta:
                bestCostDelta = delta
                bestPos = pos
                bestNewVal = clampedVal

        if bestPos >= 0 and bestCostDelta < 0:
            state.assignValue(bestPos, bestNewVal)
            state.updateNeighborPenalties(bestPos)
            improved = true

    return improved


proc tryCompoundCountRepair*[T](state: TabuState[T]): bool =
    ## Compound repair for graduated EqualTo on bool/binary sums:
    ## when single-position flips give delta=0 (because flipping a position
    ## breaks an implication that was previously satisfied by the other
    ## endpoint), try flipping pairs of positions together.
    ##
    ## Use case: SFC-style problems where `selected_nodes[v]` is search and
    ## `link_selection[arc] = 1 → selected_nodes[v] = 1` implications mean
    ## the count constraint can only be reduced by flipping (selected_nodes[v],
    ## incident link_selection[arc]) pairs together.
    let carray = state.carray
    var improved = false
    const MAX_PARTNERS_PER_ANCHOR = 64
    const MAX_ANCHORS = 200

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo or not rc.graduated:
            continue
        if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue
        let sumExpr = rc.leftExpr.sumExpr
        let target = rc.rightValue
        let currentSum = rc.leftValue
        let residual = currentSum - target
        if residual == 0:
            continue

        # Build anchor candidates: search positions whose flip would reduce |residual|.
        # For coeff=±1 binary positions, "reducing" requires flipping in the right direction.
        var anchors: seq[int] = @[]
        for pos, coeff in sumExpr.coefficient.pairs:
            if abs(coeff) != 1: continue
            if pos in carray.fixedPositions or pos in carray.channelPositions: continue
            let dom = state.sharedDomain[][pos]
            if dom.len < 2: continue
            # Verify binary domain {0, 1} for compound move semantics
            if dom[0] != 0 or dom[^1] != 1 or dom.len != 2: continue
            let cv = state.assignment[pos]
            # Flipping pos contributes (-coeff*cv) to the sum if going to 0,
            # or (+coeff*(1-cv)) if going to 1. For sum > target (residual > 0),
            # we want to decrease sum; for sum < target, increase.
            let flipDelta = if cv == 1: -coeff else: coeff
            # Helpful flip: residual and flipDelta have opposite signs
            if (residual > 0 and flipDelta < 0) or (residual < 0 and flipDelta > 0):
                anchors.add(pos)

        if anchors.len == 0: continue
        # Sample anchors to bound work
        if anchors.len > MAX_ANCHORS:
            shuffle(anchors)
            anchors.setLen(MAX_ANCHORS)

        var bestDelta = 0
        var bestMove: seq[(int, T)]  # (pos, newVal) for accepted compound move

        for anchor in anchors:
            let oldA = state.assignment[anchor]
            let newA: T = if oldA == 0: T(1) else: T(0)
            let origCost = state.cost

            # Apply anchor flip
            state.assignValueLean(anchor, newA)

            # Greedy N-flip: iteratively flip positions that reduce cost.
            # Cap at MAX_COMPOUND_SIZE additional flips beyond the anchor.
            var compoundFlips: seq[(int, T)]  # (pos, oldVal) for revert
            const MAX_COMPOUND_SIZE = 6
            var stepImproved = true
            while stepImproved and compoundFlips.len < MAX_COMPOUND_SIZE:
                stepImproved = false
                # Find broken constraints: those involving anchor or any compound position
                # whose current penalty > 0 (i.e., violated after our flips).
                # For channel positions, also include upstream search positions that
                # can change them — those are the actual flippable partners.
                var brokenSet: HashSet[int]
                proc addPositions(state: TabuState[T], carray: ConstrainedArray[T],
                                  bs: var HashSet[int], pos: int, exclude: int) =
                    for c2 in state.constraintsAtPosition[pos]:
                        if c2.penalty() > 0:
                            for q in c2.positions:
                                if q == exclude: continue
                                if q in carray.channelPositions:
                                    if q in state.channelDepPosForChannel:
                                        for src in state.channelDepPosForChannel[q]:
                                            bs.incl(src)
                                else:
                                    bs.incl(q)
                state.addPositions(carray, brokenSet, anchor, anchor)
                for (cp, _) in compoundFlips:
                    state.addPositions(carray, brokenSet, cp, cp)

                # Also follow channel-dep reachability from each compound position:
                # constraints involving derived bools (e.g., reified bool intermediates)
                # may not appear in constraintsAtPosition for the underlying search var.
                proc addChannelDepPositions(state: TabuState[T], carray: ConstrainedArray[T],
                                            bs: var HashSet[int], pos: int, exclude: int) =
                    if pos notin state.channelDepConstraintsForPos: return
                    for c2 in state.channelDepConstraintsForPos[pos]:
                        if c2.penalty() > 0:
                            for q in c2.positions:
                                if q == exclude: continue
                                if q in carray.channelPositions:
                                    if q in state.channelDepPosForChannel:
                                        for src in state.channelDepPosForChannel[q]:
                                            bs.incl(src)
                                else:
                                    bs.incl(q)
                state.addChannelDepPositions(carray, brokenSet, anchor, anchor)
                for (cp, _) in compoundFlips:
                    state.addChannelDepPositions(carray, brokenSet, cp, cp)

                # Among broken-constraint positions, find the best flip that reduces cost.
                # Strict improvement only (stepDelta < 0) to avoid thrashing.
                var stepBestDelta = 0
                var stepBestPos = -1
                var stepBestNewVal: T = 0
                var stepCount = 0
                for src in brokenSet.items:
                    var alreadyFlipped = false
                    for (cp, _) in compoundFlips:
                        if cp == src: alreadyFlipped = true
                    if alreadyFlipped or src == anchor: continue
                    if src in carray.fixedPositions or src in carray.channelPositions: continue
                    let ds = state.sharedDomain[][src]
                    if ds.len != 2 or ds[0] != 0 or ds[^1] != 1: continue
                    let oldS = state.assignment[src]
                    let newS: T = if oldS == 0: T(1) else: T(0)
                    let beforeCost = state.cost
                    state.assignValueLean(src, newS)
                    let stepDelta = state.cost - beforeCost
                    if stepDelta < stepBestDelta:
                        stepBestDelta = stepDelta
                        stepBestPos = src
                        stepBestNewVal = newS
                    state.assignValueLean(src, oldS)
                    stepCount += 1
                    if stepCount >= MAX_PARTNERS_PER_ANCHOR: break

                if stepBestPos >= 0:
                    let oldS = state.assignment[stepBestPos]
                    state.assignValueLean(stepBestPos, stepBestNewVal)
                    compoundFlips.add((stepBestPos, oldS))
                    stepImproved = true

            let totalDelta = state.cost - origCost
            if totalDelta < bestDelta:
                bestDelta = totalDelta
                # Snapshot the entire compound move
                bestMove = @[(anchor, newA)]
                for (cp, ov) in compoundFlips:
                    let newCp: T = if ov == 0: T(1) else: T(0)
                    bestMove.add((cp, newCp))

            # Revert all compound flips (in reverse order) and the anchor
            for i in countdown(compoundFlips.len - 1, 0):
                let (cp, ov) = compoundFlips[i]
                state.assignValueLean(cp, ov)
            state.assignValueLean(anchor, oldA)

        if bestDelta < 0 and bestMove.len > 0:
            for (pos, newVal) in bestMove:
                state.assignValue(pos, newVal)
                state.updateNeighborPenalties(pos)
            improved = true

    return improved
