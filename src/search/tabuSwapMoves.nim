## Swap move initialization and evaluation.
## Included from tabu.nim — not a standalone module.

proc initSwapStructures[T](state: TabuState[T]) =
    ## Detect binary (0/1) positions and build swap neighbor adjacency.
    ## Two binary positions are swap neighbors if they share at least one constraint.
    state.swapEnabled = false
    state.binaryPositions = @[]
    state.binaryPosIndex = initTable[int, int]()
    state.swapNeighbors = @[]
    state.sharedConstraints = initTable[(int,int), seq[StatefulConstraint[T]]]()

    # Find all search positions with domain exactly {0, 1}
    for pos in state.searchPositions:
        let domain {.cursor.} = state.sharedDomain[][pos]
        if domain.len == 2 and
           ((domain[0] == 0 and domain[1] == 1) or (domain[0] == 1 and domain[1] == 0)):
            state.binaryPosIndex[pos] = state.binaryPositions.len
            state.binaryPositions.add(pos)

    if state.binaryPositions.len < 2:
        return

    # For each constraint, collect binary positions it covers
    # Then build swap neighbor pairs from positions sharing a constraint
    let binaryPosSet = block:
        var s = initPackedSet[int]()
        for p in state.binaryPositions: s.incl(p)
        s

    state.swapNeighbors = newSeq[seq[int]](state.binaryPositions.len)

    # Use a set per binary index to avoid duplicate neighbors
    var neighborSets = newSeq[PackedSet[int]](state.binaryPositions.len)
    for i in 0..<state.binaryPositions.len:
        neighborSets[i] = initPackedSet[int]()

    const maxBinaryPerConstraint = 350  # skip constraints with too many binary positions
    # Global pair budget: the sharedConstraints table holds one entry per pair, so
    # tens of thousands of binary positions in mid-sized constraints explode it
    # (warehouse: 18M pairs, ~20s and gigabytes per state). Smallest constraints
    # first until the budget is spent.
    const maxTotalSwapPairs = 2_000_000
    var candidates: seq[(int, int)]   # (binary count, constraint index)
    var binaryLists = newSeq[seq[int]](state.constraints.len)
    var pairBudget = 0
    for ci, constraint in state.constraints:
        var binaryInConstraint: seq[int] = @[]
        for pos in constraint.positions.items:
            if pos in binaryPosSet:
                binaryInConstraint.add(pos)
        if binaryInConstraint.len < 2 or binaryInConstraint.len > maxBinaryPerConstraint:
            continue
        pairBudget += binaryInConstraint.len * (binaryInConstraint.len - 1) div 2
        candidates.add((binaryInConstraint.len, ci))
        binaryLists[ci] = binaryInConstraint
    if pairBudget > maxTotalSwapPairs:
        candidates.sort()
    var pairsUsed = 0
    for (k, ci) in candidates:
        let constraint = state.constraints[ci]
        let binaryInConstraint {.cursor.} = binaryLists[ci]
        pairsUsed += k * (k - 1) div 2
        if pairsUsed > maxTotalSwapPairs:
            break

        # Add all pairs as swap neighbors and record shared constraints
        for i in 0..<binaryInConstraint.len:
            for j in (i+1)..<binaryInConstraint.len:
                let p1 = binaryInConstraint[i]
                let p2 = binaryInConstraint[j]
                let bi1 = state.binaryPosIndex[p1]
                let bi2 = state.binaryPosIndex[p2]
                neighborSets[bi1].incl(bi2)
                neighborSets[bi2].incl(bi1)

                let key = if p1 < p2: (p1, p2) else: (p2, p1)
                if key notin state.sharedConstraints:
                    state.sharedConstraints[key] = @[constraint]
                else:
                    state.sharedConstraints[key].add(constraint)

    # Convert neighbor sets to seqs
    var totalPairs = 0
    for bi in 0..<state.binaryPositions.len:
        state.swapNeighbors[bi] = @[]
        for nbi in neighborSets[bi].items:
            state.swapNeighbors[bi].add(nbi)
        totalPairs += state.swapNeighbors[bi].len

    totalPairs = totalPairs div 2  # each pair counted twice

    if totalPairs > 0:
        state.swapEnabled = true
        if state.verbose and state.id == 0:
            echo "[Init] Swap moves: " & $state.binaryPositions.len & " binary positions, " & $totalPairs & " swap pairs"


proc fastSwapEvalOk[T](state: TabuState[T]): bool {.inline.} =
    ## True when a two-position double-assignment's cost delta can be computed
    ## exactly by per-constraint decomposition: no channel bindings, inverse
    ## groups, or circuit-time writebacks through which the change could
    ## propagate beyond the constraints at the two positions.
    ## Channels that no constraint reads (hasChannelDeps false: no constraint
    ## has a channel position, or all channel-dep deltas are tautological)
    ## cannot carry cost, so their presence does not block the decomposition.
    not state.hasChannelDeps and not state.inverseEnabled and
        state.circuitTimePropConstraints.len == 0

proc exactSwapDelta[T](state: TabuState[T], p1, p2: int, newVal1, newVal2: T): int =
    ## Exact cost delta for simultaneously assigning p1→newVal1 and p2→newVal2.
    ## Decomposes into per-constraint deltas: moveDelta for constraints seeing
    ## one position, joint apply/undo evaluation for constraints seeing both.
    ## Equivalent to (but much cheaper than) simulating via 4x assignValueLean:
    ## no violation-count churn, no channel scans, no per-position penalty calls.
    ## Only valid when fastSwapEvalOk holds.
    for c in state.constraintsAtPosition[p1]:
        if p2 in c.positions:
            # Shared constraint: joint delta
            if c.stateType == AllDifferentType and
               c.allDifferentState.evalMethod == PositionBased and
               newVal1 == state.assignment[p2] and newVal2 == state.assignment[p1]:
                # Pure value exchange preserves value counts: joint delta is 0
                discard
            else:
                # Joint delta by sequential composition: delta(p1 move) plus
                # delta(p2 move evaluated with p1 applied). One apply/undo pair
                # instead of two.
                result += state.movePenalty(c, p1, newVal1)
                c.updatePosition(p1, newVal1)
                result += state.movePenalty(c, p2, newVal2)
                c.updatePosition(p1, state.assignment[p1])
        else:
            result += state.movePenalty(c, p1, newVal1)
    for c in state.constraintsAtPosition[p2]:
        if p1 in c.positions:
            continue  # shared: handled above
        result += state.movePenalty(c, p2, newVal2)


proc swapDelta[T](state: TabuState[T], p1, p2: int, newVal1, newVal2: T): int =
    ## Compute the cost delta for simultaneously assigning p1→newVal1 and p2→newVal2.
    ## Uses penalty maps for independent contributions and corrects for shared constraints.
    let newIdx1 = state.domIdx(p1, newVal1)
    let newIdx2 = state.domIdx(p2, newVal2)
    if newIdx1 < 0 or newIdx2 < 0:
        return high(int)

    # Start with sum of independent single-move deltas from penalty maps
    result = state.penaltyMap[p1][newIdx1] + state.penaltyMap[p2][newIdx2]

    # Correct for shared constraints where independent deltas double-count
    let key = if p1 < p2: (p1, p2) else: (p2, p1)
    if key in state.sharedConstraints:
        for constraint in state.sharedConstraints[key]:
            # Get independent deltas from per-constraint penalty cache
            let localIdx1 = state.findLocalConstraintIdx(p1, constraint)
            let localIdx2 = state.findLocalConstraintIdx(p2, constraint)
            let indep1 = state.constraintPenalties[p1][localIdx1][newIdx1]
            let indep2 = state.constraintPenalties[p2][localIdx2][newIdx2]

            # Compute joint delta for both changes simultaneously
            var jointDelta: int
            if constraint.stateType == AllDifferentType and
               newVal1 == state.assignment[p2] and newVal2 == state.assignment[p1]:
                # Fast path: exchanging values between two positions preserves
                # the alldifferent constraint. Joint delta is 0.
                jointDelta = 0
            elif constraint.stateType == RelationalType:
                let rc = constraint.relationalState
                # Fast path for relational constraints with linear expressions
                var leftOk = true
                var rightOk = true
                var leftCoeff1, leftCoeff2, rightCoeff1, rightCoeff2: T

                case rc.leftExpr.kind
                of SumExpr:
                    let s = rc.leftExpr.sumExpr
                    if s.evalMethod == PositionBased:
                        leftCoeff1 = s.coefficient.getOrDefault(p1, T(0))
                        leftCoeff2 = s.coefficient.getOrDefault(p2, T(0))
                    else:
                        leftOk = false
                of ConstantExpr:
                    leftCoeff1 = 0
                    leftCoeff2 = 0
                else:
                    leftOk = false

                case rc.rightExpr.kind
                of SumExpr:
                    let s = rc.rightExpr.sumExpr
                    if s.evalMethod == PositionBased:
                        rightCoeff1 = s.coefficient.getOrDefault(p1, T(0))
                        rightCoeff2 = s.coefficient.getOrDefault(p2, T(0))
                    else:
                        rightOk = false
                of ConstantExpr:
                    rightCoeff1 = 0
                    rightCoeff2 = 0
                else:
                    rightOk = false

                if leftOk and rightOk:
                    let oldVal1 = state.assignment[p1]
                    let oldVal2 = state.assignment[p2]
                    let newLeft = rc.leftValue + leftCoeff1 * (newVal1 - oldVal1) + leftCoeff2 * (newVal2 - oldVal2)
                    let newRight = rc.rightValue + rightCoeff1 * (newVal1 - oldVal1) + rightCoeff2 * (newVal2 - oldVal2)
                    jointDelta = rc.computeCost(newLeft, newRight) - rc.cost
                else:
                    # Fallback: simulate both changes
                    let oldVal1 = state.assignment[p1]
                    let oldVal2 = state.assignment[p2]
                    let delta1 = constraint.relationalState.moveDelta(p1, oldVal1, newVal1)
                    # Temporarily apply first change to get joint delta
                    constraint.relationalState.updatePosition(p1, newVal1)
                    let delta2 = constraint.relationalState.moveDelta(p2, oldVal2, newVal2)
                    # Restore
                    constraint.relationalState.updatePosition(p1, oldVal1)
                    jointDelta = delta1 + delta2
            else:
                # Generic fallback: simulate and restore
                let oldVal1 = state.assignment[p1]
                let oldVal2 = state.assignment[p2]
                let costBefore = constraint.penalty()
                constraint.updatePosition(p1, newVal1)
                constraint.updatePosition(p2, newVal2)
                let costAfter = constraint.penalty()
                # Restore original state
                constraint.updatePosition(p2, oldVal2)
                constraint.updatePosition(p1, oldVal1)
                jointDelta = costAfter - costBefore

            # Correction: replace independent sum with joint delta
            result += jointDelta - indep1 - indep2


proc bestSwapMoves[T](state: TabuState[T]): (seq[(int, int, T, T)], int) =
    ## Find the best swap move among binary variable pairs.
    ## Returns (moves, bestCost) where moves is a list of equally-best
    ## (p1, p2, newVal1, newVal2) tuples and bestCost is the projected cost.
    ## Only active when flow structure is detected (swap moves are designed for
    ## network flow problems; for non-flow binary variables like channeling
    ## indicators, swapping without coordinating linked variables is counterproductive).
    if not state.flowEnabled:
        return (@[], high(int))

    const MAX_SWAP_EVALUATIONS = 2000

    var
        bestSwapCost = high(int)
        moves: seq[(int, int, T, T)] = @[]
        swapsEvaluated = 0

    # Iterate binary positions, prefer violated ones
    for bi1 in 0..<state.binaryPositions.len:
        let p1 = state.binaryPositions[bi1]
        if state.violationCount[p1] == 0 and
           state.channelDepPenalties[p1].len == 0:
            continue

        let val1 = state.assignment[p1]
        let newVal1 = 1 - val1  # flip: 0→1 or 1→0

        for bi2 in state.swapNeighbors[bi1]:
            let p2 = state.binaryPositions[bi2]
            let val2 = state.assignment[p2]

            # Only swap if they have different values (one 0→1, one 1→0)
            if val1 == val2:
                continue

            # Avoid evaluating (p2,p1) when we already evaluated (p1,p2)
            if p2 < p1:
                continue

            let newVal2 = 1 - val2

            let delta = state.swapDelta(p1, p2, newVal1, newVal2)
            let newCost = state.cost + delta
            inc swapsEvaluated

            # Tabu check: swap is tabu only if BOTH legs are tabu AND no aspiration
            let newIdx1 = state.domIdx(p1, newVal1)
            let newIdx2 = state.domIdx(p2, newVal2)
            let tabu1 = newIdx1 >= 0 and not state.isLazy[p1] and state.tabu[p1][newIdx1] > state.iteration
            let tabu2 = newIdx2 >= 0 and not state.isLazy[p2] and state.tabu[p2][newIdx2] > state.iteration
            let isTabu = tabu1 and tabu2
            let aspiration = newCost < state.bestCost

            if isTabu and not aspiration:
                continue

            if newCost < bestSwapCost:
                moves = @[(p1, p2, newVal1, newVal2)]
                bestSwapCost = newCost
            elif newCost == bestSwapCost:
                moves.add((p1, p2, newVal1, newVal2))

            if swapsEvaluated >= MAX_SWAP_EVALUATIONS:
                return (moves, bestSwapCost)

            # Early exit on improvement
            if bestSwapCost < state.cost:
                return (moves, bestSwapCost)

    return (moves, bestSwapCost)


proc evalSwapPair[T](state: TabuState[T], p1, p2: int, fastEval: bool,
                     delta: var int, tabuBlocked: var bool): bool {.inline.} =
    ## Exact cost change of exchanging the values of p1 and p2. Returns false
    ## when the exchange is not allowed (equal values, value outside the other
    ## domain); `tabuBlocked` when both old values are tabu.
    let val1 = state.assignment[p1]
    let val2 = state.assignment[p2]
    if val1 == val2: return false
    let idx1 = state.domIdx(p1, val2)
    let idx2 = state.domIdx(p2, val1)
    if idx1 < 0 or idx2 < 0: return false
    tabuBlocked = (not state.isLazy[p1] and state.tabu[p1][idx1] > state.iteration) and
                  (not state.isLazy[p2] and state.tabu[p2][idx2] > state.iteration)
    # Exact swap delta: decomposed when safe, else full simulation
    if fastEval:
        delta = state.exactSwapDelta(p1, p2, val2, val1)
    else:
        let origCost = state.cost
        state.assignValueLean(p1, val2)
        state.assignValueLean(p2, val1)
        delta = state.cost - origCost
        # Restore (reverse order)
        state.assignValueLean(p2, val2)
        state.assignValueLean(p1, val1)
    true

proc applySwap[T](state: TabuState[T], p1, p2: int) =
    let oldVal1 = state.assignment[p1]
    let oldVal2 = state.assignment[p2]
    state.commitValue(p1, oldVal2)
    state.commitValue(p2, oldVal1)

    # Set tabu on old values
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    let oldIdx1 = state.domIdx(p1, oldVal1)
    if oldIdx1 >= 0 and not state.isLazy[p1]:
        state.tabu[p1][oldIdx1] = tabuTenure
    let oldIdx2 = state.domIdx(p2, oldVal2)
    if oldIdx2 >= 0 and not state.isLazy[p2]:
        state.tabu[p2][oldIdx2] = tabuTenure

template swapStopRequested[T](state: TabuState[T]): bool =
    (state.stopSignal != nil and state.stopSignal[].load()) or
        (state.searchDeadline > 0 and epochTime() > state.searchDeadline)

proc tryGeneralSwapMoves[T](state: TabuState[T]): bool =
    ## Try value-exchange swaps between search positions.
    ## Uses assignValueLean simulation for exact delta computation.
    ## Returns true if an improving swap was found and applied.
    const MAX_SWAP_EVALS = 2000

    var bestDelta = 0
    var bestSwaps: seq[(int, int)] = @[]
    var evalsCount = 0
    let fastEval = state.fastSwapEvalOk

    for i in 0..<state.searchPositions.len:
        let p1 = state.searchPositions[i]
        if state.violationCount[p1] == 0 and
           state.channelDepPenalties[p1].len == 0:
            continue
        # Swapping two successors of one valid tour splits it: tour moves cover these
        if state.onValidCtpCircuit(p1): continue

        for j in (i+1)..<state.searchPositions.len:
            let p2 = state.searchPositions[j]
            if state.onValidCtpCircuit(p2): continue
            var delta: int
            var tabuBlocked: bool
            if not state.evalSwapPair(p1, p2, fastEval, delta, tabuBlocked):
                continue

            inc evalsCount
            if (evalsCount and 63) == 0 and state.swapStopRequested():
                return false

            let aspiration = state.cost + delta < state.bestCost
            if tabuBlocked and not aspiration:
                continue

            if delta < bestDelta:
                bestDelta = delta
                bestSwaps = @[(p1, p2)]
            elif delta == bestDelta and delta < 0:
                bestSwaps.add((p1, p2))

            if evalsCount >= MAX_SWAP_EVALS:
                break
        if evalsCount >= MAX_SWAP_EVALS:
            break

    if bestSwaps.len == 0:
        return false

    # Apply the best swap
    let (p1, p2) = sample(bestSwaps)
    state.applySwap(p1, p2)
    return true


# Neighbour swaps for models above the general-swap size limit.
#
# The general scan above is all-pairs from position 0, so past ~200 search
# positions its 2000-evaluation budget never leaves the first few positions.
# Improving exchanges sit between positions that share a small constraint
# (gbac UD1, 307 courses: at a single-move local optimum all 51 improving
# swaps of 41694 pairs exchange two courses of one curriculum, i.e. two
# positions of one per-curriculum count constraint). Partners are the search
# positions sharing a constraint of at most NbSwapMaxConstraintSize positions;
# the scan resumes where the previous call stopped, and calls back off
# geometrically while they find nothing.
const NbSwapMaxConstraintSize = 64
const NbSwapMaxPartners = 256
const NbSwapMinGap = 20
const NbSwapMaxGap = 640

proc buildNeighborSwapPartners[T](state: TabuState[T]) =
    state.nbSwapBuilt = true
    state.nbSwapGap = NbSwapMinGap
    let n = state.searchPositions.len
    var isCand = newSeq[bool](state.assignment.len)
    for p in state.searchPositions:
        if p in state.carray.fixedPositions: continue
        # Two-value positions: an exchange is a double flip, which the binary
        # swap moves cover (roster_shifts_bool_small, 1450 booleans, lost
        # ~3% of its objective to these exchanges).
        if state.sharedDomain[][p].len <= 2: continue
        isCand[p] = true
    state.nbSwapPartners = newSeq[seq[int]](n)
    var total = 0
    for i, p in state.searchPositions:
        if not isCand[p]: continue
        var seen = initPackedSet[int]()
        var partners: seq[int]
        block scan:
            for c in state.constraintsAtPosition[p]:
                if c.isObjectiveBound or c.positions.len > NbSwapMaxConstraintSize:
                    continue
                for q in c.positions.items:
                    if q == p or not isCand[q] or q in seen: continue
                    seen.incl(q)
                    partners.add(q)
                    if partners.len >= NbSwapMaxPartners: break scan
        total += partners.len
        state.nbSwapPartners[i] = partners
    if total == 0:
        state.nbSwapPartners = @[]
    elif n > 0:
        state.nbSwapCursor = rand(n - 1)

proc tryNeighborSwapMoves[T](state: TabuState[T]): bool =
    ## Best improving exchange among (position, partner) pairs, scanning from
    ## the cursor for up to NbSwapMaxEvals evaluations. Same scoring, tabu and
    ## aspiration rules as tryGeneralSwapMoves.
    const NbSwapMaxEvals = 2000
    if not state.nbSwapBuilt: state.buildNeighborSwapPartners()
    let n = state.nbSwapPartners.len
    if n == 0: return false

    var bestDelta = 0
    var bestSwaps: seq[(int, int)] = @[]
    var evalsCount = 0
    let fastEval = state.fastSwapEvalOk
    let start = state.nbSwapCursor mod n
    var scanned = 0
    while scanned < n and evalsCount < NbSwapMaxEvals:
        let i = (start + scanned) mod n
        inc scanned
        let p1 = state.searchPositions[i]
        if state.nbSwapPartners[i].len == 0: continue
        if state.violationCount[p1] == 0 and
           state.channelDepPenalties[p1].len == 0:
            continue
        if state.onValidCtpCircuit(p1): continue
        for p2 in state.nbSwapPartners[i]:
            if state.onValidCtpCircuit(p2): continue
            var delta: int
            var tabuBlocked: bool
            if not state.evalSwapPair(p1, p2, fastEval, delta, tabuBlocked):
                continue
            inc evalsCount
            if (evalsCount and 63) == 0 and state.swapStopRequested():
                return false
            let aspiration = state.cost + delta < state.bestCost
            if tabuBlocked and not aspiration:
                continue
            if delta < bestDelta:
                bestDelta = delta
                bestSwaps = @[(p1, p2)]
            elif delta == bestDelta and delta < 0:
                bestSwaps.add((p1, p2))
    state.nbSwapCursor = (start + scanned) mod n
    inc state.nbSwapCalls

    if bestSwaps.len == 0:
        state.nbSwapGap = min(state.nbSwapGap * 2, NbSwapMaxGap)
        return false
    state.nbSwapGap = NbSwapMinGap
    inc state.nbSwapApplied
    let (p1, p2) = sample(bestSwaps)
    state.applySwap(p1, p2)
    return true


proc bestPartitionSwapMoves[T](state: TabuState[T]): (seq[(int, int, T, int)], int) =
    ## Find the best partition swap move. Returns (moves, bestCost) where moves
    ## is a list of equally-best (deactivate_pos, activate_pos, new_value, group_idx)
    ## tuples. Follows the same convention as bestSwapMoves: considers tabu status
    ## and aspiration, and returns ALL non-tabu moves ranked by projected cost
    ## (including worsening moves, so the tabu search can always make progress).
    if not state.partitionEnabled:
        return (@[], high(int))

    var bestCost = high(int)
    var moves: seq[(int, int, T, int)] = @[]
    let fastEval = state.fastSwapEvalOk

    for gi, group in state.partitionGroups:
        let nullVal = group.nullValue

        # Find active member
        var activePos = -1
        for pos in group.searchPositions:
            if state.assignment[pos] != nullVal:
                if activePos >= 0:
                    activePos = -1; break
                activePos = pos
        if activePos < 0: continue
        let activeVal = state.assignment[activePos]

        for pos in group.searchPositions:
            if pos == activePos: continue
            if state.assignment[pos] != nullVal: continue

            let domain {.cursor.} = state.sharedDomain[][pos]
            for newVal in domain:
                if newVal == nullVal: continue

                # Exact double-assign delta: decomposed when safe, else simulation
                var newCost: int
                if fastEval:
                    newCost = state.cost + state.exactSwapDelta(activePos, pos, nullVal, newVal)
                else:
                    state.assignValueLean(activePos, nullVal)
                    state.assignValueLean(pos, newVal)
                    newCost = state.cost
                    # Restore
                    state.assignValueLean(pos, nullVal)
                    state.assignValueLean(activePos, activeVal)

                # Tabu check: both legs must be tabu AND no aspiration
                let nullIdx = state.domIdx(activePos, nullVal)
                let newIdx = state.domIdx(pos, newVal)
                let tabu1 = nullIdx >= 0 and not state.isLazy[activePos] and
                            state.tabu[activePos][nullIdx] > state.iteration
                let tabu2 = newIdx >= 0 and not state.isLazy[pos] and
                            state.tabu[pos][newIdx] > state.iteration
                let isTabu = tabu1 and tabu2
                let aspiration = newCost < state.bestCost

                if isTabu and not aspiration:
                    continue

                if newCost < bestCost:
                    moves = @[(activePos, pos, newVal, gi)]
                    bestCost = newCost
                elif newCost == bestCost:
                    moves.add((activePos, pos, newVal, gi))

    return (moves, bestCost)


proc bestPermutationSwapMoves[T](state: TabuState[T]): (seq[(int, int, T, T)], int) =
    ## Find the best value-exchange swap within GCC/permutation groups.
    ## Uses assignValueLean for exact cost evaluation (correct with channel-dep).
    ## Filters by violated positions and caps evaluations for efficiency.
    if state.gccGroupPositions.len == 0:
        return (@[], high(int))

    let fastEval = state.fastSwapEvalOk
    var maxEvals = if state.maxPermSwapEvals > 0: state.maxPermSwapEvals else: 500
    var tSlow = 0.0
    inc state.permSwapCalls
    if not fastEval:
        # Simulated evaluation costs four assignValueLean calls per pair, each
        # propagating channels. On large groups with deep cascades (warehouse:
        # thousands of positions, 2000-pair budget) that was most of the
        # iteration time; on small groups (work-task-variation: 32 groups of
        # ~12) it is cheap and the swaps are what reach feasibility. Regulate
        # by measured share: once simulated swap evaluation has consumed more
        # than half of the search's wall time, sample sparsely until it falls
        # back below that share.
        let elapsed = epochTime() - state.startTime
        if state.permSwapSlowTime > 0.5 * elapsed:
            if state.iteration mod 4 != 0:
                inc state.permSwapThrottled
                return (@[], high(int))
            maxEvals = min(maxEvals, 128)
        tSlow = epochTime()
    defer:
        if tSlow > 0.0: state.permSwapSlowTime += epochTime() - tSlow
    var bestCost = high(int)
    var moves: seq[(int, int, T, T)] = @[]
    var evalsCount = 0

    for group in state.gccGroupPositions:
        for i in 0..<group.len:
            let p1 = group[i]
            # Only consider positions involved in violations
            if state.violationCount[p1] == 0 and
               (p1 >= state.channelDepPenalties.len or state.channelDepPenalties[p1].len == 0):
                continue
            let val1 = state.assignment[p1]

            for j in (i+1)..<group.len:
                let p2 = group[j]
                let val2 = state.assignment[p2]
                if val1 == val2: continue

                # Check domain compatibility
                let idx1 = state.domIdx(p1, val2)
                let idx2 = state.domIdx(p2, val1)
                if idx1 < 0 or idx2 < 0: continue

                # Exact swap delta: decomposed when safe, else full simulation
                var delta: int
                if fastEval:
                    delta = state.exactSwapDelta(p1, p2, val2, val1)
                else:
                    let origCost = state.cost
                    state.assignValueLean(p1, val2)
                    state.assignValueLean(p2, val1)
                    delta = state.cost - origCost
                    # Restore
                    state.assignValueLean(p2, val2)
                    state.assignValueLean(p1, val1)

                let newCost = state.cost + delta
                inc evalsCount

                # Tabu: both legs must be tabu to block
                let tabu1 = not state.isLazy[p1] and state.tabu[p1][idx1] > state.iteration
                let tabu2 = not state.isLazy[p2] and state.tabu[p2][idx2] > state.iteration
                if tabu1 and tabu2 and newCost >= state.bestCost:
                    continue

                if newCost < bestCost:
                    bestCost = newCost
                    moves = @[(p1, p2, val2, val1)]
                elif newCost == bestCost:
                    moves.add((p1, p2, val2, val1))

                if evalsCount >= maxEvals:
                    return (moves, bestCost)

            if evalsCount >= maxEvals:
                break
        if evalsCount >= maxEvals:
            break

    return (moves, bestCost)
