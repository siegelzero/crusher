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
        let domain = state.sharedDomain[][pos]
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
    for constraint in state.constraints:
        # Collect binary positions in this constraint
        var binaryInConstraint: seq[int] = @[]
        for pos in constraint.positions.items:
            if pos in binaryPosSet:
                binaryInConstraint.add(pos)

        if binaryInConstraint.len < 2:
            continue

        # Skip constraints with too many binary positions (O(n^2) pair explosion)
        if binaryInConstraint.len > maxBinaryPerConstraint:
            continue

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


proc swapDelta[T](state: TabuState[T], p1, p2: int, newVal1, newVal2: T): int =
    ## Compute the cost delta for simultaneously assigning p1→newVal1 and p2→newVal2.
    ## Uses penalty maps for independent contributions and corrects for shared constraints.
    let newIdx1 = state.domainIndex[p1].getOrDefault(newVal1, -1)
    let newIdx2 = state.domainIndex[p2].getOrDefault(newVal2, -1)
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
            if constraint.stateType == RelationalType:
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
            let newIdx1 = state.domainIndex[p1].getOrDefault(newVal1, -1)
            let newIdx2 = state.domainIndex[p2].getOrDefault(newVal2, -1)
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


proc tryGeneralSwapMoves[T](state: TabuState[T]): bool =
    ## Try value-exchange swaps between search positions.
    ## Uses assignValueLean simulation for exact delta computation.
    ## Returns true if an improving swap was found and applied.
    const MAX_SWAP_EVALS = 2000

    var bestDelta = 0
    var bestSwaps: seq[(int, int)] = @[]
    var evalsCount = 0

    for i in 0..<state.searchPositions.len:
        let p1 = state.searchPositions[i]
        if state.violationCount[p1] == 0 and
           state.channelDepPenalties[p1].len == 0:
            continue
        let val1 = state.assignment[p1]

        for j in (i+1)..<state.searchPositions.len:
            let p2 = state.searchPositions[j]
            let val2 = state.assignment[p2]
            if val1 == val2:
                continue

            # Check both values are in each other's domain
            let idx1 = state.domainIndex[p1].getOrDefault(val2, -1)
            let idx2 = state.domainIndex[p2].getOrDefault(val1, -1)
            if idx1 < 0 or idx2 < 0:
                continue
            let tabu1 = not state.isLazy[p1] and state.tabu[p1][idx1] > state.iteration
            let tabu2 = not state.isLazy[p2] and state.tabu[p2][idx2] > state.iteration

            # Simulate swap via 4x assignValueLean
            let origCost = state.cost
            state.assignValueLean(p1, val2)
            state.assignValueLean(p2, val1)
            let delta = state.cost - origCost
            # Restore (reverse order)
            state.assignValueLean(p2, val2)
            state.assignValueLean(p1, val1)

            inc evalsCount

            let aspiration = origCost + delta < state.bestCost
            if tabu1 and tabu2 and not aspiration:
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
    let oldVal1 = state.assignment[p1]
    let oldVal2 = state.assignment[p2]
    state.assignValue(p1, oldVal2)
    state.assignValue(p2, oldVal1)

    # Set tabu on old values
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    let oldIdx1 = state.domainIndex[p1].getOrDefault(oldVal1, -1)
    if oldIdx1 >= 0 and not state.isLazy[p1]:
        state.tabu[p1][oldIdx1] = tabuTenure
    let oldIdx2 = state.domainIndex[p2].getOrDefault(oldVal2, -1)
    if oldIdx2 >= 0 and not state.isLazy[p2]:
        state.tabu[p2][oldIdx2] = tabuTenure
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

            let domain = state.sharedDomain[][pos]
            for newVal in domain:
                if newVal == nullVal: continue

                # Simulate swap and compute exact cost
                state.assignValueLean(activePos, nullVal)
                state.assignValueLean(pos, newVal)
                let newCost = state.cost
                # Restore
                state.assignValueLean(pos, nullVal)
                state.assignValueLean(activePos, activeVal)

                # Tabu check: both legs must be tabu AND no aspiration
                let nullIdx = state.domainIndex[activePos].getOrDefault(nullVal, -1)
                let newIdx = state.domainIndex[pos].getOrDefault(newVal, -1)
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


proc tryGCCSwapMoves[T](state: TabuState[T]): bool =
    ## Try value-exchange swaps within GCC groups.
    ## Swapping values between positions in the same GCC group preserves
    ## GCC cardinality counts by construction, allowing the search to fix
    ## other constraints without disturbing GCC satisfaction.
    const MAX_SWAP_EVALS = 3000

    var bestDelta = 0
    var bestSwaps: seq[(int, int)] = @[]
    var evalsCount = 0

    for group in state.gccGroupPositions:
        for i in 0..<group.len:
            let p1 = group[i]
            # Only consider violated positions as sources
            if state.violationCount[p1] == 0 and
               (p1 >= state.channelDepPenalties.len or
                state.channelDepPenalties[p1].len == 0):
                continue
            let val1 = state.assignment[p1]

            for j in (i+1)..<group.len:
                let p2 = group[j]
                let val2 = state.assignment[p2]
                if val1 == val2:
                    continue

                # Check both values are in each other's domain
                let idx1 = state.domainIndex[p1].getOrDefault(val2, -1)
                let idx2 = state.domainIndex[p2].getOrDefault(val1, -1)
                if idx1 < 0 or idx2 < 0:
                    continue

                # Simulate swap via assignValueLean
                let origCost = state.cost
                state.assignValueLean(p1, val2)
                state.assignValueLean(p2, val1)
                let delta = state.cost - origCost
                # Restore
                state.assignValueLean(p2, val2)
                state.assignValueLean(p1, val1)

                inc evalsCount

                # Tabu check
                let tabu1 = not state.isLazy[p1] and state.tabu[p1][idx1] > state.iteration
                let tabu2 = not state.isLazy[p2] and state.tabu[p2][idx2] > state.iteration
                let aspiration = origCost + delta < state.bestCost
                if tabu1 and tabu2 and not aspiration:
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
        if evalsCount >= MAX_SWAP_EVALS:
            break

    if bestSwaps.len == 0:
        return false

    # Apply the best swap
    let (p1, p2) = sample(bestSwaps)
    let oldVal1 = state.assignment[p1]
    let oldVal2 = state.assignment[p2]
    state.assignValue(p1, oldVal2)
    state.assignValue(p2, oldVal1)

    # Set tabu on old values
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    let oldIdx1 = state.domainIndex[p1].getOrDefault(oldVal1, -1)
    if oldIdx1 >= 0 and not state.isLazy[p1]:
        state.tabu[p1][oldIdx1] = tabuTenure
    let oldIdx2 = state.domainIndex[p2].getOrDefault(oldVal2, -1)
    if oldIdx2 >= 0 and not state.isLazy[p2]:
        state.tabu[p2][oldIdx2] = tabuTenure
    return true
