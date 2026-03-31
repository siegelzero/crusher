## Element implied move initialization and application.
## Included from tabu.nim — not a standalone module.

proc recomputeElementImpliedDiscounts[T](state: TabuState[T]) =
    ## Recompute the penalty discount for all element index positions.
    ## For each candidate value of an index position, estimates how many element
    ## constraints can be fixed by implied moves and discounts the penalty by -1 each.
    ## This makes the solver see the benefit of compound moves before selecting them.
    if not state.elementImpliedEnabled:
        return

    let channelPos = state.carray.channelPositions

    for idxPos, constraints in state.elementImpliedMoves.pairs:
        let domain = state.sharedDomain[][idxPos]
        let dLen = domain.len
        if dLen == 0: continue

        # Initialize or reset discount seq
        if idxPos notin state.elementImpliedDiscount:
            state.elementImpliedDiscount[idxPos] = newSeq[int](dLen)
        else:
            for i in 0..<dLen:
                state.elementImpliedDiscount[idxPos][i] = 0

        for i in 0..<dLen:
            let candidateValue = domain[i]
            var discount = 0
            for constraint in constraints:
                let es = constraint.elementState
                # Evaluate what index the candidate value would produce
                var newIdx: int
                case es.evalMethod:
                of PositionBased:
                    newIdx = candidateValue
                of ExpressionBased:
                    let oldVal = es.currentAssignment.getOrDefault(idxPos, candidateValue)
                    es.currentAssignment[idxPos] = candidateValue
                    newIdx = es.indexExpression.evaluate(es.currentAssignment)
                    es.currentAssignment[idxPos] = oldVal

                let arraySize = es.getArraySize()
                if newIdx < 0 or newIdx >= arraySize:
                    continue

                # Would this element constraint be violated?
                let targetValue = es.getValueValue()
                let currentArrayValue = es.getArrayValue(newIdx)
                if currentArrayValue == targetValue:
                    continue  # Already satisfied, no discount needed

                # Can we fix it? Check if target position is a fixable variable
                var targetPos = -1
                case es.evalMethod:
                of PositionBased:
                    if es.isConstantArray: continue
                    let elem = es.arrayElements[newIdx]
                    if elem.isConstant: continue
                    targetPos = elem.variablePosition
                of ExpressionBased:
                    if es.isConstantArrayEB: continue
                    let expr = es.arrayExpressionsEB[newIdx]
                    if expr.node.kind != RefNode: continue
                    targetPos = expr.node.position

                if targetPos < 0 or targetPos in channelPos or targetPos == idxPos:
                    continue

                if targetValue in state.domainIndex[targetPos]:
                    discount -= 1

            state.elementImpliedDiscount[idxPos][i] = discount

proc initElementImpliedStructures[T](state: TabuState[T]) =
    ## Detect element constraints with non-channel index positions and build
    ## a map from index positions to their element constraints, enabling
    ## compound moves that greedily fix array element targets after index changes.
    state.elementImpliedEnabled = false
    state.elementImpliedMoves = initTable[int, seq[StatefulConstraint[T]]]()

    let channelPos = state.carray.channelPositions

    for constraint in state.constraints:
        if constraint.stateType != ElementType:
            continue
        let es = constraint.elementState

        case es.evalMethod:
        of PositionBased:
            # Skip if the array is all constants (no variable target to fix)
            if es.isConstantArray:
                continue
            # Check that at least one array element is a variable
            var hasVariable = false
            for elem in es.arrayElements:
                if not elem.isConstant:
                    hasVariable = true
                    break
            if not hasVariable:
                continue

            let idxPos = es.indexPosition
            if idxPos in channelPos:
                continue
            if idxPos notin state.elementImpliedMoves:
                state.elementImpliedMoves[idxPos] = @[]
            state.elementImpliedMoves[idxPos].add(constraint)

        of ExpressionBased:
            # Skip if the array is all constants
            if es.isConstantArrayEB:
                continue
            # For expression-based, add each position in indexExprPositions if it's a search position
            for pos in es.indexExprPositions.keys:
                if pos in channelPos:
                    continue
                if pos notin state.elementImpliedMoves:
                    state.elementImpliedMoves[pos] = @[]
                state.elementImpliedMoves[pos].add(constraint)

    # Pre-allocate discount and old-discount buffers
    state.elementImpliedDiscount = initTable[int, seq[int]]()
    if state.elementImpliedMoves.len > 0:
        state.elementImpliedEnabled = true
        for idxPos in state.elementImpliedMoves.keys:
            let dLen = state.sharedDomain[][idxPos].len
            state.elementImpliedDiscount[idxPos] = newSeq[int](dLen)
        if state.verbose and state.id == 0:
            var totalConstraints = 0
            for constraints in state.elementImpliedMoves.values:
                totalConstraints += constraints.len
            echo "[Init] Element implied moves: " & $state.elementImpliedMoves.len &
                 " index positions, " & $totalConstraints & " element constraints"

proc applyElementImpliedMoves[T](state: TabuState[T], movedPosition: int) =
    ## After a primary move at movedPosition, check if it's an element index position.
    ## If so, greedily apply follow-up moves at array element positions that produce
    ## a net cost improvement (strict delta < 0).
    if not state.elementImpliedEnabled:
        return
    if movedPosition notin state.elementImpliedMoves:
        return

    let channelPos = state.carray.channelPositions

    for constraint in state.elementImpliedMoves[movedPosition]:
        let es = constraint.elementState

        # Get current index value (reflects primary move)
        let newIdx = es.getIndexValue()
        let arraySize = es.getArraySize()
        if newIdx < 0 or newIdx >= arraySize:
            continue

        # What does the constraint need the array value to be?
        let targetValue = es.getValueValue()

        # What is the array currently holding at that index?
        let currentArrayValue = es.getArrayValue(newIdx)
        if currentArrayValue == targetValue:
            continue  # Already satisfied

        # Extract the target position from the array element at new index
        var targetPos = -1
        case es.evalMethod:
        of PositionBased:
            if es.isConstantArray:
                continue  # Can't change a constant
            let elem = es.arrayElements[newIdx]
            if elem.isConstant:
                continue  # Can't change a constant element
            targetPos = elem.variablePosition
        of ExpressionBased:
            if es.isConstantArrayEB:
                continue
            let expr = es.arrayExpressionsEB[newIdx]
            if expr.node.kind != RefNode:
                continue  # Only handle simple variable references
            targetPos = expr.node.position

        if targetPos < 0:
            continue
        if targetPos in channelPos:
            continue
        if targetPos == movedPosition:
            continue

        # Check if target value is in the domain
        let domIdx = state.domainIndex[targetPos].getOrDefault(targetValue, -1)
        if domIdx < 0:
            continue

        # Apply if net improvement or neutral (delta <= 0).
        # The element constraint contributes -1, so we apply even if other constraints
        # contribute +1 (net 0), since we're completing a compound move.
        var delta: int
        if state.isLazy[targetPos]:
            delta = state.costDelta(targetPos, targetValue)
        else:
            delta = state.penaltyMap[targetPos][domIdx]
            if state.hasChannelDeps and state.channelDepPenalties[targetPos].len > 0:
                delta += state.channelDepPenalties[targetPos][domIdx]
        if delta > 0:
            continue
        let oldValue = state.assignment[targetPos]
        state.assignValue(targetPos, targetValue)
        # Set tabu on the old value to prevent undoing
        let oldIdx = state.domainIndex[targetPos].getOrDefault(oldValue, -1)
        if oldIdx >= 0 and not state.isLazy[targetPos]:
            state.tabu[targetPos][oldIdx] = state.iteration + 1 + state.iteration mod 10

proc initReverseElementImpliedStructures[T](state: TabuState[T]) =
    ## Build reverse mapping: for each position that appears as an array element
    ## in an element constraint with a non-channel index, record the constraint
    ## and index position. This enables adjusting the index when the array element
    ## changes (e.g., due to channel cascade after a component move).
    state.reverseElementImpliedEnabled = false
    state.reverseElementImpliedMap = newSeq[seq[tuple[constraintIdx: int, idxPos: int]]](state.carray.len)

    let channelPos = state.carray.channelPositions
    var nPositions, nEntries = 0

    for ci, constraint in state.constraints:
        if constraint.stateType != ElementType:
            continue
        let es = constraint.elementState

        var idxPos = -1
        case es.evalMethod:
        of PositionBased:
            idxPos = es.indexPosition
            if idxPos in channelPos: continue
            if es.isConstantArray: continue
            for i, elem in es.arrayElements:
                if not elem.isConstant and elem.variablePosition in channelPos:
                    let arrPos = elem.variablePosition
                    state.reverseElementImpliedMap[arrPos].add(
                        (constraintIdx: ci, idxPos: idxPos))
        of ExpressionBased:
            # Find the single index source position
            if es.indexExpression.positions.len != 1: continue
            for p in es.indexExpression.positions.items:
                idxPos = p
            if idxPos < 0 or idxPos in channelPos: continue
            let arrLen = if es.isConstantArrayEB: es.constantArrayEB.len
                         else: es.arrayExpressionsEB.len
            if not es.isConstantArrayEB:
                for i in 0..<arrLen:
                    let expr = es.arrayExpressionsEB[i]
                    if expr.node.kind == RefNode and expr.node.position in channelPos:
                        let arrPos = expr.node.position
                        state.reverseElementImpliedMap[arrPos].add(
                            (constraintIdx: ci, idxPos: idxPos))

    for pos in 0..<state.reverseElementImpliedMap.len:
        if state.reverseElementImpliedMap[pos].len > 0:
            nPositions += 1
            nEntries += state.reverseElementImpliedMap[pos].len

    if nEntries > 0:
        state.reverseElementImpliedEnabled = true
        if state.verbose and state.id == 0:
            echo "[Init] Reverse element implied: " & $nPositions &
                 " array positions, " & $nEntries & " entries"

proc applyReverseElementImpliedMoves[T](state: TabuState[T]) =
    ## After channel propagation, check if any changed channel positions appear in
    ## element constraint arrays. If so, try to re-point the index variable to a value
    ## that satisfies the element constraint.
    ## Uses state.changedChannelsBuf which was populated by propagateChannels.
    ## Note: we snapshot the buffer since assignValue may modify it.
    ## Guard against recursion: assignValue -> applyReverse -> assignValue -> ...
    if not state.reverseElementImpliedEnabled:
        return
    # Prevent re-entrant calls (assignValue on the index may trigger channel
    # propagation which would call us again)
    state.reverseElementImpliedEnabled = false
    defer: state.reverseElementImpliedEnabled = true

    # Collect relevant changed positions (snapshot to avoid iteration-during-mutation)
    var relevantChanges: seq[int]
    for chanPos in state.changedChannelsBuf:
        if chanPos < state.reverseElementImpliedMap.len and
           state.reverseElementImpliedMap[chanPos].len > 0:
            relevantChanges.add(chanPos)
    if relevantChanges.len == 0: return

    for chanPos in relevantChanges:
        if state.reverseElementImpliedMap[chanPos].len == 0: continue

        for entry in state.reverseElementImpliedMap[chanPos]:
            let constraint = state.constraints[entry.constraintIdx]
            let es = constraint.elementState
            let idxPos = entry.idxPos

            # Check if this constraint is currently violated
            if constraint.penalty() == 0:
                continue  # Already satisfied

            # Try to find a better index value
            let domain = state.sharedDomain[][idxPos]
            let currentIdxValue = state.assignment[idxPos]
            var bestValue = currentIdxValue
            var bestDelta = 0

            for v in domain:
                if v == currentIdxValue: continue
                # Check tabu
                let domIdx = state.domainIndex[idxPos].getOrDefault(v, -1)
                if domIdx < 0: continue
                if not state.isLazy[idxPos] and state.tabu[idxPos][domIdx] > state.iteration:
                    continue  # Skip tabu values

                # Compute cost delta for changing index to v
                let delta = if state.isLazy[idxPos]:
                    state.costDelta(idxPos, v)
                else:
                    var d = state.penaltyMap[idxPos][domIdx]
                    if state.hasChannelDeps and state.channelDepPenalties[idxPos].len > 0:
                        d += state.channelDepPenalties[idxPos][domIdx]
                    d

                if delta < bestDelta:
                    bestDelta = delta
                    bestValue = v

            # Apply if strictly improving
            if bestDelta < 0 and bestValue != currentIdxValue:
                let oldValue = state.assignment[idxPos]
                state.assignValue(idxPos, bestValue)
                # Set tabu on old value
                let oldIdx = state.domainIndex[idxPos].getOrDefault(oldValue, -1)
                if oldIdx >= 0 and not state.isLazy[idxPos]:
                    state.tabu[idxPos][oldIdx] = state.iteration + 1 + state.iteration mod 10
