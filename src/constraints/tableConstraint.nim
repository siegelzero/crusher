## Table Constraint Implementation (Extensional Constraint)
##
## tableIn: variable tuple must match one of the allowed tuples
## tableNotIn: variable tuple must NOT match any of the forbidden tuples
##
## **tableIn penalty**: minimum Hamming distance to any allowed tuple (graduated)
## **tableNotIn penalty**: 1 if exact match with any forbidden tuple, else 0

import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    TableMode* = enum
        TableIn,
        TableNotIn

    TableConstraint*[T] = ref object
        mode*: TableMode
        tuples*: seq[seq[T]]
        sortedPositions*: seq[int]
        positionToIndex*: Table[int, int]
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        cost*: int
        # Cached Hamming distances for tableIn mode
        hammingDistances*: seq[int]
        # Precomputed index: [colIdx][value] -> tuple indices with that value at that column
        tuplesByColumnValue*: seq[Table[T, seq[int]]]
        # Cached groupMin: [col][val] -> min Hamming distance among tuples where tuples[t][col] == val
        cachedGroupMin*: seq[Table[T, int]]
        # Count of tuples at the minimum distance for each group
        cachedGroupMinCount*: seq[Table[T, int]]
        # Positions affected by the last updatePosition call
        lastAffectedPositions*: PackedSet[int]

################################################################################
# Constructor
################################################################################

proc newTableConstraint*[T](positions: openArray[int], tuples: seq[seq[T]],
                            mode: TableMode): TableConstraint[T] =
    new(result)
    result.mode = mode
    result.tuples = tuples
    result.sortedPositions = @positions
    result.positions = toPackedSet[int](positions)
    result.currentAssignment = initTable[int, T]()
    result.cost = 0
    result.positionToIndex = initTable[int, int]()

    for i, pos in positions:
        result.positionToIndex[pos] = i

    result.hammingDistances = newSeq[int](tuples.len)

    # Build tuplesByColumnValue index
    let nCols = positions.len
    result.tuplesByColumnValue = newSeq[Table[T, seq[int]]](nCols)
    for col in 0..<nCols:
        result.tuplesByColumnValue[col] = initTable[T, seq[int]]()
    for t in 0..<tuples.len:
        for col in 0..<nCols:
            let val = tuples[t][col]
            if val notin result.tuplesByColumnValue[col]:
                result.tuplesByColumnValue[col][val] = @[t]
            else:
                result.tuplesByColumnValue[col][val].add(t)

################################################################################
# Penalty computation
################################################################################

proc computeHammingDistances[T](state: TableConstraint[T]) =
    for t in 0..<state.tuples.len:
        var dist = 0
        for i in 0..<state.sortedPositions.len:
            if state.currentAssignment[state.sortedPositions[i]] != state.tuples[t][i]:
                dist += 1
        state.hammingDistances[t] = dist

proc computePenalty[T](state: TableConstraint[T]): int =
    case state.mode:
        of TableIn:
            # Minimum Hamming distance to any allowed tuple
            result = state.sortedPositions.len + 1  # max possible + 1
            for dist in state.hammingDistances:
                if dist < result:
                    result = dist
        of TableNotIn:
            # 1 if any forbidden tuple is an exact match, else 0
            result = 0
            for dist in state.hammingDistances:
                if dist == 0:
                    result = 1
                    return

################################################################################
# Initialization and updates
################################################################################

proc buildGroupMinCache[T](state: TableConstraint[T]) =
    ## Build cachedGroupMin and cachedGroupMinCount from current Hamming distances.
    let nCols = state.sortedPositions.len
    state.cachedGroupMin = newSeq[Table[T, int]](nCols)
    state.cachedGroupMinCount = newSeq[Table[T, int]](nCols)
    for col in 0..<nCols:
        state.cachedGroupMin[col] = initTable[T, int]()
        state.cachedGroupMinCount[col] = initTable[T, int]()
        for val, tupleIndices in state.tuplesByColumnValue[col].pairs:
            var minDist = high(int)
            var count = 0
            for t in tupleIndices:
                let d = state.hammingDistances[t]
                if d < minDist:
                    minDist = d
                    count = 1
                elif d == minDist:
                    count += 1
            state.cachedGroupMin[col][val] = minDist
            state.cachedGroupMinCount[col][val] = count

proc computeCostFromGroupMin[T](state: TableConstraint[T]): int =
    ## Compute cost as min over cachedGroupMin[0] values.
    result = state.sortedPositions.len + 1
    for val, minDist in state.cachedGroupMin[0].pairs:
        if minDist < result:
            result = minDist

proc initialize*[T](state: TableConstraint[T], assignment: seq[T]) =
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]
    state.computeHammingDistances()
    if state.mode == TableIn:
        state.buildGroupMinCache()
        state.cost = state.computeCostFromGroupMin()
    else:
        state.cost = state.computePenalty()


proc updatePosition*[T](state: TableConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return
    let idx = state.positionToIndex[position]
    state.currentAssignment[position] = newValue

    case state.mode:
    of TableIn:
        let nCols = state.sortedPositions.len

        # Phase 1: Update only affected Hamming distances via tuplesByColumnValue[idx]
        # Collect (tupleIdx, oldDist, newDist) for Phase 2
        type ChangeRecord = tuple[tupleIdx: int, oldDist: int, newDist: int]
        var changes: seq[ChangeRecord] = @[]

        # Group 1: tuples where tuples[t][idx] == oldValue → distance += 1
        if oldValue in state.tuplesByColumnValue[idx]:
            for t in state.tuplesByColumnValue[idx][oldValue]:
                let oldDist = state.hammingDistances[t]
                let newDist = oldDist + 1
                state.hammingDistances[t] = newDist
                changes.add((t, oldDist, newDist))

        # Group 2: tuples where tuples[t][idx] == newValue → distance -= 1
        if newValue in state.tuplesByColumnValue[idx]:
            for t in state.tuplesByColumnValue[idx][newValue]:
                let oldDist = state.hammingDistances[t]
                let newDist = oldDist - 1
                state.hammingDistances[t] = newDist
                changes.add((t, oldDist, newDist))

        # Phase 2: Incremental groupMin maintenance
        # Track dirty (col, val) groups that need full rescan
        var dirtyGroups: seq[(int, T)] = @[]
        # Track already-dirty (col, val) to skip further processing
        var isDirty = initTable[(int, T), bool]()
        # Track which columns had their groupMin modified
        var dirtyColumns: set[0..63]

        for change in changes:
            let (tupleIdx, oldDist, newDist) = change
            for col in 0..<nCols:
                let val = state.tuples[tupleIdx][col]
                let key = (col, val)
                if key in isDirty:
                    continue  # Already dirty, will be rescanned

                if newDist > oldDist:
                    # Distance increased
                    if oldDist == state.cachedGroupMin[col][val]:
                        let newCount = state.cachedGroupMinCount[col][val] - 1
                        if newCount <= 0:
                            dirtyGroups.add(key)
                            isDirty[key] = true
                            dirtyColumns.incl(col)
                        else:
                            state.cachedGroupMinCount[col][val] = newCount
                elif newDist < oldDist:
                    # Distance decreased
                    let curMin = state.cachedGroupMin[col][val]
                    if newDist < curMin:
                        state.cachedGroupMin[col][val] = newDist
                        state.cachedGroupMinCount[col][val] = 1
                        dirtyColumns.incl(col)
                    elif newDist == curMin:
                        state.cachedGroupMinCount[col][val] += 1

        # Rescan dirty groups
        for (col, val) in dirtyGroups:
            var minDist = high(int)
            var count = 0
            for t in state.tuplesByColumnValue[col][val]:
                let d = state.hammingDistances[t]
                if d < minDist:
                    minDist = d
                    count = 1
                elif d == minDist:
                    count += 1
            state.cachedGroupMin[col][val] = minDist
            state.cachedGroupMinCount[col][val] = count

        # Phase 3: Recompute cost from cachedGroupMin[0]
        let oldCost = state.cost
        state.cost = state.computeCostFromGroupMin()

        # Track affected positions for getAffectedPositions
        if state.cost != oldCost:
            state.lastAffectedPositions = state.positions
        else:
            state.lastAffectedPositions = initPackedSet[int]()
            for col in dirtyColumns:
                state.lastAffectedPositions.incl(state.sortedPositions[col])

    of TableNotIn:
        # Only update affected tuples
        if oldValue in state.tuplesByColumnValue[idx]:
            for t in state.tuplesByColumnValue[idx][oldValue]:
                state.hammingDistances[t] += 1
        if newValue in state.tuplesByColumnValue[idx]:
            for t in state.tuplesByColumnValue[idx][newValue]:
                state.hammingDistances[t] -= 1
        let oldCost = state.cost
        state.cost = state.computePenalty()
        if state.cost != oldCost:
            state.lastAffectedPositions = state.positions
        else:
            state.lastAffectedPositions = initPackedSet[int]()


func getAffectedPositions*[T](state: TableConstraint[T]): PackedSet[int] =
    state.lastAffectedPositions


proc moveDelta*[T](state: TableConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    let idx = state.positionToIndex[position]

    # Temporarily update Hamming distances
    var tempDistances = newSeq[int](state.tuples.len)
    for t in 0..<state.tuples.len:
        tempDistances[t] = state.hammingDistances[t]
        let tupleVal = state.tuples[t][idx]
        if oldValue == tupleVal and newValue != tupleVal:
            tempDistances[t] += 1
        elif oldValue != tupleVal and newValue == tupleVal:
            tempDistances[t] -= 1

    # Compute new penalty from temp distances
    var newCost: int
    case state.mode:
        of TableIn:
            newCost = state.sortedPositions.len + 1
            for dist in tempDistances:
                if dist < newCost:
                    newCost = dist
        of TableNotIn:
            newCost = 0
            for dist in tempDistances:
                if dist == 0:
                    newCost = 1
                    break

    return newCost - state.cost


################################################################################
# Batch penalty computation
################################################################################

proc batchMovePenalty*[T](state: TableConstraint[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
    ## Compute moveDelta for ALL domain values at a position in O(nTuples + domainSize).
    ## For TableIn: penalty = min Hamming distance to any allowed tuple.
    ## Key insight: tuples partition by their value at column idx. For candidate v:
    ##   - Tuples matching currentValue at idx: Hamming dist + 1
    ##   - Tuples matching v at idx: Hamming dist - 1
    ##   - Other tuples: unchanged
    ## Precompute groupMin per value group, then use top-3 tracking for O(1) per candidate.
    let idx = state.positionToIndex[position]
    result = newSeq[int](domain.len)

    case state.mode:
    of TableIn:
        # Use cached groupMin instead of scanning all tuples
        let groupMin = state.cachedGroupMin[idx]

        # Track top-3 smallest groupMin values (value, minDist) for fast "min excluding keys"
        # We need: min of groupMin[val] for val not in {currentValue, candidateValue}
        var top3: array[3, (T, int)]  # (value, minDist), sorted ascending by minDist
        var top3Len = 0
        for val, minDist in groupMin.pairs:
            if top3Len < 3:
                top3[top3Len] = (val, minDist)
                top3Len += 1
                # Insertion sort to keep sorted
                var j = top3Len - 1
                while j > 0 and top3[j][1] < top3[j-1][1]:
                    swap(top3[j], top3[j-1])
                    dec j
            elif minDist < top3[2][1]:
                top3[2] = (val, minDist)
                # Re-sort
                if top3[2][1] < top3[1][1]:
                    swap(top3[2], top3[1])
                    if top3[1][1] < top3[0][1]:
                        swap(top3[1], top3[0])

        # minCurrentGroup: min Hamming dist among tuples matching currentValue, +1
        let minCurrentGroup = if currentValue in groupMin:
            groupMin[currentValue] + 1
        else:
            high(int)

        let maxPossible = state.sortedPositions.len + 1

        for i in 0..<domain.len:
            let v = domain[i]
            if v == currentValue:
                result[i] = 0  # No change
                continue

            # term1: tuples that matched currentValue now have dist+1
            let term1 = minCurrentGroup

            # term2: tuples that match v now have dist-1
            let term2 = if v in groupMin:
                groupMin[v] - 1
            else:
                maxPossible

            # term3: min of groupMin[val] for val not in {currentValue, v}
            var term3 = maxPossible
            for k in 0..<top3Len:
                if top3[k][0] != currentValue and top3[k][0] != v:
                    term3 = top3[k][1]
                    break

            let newCost = min(term1, min(term2, term3))
            result[i] = newCost - state.cost

    of TableNotIn:
        # For TableNotIn: penalty = 1 if any forbidden tuple has dist=0, else 0
        # When varying position idx from currentValue to v:
        #   - Tuples with dist=0 (exact matches): if tuples[t][idx]==currentValue, dist becomes 1 (no longer match)
        #   - Tuples with dist=1 where tuples[t][idx]==v: dist becomes 0 (new match)
        #   - Tuples with dist=0 where tuples[t][idx]!=currentValue: impossible (dist=0 means all match)

        # Count tuples with dist=0 and dist=1, partitioned by value at idx
        var totalZeros = 0
        var zerosInCurrentGroup = 0
        var hasDistOneInGroup = initTable[T, bool]()

        for val, tupleIndices in state.tuplesByColumnValue[idx].pairs:
            for t in tupleIndices:
                if state.hammingDistances[t] == 0:
                    totalZeros += 1
                    if val == currentValue:
                        zerosInCurrentGroup += 1
                elif state.hammingDistances[t] == 1:
                    # This tuple differs from current assignment only at some position.
                    # If that position is idx (i.e., tuples[t][idx] != currentValue but
                    # all other positions match), then changing idx to val would make dist=0.
                    # But val == tuples[t][idx] for this group, so check if only mismatch is at idx.
                    if val != currentValue:
                        # Check if the only mismatch in this tuple is at column idx
                        # (dist=1 and value at idx differs from current means idx IS the mismatch)
                        hasDistOneInGroup[val] = true

        # Zeros outside current group can't be affected by changing idx
        let zerosOutsideCurrentGroup = totalZeros - zerosInCurrentGroup

        for i in 0..<domain.len:
            let v = domain[i]
            if v == currentValue:
                result[i] = 0
                continue

            # After changing idx to v:
            # - Zeros that had tuples[t][idx]==currentValue: dist becomes 1 (removed from zeros)
            # - Zeros that had tuples[t][idx]!=currentValue: impossible (were zeros)
            # - Dist-1 tuples in group v (where idx was the mismatch): dist becomes 0 (new zeros)
            var newHasZero = zerosOutsideCurrentGroup > 0 or
                             hasDistOneInGroup.getOrDefault(v, false)
            let newCost = if newHasZero: 1 else: 0
            result[i] = newCost - state.cost
