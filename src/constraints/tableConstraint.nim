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

proc initialize*[T](state: TableConstraint[T], assignment: seq[T]) =
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]
    state.computeHammingDistances()
    state.cost = state.computePenalty()


proc updatePosition*[T](state: TableConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return
    let idx = state.positionToIndex[position]
    state.currentAssignment[position] = newValue

    # Incrementally update Hamming distances
    for t in 0..<state.tuples.len:
        let tupleVal = state.tuples[t][idx]
        if oldValue == tupleVal and newValue != tupleVal:
            state.hammingDistances[t] += 1
        elif oldValue != tupleVal and newValue == tupleVal:
            state.hammingDistances[t] -= 1

    state.cost = state.computePenalty()


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
