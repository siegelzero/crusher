## NValue Constraint Implementation
## =================================
##
## Implements nvalue(n, array): the number of distinct values in `array`
## must equal the current value of `n`.
##
## **Penalty**: |distinctCount - requiredCount|
## **moveDelta**: O(1) incremental evaluation — tracks per-value occurrence
## counts to detect when a value's count crosses the 0 boundary.

import std/[packedsets, tables]

type
    NValueConstraint*[T] = ref object
        arrayPositions*: PackedSet[int]
        targetPosition*: int
        valueCounts*: Table[T, int]       # value -> number of occurrences
        distinctCount*: int                # |{v : valueCounts[v] > 0}|
        requiredCount*: T                  # current value at targetPosition
        cost*: int                         # |distinctCount - requiredCount|
        currentAssignment*: Table[int, T]
        allPositions*: PackedSet[int]
        lastChangeAffectedCost*: bool
        # targetPosition = -1: the count is the constant fixedCount
        fixedCount*: T
        # Literal entries of the array: always present, counted at initialization
        constantValues*: seq[T]

func newNValueConstraint*[T](arrayPositions: openArray[int], targetPosition: int,
                             constantValues: openArray[T] = [], fixedCount: T = 0): NValueConstraint[T] =
    ## targetPosition < 0 means the required number of distinct values is the
    ## constant `fixedCount` (e.g. MiniZinc fixed the count at compile time).
    new(result)
    result.arrayPositions = toPackedSet[int](arrayPositions)
    result.targetPosition = if targetPosition < 0: -1 else: targetPosition
    result.valueCounts = initTable[T, int]()
    result.distinctCount = 0
    result.requiredCount = fixedCount
    result.fixedCount = fixedCount
    result.constantValues = @constantValues
    result.cost = 0
    result.currentAssignment = initTable[int, T]()
    result.allPositions = toPackedSet[int](arrayPositions)
    if result.targetPosition >= 0:
        result.allPositions.incl(targetPosition)

{.push overflowChecks: off.}
proc initialize*[T](state: NValueConstraint[T], assignment: seq[T]) =
    state.valueCounts.clear()
    state.distinctCount = 0
    for v in state.constantValues:
        let oldCount = state.valueCounts.getOrDefault(v, 0)
        state.valueCounts[v] = oldCount + 1
        if oldCount == 0:
            state.distinctCount += 1
    for pos in state.arrayPositions.items:
        state.currentAssignment[pos] = assignment[pos]
        let v = assignment[pos]
        let oldCount = state.valueCounts.getOrDefault(v, 0)
        state.valueCounts[v] = oldCount + 1
        if oldCount == 0:
            state.distinctCount += 1
    if state.targetPosition >= 0:
        state.currentAssignment[state.targetPosition] = assignment[state.targetPosition]
        state.requiredCount = assignment[state.targetPosition]
    else:
        state.requiredCount = state.fixedCount
    state.cost = abs(state.distinctCount - state.requiredCount)

proc updatePosition*[T](state: NValueConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        state.lastChangeAffectedCost = false
        return
    state.currentAssignment[position] = newValue

    var affected = false

    if position in state.arrayPositions:
        # Remove old value
        let oldCount = state.valueCounts.getOrDefault(oldValue, 0)
        if oldCount > 0:
            state.valueCounts[oldValue] = oldCount - 1
            if oldCount == 1:
                state.distinctCount -= 1
                affected = true
        # Add new value
        let newCount = state.valueCounts.getOrDefault(newValue, 0)
        state.valueCounts[newValue] = newCount + 1
        if newCount == 0:
            state.distinctCount += 1
            affected = true
        # Even if distinctCount didn't change, the distribution changed which
        # doesn't affect cost but we only care about cost changes
        if not affected and oldCount > 0:
            # distinctCount unchanged, no cost effect from array side
            discard

    if position == state.targetPosition:
        state.requiredCount = newValue
        affected = true

    state.lastChangeAffectedCost = affected
    state.cost = abs(state.distinctCount - state.requiredCount)

proc moveDelta*[T](state: NValueConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    var distinctDelta = 0
    var newRequired = state.requiredCount

    if position in state.arrayPositions:
        let oldCount = state.valueCounts.getOrDefault(oldValue, 0)
        if oldCount == 1:
            # Removing the last occurrence of oldValue
            distinctDelta -= 1
        let newCount = state.valueCounts.getOrDefault(newValue, 0)
        if newCount == 0:
            # Adding first occurrence of newValue
            distinctDelta += 1

    if position == state.targetPosition:
        newRequired = newValue

    let newCost = abs(state.distinctCount + distinctDelta - newRequired)
    return newCost - state.cost
{.pop.}

proc getAffectedPositions*[T](state: NValueConstraint[T]): PackedSet[int] =
    if not state.lastChangeAffectedCost:
        return initPackedSet[int]()
    return state.allPositions

proc getAffectedDomainValues*[T](state: NValueConstraint[T], position: int): seq[T] =
    return @[]

proc deepCopy*[T](state: NValueConstraint[T]): NValueConstraint[T] =
    new(result)
    result.arrayPositions = state.arrayPositions
    result.targetPosition = state.targetPosition
    result.valueCounts = initTable[T, int]()
    for k, v in state.valueCounts.pairs:
        result.valueCounts[k] = v
    result.distinctCount = state.distinctCount
    result.requiredCount = state.requiredCount
    result.cost = state.cost
    result.currentAssignment = initTable[int, T]()
    for k, v in state.currentAssignment.pairs:
        result.currentAssignment[k] = v
    result.allPositions = state.allPositions
    result.lastChangeAffectedCost = state.lastChangeAffectedCost
    result.fixedCount = state.fixedCount
    result.constantValues = state.constantValues
