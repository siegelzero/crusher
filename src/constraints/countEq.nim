## CountEq Constraint Implementation
## ==================================
##
## Implements count_eq(array, value, target): the number of elements in `array`
## equal to `value` must equal the current value of `target`.
##
## **Key difference from AtLeast/AtMost**: the required count is a *variable*,
## not a constant. When the target variable changes, the penalty changes.
## In the nmseq (number sequence) problem the target is one of the array
## elements itself (self-referential).
##
## **Penalty**: |actualCount - requiredCount|
## **moveDelta**: O(1) incremental evaluation

import std/[packedsets, tables]

type
    CountEqConstraint*[T] = ref object
        arrayPositions*: PackedSet[int]
        targetPosition*: int
        countValue*: T
        actualCount*: int
        requiredCount*: T
        cost*: int
        currentAssignment*: Table[int, T]
        # All positions (array + target) for the constraint positions field
        allPositions*: PackedSet[int]
        # Tracking for getAffectedPositions/getAffectedDomainValues
        lastChangeAffectedCost*: bool

func newCountEqConstraint*[T](arrayPositions: openArray[int], countValue: T, targetPosition: int): CountEqConstraint[T] =
    new(result)
    result.arrayPositions = toPackedSet[int](arrayPositions)
    result.targetPosition = targetPosition
    result.countValue = countValue
    result.actualCount = 0
    result.requiredCount = 0
    result.cost = 0
    result.currentAssignment = initTable[int, T]()
    result.allPositions = toPackedSet[int](arrayPositions)
    result.allPositions.incl(targetPosition)

proc initialize*[T](state: CountEqConstraint[T], assignment: seq[T]) =
    state.actualCount = 0
    for pos in state.arrayPositions.items:
        state.currentAssignment[pos] = assignment[pos]
        if assignment[pos] == state.countValue:
            state.actualCount += 1
    state.currentAssignment[state.targetPosition] = assignment[state.targetPosition]
    state.requiredCount = assignment[state.targetPosition]
    state.cost = abs(state.actualCount - state.requiredCount)

proc updatePosition*[T](state: CountEqConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        state.lastChangeAffectedCost = false
        return
    state.currentAssignment[position] = newValue

    # Track whether actualCount or requiredCount changes
    var affected = false

    if position in state.arrayPositions:
        if oldValue == state.countValue:
            state.actualCount -= 1
            affected = true
        if newValue == state.countValue:
            state.actualCount += 1
            affected = true

    if position == state.targetPosition:
        state.requiredCount = newValue
        affected = true

    state.lastChangeAffectedCost = affected
    state.cost = abs(state.actualCount - state.requiredCount)

proc moveDelta*[T](state: CountEqConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    var countDelta = 0
    var newRequired = state.requiredCount

    if position in state.arrayPositions:
        if oldValue == state.countValue:
            countDelta -= 1
        if newValue == state.countValue:
            countDelta += 1

    if position == state.targetPosition:
        newRequired = newValue

    let newCost = abs(state.actualCount + countDelta - newRequired)
    return newCost - state.cost

proc getAffectedPositions*[T](state: CountEqConstraint[T]): PackedSet[int] =
    ## Returns positions needing penalty map updates after the last updatePosition.
    ## If actualCount and requiredCount didn't change, no neighbor's moveDelta
    ## will return different values, so return empty set.
    if not state.lastChangeAffectedCost:
        return initPackedSet[int]()
    return state.allPositions

proc getAffectedDomainValues*[T](state: CountEqConstraint[T], position: int): seq[T] =
    ## Returns domain values needing recalculation at a neighbor position.
    ## When cost landscape changed, all values may be affected since
    ## the baseline (actualCount or requiredCount) shifted.
    return @[]

proc deepCopy*[T](state: CountEqConstraint[T]): CountEqConstraint[T] =
    new(result)
    result.arrayPositions = state.arrayPositions
    result.targetPosition = state.targetPosition
    result.countValue = state.countValue
    result.actualCount = state.actualCount
    result.requiredCount = state.requiredCount
    result.cost = state.cost
    result.currentAssignment = initTable[int, T]()
    for k, v in state.currentAssignment.pairs:
        result.currentAssignment[k] = v
    result.allPositions = state.allPositions
    result.lastChangeAffectedCost = state.lastChangeAffectedCost
