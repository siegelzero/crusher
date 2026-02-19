## AtMost Constraint Implementation
## ================================
##
## This module implements the AtMost constraint, which ensures that a target value
## appears at most a maximum number of times in specified positions or expressions.
##
## **Constraint Definition**:
## `|{i ∈ positions : x[i] = targetValue}| ≤ maxOccurrences`
##
## **Key Features**:
## - Position-based evaluation: Direct variable position checking
## - Expression-based evaluation: Algebraic expression result checking
## - Efficient incremental updates for search algorithms
## - Linear violation cost: `max(0, actualOccurrences - maxOccurrences)`
##
## **Applications**:
## - Capacity management: Preventing resource overload
## - Regulatory compliance: Maximum working hours, overtime limits
## - Risk management: Limiting exposure to high-risk activities
## - Budget constraints: Maximum expensive operations
##
## **Performance**: O(1) incremental move evaluation, O(n) initialization where n = number of positions/expressions

import std/[packedsets, tables]

import ../expressions/expressions
import ../expressions/types

################################################################################
# Type definitions
################################################################################

type
    AtMostConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        targetValue*: T
        maxOccurrences*: int
        actualOccurrences: int
        cost*: int
        lastOldOccurrences*: int
        lastNewOccurrences*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions: PackedSet[int]
            of ExpressionBased:
                expressions: seq[AlgebraicExpression[T]]
                expressionsAtPosition: Table[int, seq[int]]

################################################################################
# AtMostConstraint creation
################################################################################

func newAtMostConstraint*[T](positions: openArray[int], targetValue: T, maxOccurrences: int): AtMostConstraint[T] =
    # Allocates and initializes new AtMostConstraint[T] for positions
    new(result)
    result = AtMostConstraint[T](
        cost: 0,  # Initially no excess occurrences
        targetValue: targetValue,
        maxOccurrences: maxOccurrences,
        actualOccurrences: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T](),
    )

func newAtMostConstraint*[T](expressions: seq[AlgebraicExpression[T]], targetValue: T, maxOccurrences: int): AtMostConstraint[T] =
    # Allocates and initializes new AtMostConstraint[T] for expressions
    new(result)
    result = AtMostConstraint[T](
        cost: 0,  # Initially no excess occurrences
        targetValue: targetValue,
        maxOccurrences: maxOccurrences,
        actualOccurrences: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        currentAssignment: initTable[int, T](),
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

################################################################################
# AtMostConstraint initialization and updates
################################################################################

proc initialize*[T](state: AtMostConstraint[T], assignment: seq[T]) =
    var value: T
    state.actualOccurrences = 0

    case state.evalMethod:
        of PositionBased:
            for pos in state.positions.items:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                if value == state.targetValue:
                    state.actualOccurrences += 1

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                if value == state.targetValue:
                    state.actualOccurrences += 1

    state.cost = max(0, state.actualOccurrences - state.maxOccurrences)

proc updatePosition*[T](state: AtMostConstraint[T], position: int, newValue: T) =
    # State Update assigning newValue to position
    let oldValue = state.currentAssignment[position]
    state.lastOldOccurrences = state.actualOccurrences
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue
                # Update occurrence count and cost efficiently
                var occurrenceDelta = 0
                if oldValue == state.targetValue:
                    occurrenceDelta -= 1
                if newValue == state.targetValue:
                    occurrenceDelta += 1

                state.actualOccurrences += occurrenceDelta
                state.cost = max(0, state.actualOccurrences - state.maxOccurrences)

            of ExpressionBased:
                var oldExpValue, newExpValue: T
                var totalOccurrenceDelta = 0

                for i in state.expressionsAtPosition[position]:
                    oldExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.currentAssignment[position] = newValue
                    newExpValue = state.expressions[i].evaluate(state.currentAssignment)

                    # Accumulate occurrence changes
                    if oldExpValue == state.targetValue:
                        totalOccurrenceDelta -= 1
                    if newExpValue == state.targetValue:
                        totalOccurrenceDelta += 1

                state.actualOccurrences += totalOccurrenceDelta
                state.cost = max(0, state.actualOccurrences - state.maxOccurrences)
    state.lastNewOccurrences = state.actualOccurrences

proc moveDelta*[T](state: AtMostConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    var oldExpValue, newExpValue: T
    var deltaOccurrences = 0

    case state.evalMethod:
        of PositionBased:
            # Calculate change in occurrences for position-based evaluation
            if oldValue == state.targetValue:
                deltaOccurrences -= 1
            if newValue == state.targetValue:
                deltaOccurrences += 1

        of ExpressionBased:
            # Calculate change in occurrences for expression-based evaluation
            for i in state.expressionsAtPosition[position]:
                oldExpValue = state.expressions[i].evaluate(state.currentAssignment)

                state.currentAssignment[position] = newValue
                newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue

                if oldExpValue == state.targetValue:
                    deltaOccurrences -= 1
                if newExpValue == state.targetValue:
                    deltaOccurrences += 1

    # Calculate cost delta efficiently
    let newActualOccurrences = state.actualOccurrences + deltaOccurrences
    let newCost = max(0, newActualOccurrences - state.maxOccurrences)

    return newCost - state.cost

proc getAffectedPositions*[T](state: AtMostConstraint[T]): PackedSet[int] =
    ## Returns positions needing penalty map updates after the last updatePosition.
    ## If occurrence count didn't cross a critical boundary, no neighbor's moveDelta
    ## will return different values, so return empty set.
    let old = state.lastOldOccurrences
    let new2 = state.lastNewOccurrences
    if old == new2:
        return initPackedSet[int]()
    let maxOcc = state.maxOccurrences
    # Adding target value becomes costly when count crosses from < maxOcc to >= maxOcc
    let addMarginalChanged = (old < maxOcc) != (new2 < maxOcc)
    # Removing target value becomes beneficial when count crosses from > maxOcc to <= maxOcc
    let removeMarginalChanged = (old <= maxOcc) != (new2 <= maxOcc)
    if not addMarginalChanged and not removeMarginalChanged:
        return initPackedSet[int]()
    case state.evalMethod:
        of PositionBased:
            return state.positions
        of ExpressionBased:
            var allPos = initPackedSet[int]()
            for exp in state.expressions:
                allPos.incl(exp.positions)
            return allPos

proc getAffectedDomainValues*[T](state: AtMostConstraint[T], position: int): seq[T] =
    ## Returns domain values needing recalculation at a neighbor position.
    ## If current value is NOT the target, only flipping TO target changes occurrence count.
    ## If current value IS the target, any non-target value changes it, so return all.
    case state.evalMethod:
        of PositionBased:
            if state.currentAssignment[position] != state.targetValue:
                return @[state.targetValue]
            else:
                return @[]  # all values
        of ExpressionBased:
            return @[]  # all values for expression-based