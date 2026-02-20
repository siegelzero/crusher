## AtLeast Constraint Implementation
## ================================
##
## This module implements the AtLeast constraint, which ensures that a target value
## appears at least a minimum number of times in specified positions or expressions.
##
## **Constraint Definition**:
## `|{i ∈ positions : x[i] = targetValue}| ≥ minOccurrences`
##
## **Key Features**:
## - Position-based evaluation: Direct variable position checking
## - Expression-based evaluation: Algebraic expression result checking
## - Efficient incremental updates for search algorithms
## - Linear violation cost: `max(0, minOccurrences - actualOccurrences)`
##
## **Applications**:
## - Resource allocation: Minimum staff per shift
## - Quality control: Minimum acceptable outcomes
## - Load balancing: Minimum tasks per server
## - Scheduling: Minimum occurrences of critical activities
##
## **Performance**: O(1) incremental move evaluation, O(n) initialization where n = number of positions/expressions

import std/[packedsets, tables]

import ../expressions/expressions
import ../expressions/types

################################################################################
# Type definitions
################################################################################

type
    AtLeastConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        targetValue*: T
        minOccurrences*: int
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
# AtLeastConstraint creation
################################################################################

func newAtLeastConstraint*[T](positions: openArray[int], targetValue: T, minOccurrences: int): AtLeastConstraint[T] =
    # Allocates and initializes new AtLeastConstraint[T] for positions
    new(result)
    result = AtLeastConstraint[T](
        cost: minOccurrences,  # Initially all occurrences are missing
        targetValue: targetValue,
        minOccurrences: minOccurrences,
        actualOccurrences: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T](),
    )

func newAtLeastConstraint*[T](expressions: seq[AlgebraicExpression[T]], targetValue: T, minOccurrences: int): AtLeastConstraint[T] =
    # Allocates and initializes new AtLeastConstraint[T] for expressions
    new(result)
    result = AtLeastConstraint[T](
        cost: minOccurrences,  # Initially all occurrences are missing
        targetValue: targetValue,
        minOccurrences: minOccurrences,
        actualOccurrences: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        currentAssignment: initTable[int, T](),
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

proc getExpressions*[T](state: AtLeastConstraint[T]): seq[AlgebraicExpression[T]] =
    state.expressions

################################################################################
# AtLeastConstraint initialization and updates
################################################################################

proc initialize*[T](state: AtLeastConstraint[T], assignment: seq[T]) =
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

    state.cost = max(0, state.minOccurrences - state.actualOccurrences)

proc updatePosition*[T](state: AtLeastConstraint[T], position: int, newValue: T) =
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
                state.cost = max(0, state.minOccurrences - state.actualOccurrences)

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
                state.cost = max(0, state.minOccurrences - state.actualOccurrences)
    state.lastNewOccurrences = state.actualOccurrences

proc moveDelta*[T](state: AtLeastConstraint[T], position: int, oldValue, newValue: T): int =
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
    let newCost = max(0, state.minOccurrences - newActualOccurrences)

    return newCost - state.cost

proc getAffectedPositions*[T](state: AtLeastConstraint[T]): PackedSet[int] =
    ## Returns positions needing penalty map updates after the last updatePosition.
    ## If occurrence count didn't cross a critical boundary, no neighbor's moveDelta
    ## will return different values, so return empty set.
    let old = state.lastOldOccurrences
    let new2 = state.lastNewOccurrences
    if old == new2:
        return initPackedSet[int]()
    let minOcc = state.minOccurrences
    # Adding target value stops being beneficial when count crosses from < minOcc to >= minOcc
    let addMarginalChanged = (old < minOcc) != (new2 < minOcc)
    # Removing target value starts being costly when count crosses from > minOcc to <= minOcc
    let removeMarginalChanged = (old <= minOcc) != (new2 <= minOcc)
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

proc getAffectedDomainValues*[T](state: AtLeastConstraint[T], position: int): seq[T] =
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
