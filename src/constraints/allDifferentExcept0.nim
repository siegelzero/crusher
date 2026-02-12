## AllDifferentExcept0 Constraint Implementation
##
## Like AllDifferent but only enforces uniqueness among non-zero values.
## Zero values are ignored (any number of variables can be 0).
##
## **Violation Cost**: Sum of conflicts among duplicate non-zero values

import std/[packedsets, tables]

import ../expressions/expressions
import common

################################################################################
# Type definitions
################################################################################

type
    AllDifferentExcept0Constraint*[T] = ref object
        currentAssignment*: Table[int, T]
        countTable: Table[T, int]
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions: PackedSet[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition: Table[int, seq[int]]

################################################################################
# AllDifferentExcept0Constraint creation
################################################################################

func newAllDifferentExcept0Constraint*[T](positions: openArray[int]): AllDifferentExcept0Constraint[T] =
    new(result)
    result = AllDifferentExcept0Constraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        countTable: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )

func newAllDifferentExcept0Constraint*[T](expressions: seq[AlgebraicExpression[T]]): AllDifferentExcept0Constraint[T] =
    new(result)
    result = AllDifferentExcept0Constraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        countTable: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )
    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

################################################################################
# Utility functions
################################################################################

func contribution[T](state: AllDifferentExcept0Constraint[T], value: T): int {.inline.} =
    if value == 0:
        return 0
    max(0, getCount(state.countTable, value) - 1)

proc adjustCounts[T](state: AllDifferentExcept0Constraint[T], oldValue, newValue: T) {.inline.} =
    # Only track non-zero values in the count table
    if oldValue != 0:
        state.cost -= state.contribution(oldValue)
    if newValue != 0:
        state.cost -= state.contribution(newValue)

    if oldValue != 0:
        decrementCount(state.countTable, oldValue)
    if newValue != 0:
        incrementCount(state.countTable, newValue)

    if oldValue != 0:
        state.cost += state.contribution(oldValue)
    if newValue != 0:
        state.cost += state.contribution(newValue)

################################################################################
# Initialization and updates
################################################################################

proc initialize*[T](state: AllDifferentExcept0Constraint[T], assignment: seq[T]) =
    var value: T
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions.items:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                if value != 0:
                    incrementCount(state.countTable, value)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                if value != 0:
                    incrementCount(state.countTable, value)

    # Calculate cost from count table
    for value, count in state.countTable.pairs:
        state.cost += max(0, count - 1)


proc updatePosition*[T](state: AllDifferentExcept0Constraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue
                state.adjustCounts(oldValue, newValue)

            of ExpressionBased:
                var oldExpValue, newExpValue: T
                for i in state.expressionsAtPosition[position]:
                    oldExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.currentAssignment[position] = newValue
                    newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.adjustCounts(oldExpValue, newExpValue)


proc moveDelta*[T](state: AllDifferentExcept0Constraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    var oldExpValue, newExpValue: T
    var oldValueCount, newValueCount: int

    case state.evalMethod:
        of PositionBased:
            # Handle old value (removing it)
            if oldValue != 0:
                oldValueCount = getCount(state.countTable, oldValue)
                doAssert oldValueCount >= 1, "oldValue should exist in count table"
                result -= oldValueCount - 1
                oldValueCount -= 1
                result += max(0, oldValueCount - 1)

            # Handle new value (adding it)
            if newValue != 0:
                newValueCount = getCount(state.countTable, newValue)
                result -= max(0, newValueCount - 1)
                newValueCount += 1
                result += newValueCount - 1

        of ExpressionBased:
            for i in state.expressionsAtPosition[position]:
                oldExpValue = state.expressions[i].evaluate(state.currentAssignment)

                state.currentAssignment[position] = newValue
                newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue

                # Handle old expression value
                if oldExpValue != 0:
                    oldValueCount = getCount(state.countTable, oldExpValue)
                    result -= oldValueCount - 1
                    oldValueCount -= 1
                    result += max(0, oldValueCount - 1)

                # Handle new expression value
                if newExpValue != 0:
                    newValueCount = getCount(state.countTable, newExpValue)
                    result -= max(0, newValueCount - 1)
                    newValueCount += 1
                    result += newValueCount - 1
