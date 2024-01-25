import std/[packedsets, sequtils, tables]

import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    StateEvalMethod = enum
        ExpressionBased,
        PositionBased

    AllDifferentState*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                count: seq[int]
                positions: PackedSet[int]
            of ExpressionBased:
                countTable: Table[T, int]
                expressions: seq[AlgebraicExpression[T]]
                expressionsAtPosition: Table[int, seq[int]]

################################################################################
# AllDifferentState Creation
################################################################################

func init*[T](state: AllDifferentState[T], positions: openArray[T]) =
    state.cost = 0
    state.evalMethod = PositionBased
    state.positions = toPackedSet[int](positions)
    state.count = newSeq[int]()
    state.currentAssignment = initTable[int, T]()

func init*[T](state: AllDifferentState[T], expressions: seq[AlgebraicExpression[T]]) =
    state.cost = 0
    state.evalMethod = ExpressionBased
    state.expressionsAtPosition = initTable[int, seq[int]]()

    for i, exp in expressions:
        for pos in exp.positions.items:
            if pos in state.expressionsAtPosition:
                state.expressionsAtPosition[pos].add(i)
            else:
                state.expressionsAtPosition[pos] = @[i]

    state.expressions = expressions
    state.countTable = initTable[T, int]()
    state.currentAssignment = initTable[int, T]()

func newAllDifferentState*[T](positions: openArray[T] ): AllDifferentState[T] =
    # Allocates and initializes new AllDifferentState[T]
    new(result)
    result.init(positions)

func newAllDifferentState*[T](expressions: seq[AlgebraicExpression[T]]): AllDifferentState[T] =
    # Allocates and initializes new AllDifferentState[T]
    new(result)
    result.init(expressions)

################################################################################
# AllDifferentState utility functions
################################################################################

func getCount[T](state: AllDifferentState[T], value: T): int {.inline.} =
    case state.evalMethod:
        of PositionBased:
            if value >= state.count.len:
                # Extend count seq with 0s if necessary
                state.count &= repeat(0, value - state.count.len + 1)
                return 0
            return state.count[value]
        of ExpressionBased:
            return state.countTable.getOrDefault(value)

func decrementCount[T](state: AllDifferentState[T], value: T) {.inline.} =
    case state.evalMethod:
        of PositionBased:
            state.count[value] -= 1
        of ExpressionBased:
            state.countTable[value] -= 1

func incrementCount[T](state: AllDifferentState[T], value: T) {.inline.} =
    case state.evalMethod:
        of PositionBased:
            if value < state.count.len:
                state.count[value] += 1
            else:
                # Extend count seq with 0s if needed
                state.count &= repeat(0, value - state.count.len + 1)
                state.count[value] = 1
        of ExpressionBased:
            if value in state.countTable:
                state.countTable[value] += 1
            else:
                state.countTable[value] = 1


func contribution*[T](state: AllDifferentState[T], value: T): int {.inline.} =
    max(0, state.getCount(value) - 1)

################################################################################
# AllDifferentState initialization and updates
################################################################################

proc initialize*[T](state: AllDifferentState[T], assignment: seq[T]) =
    var value: T
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                state.incrementCount(value)

            for count in state.count:
                state.cost += max(0, count - 1)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                state.incrementCount(value)

            for value, count in state.countTable.pairs:
                state.cost += max(0, count - 1)

proc adjustCounts*[T](state: AllDifferentState[T], oldValue, newValue: T) {.inline.} =
    # Adjust value counts and state cost for the removal of oldValue and addition of newValue
    state.cost -= state.contribution(oldValue)
    state.cost -= state.contribution(newValue)
    state.decrementCount(oldvalue)
    state.incrementCount(newValue)
    state.cost += state.contribution(oldValue)
    state.cost += state.contribution(newValue)


proc updatePosition*[T](state: AllDifferentState[T], position: int, newValue: T) =
    # State Update assigning newValue to position
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


proc moveDelta*[T](state: AllDifferentState[T], position: int, oldValue, newValue: T): int =
    if oldvalue == newValue:
        return 0

    var oldExpValue, newExpValue, oldValueCount, newValueCount: int

    case state.evalMethod:
        of PositionBased:
            oldValueCount = state.getCount(oldValue)
            doAssert oldValueCount >= 1
            result -= oldValueCount - 1
            oldValueCount -= 1
            result += max(0, oldValueCount - 1)

            newValueCount = state.getCount(newValue)
            result -= max(0, newValueCount - 1)
            newValueCount += 1
            result += newValueCount - 1

        of ExpressionBased:
            for i in state.expressionsAtPosition[position]:
                oldExpValue = state.expressions[i].evaluate(state.currentAssignment)

                oldValueCount = state.getCount(oldExpValue)
                result -= oldValueCount - 1
                oldValueCount -= 1
                result += max(0, oldValueCount - 1)

                state.currentAssignment[position] = newValue
                newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue

                newValueCount = state.getCount(newExpValue)
                result -= max(0, newValueCount - 1)
                newValueCount += 1
                result += newValueCount - 1