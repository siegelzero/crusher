import std/[packedsets, sequtils, tables]

import ../expressions

################################################################################
# Type definitions
################################################################################

type
    StateEvalMethod = enum
        ExpressionBased,
        PositionBased

    AllDifferentConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                count: seq[int]
                positions: PackedSet[Natural]
            of ExpressionBased:
                countTable: Table[T, int]
                expressions: seq[AlgebraicExpression[T]]
                expressionsAtPosition: Table[int, seq[int]]

################################################################################
# AllDifferentConstraint creation
################################################################################

func newAllDifferentConstraint*[T](positions: openArray[Natural] ): AllDifferentConstraint[T] =
    # Allocates and initializes new AllDifferentConstraint[T]
    new(result)
    result = AllDifferentConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[Natural](positions),
        count: newSeq[int](),
        currentAssignment: initTable[int, T](),
    )

func newAllDifferentConstraint*[T](expressions: seq[AlgebraicExpression[T]]): AllDifferentConstraint[T] =
    # Allocates and initializes new AllDifferentConstraint[T]
    new(result)
    result = AllDifferentConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        countTable: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )

    for i, exp in expressions:
        for pos in exp.positions.items:
            if pos in result.expressionsAtPosition:
                result.expressionsAtPosition[pos].add(i)
            else:
                result.expressionsAtPosition[pos] = @[i]

################################################################################
# AllDifferentConstraint utility functions
################################################################################

func getCount[T](state: AllDifferentConstraint[T], value: T): int {.inline.} =
    case state.evalMethod:
        of PositionBased:
            if value >= state.count.len:
                # Extend count seq with 0s if necessary
                state.count &= repeat(0, value - state.count.len + 1)
                return 0
            return state.count[value]
        of ExpressionBased:
            return state.countTable.getOrDefault(value)


func contribution[T](state: AllDifferentConstraint[T], value: T): int {.inline.} =
    max(0, state.getCount(value) - 1)


func decrementCount[T](state: AllDifferentConstraint[T], value: T) {.inline.} =
    case state.evalMethod:
        of PositionBased:
            state.count[value] -= 1
        of ExpressionBased:
            state.countTable[value] -= 1


func incrementCount[T](state: AllDifferentConstraint[T], value: T) {.inline.} =
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


proc adjustCounts[T](state: AllDifferentConstraint[T], oldValue, newValue: T) {.inline.} =
    # Adjust value counts and state cost for the removal of oldValue and addition of newValue
    state.cost -= state.contribution(oldValue)
    state.cost -= state.contribution(newValue)
    state.decrementCount(oldvalue)
    state.incrementCount(newValue)
    state.cost += state.contribution(oldValue)
    state.cost += state.contribution(newValue)

################################################################################
# AllDifferentConstraint initialization and updates
################################################################################

proc initialize*[T](state: AllDifferentConstraint[T], assignment: seq[T]) =
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


proc updatePosition*[T](state: AllDifferentConstraint[T], position: int, newValue: T) =
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


proc moveDelta*[T](state: AllDifferentConstraint[T], position: int, oldValue, newValue: T): int =
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