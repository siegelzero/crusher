import std/[packedsets, tables]

import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    StateEvalMethod* = enum
        ExpressionBased,
        PositionBased
    
    AllDifferentState*[T] = ref object
        count*: Table[T, int]
        currentAssignment*: Table[int, T]
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions: PackedSet[int]
            of ExpressionBased:
                expressions: seq[Expression[T]]
                expressionsAtPosition: Table[int, seq[Expression[T]]]

################################################################################
# AllDifferentState Creation
################################################################################

func init*[T](state: AllDifferentState[T], positions: openArray[T]) =
    state.cost = 0
    state.evalMethod = PositionBased
    state.positions = toPackedSet[T](positions)
    state.count = initTable[T, int]()
    state.currentAssignment = initTable[int, T]()

func init*[T](state: AllDifferentState[T], expressions: seq[Expression[T]]) =
    state.cost = 0
    state.evalMethod = ExpressionBased

    state.expressionsAtPosition = initTable[int, seq[Expression[T]]]()

    for exp in expressions:
        for pos in exp.positions.items:
            if pos in state.expressionsAtPosition:
                state.expressionsAtPosition[pos].add(exp)
            else:
                state.expressionsAtPosition[pos] = @[exp]

    state.expressions = expressions
    state.count = initTable[T, int]()
    state.currentAssignment = initTable[int, T]()

func newAllDifferentState*[T](positions: openArray[T] ): AllDifferentState[T] =
    # Allocates and initializes new AllDifferentState[T]
    new(result)
    result.init(positions)

func newAllDifferentState*[T](expressions: seq[Expression[T]]): AllDifferentState[T] =
    # Allocates and initializes new AllDifferentState[T]
    new(result)
    result.init(expressions)

################################################################################
# AllDifferentState utility functions
################################################################################

func decrementCount[T](state: AllDifferentState[T], value: T) {.inline.} =
    state.count[value] -= 1

func incrementCount[T](state: AllDifferentState[T], value: T) {.inline.} =
    if value in state.count:
        state.count[value] += 1
    else:
        state.count[value] = 1

func contribution*[T](state: AllDifferentState[T], value: T): int {.inline.} =
    max(0, state.count.getOrDefault(value) - 1)

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
        
        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                state.incrementCount(value)

    for value, count in state.count.pairs:
        state.cost += count - 1
                

proc updatePosition*[T](state: AllDifferentState[T], position: int, newValue: T) =
    case state.evalMethod:
        of PositionBased:
            let oldValue = state.currentAssignment[position]

            if oldValue != newValue:
                state.cost -= state.contribution(oldValue)
                state.cost -= state.contribution(newValue)
                state.decrementCount(oldValue)

                state.currentAssignment[position] = newValue

                state.incrementCount(newValue)
                state.cost += state.contribution(oldValue)
                state.cost += state.contribution(newValue)

        of ExpressionBased:
            var oldExpValue, newExpValue: T
            let oldValue = state.currentAssignment[position]

            if oldValue != newValue:
                for exp in state.expressionsAtPosition[position]:
                    oldExpValue = exp.evaluate(state.currentAssignment)
                    state.currentAssignment[position] = newValue
                    newExpValue = exp.evaluate(state.currentAssignment)

                    if oldExpValue != newExpValue:
                        state.cost -= state.contribution(oldExpValue)
                        state.cost -= state.contribution(newExpValue)
                        state.decrementCount(oldExpValue)

                        state.incrementCount(newExpValue)
                        state.cost += state.contribution(oldExpValue)
                        state.cost += state.contribution(newExpValue)



proc moveDelta*[T](state: AllDifferentState[T], position: int, oldValue, newValue: T): int =
    if oldvalue == newValue:
        return 0

    var oldExpValue, newExpValue, oldValueCount, newValueCount: int

    case state.evalMethod:
        of PositionBased:
            oldValueCount = state.count.getOrDefault(oldValue)
            doAssert oldValueCount >= 1
            result -= max(0, oldValueCount - 1)
            oldValueCount -= 1
            result += max(0, oldValueCount - 1)

            newValueCount = state.count.getOrDefault(newValue)
            result -= max(0, newValueCount - 1)
            newValueCount += 1
            result += max(0, newValueCount - 1)

        of ExpressionBased:
            for exp in state.expressionsAtPosition[position]:
                oldExpValue = exp.evaluate(state.currentAssignment)

                oldValueCount = state.count.getOrDefault(oldExpValue)
                result -= max(0, oldValueCount - 1)
                oldValueCount -= 1
                result += max(0, oldValueCount - 1)
            
                state.currentAssignment[position] = newValue
                newExpValue = exp.evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue

                newValueCount = state.count.getOrDefault(newExpValue)
                result -= max(0, newValueCount - 1)
                newValueCount += 1
                result += max(0, newValueCount - 1)