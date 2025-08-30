import std/[packedsets, sequtils, tables]

import ../expressions
import common

################################################################################
# Type definitions
################################################################################

type
    GlobalCardinalityConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        valueCardinalities*: Table[T, int]    # Required cardinalities for each value
        currentCounts*: Table[T, int]         # Current count of each value
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions*: PackedSet[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# GlobalCardinalityConstraint creation
################################################################################

func newGlobalCardinalityConstraint*[T](positions: openArray[int], cardinalities: Table[T, int]): GlobalCardinalityConstraint[T] =
    # Allocates and initializes new GlobalCardinalityConstraint[T] for positions
    new(result)
    result = GlobalCardinalityConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        valueCardinalities: cardinalities,
        currentCounts: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )

func newGlobalCardinalityConstraint*[T](expressions: seq[AlgebraicExpression[T]], cardinalities: Table[T, int]): GlobalCardinalityConstraint[T] =
    # Allocates and initializes new GlobalCardinalityConstraint[T] for expressions
    new(result)
    result = GlobalCardinalityConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        valueCardinalities: cardinalities,
        currentCounts: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )

    # Build mapping from positions to expressions that depend on them
    for i, exp in expressions:
        for pos in exp.positions.items:
            if pos in result.expressionsAtPosition:
                result.expressionsAtPosition[pos].add(i)
            else:
                result.expressionsAtPosition[pos] = @[i]

################################################################################
# GlobalCardinalityConstraint utility functions
################################################################################

func getRequiredCardinality[T](state: GlobalCardinalityConstraint[T], value: T): int {.inline.} =
    # Get required cardinality for a value (0 if not specified)
    return state.valueCardinalities.getOrDefault(value, 0)

func getCurrentCount[T](state: GlobalCardinalityConstraint[T], value: T): int {.inline.} =
    # Get current count for a value (0 if not present)
    return state.currentCounts.getOrDefault(value, 0)

func penaltyContribution[T](state: GlobalCardinalityConstraint[T], value: T): int {.inline.} =
    # Penalty contribution for a single value
    abs(state.getCurrentCount(value) - state.getRequiredCardinality(value))

func adjustCounts[T](state: GlobalCardinalityConstraint[T], oldValue, newValue: T) {.inline.} =
    # Adjust value counts and state cost for the removal of oldValue and addition of newValue
    if oldValue == newValue:
        return

    # Remove old penalty contributions
    state.cost -= state.penaltyContribution(oldValue)
    state.cost -= state.penaltyContribution(newValue)

    # Update counts
    let oldCount = state.getCurrentCount(oldValue)
    let newCount = state.getCurrentCount(newValue)

    if oldCount > 1:
        state.currentCounts[oldValue] = oldCount - 1
    else:
        state.currentCounts.del(oldValue)

    state.currentCounts[newValue] = newCount + 1

    # Add new penalty contributions
    state.cost += state.penaltyContribution(oldValue)
    state.cost += state.penaltyContribution(newValue)

################################################################################
# GlobalCardinalityConstraint initialization and updates
################################################################################

proc initialize*[T](state: GlobalCardinalityConstraint[T], assignment: seq[T]) =
    # Reset all state before initialization
    state.cost = 0
    state.currentAssignment.clear()
    state.currentCounts.clear()

    var value: T
    case state.evalMethod:
        of PositionBased:
            # Count values at each position
            for pos in state.positions:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                let currentCount = state.getCurrentCount(value)
                state.currentCounts[value] = currentCount + 1

        of ExpressionBased:
            # Store assignment for all relevant positions
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            # Evaluate expressions and count their values
            for exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                let currentCount = state.getCurrentCount(value)
                state.currentCounts[value] = currentCount + 1

    # Compute total penalty based on cardinality violations
    for requiredValue, requiredCount in state.valueCardinalities.pairs:
        state.cost += abs(state.getCurrentCount(requiredValue) - requiredCount)

proc updatePosition*[T](state: GlobalCardinalityConstraint[T], position: int, newValue: T) =
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

proc moveDelta*[T](state: GlobalCardinalityConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    case state.evalMethod:
        of PositionBased:
            # Get current counts and required cardinalities
            let oldCount_old = state.getCurrentCount(oldValue)
            let oldCount_new = state.getCurrentCount(newValue) 
            let req_old = state.getRequiredCardinality(oldValue)
            let req_new = state.getRequiredCardinality(newValue)

            # Current penalty contribution from these two values
            let currentPenalty = abs(oldCount_old - req_old) + abs(oldCount_new - req_new)

            # Penalty after hypothetical move
            let newPenalty = abs(oldCount_old - 1 - req_old) + abs(oldCount_new + 1 - req_new)

            return newPenalty - currentPenalty

        of ExpressionBased:
            result = 0
            for i in state.expressionsAtPosition[position]:
                # Get current expression value
                let oldExprValue = state.expressions[i].evaluate(state.currentAssignment)

                # Temporarily change position and evaluate
                state.currentAssignment[position] = newValue
                let newExprValue = state.expressions[i].evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue  # Restore

                if oldExprValue != newExprValue:
                    # Compute penalty delta for this value change
                    let oldCount_old = state.getCurrentCount(oldExprValue)
                    let oldCount_new = state.getCurrentCount(newExprValue)
                    let req_old = state.getRequiredCardinality(oldExprValue)
                    let req_new = state.getRequiredCardinality(newExprValue)

                    result -= abs(oldCount_old - req_old)
                    result -= abs(oldCount_new - req_new)
                    result += abs(oldCount_old - 1 - req_old) 
                    result += abs(oldCount_new + 1 - req_new)
