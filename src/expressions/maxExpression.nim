import std/[packedsets, tables, sequtils]
import algebraic, types

################################################################################
# Type definitions for MaxExpression
################################################################################

type
    MaxExpression*[T] = ref object
        value*: T
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        case evalMethod*: StateEvalMethod
            of PositionBased:
                discard
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# MaxExpression creation
################################################################################

func newMaxExpression*[T](positions: openArray[int]): MaxExpression[T] =
    result = MaxExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T]()
    )

func newMaxExpression*[T](expressions: openArray[AlgebraicExpression[T]]): MaxExpression[T] =
    var allPositions = initPackedSet[int]()

    # Collect all positions involved in the expressions
    let expressionsAtPosition = buildExpressionPositionMap(expressions)
    for exp in expressions:
        allPositions.incl(exp.positions)

    result = MaxExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[int, T](),
        expressions: @expressions,
        expressionsAtPosition: expressionsAtPosition
    )

################################################################################
# MaxExpression initialization
################################################################################

func initialize*[T](state: MaxExpression[T], assignment: seq[T]) =
    # Initialize the MaxExpression with the given assignment, and updates the value.
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]
    state.value = state.evaluate(assignment)

func evaluate*[T](state: MaxExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var maxValue: T = low(T)
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions.items:
                maxValue = max(maxValue, assignment[pos])
        of ExpressionBased:
            for exp in state.expressions:
                maxValue = max(maxValue, exp.evaluate(assignment))
    return maxValue

func `$`*[T](state: MaxExpression[T]): string = $(state.value)

################################################################################
# MaxExpression updates
################################################################################

func updatePosition*[T](state: MaxExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    let oldValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue

    case state.evalMethod:
        of PositionBased:
            # For position-based: use smart updating logic
            if newValue > state.value:
                # New value is larger than current max, so it becomes the new max
                state.value = newValue
            elif oldValue == state.value and newValue < oldValue:
                # We're replacing the current maximum with a smaller value
                # Need to find the new maximum among all values
                state.value = max(state.currentAssignment.values.toSeq)
            # Otherwise, the maximum doesn't change

        of ExpressionBased:
            # For expression-based, always recalculate since tracking which expression
            # previously provided the max is complex (the old optimization was buggy)
            state.value = state.evaluate(state.currentAssignment)

func moveDelta*[T](state: MaxExpression[T], position: int, oldValue, newValue: T): T {.inline.} =
    # Returns the change in maximum value obtained by reassigning position from oldValue to newValue.
    let currentMax = state.value

    case state.evalMethod:
        of PositionBased:
            # Use optimized logic for position-based
            if newValue > currentMax:
                # New value becomes the maximum
                return newValue - currentMax
            elif oldValue == currentMax and newValue < oldValue:
                # We're changing the current maximum to a smaller value
                # Need to find what the new maximum would be among remaining values
                var newMax: T = low(T)
                for pos in state.positions.items:
                    let val = if pos == position: newValue else: state.currentAssignment[pos]
                    if val > newMax:
                        newMax = val
                return newMax - currentMax
            else:
                # Maximum doesn't change
                return 0

        of ExpressionBased:
            if position notin state.expressionsAtPosition:
                return 0

            let affected = state.expressionsAtPosition[position]

            # Compute max of affected expressions with current (old) value
            var maxOldAffected: T = low(T)
            for i in affected:
                maxOldAffected = max(maxOldAffected, state.expressions[i].evaluate(state.currentAssignment))

            # Compute max of affected expressions with new value
            state.currentAssignment[position] = newValue
            var maxNewAffected: T = low(T)
            for i in affected:
                maxNewAffected = max(maxNewAffected, state.expressions[i].evaluate(state.currentAssignment))
            state.currentAssignment[position] = oldValue

            if maxNewAffected > currentMax:
                return maxNewAffected - currentMax
            elif maxOldAffected >= currentMax and maxNewAffected < maxOldAffected:
                # Max-providing expression decreased — need full scan
                state.currentAssignment[position] = newValue
                let newMax = state.evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue
                return newMax - currentMax
            else:
                return 0

proc deepCopy*[T](state: MaxExpression[T]): MaxExpression[T] =
    # Creates a deep copy of a MaxExpression for thread-safe parallel processing
    case state.evalMethod:
        of PositionBased:
            result = MaxExpression[T](
                evalMethod: PositionBased,
                value: state.value,
                positions: state.positions,  # PackedSet is a value type, safe to copy
                currentAssignment: state.currentAssignment  # Table is a value type, safe to copy
            )
        of ExpressionBased:
            # Deep copy all expressions to ensure thread safety
            var copiedExpressions = newSeq[AlgebraicExpression[T]](state.expressions.len)
            for i, expr in state.expressions:
                copiedExpressions[i] = expr.deepCopy()
            result = MaxExpression[T](
                evalMethod: ExpressionBased,
                value: state.value,
                positions: state.positions,  # PackedSet is a value type, safe to copy
                currentAssignment: state.currentAssignment,  # Table is a value type, safe to copy
                expressions: copiedExpressions,
                expressionsAtPosition: state.expressionsAtPosition  # Table is a value type, safe to copy
            )

################################################################################
# MaxExpression creation helpers for constraint syntax
################################################################################

func max*[T](expressions: openArray[AlgebraicExpression[T]]): MaxExpression[T] =
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use efficient position-based approach if all expressions are simple variables
        return newMaxExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newMaxExpression[T](expressions)
