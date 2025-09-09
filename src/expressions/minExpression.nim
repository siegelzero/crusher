import std/[packedsets, tables, sequtils]
import algebraic, types

################################################################################
# Type definitions for MinExpression
################################################################################

type
    MinExpression*[T] = ref object
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
# MinExpression creation
################################################################################

func newMinExpression*[T](positions: openArray[int]): MinExpression[T] =
    result = MinExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T]()
    )

func newMinExpression*[T](expressions: openArray[AlgebraicExpression[T]]): MinExpression[T] =
    var allPositions = initPackedSet[int]()

    # Collect all positions involved in the expressions
    let expressionsAtPosition = buildExpressionPositionMap(expressions)
    for exp in expressions:
        allPositions.incl(exp.positions)

    result = MinExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[int, T](),
        expressions: @expressions,
        expressionsAtPosition: expressionsAtPosition
    )

################################################################################
# MinExpression initialization
################################################################################

func initialize*[T](state: MinExpression[T], assignment: seq[T]) =
    # Initialize the MinExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
    state.value = state.evaluate(assignment)

func evaluate*[T](state: MinExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var minValue: T = high(T)
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                minValue = min(minValue, assignment[pos])
        of ExpressionBased:
            for exp in state.expressions:
                minValue = min(minValue, exp.evaluate(assignment))
    return minValue

func `$`*[T](state: MinExpression[T]): string = $(state.value)

################################################################################
# MinExpression updates
################################################################################

func updatePosition*[T](state: MinExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    let oldValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue

    case state.evalMethod:
        of PositionBased:
            # For position-based: use smart updating logic
            if newValue < state.value:
                # New value is smaller than current min, so it becomes the new min
                state.value = newValue
            elif oldValue == state.value and newValue > oldValue:
                # We're replacing the current minimum with a larger value
                # Need to find the new minimum among all values
                state.value = min(state.currentAssignment.values.toSeq)
            # Otherwise, the minimum doesn't change

        of ExpressionBased:
            # Only evaluate expressions that depend on the changed position
            for idx in state.expressionsAtPosition[position]:
                let expValue = state.expressions[idx].evaluate(state.currentAssignment)
                if expValue < state.value:
                    state.value = expValue
                elif expValue == state.value and newValue > oldValue:
                    state.value = state.evaluate(state.currentAssignment)
                    break

func moveDelta*[T](state: MinExpression[T], position: int, oldValue, newValue: T): T {.inline.} =
    # Returns the change in minimum value obtained by reassigning position from oldValue to newValue.
    let currentMin = state.value

    case state.evalMethod:
        of PositionBased:
            # Use optimized logic for position-based
            if newValue < currentMin:
                # New value becomes the minimum
                return newValue - currentMin
            elif oldValue == currentMin and newValue > oldValue:
                # We're changing the current minimum to a larger value
                # Need to find what the new minimum would be among remaining values
                var newMin: T = high(T)
                for pos in state.positions:
                    let val = if pos == position: newValue else: state.currentAssignment[pos]
                    if val < newMin:
                        newMin = val
                return newMin - currentMin
            else:
                # Minimum doesn't change
                return 0

        of ExpressionBased:
            # For expression-based: compute new minimum by evaluating all expressions
            var tempAssignment = state.currentAssignment
            tempAssignment[position] = newValue

            let newMin = state.evaluate(tempAssignment)
            return newMin - currentMin

proc deepCopy*[T](state: MinExpression[T]): MinExpression[T] =
    # Creates a deep copy of a MinExpression for thread-safe parallel processing
    new(result)
    result.value = state.value
    result.positions = state.positions  # PackedSet is a value type, safe to copy
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy
    result.evalMethod = state.evalMethod

    case state.evalMethod:
        of PositionBased:
            # All fields already copied - no additional mutable state
            discard
        of ExpressionBased:
            result.expressions = state.expressions  # seq[AlgebraicExpression] should be immutable
            result.expressionsAtPosition = state.expressionsAtPosition  # Table is a value type, safe to copy

################################################################################
# MinExpression creation helpers for constraint syntax
################################################################################

func min*[T](expressions: openArray[AlgebraicExpression[T]]): MinExpression[T] =
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use efficient position-based approach if all expressions are simple variables
        return newMinExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newMinExpression[T](expressions)
