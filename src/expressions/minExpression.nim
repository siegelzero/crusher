import std/[packedsets, tables]
import algebraic, types

################################################################################
# Type definitions for MinExpression
################################################################################

type
    MinExpression*[T] = ref object
        value*: T
        positions*: PackedSet[Natural]
        currentAssignment*: Table[Natural, T]
        case evalMethod*: StateEvalMethod
            of PositionBased:
                discard  # positions and currentAssignment are sufficient
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[Natural, seq[int]]  # position -> list of expression indices

################################################################################
# MinExpression creation
################################################################################

func newMinExpression*[T](positions: openArray[Natural]): MinExpression[T] =
    result = MinExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[Natural](positions),
        currentAssignment: initTable[Natural, T]()
    )

func newMinExpression*[T](expressions: seq[AlgebraicExpression[T]]): MinExpression[T] =
    var expressionsAtPos = initTable[Natural, seq[int]]()
    var allPositions = initPackedSet[Natural]()

    # Collect all positions involved in the expressions
    for i, exp in expressions:
        allPositions.incl(exp.positions)
        # Map each position to which expressions depend on it
        for pos in exp.positions:
            if pos notin expressionsAtPos:
                expressionsAtPos[pos] = @[]
            expressionsAtPos[pos].add(i)

    result = MinExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[Natural, T](),
        expressions: expressions,
        expressionsAtPosition: expressionsAtPos
    )

################################################################################
# MinExpression initialization
################################################################################

func initialize*[T](state: MinExpression[T], assignment: seq[T]) =
    # Initialize the MinExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]

    var minValue: T = high(T)
    case state.evalMethod:
        of PositionBased:
            # For position-based: minimum of variable values directly
            for pos in state.positions:
                minValue = min(minValue, assignment[pos])
        of ExpressionBased:
            # For expression-based: minimum of expression evaluations
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                minValue = min(minValue, expValue)

    state.value = minValue

func evaluate*[T](state: MinExpression[T], assignment: seq[T]|Table[Natural, T]): T {.inline.} =
    var minValue: T = high(T)
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                minValue = min(minValue, assignment[pos])
        of ExpressionBased:
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                minValue = min(minValue, expValue)
    return minValue

func `$`*[T](state: MinExpression[T]): string = $(state.value)

################################################################################
# MinExpression updates
################################################################################

func updatePosition*[T](state: MinExpression[T], position: Natural, newValue: T) {.inline.} =
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
                var minValue: T = high(T)
                for val in state.currentAssignment.values:
                    if val < minValue:
                        minValue = val
                state.value = minValue
            # Otherwise, the minimum doesn't change

        of ExpressionBased:
            # For expression-based: need to recalculate affected expressions
            # This is less efficient but more general
            var minValue: T = high(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(state.currentAssignment)
                minValue = min(minValue, expValue)
            state.value = minValue

func moveDelta*[T](state: MinExpression[T], position: Natural, oldValue, newValue: T): T {.inline.} =
    # Returns the change in minimum value obtained by reassigning position from oldValue to newValue.
    # If position is not part of this expression, return 0 (no change)
    if position notin state.positions:
        return 0

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

            var newMin: T = high(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(tempAssignment)
                newMin = min(newMin, expValue)

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

func min*[T](expressions: seq[AlgebraicExpression[T]]): MinExpression[T] =
    # Check if all expressions are simple variable references (RefNodes)
    var allRefs = true
    var positions: seq[Natural] = @[]

    for exp in expressions:
        if exp.node.kind == RefNode:
            positions.add(exp.node.position)
        else:
            allRefs = false

    if allRefs:
        # Use efficient position-based approach if all expressions are simple variables
        return newMinExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newMinExpression[T](expressions)