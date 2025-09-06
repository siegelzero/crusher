import std/[packedsets, tables]
import algebraic, types

################################################################################
# Type definitions for MaxExpression
################################################################################

type
    MaxExpression*[T] = ref object
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
# MaxExpression creation
################################################################################

func newMaxExpression*[T](positions: openArray[Natural]): MaxExpression[T] =
    result = MaxExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[Natural](positions),
        currentAssignment: initTable[Natural, T]()
    )

func newMaxExpression*[T](expressions: seq[AlgebraicExpression[T]]): MaxExpression[T] =
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

    result = MaxExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[Natural, T](),
        expressions: expressions,
        expressionsAtPosition: expressionsAtPos
    )

################################################################################
# MaxExpression initialization
################################################################################

func initialize*[T](state: MaxExpression[T], assignment: seq[T]) =
    # Initialize the MaxExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]

    var maxValue: T = low(T)
    case state.evalMethod:
        of PositionBased:
            # For position-based: maximum of variable values directly
            for pos in state.positions:
                maxValue = max(maxValue, assignment[pos])
        of ExpressionBased:
            # For expression-based: maximum of expression evaluations
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                maxValue = max(maxValue, expValue)

    state.value = maxValue

func evaluate*[T](state: MaxExpression[T], assignment: seq[T]|Table[Natural, T]): T {.inline.} =
    var maxValue: T = low(T)
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                maxValue = max(maxValue, assignment[pos])
        of ExpressionBased:
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                maxValue = max(maxValue, expValue)
    return maxValue

func `$`*[T](state: MaxExpression[T]): string = $(state.value)

################################################################################
# MaxExpression updates
################################################################################

func updatePosition*[T](state: MaxExpression[T], position: Natural, newValue: T) {.inline.} =
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
                var maxValue: T = low(T)
                for val in state.currentAssignment.values:
                    if val > maxValue:
                        maxValue = val
                state.value = maxValue
            # Otherwise, the maximum doesn't change

        of ExpressionBased:
            # For expression-based: need to recalculate affected expressions
            # This is less efficient but more general
            var maxValue: T = low(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(state.currentAssignment)
                maxValue = max(maxValue, expValue)
            state.value = maxValue

func moveDelta*[T](state: MaxExpression[T], position: Natural, oldValue, newValue: T): T {.inline.} =
    # Returns the change in maximum value obtained by reassigning position from oldValue to newValue.
    # If position is not part of this expression, return 0 (no change)
    if position notin state.positions:
        return 0

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
                for pos in state.positions:
                    let val = if pos == position: newValue else: state.currentAssignment[pos]
                    if val > newMax:
                        newMax = val
                return newMax - currentMax
            else:
                # Maximum doesn't change
                return 0

        of ExpressionBased:
            # For expression-based: compute new maximum by evaluating all expressions
            var tempAssignment = state.currentAssignment
            tempAssignment[position] = newValue

            var newMax: T = low(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(tempAssignment)
                newMax = max(newMax, expValue)

            return newMax - currentMax

proc deepCopy*[T](state: MaxExpression[T]): MaxExpression[T] =
    # Creates a deep copy of a MaxExpression for thread-safe parallel processing
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
# MaxExpression creation helpers for constraint syntax
################################################################################

func max*[T](expressions: seq[AlgebraicExpression[T]]): MaxExpression[T] =
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
        return newMaxExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newMaxExpression[T](expressions)