import std/[packedsets, sequtils, tables]
import types

################################################################################
# Type definitions for SumExpression
################################################################################

type
    SumExpression*[T] = ref object
        value*: T
        constant*: T
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        case evalMethod*: StateEvalMethod
            of PositionBased:
                coefficient*: Table[int, T]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# SumExpression Creation
################################################################################

func newSumExpression*[T](positions: openArray[int]): SumExpression[T] =
    result = SumExpression[T](
        value: 0,
        constant: 0,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T](),
        evalMethod: PositionBased,
        coefficient: initTable[int, T]()
    )

    for pos in positions:
        result.coefficient[pos] = 1


func newSumExpression*[T](coefficients: Table[int, T], constant: T = 0): SumExpression[T] =
    var positions = initPackedSet[int]()
    for pos in coefficients.keys:
        positions.incl(pos)

    result = SumExpression[T](
        value: constant,
        constant: constant,
        positions: positions,
        currentAssignment: initTable[int, T](),
        evalMethod: PositionBased,
        coefficient: coefficients
    )

func newSumExpression*[T](expressions: openArray[AlgebraicExpression[T]]): SumExpression[T] =
    var positions = initPackedSet[int]()
    # Build position to expression mapping
    let expressionsAtPosition = buildExpressionPositionMap(expressions)
    for exp in expressions:
        positions.incl(exp.positions)

    result = SumExpression[T](
        value: 0,
        constant: 0,
        positions: positions,
        currentAssignment: initTable[int, T](),
        evalMethod: ExpressionBased,
        expressions: @expressions,
        expressionsAtPosition: expressionsAtPosition
    )

################################################################################
# SumExpression Initialization
################################################################################

func initialize*[T](state: SumExpression[T], assignment: seq[T]) =
    # Initialize the SumExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
    state.value = state.evaluate(assignment)

func evaluate*[T](state: SumExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    # Computes the value of the SumExpression given the variable assignment.
    result = state.constant

    case state.evalMethod:
        of PositionBased:
            # For position-based: sum coefficient[pos] * assignment[pos]
            for pos in state.positions:
                result += state.coefficient[pos] * assignment[pos]

        of ExpressionBased:
            # For expression-based: evaluate and sum all expressions
            for exp in state.expressions:
                result += exp.evaluate(assignment)

func `$`*[T](state: SumExpression[T]): string = $(state.value)

################################################################################
# SumExpression Updates
################################################################################

func updatePosition*[T](state: SumExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    let oldValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue

    case state.evalMethod:
        of PositionBased:
            # For position-based: simple coefficient-based update
            state.value += state.coefficient[position] * (newValue - oldValue)

        of ExpressionBased:
            # For expression-based: re-evaluate affected expressions
            for i in state.expressionsAtPosition[position]:
                # Subtract old expression value
                state.currentAssignment[position] = oldValue
                let oldExpValue = state.expressions[i].evaluate(state.currentAssignment)

                # Add new expression value
                state.currentAssignment[position] = newValue
                let newExpValue = state.expressions[i].evaluate(state.currentAssignment)

                state.value += (newExpValue - oldExpValue)

func moveDelta*[T](state: SumExpression[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns the change in value obtained by reassigning position from oldValue to newValue.
    case state.evalMethod:
        of PositionBased:
            # For position-based: simple coefficient calculation
            return state.coefficient[position] * (newValue - oldValue)

        of ExpressionBased:
            # For expression-based: calculate delta from affected expressions
            result = 0
            var tempAssignment = state.currentAssignment

            for i in state.expressionsAtPosition[position]:
                # Calculate old expression value
                tempAssignment[position] = oldValue
                let oldExpValue = state.expressions[i].evaluate(tempAssignment)

                # Calculate new expression value
                tempAssignment[position] = newValue
                let newExpValue = state.expressions[i].evaluate(tempAssignment)

                result += (newExpValue - oldExpValue)

func linearize*[T](expression: AlgebraicExpression[T]): SumExpression[T] =
    # Converts linear expression to a SumExpression
    var constant: T
    var coefficients, assignment: Table[int, T]
    # evaluate with all variables zero to get constant coefficient
    for pos in expression.positions:
        assignment[pos] = 0

    constant = expression.evaluate(assignment)
    # extract each coefficient
    for pos in expression.positions:
        assignment[pos] = 1
        coefficients[pos] = expression.evaluate(assignment) - constant
        assignment[pos] = 0

    return newSumExpression[T](coefficients, constant)

proc deepCopy*[T](state: SumExpression[T]): SumExpression[T] =
    # Creates a deep copy of a SumExpression for thread-safe parallel processing
    new(result)
    result.value = state.value
    result.constant = state.constant
    result.positions = state.positions  # PackedSet is a value type, safe to copy
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy
    result.evalMethod = state.evalMethod

    case state.evalMethod:
        of PositionBased:
            result.coefficient = state.coefficient  # Table is a value type, safe to copy
        of ExpressionBased:
            result.expressions = state.expressions  # seq[AlgebraicExpression] should be immutable
            result.expressionsAtPosition = state.expressionsAtPosition  # Table is a value type, safe to copy

func sum*[T](expressions: openArray[AlgebraicExpression[T]]): SumExpression[T] =
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position-based constraint if all expressions are RefNodes
        return newSumExpression[T](positions)
    else:
        # Use expression-based constraint for complex expressions
        return newSumExpression[T](expressions)
