import std/[packedsets, sequtils, tables]
import types

################################################################################
# Type definitions for SumExpression
################################################################################

type
    SumExpression*[T] = ref object
        value*: T
        constant*: T
        positions*: PackedSet[Natural]
        currentAssignment*: Table[Natural, T]
        case evalMethod*: StateEvalMethod
            of PositionBased:
                coefficient*: Table[Natural, T]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

# SumExpression Creation

func newSumExpression*[T](positions: openArray[Natural]): SumExpression[T] =
    result = SumExpression[T](
        value: 0,
        constant: 0,
        positions: toPackedSet[Natural](positions),
        currentAssignment: initTable[Natural, T](),
        evalMethod: PositionBased,
        coefficient: initTable[Natural, T]()
    )

    for pos in positions:
        result.coefficient[pos] = 1

func newSumExpression*[T](positions: openArray[int]): SumExpression[T] =
    # Convenience constructor that converts int positions to Natural
    var naturalPositions = newSeq[Natural](positions.len)
    for i, pos in positions:
        naturalPositions[i] = Natural(pos)

    return newSumExpression[T](naturalPositions)

func newSumExpression*[T](coefficients: Table[Natural, T], constant: T = 0): SumExpression[T] =
    var positions = initPackedSet[Natural]()
    for pos in coefficients.keys:
        positions.incl(pos)

    result = SumExpression[T](
        value: constant,
        constant: constant,
        positions: positions,
        currentAssignment: initTable[Natural, T](),
        evalMethod: PositionBased,
        coefficient: coefficients
    )

func newSumExpression*[T](expressions: seq[AlgebraicExpression[T]]): SumExpression[T] =
    var positions = initPackedSet[Natural]()
    var expressionsAtPosition = initTable[int, seq[int]]()

    # Build position to expression mapping
    for i, exp in expressions:
        for pos in exp.positions:
            positions.incl(pos)
            if pos in expressionsAtPosition:
                expressionsAtPosition[pos].add(i)
            else:
                expressionsAtPosition[pos] = @[i]

    result = SumExpression[T](
        value: 0,
        constant: 0,
        positions: positions,
        currentAssignment: initTable[Natural, T](),
        evalMethod: ExpressionBased,
        expressions: expressions,
        expressionsAtPosition: expressionsAtPosition
    )

# SumExpression Initialization

func initialize*[T](state: SumExpression[T], assignment: seq[T]) =
    # Initialize the Sum Expression with the given assignment, and updates the value.
    state.value = state.constant

    # Store current assignment for all positions
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]

    case state.evalMethod:
        of PositionBased:
            # For position-based: sum coefficient[pos] * assignment[pos]
            for pos in state.positions:
                state.value += state.coefficient[pos] * assignment[pos]

        of ExpressionBased:
            # For expression-based: evaluate and sum all expressions
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                state.value += expValue

func evaluate*[T](expression: SumExpression[T], assignment: seq[T]|Table[Natural, T]): T {.inline.} =
    # Computes the value of the Sum Expression given the variable assignment.
    result = expression.constant

    case expression.evalMethod:
        of PositionBased:
            # For position-based: sum coefficient[pos] * assignment[pos]
            for pos in expression.positions:
                result += expression.coefficient[pos] * assignment[pos]

        of ExpressionBased:
            # For expression-based: evaluate and sum all expressions
            for exp in expression.expressions:
                let expValue = exp.evaluate(assignment)
                result += expValue

func `$`*[T](state: SumExpression[T]): string = $(state.value)

# SumExpression Updates

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
    var coefficients, assignment: Table[Natural, T]
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

func sum*[T](expressions: seq[AlgebraicExpression[T]]): SumExpression[T] =
    var positions = toPackedSet[Natural]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)

    if allRefs:
        # Use more efficient position-based constraint if all expressions are RefNodes
        return newSumExpression[T](toSeq(positions))
    else:
        # Use expression-based constraint for complex expressions
        return newSumExpression[T](expressions)