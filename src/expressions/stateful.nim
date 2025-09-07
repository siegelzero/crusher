import std/[tables, sets, packedsets]
import types
import sumExpression
import minExpression
import maxExpression

################################################################################
# StatefulAlgebraicExpression - mirrors Sum/Min/MaxExpression pattern
################################################################################

type
    StatefulAlgebraicExpression*[T] = ref object
        # Stateful wrapper for AlgebraicExpression
        # Maintains current value and assignment like Sum/Min/MaxExpression
        algebraicExpr*: AlgebraicExpression[T]
        positions*: PackedSet[Natural]
        value*: T
        currentAssignment*: Table[Natural, T]

func newStatefulAlgebraicExpression*[T](expr: AlgebraicExpression[T]): StatefulAlgebraicExpression[T] =
    result = StatefulAlgebraicExpression[T](
        algebraicExpr: expr,
        positions: expr.positions,
        value: 0,
        currentAssignment: initTable[Natural, T]()
    )

func initialize*[T](expr: StatefulAlgebraicExpression[T], assignment: seq[T]) =
    # Initialize with the given assignment
    expr.currentAssignment.clear()
    for position in expr.positions:
        expr.currentAssignment[position] = assignment[position]
    expr.value = expr.algebraicExpr.evaluate(assignment)

func updatePosition*[T](expr: StatefulAlgebraicExpression[T], position: Natural, newValue: T) =
    # Update a single position incrementally
    if position in expr.positions:
        # Calculate the delta first for incremental update
        let oldValue = expr.currentAssignment[position]
        let delta = expr.moveDelta(position, oldValue, newValue)

        # Update assignment and value incrementally
        expr.currentAssignment[position] = newValue
        expr.value += delta

func moveDelta*[T](expr: StatefulAlgebraicExpression[T], position: Natural,
                   oldValue, newValue: T): T =
    # Calculate the change in value
    if position notin expr.positions:
        return 0

    # Store current value
    let currentValue = expr.value

    # Temporarily update and evaluate using table-based evaluation
    let savedValue = expr.currentAssignment[position]
    expr.currentAssignment[position] = newValue
    let newTotalValue = expr.algebraicExpr.evaluate(expr.currentAssignment)

    # Restore original value
    expr.currentAssignment[position] = savedValue

    return newTotalValue - currentValue

################################################################################
# Unified Expression wrapper type
################################################################################

type
    ExpressionKind* = enum
        StatefulAlgebraicExpr
        SumExpr
        MinExpr
        MaxExpr
        ConstantExpr

    Expression*[T] = object
        positions*: PackedSet[Natural]
        case kind*: ExpressionKind
        of StatefulAlgebraicExpr:
            algebraicExpr*: StatefulAlgebraicExpression[T]
        of SumExpr:
            sumExpr*: SumExpression[T]
        of MinExpr:
            minExpr*: MinExpression[T]
        of MaxExpr:
            maxExpr*: MaxExpression[T]
        of ConstantExpr:
            constantValue*: T

# Generic template to wrap any expression type into Expression wrapper
template wrap*[T](expr: typed): Expression[T] =
    when expr is StatefulAlgebraicExpression[T]:
        Expression[T](
            kind: StatefulAlgebraicExpr,
            algebraicExpr: expr,
            positions: expr.positions
        )
    elif expr is AlgebraicExpression[T]:
        # Convert AlgebraicExpression to StatefulAlgebraicExpression
        let statefulExpr = newStatefulAlgebraicExpression(expr)
        Expression[T](
            kind: StatefulAlgebraicExpr,
            algebraicExpr: statefulExpr,
            positions: expr.positions
        )
    elif expr is SumExpression[T]:
        Expression[T](
            kind: SumExpr,
            sumExpr: expr,
            positions: expr.positions
        )
    elif expr is MinExpression[T]:
        Expression[T](
            kind: MinExpr,
            minExpr: expr,
            positions: expr.positions
        )
    elif expr is MaxExpression[T]:
        Expression[T](
            kind: MaxExpr,
            maxExpr: expr,
            positions: expr.positions
        )
    elif expr is T:
        # Handle constant values
        Expression[T](
            kind: ConstantExpr,
            constantValue: expr,
            positions: toPackedSet[Natural]([])
        )
    else:
        {.error: "Unsupported expression type for wrap".}

# Helper functions for Expression operations
func initialize*[T](expr: Expression[T], assignment: seq[T]) =
    case expr.kind
    of StatefulAlgebraicExpr:
        expr.algebraicExpr.initialize(assignment)
    of SumExpr:
        expr.sumExpr.initialize(assignment)
    of MinExpr:
        expr.minExpr.initialize(assignment)
    of MaxExpr:
        expr.maxExpr.initialize(assignment)
    of ConstantExpr:
        discard  # Constants don't need initialization

func getValue*[T](expr: Expression[T]): T =
    case expr.kind
    of StatefulAlgebraicExpr:
        return expr.algebraicExpr.value
    of SumExpr:
        return expr.sumExpr.value
    of MinExpr:
        return expr.minExpr.value
    of MaxExpr:
        return expr.maxExpr.value
    of ConstantExpr:
        return expr.constantValue

func updatePosition*[T](expr: Expression[T], position: Natural, newValue: T) =
    if position notin expr.positions:
        return

    case expr.kind
    of StatefulAlgebraicExpr:
        expr.algebraicExpr.updatePosition(position, newValue)
    of SumExpr:
        expr.sumExpr.updatePosition(position, newValue)
    of MinExpr:
        expr.minExpr.updatePosition(position, newValue)
    of MaxExpr:
        expr.maxExpr.updatePosition(position, newValue)
    of ConstantExpr:
        discard  # Constants don't change

func moveDelta*[T](expr: Expression[T], position: Natural,
                   oldValue, newValue: T): T =
    if position notin expr.positions:
        return 0

    case expr.kind
    of StatefulAlgebraicExpr:
        return expr.algebraicExpr.moveDelta(position, oldValue, newValue)
    of SumExpr:
        return expr.sumExpr.moveDelta(position, oldValue, newValue)
    of MinExpr:
        return expr.minExpr.moveDelta(position, oldValue, newValue)
    of MaxExpr:
        return expr.maxExpr.moveDelta(position, oldValue, newValue)
    of ConstantExpr:
        return 0  # Constants don't change