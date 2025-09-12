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
        positions*: PackedSet[int]
        value*: T
        currentAssignment*: Table[int, T]

func newStatefulAlgebraicExpression*[T](expression: AlgebraicExpression[T]): StatefulAlgebraicExpression[T] =
    result = StatefulAlgebraicExpression[T](
        algebraicExpr: expression,
        positions: expression.positions,
        value: default(T),
        currentAssignment: initTable[int, T]()
    )

func initialize*[T](expression: StatefulAlgebraicExpression[T], assignment: seq[T]) =
    # Initialize with the given assignment
    expression.currentAssignment.clear()
    for position in expression.positions:
        expression.currentAssignment[position] = assignment[position]
    expression.value = expression.algebraicExpr.evaluate(assignment)

func updatePosition*[T](expression: StatefulAlgebraicExpression[T], position: int, newValue: T) =
    # Update a single position incrementally
    if position in expression.positions:
        # Calculate the delta first for incremental update
        let oldValue = expression.currentAssignment[position]
        let delta = expression.moveDelta(position, oldValue, newValue)

        # Update assignment and value incrementally
        expression.currentAssignment[position] = newValue
        expression.value += delta

# Calculate the change in cost
func moveDelta*[T](expression: StatefulAlgebraicExpression[T],
                   position: int,
                   oldValue, newValue: T): T =
    let currentValue = expression.value
    # Temporarily update and evaluate using table-based evaluation
    let savedValue = expression.currentAssignment[position]
    expression.currentAssignment[position] = newValue
    let newTotalValue = expression.algebraicExpr.evaluate(expression.currentAssignment)

    # Restore original value
    expression.currentAssignment[position] = savedValue

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
        positions*: PackedSet[int]
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

# Overloaded procs to create Expression wrapper from various expression types
proc newExpression*[T](expression: StatefulAlgebraicExpression[T]): Expression[T] =
    Expression[T](kind: StatefulAlgebraicExpr, algebraicExpr: expression, positions: expression.positions)

proc newExpression*[T](expression: AlgebraicExpression[T]): Expression[T] =
    # Convert AlgebraicExpression to StatefulAlgebraicExpression
    let statefulExpression = newStatefulAlgebraicExpression(expression)
    Expression[T](kind: StatefulAlgebraicExpr, algebraicExpr: statefulExpression, positions: expression.positions)

proc newExpression*[T](expression: SumExpression[T]): Expression[T] =
    Expression[T](kind: SumExpr, sumExpr: expression, positions: expression.positions)

proc newExpression*[T](expression: MinExpression[T]): Expression[T] =
    Expression[T](kind: MinExpr, minExpr: expression, positions: expression.positions)

proc newExpression*[T](expression: MaxExpression[T]): Expression[T] =
    Expression[T](kind: MaxExpr, maxExpr: expression, positions: expression.positions)

proc newExpression*[T](value: T): Expression[T] =
    Expression[T](kind: ConstantExpr, constantValue: value, positions: initPackedSet[int]())

# Helper functions for Expression operations
func initialize*[T](expression: Expression[T], assignment: seq[T]) =
    case expression.kind
    of StatefulAlgebraicExpr:
        expression.algebraicExpr.initialize(assignment)
    of SumExpr:
        expression.sumExpr.initialize(assignment)
    of MinExpr:
        expression.minExpr.initialize(assignment)
    of MaxExpr:
        expression.maxExpr.initialize(assignment)
    of ConstantExpr:
        discard  # Constants don't need initialization

func getValue*[T](expression: Expression[T]): T =
    case expression.kind
    of StatefulAlgebraicExpr:
        return expression.algebraicExpr.value
    of SumExpr:
        return expression.sumExpr.value
    of MinExpr:
        return expression.minExpr.value
    of MaxExpr:
        return expression.maxExpr.value
    of ConstantExpr:
        return expression.constantValue

func updatePosition*[T](expression: Expression[T], position: int, newValue: T) =
    case expression.kind
    of StatefulAlgebraicExpr:
        expression.algebraicExpr.updatePosition(position, newValue)
    of SumExpr:
        expression.sumExpr.updatePosition(position, newValue)
    of MinExpr:
        expression.minExpr.updatePosition(position, newValue)
    of MaxExpr:
        expression.maxExpr.updatePosition(position, newValue)
    of ConstantExpr:
        discard  # Constants don't change

func moveDelta*[T](expression: Expression[T], position: int,
                   oldValue, newValue: T): T =
    case expression.kind
    of StatefulAlgebraicExpr:
        return expression.algebraicExpr.moveDelta(position, oldValue, newValue)
    of SumExpr:
        return expression.sumExpr.moveDelta(position, oldValue, newValue)
    of MinExpr:
        return expression.minExpr.moveDelta(position, oldValue, newValue)
    of MaxExpr:
        return expression.maxExpr.moveDelta(position, oldValue, newValue)
    of ConstantExpr:
        return 0  # Constants don't change

################################################################################
# Deep copy implementations for thread-safe parallel processing
################################################################################

proc deepCopy*[T](expression: StatefulAlgebraicExpression[T]): StatefulAlgebraicExpression[T] =
    ## Creates a deep copy of a StatefulAlgebraicExpression preserving all runtime state
    result = StatefulAlgebraicExpression[T](
        algebraicExpr: expression.algebraicExpr.deepCopy(),  # Deep copy the underlying algebraic expression
        positions: expression.positions,  # PackedSet is a value type, safe to copy
        value: expression.value,
        currentAssignment: expression.currentAssignment  # Table is a value type, safe to copy
    )

proc deepCopy*[T](expression: Expression[T]): Expression[T] =
    ## Creates a deep copy of an Expression preserving all runtime state
    case expression.kind:
        of StatefulAlgebraicExpr:
            result = Expression[T](
                kind: StatefulAlgebraicExpr,
                positions: expression.positions,  # PackedSet is a value type, safe to copy
                algebraicExpr: expression.algebraicExpr.deepCopy()  # Deep copy StatefulAlgebraicExpression
            )
        of SumExpr:
            result = Expression[T](
                kind: SumExpr,
                positions: expression.positions,  # PackedSet is a value type, safe to copy
                sumExpr: expression.sumExpr.deepCopy()  # Deep copy SumExpression
            )
        of MinExpr:
            result = Expression[T](
                kind: MinExpr,
                positions: expression.positions,  # PackedSet is a value type, safe to copy
                minExpr: expression.minExpr.deepCopy()  # Deep copy MinExpression
            )
        of MaxExpr:
            result = Expression[T](
                kind: MaxExpr,
                positions: expression.positions,  # PackedSet is a value type, safe to copy
                maxExpr: expression.maxExpr.deepCopy()  # Deep copy MaxExpression
            )
        of ConstantExpr:
            result = Expression[T](
                kind: ConstantExpr,
                positions: expression.positions,  # PackedSet is a value type, safe to copy
                constantValue: expression.constantValue  # Constants are immutable
            )
