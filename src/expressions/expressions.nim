import std/[packedsets, tables]
import types
import sumExpression
export types, sumExpression


# AlgebraicExpression Creation

func init*[T](expression: AlgebraicExpression[T],
              positions: PackedSet[Natural],
              node: ExpressionNode[T],
              linear: bool) =
    expression.positions = positions
    expression.node = node
    expression.linear = linear

func newAlgebraicExpression*[T](positions: PackedSet[Natural],
                                node: ExpressionNode[T],
                                linear: bool): AlgebraicExpression[T] =
    new(result)
    result.init(positions, node, linear)

# Unary Expression Operations

func `-`*[T](expression: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} = -1*expression

# Binary (Expression, Expression) Operations

template ExpExpOp(op, opref: untyped) =
    func `op`*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
        let linear = case opref:
            of Addition:
                left.linear and right.linear
            of Subtraction:
                left.linear and right.linear
            of Multiplication:
                (left.linear and right.positions.len == 0) or (left.positions.len == 0 and right.linear)

        newAlgebraicExpression[T](
            positions=left.positions + right.positions,
            node=ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: left.node,
                right: right.node
            ),
            linear=linear
        )

ExpExpOp(`+`, Addition)
ExpExpOp(`*`, Multiplication)
ExpExpOp(`-`, Subtraction)

# Binary (Expression, Value) Operations

template ExpValOp(op, opref: untyped) =
    func `op`*[T](left: AlgebraicExpression[T], right: T): AlgebraicExpression[T] {.inline.} =
        newAlgebraicExpression[T](
            positions=left.positions,
            node=ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: left.node,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            ),
            linear=left.linear
        )

    func `op`*[T](left: T, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
        newAlgebraicExpression[T](
            positions=right.positions,
            node=ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.node
            ),
            linear=right.linear
        )

ExpValOp(`+`, Addition)
ExpValOp(`*`, Multiplication)
ExpValOp(`-`, Subtraction)


################################################################################
# Type definitions for MinExpression
################################################################################

type
    MinExpression*[T] = ref object
        value*: T
        positions*: PackedSet[Natural]
        currentAssignment*: Table[int, T]

# MinExpression creation

func init*[T](state: MinExpression[T], positions: openArray[Natural]) =
    state.value = 0
    state.positions = toPackedSet[Natural](positions)
    state.currentAssignment = initTable[int, T]()

func newMinExpression*[T](positions: openArray[Natural]): MinExpression[T] =
    new(result)
    result.init(positions)

# MinExpression initialization

func initialize*[T](state: MinExpression[T], assignment: seq[T]) =
    # Initialize the MinExpression with the given assignment, and updates the value.
    var minValue: T = high(T)
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
        minValue = min(minValue, assignment[pos])
    state.value = minValue

func evaluate*[T](state: MinExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var minValue: T = high(T)
    for pos in state.positions:
        minValue = min(minValue, assignment[pos])
    return minValue

func `$`*[T](state: MinExpression[T]): string = $(state.value)

# MinExpression updates

func updatePosition*[T](state: MinExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    state.currentAssignment[position] = newValue
    state.value = state.currentAssignment.values.min()

func moveDelta*[T](state: MinExpression[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns the change in value obtained by reassigning position from oldValue to newValue.
    if newValue >= state.value:
        return 0
    else:
        return state.value - newValue