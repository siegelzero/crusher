import std/[packedsets, tables]
import types
import sumExpression
export types, sumExpression


# AlgebraicExpression Creation
func newAlgebraicExpression*[T](positions: PackedSet[int],
                                node: ExpressionNode[T],
                                linear: bool): AlgebraicExpression[T] =
    new(result)
    result.positions = positions
    result.node = node
    result.linear = linear

# Unary Expression Operations
func `-`*[T](expression: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} = -1*expression

func abs*[T](expression: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    newAlgebraicExpression[T](
        positions=expression.positions,
        node=ExpressionNode[T](
            kind: UnaryOpNode,
            unaryOp: AbsoluteValue,
            target: expression.node
        ),
        linear=false
    )

func binaryMax*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    newAlgebraicExpression[T](
        positions=left.positions + right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Maximum,
            left: left.node, right: right.node
        ),
        linear=false
    )

func binaryMin*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    newAlgebraicExpression[T](
        positions=left.positions + right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Minimum,
            left: left.node, right: right.node
        ),
        linear=false
    )

# Binary (Expression, Expression) Operations
func `+`*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    # (X - k) + k → X  (when right is literal matching left's subtraction)
    if right.node.kind == LiteralNode and left.node.kind == BinaryOpNode and
       left.node.binaryOp == Subtraction and left.node.right.kind == LiteralNode and
       left.node.right.value == right.node.value:
        return newAlgebraicExpression[T](
            positions=left.positions,
            node=left.node.left,
            linear=left.linear
        )
    newAlgebraicExpression[T](
        positions=left.positions + right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Addition,
            left: left.node, right: right.node
        ),
        linear=left.linear and right.linear
    )

func `-`*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    # (X + k) - k → X  and  (k + X) - k → X
    if right.node.kind == LiteralNode and left.node.kind == BinaryOpNode and
       left.node.binaryOp == Addition:
        if left.node.right.kind == LiteralNode and left.node.right.value == right.node.value:
            return newAlgebraicExpression[T](
                positions=left.positions,
                node=left.node.left,
                linear=left.linear
            )
        if left.node.left.kind == LiteralNode and left.node.left.value == right.node.value:
            return newAlgebraicExpression[T](
                positions=left.positions,
                node=left.node.right,
                linear=left.linear
            )
    newAlgebraicExpression[T](
        positions=left.positions + right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Subtraction,
            left: left.node, right: right.node
        ),
        linear=left.linear and right.linear
    )

func `*`*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    # 1 * X → X
    if left.node.kind == LiteralNode and left.node.value == 1:
        return right
    # X * 1 → X
    if right.node.kind == LiteralNode and right.node.value == 1:
        return left
    let linear = (left.linear and right.positions.len == 0) or (left.positions.len == 0 and right.linear)
    newAlgebraicExpression[T](
        positions=left.positions + right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Multiplication,
            left: left.node, right: right.node
        ),
        linear=linear
    )

# Binary (Expression, Value) Operations
func `+`*[T](left: AlgebraicExpression[T], right: T): AlgebraicExpression[T] {.inline.} =
    # X + 0 → X
    if right == 0:
        return left
    # (X - k) + k → X
    if left.node.kind == BinaryOpNode and left.node.binaryOp == Subtraction and
       left.node.right.kind == LiteralNode and left.node.right.value == right:
        return newAlgebraicExpression[T](
            positions=left.positions, node=left.node.left, linear=left.linear)
    newAlgebraicExpression[T](
        positions=left.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Addition,
            left: left.node,
            right: ExpressionNode[T](kind: LiteralNode, value: right)
        ),
        linear=left.linear
    )

func `+`*[T](left: T, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    # 0 + X → X
    if left == 0:
        return right
    newAlgebraicExpression[T](
        positions=right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Addition,
            left: ExpressionNode[T](kind: LiteralNode, value: left),
            right: right.node
        ),
        linear=right.linear
    )

func `-`*[T](left: AlgebraicExpression[T], right: T): AlgebraicExpression[T] {.inline.} =
    # X - 0 → X
    if right == 0:
        return left
    # (X + k) - k → X  and  (k + X) - k → X
    if left.node.kind == BinaryOpNode and left.node.binaryOp == Addition:
        if left.node.right.kind == LiteralNode and left.node.right.value == right:
            return newAlgebraicExpression[T](
                positions=left.positions, node=left.node.left, linear=left.linear)
        if left.node.left.kind == LiteralNode and left.node.left.value == right:
            return newAlgebraicExpression[T](
                positions=left.positions, node=left.node.right, linear=left.linear)
    newAlgebraicExpression[T](
        positions=left.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Subtraction,
            left: left.node,
            right: ExpressionNode[T](kind: LiteralNode, value: right)
        ),
        linear=left.linear
    )

func `-`*[T](left: T, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    newAlgebraicExpression[T](
        positions=right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Subtraction,
            left: ExpressionNode[T](kind: LiteralNode, value: left),
            right: right.node
        ),
        linear=right.linear
    )

func `*`*[T](left: AlgebraicExpression[T], right: T): AlgebraicExpression[T] {.inline.} =
    if right == 1: return left
    newAlgebraicExpression[T](
        positions=left.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Multiplication,
            left: left.node,
            right: ExpressionNode[T](kind: LiteralNode, value: right)
        ),
        linear=left.linear
    )

func `*`*[T](left: T, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
    if left == 1: return right
    newAlgebraicExpression[T](
        positions=right.positions,
        node=ExpressionNode[T](
            kind: BinaryOpNode, binaryOp: Multiplication,
            left: ExpressionNode[T](kind: LiteralNode, value: left),
            right: right.node
        ),
        linear=right.linear
    )
