import std/packedsets
import expressionTree

################################################################################
# Type definitions
################################################################################

type
    Expression*[T] = object
        positions*: PackedSet[int]
        tree*: ExpressionNode[T]

################################################################################
# Binary (Expression, Expression) Operations
################################################################################

template ExpExpOp(op, opref: untyped) =
    func `op`*[T](left, right: Expression[T]): Expression[T] {.inline.} =
        Expression[T](
            positions: left.positions + right.positions,
            tree: ExpressionNode[T](
                kind: BinaryOpNode,
                binaryop: opref,
                left: left.tree,
                right: right.tree
            )
        )

ExpExpOp(`+`, Addition)
ExpExpOp(`*`, Multiplication)
ExpExpOp(`-`, Subtraction)

################################################################################
# Binary (Expression, Value) Operations
################################################################################

template ExpValOp(op, opref: untyped) =
    func `op`*[T](left: Expression[T], right: T): Expression[T] {.inline.} =
        Expression[T](
            positions: left.positions,
            tree: ExpressionNode[T](
                kind: BinaryOpNode,
                binaryop: opref,
                left: left.tree,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            )
        )

    func `op`*[T](left: T, right: Expression[T]): Expression[T] {.inline.} =
        Expression[T](
            positions: right.positions,
            tree: ExpressionNode[T](
                kind: BinaryOpNode,
                binaryop: opref,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.tree
            )
        )

ExpValOp(`+`, Addition)
ExpValOp(`*`, Multiplication)
ExpValOp(`-`, Subtraction)

################################################################################
# Evaluation
################################################################################

func evaluate*[T](exp: Expression[T], assignment: seq[T]): T {.inline.} =
    exp.tree.evaluate(assignment)