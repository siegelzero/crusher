import std/[packedsets, tables]

import expressionNode

################################################################################
# Type definitions
################################################################################

type
    Expression*[T] {.acyclic.} = object
        positions*: PackedSet[int]
        node*: ExpressionNode[T]

################################################################################
# Binary (Expression, Expression) Operations
################################################################################

template ExpExpOp(op, opref: untyped) =
    func `op`*[T](left, right: Expression[T]): Expression[T] {.inline.} =
        Expression[T](
            positions: left.positions + right.positions,
            node: ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: left.node,
                right: right.node
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
            node: ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: left.node,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            )
        )

    func `op`*[T](left: T, right: Expression[T]): Expression[T] {.inline.} =
        Expression[T](
            positions: right.positions,
            node: ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.node
            )
        )

ExpValOp(`+`, Addition)
ExpValOp(`*`, Multiplication)
ExpValOp(`-`, Subtraction)

################################################################################
# Evaluation
################################################################################

func evaluate*[T](exp: Expression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    exp.node.evaluate(assignment)
