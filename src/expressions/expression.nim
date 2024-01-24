import std/[packedsets, tables]

import expressionNode

################################################################################
# Type definitions
################################################################################

type
    Expression*[T] {.acyclic.} = object
        positions*: PackedSet[int]
        node*: ExpressionNode[T]
        linear*: bool

################################################################################
# Unary Expression Operations
################################################################################

func `-`*[T](exp: Expression[T]): Expression[T] {.inline.} = -1*exp

################################################################################
# Binary (Expression, Expression) Operations
################################################################################

template ExpExpOp(op, opref: untyped) =
    func `op`*[T](left, right: Expression[T]): Expression[T] {.inline.} =
        let linear = case opref:
            of Addition:
                left.linear and right.linear
            of Subtraction:
                left.linear and right.linear
            of Multiplication:
                (left.linear and right.positions.len == 0) or (left.positions.len == 0 and right.linear)

        Expression[T](
            positions: left.positions + right.positions,
            linear: linear,
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
            linear: left.linear,
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
            linear: right.linear,
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

################################################################################
# Computed Expressions
################################################################################

# func sum*[T](expressions: seq[Expression[T]]): LinearCombination[T] =
#     var positions = 

