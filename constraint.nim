import std/packedsets

import constraintNode
import expression
import expressionNode

################################################################################
# Type definitions
################################################################################

type
    Constraint*[T] = object
        positions*: PackedSet[int]
        tree*: ConstraintNode[T]

################################################################################
# Unary Constraint Relations
################################################################################

func `not`*[T](cons: Constraint[T]): Constraint[T] {.inline.} =
    Constraint[T](
        positions: cons.positions,
        tree: ConstraintNode[T](
            kind: UnaryRelNode,
            unaryRel: Not,
            target: cons.tree
        )
    )

################################################################################
# Binary (Expression, Expression) Relations
################################################################################

template ExpExpRel(rel, relEnum: untyped) =
    func `rel`*[T](left, right: Expression[T]): Constraint[T] {.inline.} =
        Constraint[T](
            positions: left.positions + right.positions,
            tree: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.tree,
                right: right.tree
            )
        )

ExpExpRel(`==`, EqualTo)
ExpExpRel(`>`, GreaterThan)
ExpExpRel(`>=`, GreaterThanEq)
ExpExpRel(`<`, LessThan)
ExpExpRel(`<=`, LessThanEq)

################################################################################
# Binary (Expression, Value) Relations
################################################################################

template ExpValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: Expression[T], right: T): Constraint[T] {.inline.} =
        Constraint[T](
            positions: left.positions,
            tree: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.tree,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            )
        )
    func `rel`*[T](left: T, right: Expression[T]): Constraint[T] {.inline.} =
        Constraint[T](
            positions: right.positions,
            tree: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.tree
            )
        )

ExpValRel(`==`, EqualTo)
ExpValRel(`>`, GreaterThan)
ExpValRel(`>=`, GreaterThanEq)
ExpValRel(`<`, LessThan)
ExpValRel(`<=`, LessThanEq)

################################################################################
# Evaluation
################################################################################

func evaluate*[T](cons: Constraint[T], assignment: seq[T]): bool {.inline.} =
    cons.tree.evaluate(assignment)

func penalty*[T](cons: Constraint[T], assignment: seq[T]): T {.inline.} =
    cons.tree.penalty(assignment)