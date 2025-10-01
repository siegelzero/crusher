## Algebraic constraint definitions and operations
##
## This module provides the core `AlgebraicConstraint` type for representing
## constraints as expression trees, along with operations for creating constraints
## from algebraic expressions and evaluating them against variable assignments.
##
## Key features:
## - Constraint creation from algebraic expressions using standard operators
## - Optimized constraint negation (converts `not(a == b)` to `a != b`)
## - Support for arithmetic constraints (common factors, coprimality)
## - Efficient evaluation using expression trees

import std/[packedsets, tables]

import constraintNode
import ../expressions/expressions

################################################################################
# Type definitions
################################################################################

type
    AlgebraicConstraint*[T] = object
        # Constraint stored as an expression tree on the given positions.
        # Evaluation of the constraint requires evaluating the tree.
        # This constraint form has no state; i.e. no assignment to the variables.
        positions*: PackedSet[int]
        node*: ConstraintNode[T]

################################################################################
# Unary Constraint Relations
################################################################################

func `not`*[T](constraint: AlgebraicConstraint[T]): AlgebraicConstraint[T] {.inline.} =
    # Returns the negation of the constraint.
    if constraint.node.kind == BinaryRelNode and constraint.node.binaryRel == EqualTo:
        # If `not` is being called on an equality constraint, then use
        # NotEqualTo constraint instead, since it is more efficient.
        return AlgebraicConstraint[T](
            positions: constraint.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: NotEqualTo,
                left: constraint.node.left,
                right: constraint.node.right
            )
        )
    else:
        return AlgebraicConstraint[T](
            positions: constraint.positions,
            node: ConstraintNode[T](
                kind: UnaryRelNode,
                unaryRel: Not,
                target: constraint.node
            )
        )

################################################################################
# Binary (AlgebraicExpression, AlgebraicExpression) Relations
# DEPRECATED: These operators have been moved to stateful.nim for consistency
# All relational operators now return StatefulConstraint for unified API
################################################################################

################################################################################
# Binary Boolean Operations on Constraints
################################################################################

template BooleanBinaryOp(op, opEnum: untyped) =
    func `op`*[T](left, right: AlgebraicConstraint[T]): AlgebraicConstraint[T] {.inline.} =
        AlgebraicConstraint[T](
            positions: left.positions + right.positions,
            node: ConstraintNode[T](
                kind: BooleanNode,
                booleanOp: opEnum,
                leftConstraint: left.node,
                rightConstraint: right.node
            )
        )

BooleanBinaryOp(`and`, And)
BooleanBinaryOp(`or`, Or)
BooleanBinaryOp(`xor`, Xor)
BooleanBinaryOp(`implies`, Implies)
BooleanBinaryOp(`iff`, Iff)

# More intuitive syntax for implies and iff
BooleanBinaryOp(`->`, Implies)   # Implies operator: A -> B means "if A then B"
BooleanBinaryOp(`<->`, Iff)      # If-and-only-if operator: A <-> B means "A iff B"

################################################################################
# Evaluation
################################################################################

func evaluate*[T](constraint: AlgebraicConstraint[T], assignment: seq[T] | Table[int, T]): bool {.inline.} =
    constraint.node.evaluate(assignment)

proc penalty*[T](constraint: AlgebraicConstraint[T], assignment: seq[T] | Table[int, T]): T {.inline.} =
    constraint.node.penalty(assignment)

################################################################################
# Arithmetical Constraints
################################################################################

func commonFactor*[T](left, right: AlgebraicExpression[T]): AlgebraicConstraint[T] {.inline.} =
    AlgebraicConstraint[T](
        positions: left.positions + right.positions,
        node: ConstraintNode[T](
            kind: BinaryRelNode,
            binaryRel: CommonFactor,
            left: left.node,
            right: right.node
        )
    )

func coPrime*[T](left, right: AlgebraicExpression[T]): AlgebraicConstraint[T] {.inline.} =
    AlgebraicConstraint[T](
        positions: left.positions + right.positions,
        node: ConstraintNode[T](
            kind: BinaryRelNode,
            binaryRel: CoPrime,
            left: left.node,
            right: right.node
        )
    )
