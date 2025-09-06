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
        positions*: PackedSet[Natural]
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
################################################################################

template ExpExpRel(rel, relEnum: untyped) =
    # Template for xRy for x, y Algebraic Expressions and R a binary relation
    func `rel`*[T](left, right: AlgebraicExpression[T]): AlgebraicConstraint[T] {.inline.} =
        AlgebraicConstraint[T](
            positions: left.positions + right.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.node,
                right: right.node
            )
        )

ExpExpRel(`==`, EqualTo)
ExpExpRel(`>`, GreaterThan)
ExpExpRel(`>=`, GreaterThanEq)
ExpExpRel(`<`, LessThan)
ExpExpRel(`<=`, LessThanEq)

################################################################################
# Binary (AlgebraicExpression, Value) Relations
################################################################################

template ExpValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: AlgebraicExpression[T], right: T): AlgebraicConstraint[T] {.inline.} =
        AlgebraicConstraint[T](
            positions: left.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.node,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            )
        )
    func `rel`*[T: not ref](left: T, right: AlgebraicExpression[T]): AlgebraicConstraint[T] {.inline.} =
        AlgebraicConstraint[T](
            positions: right.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.node
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

func evaluate*[T](constraint: AlgebraicConstraint[T], assignment: seq[T] | Table[int, T]): bool {.inline.} =
    constraint.node.evaluate(assignment)

proc penalty*[T](constraint: AlgebraicConstraint[T], assignment: seq[T] | Table[int, T]): T {.inline.} =
    return constraint.node.penalty(assignment)


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