import std/[packedsets, tables]

import allDifferentState, constraintNode
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    ConstraintType* = enum
        AlgebraicConstraint,
        AllDifferentConstraint 

    Constraint*[T] = object
        positions*: PackedSet[int]
        case scope*: ConstraintType
            of AlgebraicConstraint:
                node*: ConstraintNode[T]
            of AllDifferentConstraint:
                state*: AllDifferentState[T]

################################################################################
# Unary Constraint Relations
################################################################################

func `not`*[T](cons: Constraint[T]): Constraint[T] {.inline.} =
    if cons.node.kind == BinaryRelNode and cons.node.binaryRel == EqualTo:
        return Constraint[T](
            scope: AlgebraicConstraint,
            positions: cons.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: NotEqualTo,
                left: cons.node.left,
                right: cons.node.right
            )
        )
    else:
        return Constraint[T](
            scope: AlgebraicConstraint,
            positions: cons.positions,
            node: ConstraintNode[T](
                kind: UnaryRelNode,
                unaryRel: Not,
                target: cons.node
            )
        )

################################################################################
# Binary (Expression, Expression) Relations
################################################################################

template ExpExpRel(rel, relEnum: untyped) =
    func `rel`*[T](left, right: Expression[T]): Constraint[T] {.inline.} =
        Constraint[T](
            scope: AlgebraicConstraint,
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
# Binary (Expression, Value) Relations
################################################################################

template ExpValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: Expression[T], right: T): Constraint[T] {.inline.} =
        Constraint[T](
            scope: AlgebraicConstraint,
            positions: left.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.node,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            )
        )
    func `rel`*[T](left: T, right: Expression[T]): Constraint[T] {.inline.} =
        Constraint[T](
            scope: AlgebraicConstraint,
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

func evaluate*[T](cons: Constraint[T], assignment: seq[T]): bool {.inline.} =
    cons.node.evaluate(assignment)

func penalty*[T](cons: Constraint[T], assignment: seq[T]): T {.inline.} =
    case cons.scope:
        of AlgebraicConstraint:
            return cons.node.penalty(assignment)
        of AllDifferentConstraint:
            return cons.state.cost

################################################################################
# AllDifferentState Methods
################################################################################

func allDifferentConstraint*[T](positions: openArray[T]): Constraint[T] =
    return Constraint[T](
        positions: toPackedSet[T](positions),
        scope: AllDifferentConstraint,
        state: newAllDifferentState[T](positions)
    )

func allDifferentConstraint*[T](expressions: seq[Expression[T]]): Constraint[T] =
    var positions = toPackedSet[T]([])
    for exp in expressions:
        positions.incl(exp.positions)

    return Constraint[T](
        positions: positions,
        scope: AllDifferentConstraint,
        state: newAllDifferentState[T](expressions)
    )