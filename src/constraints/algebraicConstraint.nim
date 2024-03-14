import std/[packedsets, tables]

import constraintNode
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    AlgebraicConstraint*[T] = object
        positions*: PackedSet[int]
        node*: ConstraintNode[T]

################################################################################
# Unary Constraint Relations
################################################################################

func `not`*[T](constraint: AlgebraicConstraint[T]): AlgebraicConstraint[T] {.inline.} =
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
    func `rel`*[T](left: T, right: AlgebraicExpression[T]): AlgebraicConstraint[T] {.inline.} =
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

type
    AlgebraicConstraintState*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        constraint*: AlgebraicConstraint[T]
        positions: PackedSet[int]

################################################################################
# AlgebraicConstraintState Creation
################################################################################

func init*[T](state: AlgebraicConstraintState[T], constraint: AlgebraicConstraint[T]) =
    state.cost = 0
    state.positions = constraint.positions
    state.constraint = constraint
    state.currentAssignment = initTable[int, T]()

func newAlgebraicConstraintState*[T](constraint: AlgebraicConstraint[T]): AlgebraicConstraintState[T] =
    new(result)
    result.init(constraint)

################################################################################
# AlgebraicConstraintState Initialization
################################################################################

func initialize*[T](state: AlgebraicConstraintState[T], assignment: seq[T]) =
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
    state.cost = state.constraint.penalty(assignment)

################################################################################
# AlgebraicConstraintState Updates
################################################################################

func updatePosition*[T](state: AlgebraicConstraintState[T], position: int, newValue: T) {.inline.} =
    state.currentAssignment[position] = newValue
    state.cost = state.constraint.penalty(state.currentAssignment)

func moveDelta*[T](state: AlgebraicConstraintState[T], position: int, oldValue, newValue: T): int {.inline.} =
    let oldCost = state.cost
    state.currentAssignment[position] = newValue
    let newCost = state.constraint.penalty(state.currentAssignment)
    let delta = newCost - oldCost
    state.currentAssignment[position] = oldValue
    return delta
