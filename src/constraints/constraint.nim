import std/[packedsets, sequtils, tables]

import allDifferentState, constraintNode, elementState, linearCombinationState
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    ConstraintType* = enum
        AlgebraicConstraint,
        StatefulConstraint
    
    StatefulConstraintType* = enum
        AllDifferentConstraint,
        ElementConstraint,
        LinearCombinationConstraint

    Constraint*[T] = object
        positions*: PackedSet[int]
        case scope*: ConstraintType
            of AlgebraicConstraint:
                node*: ConstraintNode[T]
            of StatefulConstraint:
                case stateType*: StatefulConstraintType
                    of AllDifferentConstraint:
                        allDifferentState*: AllDifferentState[T]
                    of ElementConstraint:
                        elementState: ElementState[T]
                    of LinearCombinationConstraint:
                        linearCombinationState*: LinearCombinationState[T]
                        relation*: BinaryRelation
                        rhs*: T

################################################################################
# Unary Constraint Relations
################################################################################

func `not`*[T](constraint: Constraint[T]): Constraint[T] {.inline.} =
    doAssert constraint.scope == AlgebraicConstraint
    if constraint.node.kind == BinaryRelNode and constraint.node.binaryRel == EqualTo:
        # If `not` is being called on an equality constraint, then use
        # NotEqualTo constraint instead, since it is more efficient.
        return Constraint[T](
            scope: AlgebraicConstraint,
            positions: constraint.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: NotEqualTo,
                left: constraint.node.left,
                right: constraint.node.right
            )
        )
    else:
        return Constraint[T](
            scope: AlgebraicConstraint,
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
    func `rel`*[T](left, right: AlgebraicExpression[T]): Constraint[T] {.inline.} =
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
# Binary (AlgebraicExpression, Value) Relations
################################################################################

template ExpValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: AlgebraicExpression[T], right: T): Constraint[T] {.inline.} =
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
    func `rel`*[T](left: T, right: AlgebraicExpression[T]): Constraint[T] {.inline.} =
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

func evaluate*[T](constraint: Constraint[T], assignment: seq[T]): bool {.inline.} =
    constraint.node.evaluate(assignment)

proc penalty*[T](constraint: Constraint[T], assignment: seq[T]): T {.inline.} =
    case constraint.scope:
        of AlgebraicConstraint:
            return constraint.node.penalty(assignment)
        of StatefulConstraint:
            case constraint.stateType:
                of AllDifferentConstraint:
                    return constraint.allDifferentState.cost
                of ElementConstraint:
                    return constraint.elementState.cost
                of LinearCombinationConstraint:
                    let left = constraint.linearCombinationState.value
                    let right = constraint.rhs

                    case constraint.relation:
                        of EqualTo:
                            return if left == right: 0 else: 1
                        of NotEqualTo:
                            return if left != right: 0 else: 1
                        of GreaterThan:
                            return if left > right: 0 else: 1
                        of GreaterThanEq:
                            return if left >= right: 0 else: 1
                        of LessThan:
                            return if left < right: 0 else: 1
                        of LessThanEq:
                            return if left <= right: 0 else: 1

################################################################################
# Computed Constraints
################################################################################

func allDifferent*[T](positions: openArray[int]): Constraint[T] =
    # Returns allDifferent constraint for the given positions.
    return Constraint[T](
        positions: toPackedSet[int](positions),
        scope: StatefulConstraint,
        stateType: AllDifferentConstraint,
        allDifferentState: newAllDifferentState[T](positions)
    )

func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): Constraint[T] =
    # Returns allDifferent constraint for the given expressions.
    var positions = toPackedSet[int]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return allDifferent[T](toSeq[int](positions))
    else:
        return Constraint[T](
            positions: positions,
            scope: StatefulConstraint,
            stateType: AllDifferentConstraint,
            allDifferentState: newAllDifferentState[T](expressions)
        )

proc linearCombinationEq*[T](positions: openArray[int], target: T): Constraint[T] =
    return Constraint[T](
        positions: toPackedSet[int](positions),
        scope: StatefulConstraint,
        stateType: LinearCombinationConstraint,
        relation: EqualTo,
        rhs: target,
        linearCombinationState: newLinearCombinationState[T](positions)
    )

proc linearCombinationEq*[T](expressions: seq[AlgebraicExpression[T]], target: T): Constraint[T] =
    var positions = toPackedSet[int]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    doAssert allRefs
    # Use more efficient position based constraint since all expressions are refnodes
    return linearCombinationEq(toSeq[int](positions), target)

################################################################################
# Computed Constraint State interface
################################################################################

func initialize*[T](constraint: Constraint[T], assignment: seq[T]) =
    case constraint.scope:
        of AlgebraicConstraint:
            return
        of StatefulConstraint:
            case constraint.stateType:
                of AllDifferentConstraint:
                    constraint.allDifferentState.initialize(assignment)
                of ElementConstraint:
                    constraint.elementState.initialize(assignment)
                of LinearCombinationConstraint:
                    constraint.linearCombinationState.initialize(assignment)


func moveDelta*[T](constraint: Constraint[T], position: int, oldValue, newValue: T): int =
    case constraint.scope:
        of AlgebraicConstraint:
            return
        of StatefulConstraint:
            case constraint.stateType:
                of AllDifferentConstraint:
                    constraint.allDifferentState.moveDelta(position, oldValue, newValue)
                of ElementConstraint:
                    constraint.elementState.moveDelta(position, oldValue, newValue)
                of LinearCombinationConstraint:
                    constraint.linearCombinationState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: Constraint[T], position: int, newValue: T) =
    case constraint.scope:
        of AlgebraicConstraint:
            return
        of StatefulConstraint:
            case constraint.stateType:
                of AllDifferentConstraint:
                    constraint.allDifferentState.updatePosition(position, newValue)
                of ElementConstraint:
                    constraint.elementState.updatePosition(position, newValue)
                of LinearCombinationConstraint:
                    constraint.linearCombinationState.updatePosition(position, newValue)
