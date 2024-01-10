import std/[packedsets, sequtils, strformat, tables]

import allDifferentState, constraintNode, linearCombinationState
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    ConstraintType* = enum
        AlgebraicConstraint,
        AllDifferentConstraint,
        LinearCombinationConstraint

    Constraint*[T] = object
        positions*: PackedSet[int]
        case scope*: ConstraintType
            of AlgebraicConstraint:
                node*: ConstraintNode[T]
            of AllDifferentConstraint:
                state*: AllDifferentState[T]
            of LinearCombinationConstraint:
                lincomb*: LinearCombinationState[T]
                linrel*: BinaryRelation
                rhs*: T

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

proc penalty*[T](cons: Constraint[T], assignment: seq[T]): T {.inline.} =
    case cons.scope:
        of AlgebraicConstraint:
            return cons.node.penalty(assignment)
        of AllDifferentConstraint:
            return cons.state.cost
        of LinearCombinationConstraint:
            var left = cons.lincomb.value
            var right = cons.rhs
            case cons.linrel:
                of EqualTo:
                    # return abs(left - right)
                    return if left == right: 0 else: 1
                    # return if left == right: 0 else: cons.positions.len
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

func allDifferent*[T](positions: openArray[T]): Constraint[T] =
    # Returns allDifferent constraint for the given positions.
    return Constraint[T](
        positions: toPackedSet[T](positions),
        scope: AllDifferentConstraint,
        state: newAllDifferentState[T](positions)
    )

func allDifferent*[T](expressions: seq[Expression[T]]): Constraint[T] =
    # Returns allDifferent constraint for the given expressions.
    var positions = toPackedSet[T]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return allDifferent(positions.items.toSeq)
    else:
        return Constraint[T](
            positions: positions,
            scope: AllDifferentConstraint,
            state: newAllDifferentState[T](expressions)
        )

proc linearCombinationEq*[T](positions: seq[int], target: T): Constraint[T] =
    return Constraint[T](
        positions: toPackedSet[T](positions),
        scope: LinearCombinationConstraint,
        linrel: EqualTo,
        rhs: target,
        lincomb: newLinearCombinationState[T](positions)
    )

proc linearCombinationEq*[T](expressions: seq[Expression[T]], target: T): Constraint[T] =
    # Returns allDifferent constraint for the given expressions.
    var positions = toPackedSet[T]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    doAssert allRefs
    # Use more efficient position based constraint if all expressions are refnodes
    echo "fancypants"
    return linearCombinationEq(positions.items.toSeq, target)

################################################################################
# Computed Constraint State interface
################################################################################

func initialize*[T](cons: Constraint[T], assignment: seq[T]) =
    case cons.scope:
        of AlgebraicConstraint:
            return
        of AllDifferentConstraint:
            cons.state.initialize(assignment)
        of LinearCombinationConstraint:
            cons.lincomb.initialize(assignment)


func moveDelta*[T](cons: Constraint[T], position: int, oldValue, newValue: T): int =
    case cons.scope:
        of AlgebraicConstraint:
            return
        of AllDifferentConstraint:
            cons.state.moveDelta(position, oldValue, newValue)
        of LinearCombinationConstraint:
            cons.lincomb.moveDelta(position, oldValue, newValue)


func updatePosition*[T](cons: Constraint[T], position: int, newValue: T) =
    case cons.scope:
        of AlgebraicConstraint:
            return
        of AllDifferentConstraint:
            cons.state.updatePosition(position, newValue)
        of LinearCombinationConstraint:
            cons.lincomb.updatePosition(position, newValue)