import std/[packedsets, sequtils, tables]

import algebraicConstraint, allDifferentState, constraintNode, elementState, linearCombinationState
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentConstraint,
        ElementConstraint,
        LinearCombinationConstraint,
        StatefulAlgebraicConstraint

    ConstraintState*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentConstraint:
                allDifferentState*: AllDifferentState[T]
            of ElementConstraint:
                elementState: ElementState[T]
            of LinearCombinationConstraint:
                linearCombinationState*: LinearCombinationState[T]
                relation*: BinaryRelation
                rhs*: T
            of StatefulAlgebraicConstraint:
                algebraicConstraintState*: AlgebraicConstraintState[T]

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: ConstraintState[T]): T {.inline.} =
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
        
        of StatefulAlgebraicConstraint:
            return constraint.algebraicConstraintState.cost

################################################################################
# Computed Constraints
################################################################################

func allDifferent*[T](positions: openArray[int]): ConstraintState[T] =
    # Returns allDifferent constraint for the given positions.
    return ConstraintState[T](
        positions: toPackedSet[int](positions),
        stateType: AllDifferentConstraint,
        allDifferentState: newAllDifferentState[T](positions)
    )

func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): ConstraintState[T] =
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
        return ConstraintState[T](
            positions: positions,
            stateType: AllDifferentConstraint,
            allDifferentState: newAllDifferentState[T](expressions)
        )

proc linearCombinationEq*[T](positions: openArray[int], target: T): ConstraintState[T] =
    return ConstraintState[T](
        positions: toPackedSet[int](positions),
        stateType: LinearCombinationConstraint,
        relation: EqualTo,
        rhs: target,
        linearCombinationState: newLinearCombinationState[T](positions)
    )

proc linearCombinationEq*[T](expressions: seq[AlgebraicExpression[T]], target: T): ConstraintState[T] =
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

func initialize*[T](constraint: ConstraintState[T], assignment: seq[T]) =
    case constraint.stateType:
        of AllDifferentConstraint:
            constraint.allDifferentState.initialize(assignment)
        of ElementConstraint:
            constraint.elementState.initialize(assignment)
        of LinearCombinationConstraint:
            constraint.linearCombinationState.initialize(assignment)
        of StatefulAlgebraicConstraint:
            constraint.algebraicConstraintState.initialize(assignment)


func moveDelta*[T](constraint: ConstraintState[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentConstraint:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of LinearCombinationConstraint:
            constraint.linearCombinationState.moveDelta(position, oldValue, newValue)
        of StatefulAlgebraicConstraint:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: ConstraintState[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentConstraint:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of LinearCombinationConstraint:
            constraint.linearCombinationState.updatePosition(position, newValue)
        of StatefulAlgebraicConstraint:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
