import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, constraintNode, elementState, linearCombinationState
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentType,
        ElementConstraint,
        LinearCombinationConstraint,
        AlgebraicType

    StatefulConstraint*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementConstraint:
                elementState: ElementState[T]
            of LinearCombinationConstraint:
                linearCombinationState*: LinearCombinationState[T]
                relation*: BinaryRelation
                rhs*: T
            of AlgebraicType:
                algebraicConstraintState*: StatefulAlgebraicConstraint[T]

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: StatefulConstraint[T]): T {.inline.} =
    case constraint.stateType:
        of AllDifferentType:
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
        
        of AlgebraicType:
            return constraint.algebraicConstraintState.cost

################################################################################
# Computed Constraints
################################################################################

func allDifferent*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AllDifferentType,
        allDifferentState: newAllDifferentConstraint[T](positions)
    )

func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
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
        return StatefulConstraint[T](
            positions: positions,
            stateType: AllDifferentType,
            allDifferentState: newAllDifferentConstraint[T](expressions)
        )

proc linearCombinationEq*[T](positions: openArray[int], target: T): StatefulConstraint[T] =
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: LinearCombinationConstraint,
        relation: EqualTo,
        rhs: target,
        linearCombinationState: newLinearCombinationState[T](positions)
    )

proc linearCombinationEq*[T](expressions: seq[AlgebraicExpression[T]], target: T): StatefulConstraint[T] =
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

func initialize*[T](constraint: StatefulConstraint[T], assignment: seq[T]) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.initialize(assignment)
        of ElementConstraint:
            constraint.elementState.initialize(assignment)
        of LinearCombinationConstraint:
            constraint.linearCombinationState.initialize(assignment)
        of AlgebraicType:
            constraint.algebraicConstraintState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentConstraint:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of LinearCombinationConstraint:
            constraint.linearCombinationState.moveDelta(position, oldValue, newValue)
        of StatefulAlgebraicConstraint:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of LinearCombinationConstraint:
            constraint.linearCombinationState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
