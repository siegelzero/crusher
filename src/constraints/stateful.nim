import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, elementState, linear
import constraintNode
import ../expressions

################################################################################
# Type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentType,
        ElementConstraint,
        LinearType,
        AlgebraicType

    StatefulConstraint*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementConstraint:
                elementState*: ElementState[T]
            of LinearType:
                linearConstraintState*: LinearConstraint[T]
            of AlgebraicType:
                algebraicConstraintState*: StatefulAlgebraicConstraint[T]


func `$`*[T](constraint: StatefulConstraint[T]): string =
    case constraint.stateType:
        of AllDifferentType:
            return "AllDifferent Constraint"
        of ElementConstraint:
            return "Element Constraint"
        of LinearType:
            return constraint.linearConstraintState.cost
        of AlgebraicType:
            return "Algebraic Constraint"

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: StatefulConstraint[T]): T {.inline.} =
    case constraint.stateType:
        of AllDifferentType:
            return constraint.allDifferentState.cost
        of ElementConstraint:
            return constraint.elementState.cost
        of LinearType:
            return constraint.linearConstraintState.cost
        of AlgebraicType:
            return constraint.algebraicConstraintState.cost

################################################################################
# Computed Constraints
################################################################################

template LCValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: LinearCombination[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: LinearType,
            linearConstraintState: newLinearConstraint[T](left, relEnum, right)
        )

LCValRel(`==`, EqualTo)
LCValRel(`>`, GreaterThan)
LCValRel(`>=`, GreaterThanEq)
LCValRel(`<`, LessThan)
LCValRel(`<=`, LessThanEq)


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
        return allDifferent[T](toSeq(positions))
    else:
        return StatefulConstraint[T](
            positions: positions,
            stateType: AllDifferentType,
            allDifferentState: newAllDifferentConstraint[T](expressions)
        )

################################################################################
# Computed Constraint State interface
################################################################################

func initialize*[T](constraint: StatefulConstraint[T], assignment: seq[T]) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.initialize(assignment)
        of ElementConstraint:
            constraint.elementState.initialize(assignment)
        of LinearType:
            constraint.linearConstraintState.initialize(assignment)
        of AlgebraicType:
            constraint.algebraicConstraintState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentConstraint:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of LinearType:
            constraint.linearConstraintState.moveDelta(position, oldValue, newValue)
        of StatefulAlgebraicConstraint:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of LinearType:
            constraint.linearConstraintState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
