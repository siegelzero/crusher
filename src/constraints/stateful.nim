import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, elementState, sumConstraint
import constraintNode
import ../expressions/expressions

################################################################################
# Type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentType,
        ElementConstraint,
        SumExpressionType,
        AlgebraicType

    StatefulConstraint*[T] = object
        positions*: PackedSet[Natural]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementConstraint:
                elementState*: ElementState[T]
            of SumExpressionType:
                sumExpressionConstraintState*: SumExpressionConstraint[T]
            of AlgebraicType:
                algebraicConstraintState*: StatefulAlgebraicConstraint[T]


func `$`*[T](constraint: StatefulConstraint[T]): string =
    case constraint.stateType:
        of AllDifferentType:
            return "AllDifferent Constraint"
        of ElementConstraint:
            return "Element Constraint"
        of SumExpressionType:
            return constraint.sumExpressionConstraintState.cost
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
        of SumExpressionType:
            return constraint.sumExpressionConstraintState.cost
        of AlgebraicType:
            return constraint.algebraicConstraintState.cost

################################################################################
# Computed Constraints
################################################################################

template LCValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: SumExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: SumExpressionType,
            sumExpressionConstraintState: newSumExpressionConstraint[T](left, relEnum, right)
        )

LCValRel(`==`, EqualTo)
LCValRel(`>`, GreaterThan)
LCValRel(`>=`, GreaterThanEq)
LCValRel(`<`, LessThan)
LCValRel(`<=`, LessThanEq)


func allDifferent*[T](positions: openArray[Natural]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[Natural](positions),
        stateType: AllDifferentType,
        allDifferentState: newAllDifferentConstraint[T](positions)
    )

func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given expressions.
    var positions = toPackedSet[Natural]([])
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
        of SumExpressionType:
            constraint.sumExpressionConstraintState.initialize(assignment)
        of AlgebraicType:
            constraint.algebraicConstraintState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentConstraint:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of SumExpressionType:
            constraint.sumExpressionConstraintState.moveDelta(position, oldValue, newValue)
        of StatefulAlgebraicConstraint:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of SumExpressionType:
            constraint.sumExpressionConstraintState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
