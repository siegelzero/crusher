import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, elementState, sumConstraint, minConstraint, maxConstraint
import constraintNode
import ../expressions/[algebraic, maxExpression, minExpression]

################################################################################
# StatefulAlgebraicConstraint - moved from algebraic.nim
################################################################################

type
    StatefulAlgebraicConstraint*[T] = ref object
        # Stateful Constraint backed by an Algebraic Constraint, where the current
        # assignment is saved, along with the cost.
        # This constraint form has state which is updated as the assignment changes.
        currentAssignment*: Table[Natural, T]
        cost*: int
        constraint*: AlgebraicConstraint[T]
        positions: PackedSet[Natural]

# StatefulAlgebraicConstraint Creation

func init*[T](state: StatefulAlgebraicConstraint[T], constraint: AlgebraicConstraint[T]) =
    # Initializes StatefulAlgebraicConstraint version of the given constraint
    state.cost = 0
    state.positions = constraint.positions
    state.constraint = constraint
    state.currentAssignment = initTable[Natural, T]()

func newAlgebraicConstraintState*[T](constraint: AlgebraicConstraint[T]): StatefulAlgebraicConstraint[T] =
    new(result)
    result.init(constraint)

# StatefulAlgebraicConstraint Initialization

func initialize*[T](state: StatefulAlgebraicConstraint[T], assignment: seq[T]) =
    # Initializes the state with the given assignment.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
    state.cost = state.constraint.penalty(assignment)

# StatefulAlgebraicConstraint Updates

func updatePosition*[T](state: StatefulAlgebraicConstraint[T], position: int, newValue: T) {.inline.} =
    # Sets position=newValue in the given state and updates cost.
    state.currentAssignment[position] = newValue
    state.cost = state.constraint.penalty(state.currentAssignment)

func moveDelta*[T](state: StatefulAlgebraicConstraint[T], position: Natural, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    state.currentAssignment[position] = newValue
    let newCost = state.constraint.penalty(state.currentAssignment)
    let delta = newCost - oldCost
    state.currentAssignment[position] = oldValue
    return delta

################################################################################
# Stateful Constraint Wrapper Type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentType,
        ElementConstraint,
        SumExpressionType,
        AlgebraicType,
        MinConstraintType,
        MaxConstraintType

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
            of MinConstraintType:
                minConstraintState*: MinConstraint[T]
            of MaxConstraintType:
                maxConstraintState*: MaxConstraint[T]


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
        of MinConstraintType:
            return "Min Constraint"
        of MaxConstraintType:
            return "Max Constraint"

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
        of MinConstraintType:
            return constraint.minConstraintState.cost
        of MaxConstraintType:
            return constraint.maxConstraintState.cost

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

template MinValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: MinExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: MinConstraintType,
            minConstraintState: newMinConstraint[T](left, relEnum, right)
        )

MinValRel(`==`, EqualTo)
MinValRel(`>`, GreaterThan)
MinValRel(`>=`, GreaterThanEq)
MinValRel(`<`, LessThan)
MinValRel(`<=`, LessThanEq)

template MaxValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: MaxExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: MaxConstraintType,
            maxConstraintState: newMaxConstraint[T](left, relEnum, right)
        )

MaxValRel(`==`, EqualTo)
MaxValRel(`>`, GreaterThan)
MaxValRel(`>=`, GreaterThanEq)
MaxValRel(`<`, LessThan)
MaxValRel(`<=`, LessThanEq)

# Variable target operators for MinExpression (RefNode only)
template MinVarRel(rel, relEnum: untyped) =
    func `rel`*[T](left: MinExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        if right.node.kind != RefNode:
            raise newException(ValueError, "Variable target constraints require right side to be a simple variable reference")
        var positions = left.positions
        positions.incl(right.positions)
        return StatefulConstraint[T](
            positions: positions,
            stateType: MinConstraintType,
            minConstraintState: newMinConstraintWithVariableTarget[T](left, relEnum, right.node.position)
        )

MinVarRel(`==`, EqualTo)
MinVarRel(`>`, GreaterThan)
MinVarRel(`>=`, GreaterThanEq)
MinVarRel(`<`, LessThan)
MinVarRel(`<=`, LessThanEq)

# Variable target operators for MaxExpression (RefNode only)
template MaxVarRel(rel, relEnum: untyped) =
    func `rel`*[T](left: MaxExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        if right.node.kind != RefNode:
            raise newException(ValueError, "Variable target constraints require right side to be a simple variable reference")
        var positions = left.positions
        positions.incl(right.positions)
        return StatefulConstraint[T](
            positions: positions,
            stateType: MaxConstraintType,
            maxConstraintState: newMaxConstraintWithVariableTarget[T](left, relEnum, right.node.position)
        )

MaxVarRel(`==`, EqualTo)
MaxVarRel(`>`, GreaterThan)
MaxVarRel(`>=`, GreaterThanEq)
MaxVarRel(`<`, LessThan)
MaxVarRel(`<=`, LessThanEq)


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
        of MinConstraintType:
            constraint.minConstraintState.initialize(assignment)
        of MaxConstraintType:
            constraint.maxConstraintState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: Natural, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of SumExpressionType:
            constraint.sumExpressionConstraintState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)
        of MinConstraintType:
            constraint.minConstraintState.moveDelta(position, oldValue, newValue)
        of MaxConstraintType:
            constraint.maxConstraintState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: Natural, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of SumExpressionType:
            constraint.sumExpressionConstraintState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
        of MinConstraintType:
            constraint.minConstraintState.updatePosition(position, newValue)
        of MaxConstraintType:
            constraint.maxConstraintState.updatePosition(position, newValue)

