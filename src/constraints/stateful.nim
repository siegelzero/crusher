import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, elementState, relationalConstraint
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
        AlgebraicType,
        RelationalConstraintType

    StatefulConstraint*[T] = object
        positions*: PackedSet[Natural]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementConstraint:
                elementState*: ElementState[T]
            of AlgebraicType:
                algebraicConstraintState*: StatefulAlgebraicConstraint[T]
            of RelationalConstraintType:
                relationalConstraintState*: RelationalConstraint[T]


func `$`*[T](constraint: StatefulConstraint[T]): string =
    case constraint.stateType:
        of AllDifferentType:
            return "AllDifferent Constraint"
        of ElementConstraint:
            return "Element Constraint"
        of AlgebraicType:
            return "Algebraic Constraint"
        of RelationalConstraintType:
            return "Relational Constraint"

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: StatefulConstraint[T]): T {.inline.} =
    case constraint.stateType:
        of AllDifferentType:
            return constraint.allDifferentState.cost
        of ElementConstraint:
            return constraint.elementState.cost
        of AlgebraicType:
            return constraint.algebraicConstraintState.cost
        of RelationalConstraintType:
            return constraint.relationalConstraintState.cost

################################################################################
# Computed Constraints
################################################################################


################################################################################
# Expression-to-Expression Relational Operators (using RelationalConstraint)
################################################################################

import ../expressions/stateful

# Template for expression-to-expression relations
template ExprExprRel(rel, relEnum: untyped) =
    # Sum-to-Sum relations
    func `rel`*[T](left: SumExpression[T], right: SumExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Min-to-Min relations
    func `rel`*[T](left: MinExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Max-to-Max relations
    func `rel`*[T](left: MaxExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Min-to-Max relations
    func `rel`*[T](left: MinExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Max-to-Min relations
    func `rel`*[T](left: MaxExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Sum-to-Min relations
    func `rel`*[T](left: SumExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Sum-to-Max relations
    func `rel`*[T](left: SumExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # AlgebraicExpression-to-any relations
    func `rel`*[T](left: AlgebraicExpression[T], right: SumExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    func `rel`*[T](left: SumExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    func `rel`*[T](left: AlgebraicExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    func `rel`*[T](left: MinExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    func `rel`*[T](left: AlgebraicExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    func `rel`*[T](left: MaxExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    func `rel`*[T](left: AlgebraicExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

# Generate all relational operators for expression-to-expression
ExprExprRel(`==`, EqualTo)
ExprExprRel(`!=`, NotEqualTo)
ExprExprRel(`>`, GreaterThan)
ExprExprRel(`>=`, GreaterThanEq)
ExprExprRel(`<`, LessThan)
ExprExprRel(`<=`, LessThanEq)

# Template for expression-to-constant relations (replaces old LCValRel, MinValRel, MaxValRel)
template ExprConstRel(rel, relEnum: untyped) =
    # Sum-to-constant relations
    func `rel`*[T](left: SumExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Min-to-constant relations
    func `rel`*[T](left: MinExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Max-to-constant relations
    func `rel`*[T](left: MaxExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

    # Algebraic-to-constant relations
    func `rel`*[T](left: AlgebraicExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalConstraintType,
            relationalConstraintState: constraint
        )

# Generate expression-to-constant operators
ExprConstRel(`==`, EqualTo)
ExprConstRel(`!=`, NotEqualTo)
ExprConstRel(`>`, GreaterThan)
ExprConstRel(`>=`, GreaterThanEq)
ExprConstRel(`<`, LessThan)
ExprConstRel(`<=`, LessThanEq)


func allDifferent*[T](positions: openArray[Natural]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[Natural](positions),
        stateType: AllDifferentType,
        allDifferentState: newAllDifferentConstraint[T](positions)
    )

func allDifferent*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given positions (int overload).
    var naturalPositions = newSeq[Natural](positions.len)
    for i, pos in positions:
        naturalPositions[i] = Natural(pos)
    return allDifferent[T](naturalPositions)

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
        of AlgebraicType:
            constraint.algebraicConstraintState.initialize(assignment)
        of RelationalConstraintType:
            constraint.relationalConstraintState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: Natural, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)
        of RelationalConstraintType:
            constraint.relationalConstraintState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: Natural, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
        of RelationalConstraintType:
            constraint.relationalConstraintState.updatePosition(position, newValue)

