import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, elementState, relationalConstraint, ordering
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
        currentAssignment*: Table[int, T]
        cost*: int
        constraint*: AlgebraicConstraint[T]
        positions: PackedSet[int]

# StatefulAlgebraicConstraint Creation

func init*[T](state: StatefulAlgebraicConstraint[T], constraint: AlgebraicConstraint[T]) =
    # Initializes StatefulAlgebraicConstraint version of the given constraint
    state.cost = 0
    state.positions = constraint.positions
    state.constraint = constraint
    state.currentAssignment = initTable[int, T]()

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

func moveDelta*[T](state: StatefulAlgebraicConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
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
        RelationalConstraintType,
        OrderingType

    StatefulConstraint*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementConstraint:
                elementState*: ElementState[T]
            of AlgebraicType:
                algebraicConstraintState*: StatefulAlgebraicConstraint[T]
            of RelationalConstraintType:
                relationalConstraintState*: RelationalConstraint[T]
            of OrderingType:
                orderingState*: OrderingConstraint[T]


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
        of OrderingType:
            return "Ordering Constraint"

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
        of OrderingType:
            return constraint.orderingState.cost

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


func allDifferent*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AllDifferentType,
        allDifferentState: newAllDifferentConstraint[T](positions)
    )


func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return allDifferent[T](positions)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: AllDifferentType,
            allDifferentState: newAllDifferentConstraint[T](expressions)
        )


func increasing*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns increasing constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newIncreasingConstraint[T](positions)
    )


func increasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns increasing constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return increasing[T](positions)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: OrderingType,
            orderingState: newIncreasingConstraint[T](expressions)
        )


func strictlyIncreasing*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns strictly increasing constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newStrictlyIncreasingConstraint[T](positions)
    )


func strictlyIncreasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns strictly increasing constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return strictlyIncreasing[T](positions)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: OrderingType,
            orderingState: newStrictlyIncreasingConstraint[T](expressions)
        )


func decreasing*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns decreasing constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newDecreasingConstraint[T](positions)
    )


func decreasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns decreasing constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return decreasing[T](positions)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: OrderingType,
            orderingState: newDecreasingConstraint[T](expressions)
        )


func strictlyDecreasing*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns strictly decreasing constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newStrictlyDecreasingConstraint[T](positions)
    )


func strictlyDecreasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns strictly decreasing constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return strictlyDecreasing[T](positions)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: OrderingType,
            orderingState: newStrictlyDecreasingConstraint[T](expressions)
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
        of OrderingType:
            constraint.orderingState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)
        of RelationalConstraintType:
            constraint.relationalConstraintState.moveDelta(position, oldValue, newValue)
        of OrderingType:
            constraint.orderingState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
        of RelationalConstraintType:
            constraint.relationalConstraintState.updatePosition(position, newValue)
        of OrderingType:
            constraint.orderingState.updatePosition(position, newValue)

