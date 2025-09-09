import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, elementState, relationalConstraint, ordering, globalCardinality
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
        ElementType,
        AlgebraicType,
        RelationalType,
        OrderingType,
        GlobalCardinalityType

    StatefulConstraint*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementType:
                elementState*: ElementState[T]
            of AlgebraicType:
                algebraicState*: StatefulAlgebraicConstraint[T]
            of RelationalType:
                relationalState*: RelationalConstraint[T]
            of OrderingType:
                orderingState*: OrderingConstraint[T]
            of GlobalCardinalityType:
                globalCardinalityState*: GlobalCardinalityConstraint[T]


func `$`*[T](constraint: StatefulConstraint[T]): string =
    case constraint.stateType:
        of AllDifferentType:
            return "AllDifferent Constraint"
        of ElementType:
            return "Element Constraint"
        of AlgebraicType:
            return "Algebraic Constraint"
        of RelationalType:
            return "Relational Constraint"
        of OrderingType:
            return "Ordering Constraint"
        of GlobalCardinalityType:
            return "Global Cardinality Constraint"

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: StatefulConstraint[T]): T {.inline.} =
    case constraint.stateType:
        of AllDifferentType:
            return constraint.allDifferentState.cost
        of ElementType:
            return constraint.elementState.cost
        of AlgebraicType:
            return constraint.algebraicState.cost
        of RelationalType:
            return constraint.relationalState.cost
        of OrderingType:
            return constraint.orderingState.cost
        of GlobalCardinalityType:
            return constraint.globalCardinalityState.cost

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
            stateType: RelationalType,
            relationalState: constraint
        )

    # Min-to-Min relations
    func `rel`*[T](left: MinExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Max-to-Max relations
    func `rel`*[T](left: MaxExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Min-to-Max relations
    func `rel`*[T](left: MinExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Max-to-Min relations
    func `rel`*[T](left: MaxExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Sum-to-Min relations
    func `rel`*[T](left: SumExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Sum-to-Max relations
    func `rel`*[T](left: SumExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # AlgebraicExpression-to-any relations
    func `rel`*[T](left: AlgebraicExpression[T], right: SumExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    func `rel`*[T](left: SumExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    func `rel`*[T](left: AlgebraicExpression[T], right: MinExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    func `rel`*[T](left: MinExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    func `rel`*[T](left: AlgebraicExpression[T], right: MaxExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    func `rel`*[T](left: MaxExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    func `rel`*[T](left: AlgebraicExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
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
            stateType: RelationalType,
            relationalState: constraint
        )

    # Min-to-constant relations
    func `rel`*[T](left: MinExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Max-to-constant relations
    func `rel`*[T](left: MaxExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

    # Algebraic-to-constant relations
    func `rel`*[T](left: AlgebraicExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left, right, relEnum)
        return StatefulConstraint[T](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
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


func globalCardinality*[T](positions: openArray[int], cover: openArray[T], counts: openArray[int]): StatefulConstraint[T] =
    # Returns global cardinality constraint for the given positions with exact counts.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: GlobalCardinalityType,
        globalCardinalityState: newExactGlobalCardinality[T](positions, cover, counts)
    )


func globalCardinality*[T](expressions: seq[AlgebraicExpression[T]], cover: openArray[T], counts: openArray[int]): StatefulConstraint[T] =
    # Returns global cardinality constraint for the given expressions with exact counts.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return globalCardinality[T](positions, cover, counts)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: GlobalCardinalityType,
            globalCardinalityState: newExactGlobalCardinality[T](expressions, cover, counts)
        )


func globalCardinalityBounded*[T](positions: openArray[int], cover: openArray[T], lbound: openArray[int], ubound: openArray[int]): StatefulConstraint[T] =
    # Returns global cardinality constraint for the given positions with lower/upper bounds.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: GlobalCardinalityType,
        globalCardinalityState: newBoundedGlobalCardinality[T](positions, cover, lbound, ubound)
    )


func globalCardinalityBounded*[T](expressions: seq[AlgebraicExpression[T]], cover: openArray[T], lbound: openArray[int], ubound: openArray[int]): StatefulConstraint[T] =
    # Returns global cardinality constraint for the given expressions with lower/upper bounds.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return globalCardinalityBounded[T](positions, cover, lbound, ubound)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: GlobalCardinalityType,
            globalCardinalityState: newBoundedGlobalCardinality[T](expressions, cover, lbound, ubound)
        )

################################################################################
# Computed Constraint State interface
################################################################################

func initialize*[T](constraint: StatefulConstraint[T], assignment: seq[T]) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.initialize(assignment)
        of ElementType:
            constraint.elementState.initialize(assignment)
        of AlgebraicType:
            constraint.algebraicState.initialize(assignment)
        of RelationalType:
            constraint.relationalState.initialize(assignment)
        of OrderingType:
            constraint.orderingState.initialize(assignment)
        of GlobalCardinalityType:
            constraint.globalCardinalityState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementType:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            constraint.algebraicState.moveDelta(position, oldValue, newValue)
        of RelationalType:
            constraint.relationalState.moveDelta(position, oldValue, newValue)
        of OrderingType:
            constraint.orderingState.moveDelta(position, oldValue, newValue)
        of GlobalCardinalityType:
            constraint.globalCardinalityState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementType:
            constraint.elementState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicState.updatePosition(position, newValue)
        of RelationalType:
            constraint.relationalState.updatePosition(position, newValue)
        of OrderingType:
            constraint.orderingState.updatePosition(position, newValue)
        of GlobalCardinalityType:
            constraint.globalCardinalityState.updatePosition(position, newValue)

################################################################################
# Deep copy for StatefulConstraint
################################################################################

proc deepCopy*[T](constraint: StatefulConstraint[T]): StatefulConstraint[T] =
    ## Creates a deep copy of a stateful constraint for thread-safe parallel processing
    ## All constraints are reset to their initial state (cost = 0) for consistency
    case constraint.stateType:
        of AllDifferentType:
            # Create fresh AllDifferent constraint (initialize with cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: AllDifferentType,
                allDifferentState: newAllDifferentConstraint[T](constraint.positions.toSeq())
            )
        of ElementType:
            # Create fresh Element constraint (initialize with cost: 0)
            if constraint.elementState.isConstantArray:
                result = StatefulConstraint[T](
                    positions: constraint.positions,
                    stateType: ElementType,
                    elementState: newElementState[T](
                        constraint.elementState.indexPosition,
                        constraint.elementState.constantArray,
                        constraint.elementState.valuePosition
                    )
                )
            else:
                result = StatefulConstraint[T](
                    positions: constraint.positions,
                    stateType: ElementType,
                    elementState: newElementState[T](
                        constraint.elementState.indexPosition,
                        constraint.elementState.arrayElements,
                        constraint.elementState.valuePosition
                    )
                )
        of AlgebraicType:
            # Create fresh AlgebraicConstraint (constructor sets cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: AlgebraicType,
                algebraicState: newAlgebraicConstraintState[T](
                    constraint.algebraicState.constraint
                )
            )
        of RelationalType:
            # Create fresh RelationalConstraint (initialize with cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: RelationalType,
                relationalState: RelationalConstraint[T](
                    lincomb: constraint.relationalState.lincomb,
                    relation: constraint.relationalState.relation,
                    rhs: constraint.relationalState.rhs,
                    cost: 0
                )
            )
        of OrderingType:
            # Create fresh OrderingConstraint (initialize with cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: OrderingType,
                orderingState: OrderingConstraint[T](
                    beforePos: constraint.orderingState.beforePos,
                    afterPos: constraint.orderingState.afterPos,
                    cost: 0
                )
            )
        of GlobalCardinalityType:
            # Create fresh GlobalCardinalityConstraint (initialize with cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: GlobalCardinalityType,
                globalCardinalityState: GlobalCardinalityConstraint[T](
                    positions: constraint.globalCardinalityState.positions,
                    cardinalityConstraints: constraint.globalCardinalityState.cardinalityConstraints,
                    cost: 0
                )
            )

