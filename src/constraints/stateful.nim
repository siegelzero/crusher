import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, atleast, atmost, elementState, relationalConstraint, ordering, globalCardinality, multiknapsack, sequence
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
        AtLeastType,
        AtMostType,
        ElementType,
        AlgebraicType,
        RelationalType,
        OrderingType,
        GlobalCardinalityType,
        MultiknapsackType,
        SequenceType

    StatefulConstraint*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of AtLeastType:
                atLeastState*: AtLeastConstraint[T]
            of AtMostType:
                atMostState*: AtMostConstraint[T]
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
            of MultiknapsackType:
                multiknapsackState*: MultiknapsackConstraint[T]
            of SequenceType:
                sequenceState*: SequenceConstraint[T]


func `$`*[T](constraint: StatefulConstraint[T]): string =
    case constraint.stateType:
        of AllDifferentType:
            return "AllDifferent Constraint"
        of AtLeastType:
            return "AtLeast Constraint"
        of AtMostType:
            return "AtMost Constraint"
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
        of MultiknapsackType:
            return "Multiknapsack Constraint"
        of SequenceType:
            return "Sequence Constraint"

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: StatefulConstraint[T]): T {.inline.} =
    case constraint.stateType:
        of AllDifferentType:
            return constraint.allDifferentState.cost
        of AtLeastType:
            return constraint.atLeastState.cost
        of AtMostType:
            return constraint.atMostState.cost
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
        of MultiknapsackType:
            return constraint.multiknapsackState.cost
        of SequenceType:
            return constraint.sequenceState.cost

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
    ## Creates an AllDifferent constraint ensuring all variables have distinct values.
    ##
    ## **Mathematical Form**: `∀i,j ∈ positions, i ≠ j : x[i] ≠ x[j]`
    ##
    ## **Parameters**:
    ## - `positions`: Array of variable positions that must have unique values
    ##
    ## **Applications**: N-Queens, resource assignment, scheduling, permutation problems
    ##
    ## **Violation Cost**: Sum of duplicate pairs, computed efficiently with frequency counts
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AllDifferentType,
        allDifferentState: newAllDifferentConstraint[T](positions)
    )


func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates an AllDifferent constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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


func atLeast*[T](positions: openArray[int], targetValue: T, minOccurrences: int): StatefulConstraint[T] =
    ## Creates an AtLeast constraint ensuring minimum occurrences of a target value.
    ##
    ## **Mathematical Form**: `|{i ∈ positions : x[i] = targetValue}| ≥ minOccurrences`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions to check
    ## - `targetValue`: Value that must appear at least minOccurrences times
    ## - `minOccurrences`: Minimum required count of targetValue
    ##
    ## **Applications**: Resource allocation, quality control, load balancing
    ##
    ## **Violation Cost**: `max(0, minOccurrences - actualOccurrences)`
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AtLeastType,
        atLeastState: newAtLeastConstraint[T](positions, targetValue, minOccurrences)
    )


func atLeast*[T](expressions: seq[AlgebraicExpression[T]], targetValue: T, minOccurrences: int): StatefulConstraint[T] =
    ## Creates an AtLeast constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return atLeast[T](positions, targetValue, minOccurrences)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: AtLeastType,
            atLeastState: newAtLeastConstraint[T](expressions, targetValue, minOccurrences)
        )


func atMost*[T](positions: openArray[int], targetValue: T, maxOccurrences: int): StatefulConstraint[T] =
    ## Creates an AtMost constraint ensuring maximum occurrences of a target value.
    ##
    ## **Mathematical Form**: `|{i ∈ positions : x[i] = targetValue}| ≤ maxOccurrences`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions to check
    ## - `targetValue`: Value that must appear at most maxOccurrences times
    ## - `maxOccurrences`: Maximum allowed count of targetValue
    ##
    ## **Applications**: Capacity management, regulatory compliance, risk management
    ##
    ## **Violation Cost**: `max(0, actualOccurrences - maxOccurrences)`
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AtMostType,
        atMostState: newAtMostConstraint[T](positions, targetValue, maxOccurrences)
    )


func atMost*[T](expressions: seq[AlgebraicExpression[T]], targetValue: T, maxOccurrences: int): StatefulConstraint[T] =
    ## Creates an AtMost constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return atMost[T](positions, targetValue, maxOccurrences)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: AtMostType,
            atMostState: newAtMostConstraint[T](expressions, targetValue, maxOccurrences)
        )


func increasing*[T](positions: openArray[int]): StatefulConstraint[T] =
    ## Creates an Increasing constraint ensuring non-decreasing order.
    ##
    ## **Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] ≤ x[positions[i+1]]`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions that must be in non-decreasing order
    ##
    ## **Applications**: Scheduling (start ≤ finish), resource allocation, data sorting
    ##
    ## **Violation Cost**: Count of adjacent pairs that violate ordering
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newIncreasingConstraint[T](positions)
    )


func increasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates an Increasing constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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
    ## Creates a Strictly Increasing constraint ensuring strict ordering.
    ##
    ## **Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] < x[positions[i+1]]`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions that must be in strictly increasing order
    ##
    ## **Applications**: Ranking systems, tournament ordering, strict improvement requirements
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newStrictlyIncreasingConstraint[T](positions)
    )


func strictlyIncreasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates a Strictly Increasing constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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
    ## Creates a Decreasing constraint ensuring non-increasing order.
    ##
    ## **Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] ≥ x[positions[i+1]]`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions that must be in non-increasing order
    ##
    ## **Applications**: Resource depletion, priority allocation, performance degradation modeling
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newDecreasingConstraint[T](positions)
    )


func decreasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates a Decreasing constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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
    ## Creates a Strictly Decreasing constraint ensuring strict ordering.
    ##
    ## **Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] > x[positions[i+1]]`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions that must be in strictly decreasing order
    ##
    ## **Applications**: Tournament rankings, temperature cooling, quality control
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: OrderingType,
        orderingState: newStrictlyDecreasingConstraint[T](positions)
    )


func strictlyDecreasing*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates a Strictly Decreasing constraint for algebraic expressions.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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
    ## Creates a Global Cardinality constraint with exact count requirements.
    ##
    ## **Mathematical Form**: `∀v ∈ cover : |{i ∈ positions : x[i] = v}| = counts[v]`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions to check
    ## - `cover`: Values to track occurrences for
    ## - `counts`: Exact required count for each value in cover
    ##
    ## **Applications**: Workforce scheduling, resource allocation, load balancing
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: GlobalCardinalityType,
        globalCardinalityState: newExactGlobalCardinality[T](positions, cover, counts)
    )


func globalCardinality*[T](expressions: seq[AlgebraicExpression[T]], cover: openArray[T], counts: openArray[int]): StatefulConstraint[T] =
    ## Creates a Global Cardinality constraint for algebraic expressions with exact counts.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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
    ## Creates a Global Cardinality constraint with bounded count requirements.
    ##
    ## **Mathematical Form**: `∀v ∈ cover : lbound[v] ≤ |{i ∈ positions : x[i] = v}| ≤ ubound[v]`
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions to check
    ## - `cover`: Values to track occurrences for
    ## - `lbound`: Minimum required count for each value
    ## - `ubound`: Maximum allowed count for each value
    ##
    ## **Applications**: Flexible resource allocation, capacity management, quality control
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: GlobalCardinalityType,
        globalCardinalityState: newBoundedGlobalCardinality[T](positions, cover, lbound, ubound)
    )


func globalCardinalityBounded*[T](expressions: seq[AlgebraicExpression[T]], cover: openArray[T], lbound: openArray[int], ubound: openArray[int]): StatefulConstraint[T] =
    ## Creates a Global Cardinality constraint for algebraic expressions with bounded counts.
    ## Optimizes to position-based evaluation when expressions are simple variable references.
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
        of AtLeastType:
            constraint.atLeastState.initialize(assignment)
        of AtMostType:
            constraint.atMostState.initialize(assignment)
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
        of MultiknapsackType:
            constraint.multiknapsackState.initialize(assignment)
        of SequenceType:
            constraint.sequenceState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of AtLeastType:
            constraint.atLeastState.moveDelta(position, oldValue, newValue)
        of AtMostType:
            constraint.atMostState.moveDelta(position, oldValue, newValue)
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
        of MultiknapsackType:
            constraint.multiknapsackState.moveDelta(position, oldValue, newValue)
        of SequenceType:
            constraint.sequenceState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of AtLeastType:
            constraint.atLeastState.updatePosition(position, newValue)
        of AtMostType:
            constraint.atMostState.updatePosition(position, newValue)
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
        of MultiknapsackType:
            constraint.multiknapsackState.updatePosition(position, newValue)
        of SequenceType:
            constraint.sequenceState.updatePosition(position, newValue)

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
        of AtLeastType:
            # Create fresh AtLeast constraint (initialize with cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: AtLeastType,
                atLeastState: newAtLeastConstraint[T](
                    constraint.positions.toSeq(),
                    constraint.atLeastState.targetValue,
                    constraint.atLeastState.minOccurrences
                )
            )
        of AtMostType:
            # Create fresh AtMost constraint (initialize with cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: AtMostType,
                atMostState: newAtMostConstraint[T](
                    constraint.positions.toSeq(),
                    constraint.atMostState.targetValue,
                    constraint.atMostState.maxOccurrences
                )
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
            # Create deep copy preserving all runtime state including expression state
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: RelationalType,
                relationalState: RelationalConstraint[T](
                    leftExpr: constraint.relationalState.leftExpr.deepCopy(),
                    rightExpr: constraint.relationalState.rightExpr.deepCopy(),
                    relation: constraint.relationalState.relation,
                    cost: constraint.relationalState.cost,
                    positions: constraint.relationalState.positions,
                    leftValue: constraint.relationalState.leftValue,
                    rightValue: constraint.relationalState.rightValue
                )
            )
        of OrderingType:
            # Create proper deep copy preserving all runtime state
            case constraint.orderingState.evalMethod:
                of PositionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: OrderingType,
                        orderingState: OrderingConstraint[T](
                            orderingType: constraint.orderingState.orderingType,
                            currentAssignment: constraint.orderingState.currentAssignment,
                            cost: constraint.orderingState.cost,
                            evalMethod: PositionBased,
                            positions: constraint.orderingState.positions,
                            sortedPositions: constraint.orderingState.sortedPositions
                        )
                    )
                of ExpressionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: OrderingType,
                        orderingState: OrderingConstraint[T](
                            orderingType: constraint.orderingState.orderingType,
                            currentAssignment: constraint.orderingState.currentAssignment,
                            cost: constraint.orderingState.cost,
                            evalMethod: ExpressionBased,
                            expressions: constraint.orderingState.expressions,
                            expressionsAtPosition: constraint.orderingState.expressionsAtPosition
                        )
                    )
        of GlobalCardinalityType:
            # Create deep copy preserving all runtime state
            case constraint.globalCardinalityState.evalMethod:
                of PositionBased:
                    case constraint.globalCardinalityState.constraintType:
                        of ExactCounts:
                            result = StatefulConstraint[T](
                                positions: constraint.positions,
                                stateType: GlobalCardinalityType,
                                globalCardinalityState: GlobalCardinalityConstraint[T](
                                    currentAssignment: constraint.globalCardinalityState.currentAssignment,
                                    countTable: constraint.globalCardinalityState.countTable,
                                    cover: constraint.globalCardinalityState.cover,
                                    cost: constraint.globalCardinalityState.cost,
                                    evalMethod: PositionBased,
                                    positions: constraint.globalCardinalityState.positions,
                                    constraintType: ExactCounts,
                                    targetCounts: constraint.globalCardinalityState.targetCounts
                                )
                            )
                        of BoundedCounts:
                            result = StatefulConstraint[T](
                                positions: constraint.positions,
                                stateType: GlobalCardinalityType,
                                globalCardinalityState: GlobalCardinalityConstraint[T](
                                    currentAssignment: constraint.globalCardinalityState.currentAssignment,
                                    countTable: constraint.globalCardinalityState.countTable,
                                    cover: constraint.globalCardinalityState.cover,
                                    cost: constraint.globalCardinalityState.cost,
                                    evalMethod: PositionBased,
                                    positions: constraint.globalCardinalityState.positions,
                                    constraintType: BoundedCounts,
                                    lowerBounds: constraint.globalCardinalityState.lowerBounds,
                                    upperBounds: constraint.globalCardinalityState.upperBounds
                                )
                            )
                of ExpressionBased:
                    case constraint.globalCardinalityState.constraintType:
                        of ExactCounts:
                            result = StatefulConstraint[T](
                                positions: constraint.positions,
                                stateType: GlobalCardinalityType,
                                globalCardinalityState: GlobalCardinalityConstraint[T](
                                    currentAssignment: constraint.globalCardinalityState.currentAssignment,
                                    countTable: constraint.globalCardinalityState.countTable,
                                    cover: constraint.globalCardinalityState.cover,
                                    cost: constraint.globalCardinalityState.cost,
                                    evalMethod: ExpressionBased,
                                    expressions: constraint.globalCardinalityState.expressions,
                                    expressionsAtPosition: constraint.globalCardinalityState.expressionsAtPosition,
                                    constraintType: ExactCounts,
                                    targetCounts: constraint.globalCardinalityState.targetCounts
                                )
                            )
                        of BoundedCounts:
                            result = StatefulConstraint[T](
                                positions: constraint.positions,
                                stateType: GlobalCardinalityType,
                                globalCardinalityState: GlobalCardinalityConstraint[T](
                                    currentAssignment: constraint.globalCardinalityState.currentAssignment,
                                    countTable: constraint.globalCardinalityState.countTable,
                                    cover: constraint.globalCardinalityState.cover,
                                    cost: constraint.globalCardinalityState.cost,
                                    evalMethod: ExpressionBased,
                                    expressions: constraint.globalCardinalityState.expressions,
                                    expressionsAtPosition: constraint.globalCardinalityState.expressionsAtPosition,
                                    constraintType: BoundedCounts,
                                    lowerBounds: constraint.globalCardinalityState.lowerBounds,
                                    upperBounds: constraint.globalCardinalityState.upperBounds
                                )
                            )
        of MultiknapsackType:
            # Create proper deep copy preserving all runtime state
            case constraint.multiknapsackState.evalMethod:
                of PositionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: MultiknapsackType,
                        multiknapsackState: MultiknapsackConstraint[T](
                            currentAssignment: constraint.multiknapsackState.currentAssignment,
                            weights: constraint.multiknapsackState.weights,
                            capacities: constraint.multiknapsackState.capacities,
                            loadTable: constraint.multiknapsackState.loadTable,
                            cost: constraint.multiknapsackState.cost,
                            evalMethod: PositionBased,
                            positions: constraint.multiknapsackState.positions
                        )
                    )
                of ExpressionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: MultiknapsackType,
                        multiknapsackState: MultiknapsackConstraint[T](
                            currentAssignment: constraint.multiknapsackState.currentAssignment,
                            weights: constraint.multiknapsackState.weights,
                            capacities: constraint.multiknapsackState.capacities,
                            loadTable: constraint.multiknapsackState.loadTable,
                            cost: constraint.multiknapsackState.cost,
                            evalMethod: ExpressionBased,
                            expressions: constraint.multiknapsackState.expressions,
                            expressionsAtPosition: constraint.multiknapsackState.expressionsAtPosition
                        )
                    )
        of SequenceType:
            # Create deep copy preserving all runtime state
            case constraint.sequenceState.evalMethod:
                of PositionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: SequenceType,
                        sequenceState: SequenceConstraint[T](
                            currentAssignment: constraint.sequenceState.currentAssignment,
                            cost: constraint.sequenceState.cost,
                            minInSet: constraint.sequenceState.minInSet,
                            maxInSet: constraint.sequenceState.maxInSet,
                            windowSize: constraint.sequenceState.windowSize,
                            targetSet: constraint.sequenceState.targetSet,
                            evalMethod: PositionBased,
                            positions: constraint.sequenceState.positions
                        )
                    )
                of ExpressionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: SequenceType,
                        sequenceState: SequenceConstraint[T](
                            currentAssignment: constraint.sequenceState.currentAssignment,
                            cost: constraint.sequenceState.cost,
                            minInSet: constraint.sequenceState.minInSet,
                            maxInSet: constraint.sequenceState.maxInSet,
                            windowSize: constraint.sequenceState.windowSize,
                            targetSet: constraint.sequenceState.targetSet,
                            evalMethod: ExpressionBased,
                            expressions: constraint.sequenceState.expressions,
                            expressionsAtPosition: constraint.sequenceState.expressionsAtPosition
                        )
                    )



################################################################################
# Multiknapsack wrapper functions
################################################################################

func multiknapsack*[T](positions: openArray[int], weights: openArray[T], capacities: openArray[(T, T)]): StatefulConstraint[T] =
    ## Creates a multiknapsack constraint ensuring total weight per value doesn't exceed capacity.
    ## - positions: Variable positions/indices
    ## - weights: Weight of each position
    ## - capacities: Array of (value, capacity) pairs
    ## Example: multiknapsack([0,1,2], [2,3,1], [(1,5), (2,4)]) for bin packing
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: MultiknapsackType,
        multiknapsackState: newMultiknapsackConstraint[T](positions, weights, capacities)
    )

func multiknapsack*[T](expressions: seq[AlgebraicExpression[T]], weights: openArray[T], capacities: openArray[(T, T)]): StatefulConstraint[T] =
    # Returns multiknapsack constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return multiknapsack[T](positions, weights, capacities)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)

        return StatefulConstraint[T](
            positions: allPositions,
            stateType: MultiknapsackType,
            multiknapsackState: newMultiknapsackConstraint[T](expressions, weights, capacities)
        )

################################################################################
# Sequence wrapper functions
################################################################################

func sequence*[T](positions: openArray[int], minInSet, maxInSet, windowSize: int, targetSet: openArray[T]): StatefulConstraint[T] =
    ## Creates a sequence constraint ensuring count of target values in consecutive windows.
    ## - positions: Variable positions forming the sequence
    ## - minInSet/maxInSet: Min/max occurrences of target values per window
    ## - windowSize: Size of consecutive window to check
    ## - targetSet: Values to count in each window
    ## Example: sequence([0,1,2,3,4,5,6], 2, 7, 7, [REST]) for work scheduling
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: SequenceType,
        sequenceState: newSequenceConstraint[T](positions, minInSet, maxInSet, windowSize, targetSet)
    )

func sequence*[T](expressions: seq[AlgebraicExpression[T]], minInSet, maxInSet, windowSize: int, targetSet: openArray[T]): StatefulConstraint[T] =
    # Returns sequence constraint for the given expressions.
    let (allRefs, positions) = isAllRefs(expressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return sequence[T](positions, minInSet, maxInSet, windowSize, targetSet)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)

        return StatefulConstraint[T](
            positions: allPositions,
            stateType: SequenceType,
            sequenceState: newSequenceConstraint[T](expressions, minInSet, maxInSet, windowSize, targetSet)
        )
