import std/[packedsets, sequtils, tables]

import algebraic, allDifferent, allDifferentExcept0, atleast, atmost, elementState, relationalConstraint, ordering, globalCardinality, multiknapsack, sequence, cumulative, geost, irdcs, circuit, lexOrder, tableConstraint, regular
import constraintNode, types
import ../expressions/[algebraic, maxExpression, minExpression]

export StatefulConstraint, StatefulConstraintType, StatefulAlgebraicConstraint, BooleanConstraint

# StatefulAlgebraicConstraint moved to types.nim

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
    for pos in state.positions.items:
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

# StatefulConstraint definition moved to types.nim

################################################################################
# BooleanConstraint implementation - type definition is in types.nim
################################################################################

# Helper functions for penalty calculation
func calculateUnaryPenalty[T](op: UnaryRelation, targetPenalty: T): T {.inline.} =
    ## Calculates penalty for unary operations
    case op:
    of Not:
        return if targetPenalty == 0: 1 else: 0

func calculateBooleanPenalty[T](op: BooleanOperation, leftPenalty, rightPenalty: T): T {.inline.} =
    ## Calculates penalty for boolean operations based on child constraint penalties.
    ## Uses graduated penalties where possible to give the tabu search gradient information.
    case op:
    of And:
        # Both must be satisfied
        return leftPenalty + rightPenalty
    of Or:
        # At least one must be satisfied
        return min(leftPenalty, rightPenalty)
    of Xor:
        # Exactly one must be satisfied
        if (leftPenalty == 0) != (rightPenalty == 0): return 0  # exactly one satisfied
        elif leftPenalty == 0: return 1                         # both satisfied, must break one
        else: return min(leftPenalty, rightPenalty)              # both violated, guide toward easier fix
    of Implies:
        # If left then right: graduated consequent penalty guides search
        if leftPenalty > 0: return 0       # antecedent false → trivially satisfied
        else: return rightPenalty           # antecedent true → pass through consequent penalty
    of Iff:
        # Both or neither: graduated penalty guides toward satisfying the violated side
        if leftPenalty == 0 and rightPenalty == 0: return 0
        elif leftPenalty > 0 and rightPenalty > 0: return 0
        elif leftPenalty == 0: return rightPenalty  # left satisfied, guide toward satisfying right
        else: return leftPenalty                    # right satisfied, guide toward satisfying left

# BooleanConstraint creation functions
func newBooleanConstraint*[T](leftConstraint, rightConstraint: StatefulConstraint[T],
                              booleanOp: BooleanOperation): BooleanConstraint[T] =
    ## Creates a new binary BooleanConstraint combining two stateful constraints
    result = BooleanConstraint[T](
        isUnary: false,
        booleanOp: booleanOp,
        leftConstraint: leftConstraint,
        rightConstraint: rightConstraint,
        cachedLeftPenalty: 0,
        cachedRightPenalty: 0,
        cost: 0,
        positions: leftConstraint.positions + rightConstraint.positions
    )

func newUnaryBooleanConstraint*[T](targetConstraint: StatefulConstraint[T],
                                   unaryOp: UnaryRelation): BooleanConstraint[T] =
    ## Creates a new unary BooleanConstraint (like NOT)
    result = BooleanConstraint[T](
        isUnary: true,
        unaryOp: unaryOp,
        targetConstraint: targetConstraint,
        cachedTargetPenalty: 0,
        cost: 0,
        positions: targetConstraint.positions
    )

# BooleanConstraint State Management
func initialize*[T](constraint: BooleanConstraint[T], assignment: seq[T]) =
    ## Initialize the boolean constraint with the given assignment and cache child penalties
    case constraint.isUnary:
    of true:
        constraint.targetConstraint.initialize(assignment)
        constraint.cachedTargetPenalty = constraint.targetConstraint.penalty()
        constraint.cost = calculateUnaryPenalty(constraint.unaryOp, constraint.cachedTargetPenalty)
    of false:
        constraint.leftConstraint.initialize(assignment)
        constraint.rightConstraint.initialize(assignment)
        constraint.cachedLeftPenalty = constraint.leftConstraint.penalty()
        constraint.cachedRightPenalty = constraint.rightConstraint.penalty()
        constraint.cost = calculateBooleanPenalty(
            constraint.booleanOp,
            constraint.cachedLeftPenalty,
            constraint.cachedRightPenalty
        )

func moveDelta*[T](constraint: BooleanConstraint[T], position: int, oldValue, newValue: T): int =
    ## Calculate the change in penalty for a position change using cached penalties.
    ## Uses short-circuit logic to skip expensive child moveDelta calls when cached
    ## state proves the overall result cannot change.
    # Early exit if position doesn't affect this constraint
    if position notin constraint.positions:
        return 0

    case constraint.isUnary:
    of true:
        # Only calculate delta if position affects the target constraint
        let targetDelta = if position in constraint.targetConstraint.positions:
            constraint.targetConstraint.moveDelta(position, oldValue, newValue)
        else: 0

        let newTargetPenalty = constraint.cachedTargetPenalty + targetDelta
        let newCost = calculateUnaryPenalty(constraint.unaryOp, newTargetPenalty)
        return newCost - constraint.cost
    of false:
        let posInLeft = position in constraint.leftConstraint.positions
        let posInRight = position in constraint.rightConstraint.positions

        # Short-circuit: skip expensive child moveDelta when cached state proves result is unchanged
        case constraint.booleanOp:
        of Implies:
            # Implies satisfied when antecedent is false (leftPenalty > 0) or consequent is true (rightPenalty == 0)
            if not posInLeft and constraint.cachedLeftPenalty > 0:
                return 0  # antecedent stays false → trivially satisfied regardless of right
            if not posInRight and constraint.cachedRightPenalty == 0:
                return 0  # consequent stays true → satisfied regardless of left
        of Or:
            # Or satisfied when either side has penalty 0
            if not posInLeft and constraint.cachedLeftPenalty == 0:
                return 0  # left stays satisfied → Or stays at 0 regardless of right
            if not posInRight and constraint.cachedRightPenalty == 0:
                return 0  # right stays satisfied → Or stays at 0 regardless of left
        else:
            discard

        let leftDelta = if posInLeft:
            constraint.leftConstraint.moveDelta(position, oldValue, newValue)
        else: 0

        let rightDelta = if posInRight:
            constraint.rightConstraint.moveDelta(position, oldValue, newValue)
        else: 0

        let newLeftPenalty = constraint.cachedLeftPenalty + leftDelta
        let newRightPenalty = constraint.cachedRightPenalty + rightDelta

        let newCost = calculateBooleanPenalty(constraint.booleanOp, newLeftPenalty, newRightPenalty)
        return newCost - constraint.cost

func updatePosition*[T](constraint: BooleanConstraint[T], position: int, newValue: T) =
    ## Update a position with a new value and maintain cached penalties.
    ## Only updates children that are actually affected by the position change.
    case constraint.isUnary:
    of true:
        if position in constraint.targetConstraint.positions:
            constraint.targetConstraint.updatePosition(position, newValue)
            constraint.cachedTargetPenalty = constraint.targetConstraint.penalty()
            constraint.cost = calculateUnaryPenalty(constraint.unaryOp, constraint.cachedTargetPenalty)
    of false:
        if position in constraint.leftConstraint.positions:
            constraint.leftConstraint.updatePosition(position, newValue)
            constraint.cachedLeftPenalty = constraint.leftConstraint.penalty()
        if position in constraint.rightConstraint.positions:
            constraint.rightConstraint.updatePosition(position, newValue)
            constraint.cachedRightPenalty = constraint.rightConstraint.penalty()
        constraint.cost = calculateBooleanPenalty(
            constraint.booleanOp,
            constraint.cachedLeftPenalty,
            constraint.cachedRightPenalty
        )

func penalty*[T](constraint: BooleanConstraint[T]): int =
    ## Get the current penalty
    return constraint.cost

# Deep copy support
proc deepCopy*[T](constraint: BooleanConstraint[T]): BooleanConstraint[T] =
    ## Creates a deep copy of a BooleanConstraint for thread-safe parallel processing
    case constraint.isUnary:
    of true:
        result = BooleanConstraint[T](
            isUnary: true,
            unaryOp: constraint.unaryOp,
            targetConstraint: constraint.targetConstraint.deepCopy(),
            cachedTargetPenalty: constraint.cachedTargetPenalty,
            cost: constraint.cost,
            positions: constraint.positions  # PackedSet is a value type, safe to copy
        )
    of false:
        result = BooleanConstraint[T](
            isUnary: false,
            booleanOp: constraint.booleanOp,
            leftConstraint: constraint.leftConstraint.deepCopy(),
            rightConstraint: constraint.rightConstraint.deepCopy(),
            cachedLeftPenalty: constraint.cachedLeftPenalty,
            cachedRightPenalty: constraint.cachedRightPenalty,
            cost: constraint.cost,
            positions: constraint.positions  # PackedSet is a value type, safe to copy
        )

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
        of BooleanType:
            return "Boolean Constraint"
        of CumulativeType:
            return "Cumulative Constraint"
        of GeostType:
            return "Geost Constraint"
        of IrdcsType:
            return "IRDCS Constraint"
        of CircuitType:
            return "Circuit Constraint"
        of AllDifferentExcept0Type:
            return "AllDifferentExcept0 Constraint"
        of LexOrderType:
            return "LexOrder Constraint"
        of TableConstraintType:
            return "Table Constraint"
        of RegularType:
            return "Regular Constraint"

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
        of BooleanType:
            return constraint.booleanState.cost
        of CumulativeType:
            return constraint.cumulativeState.cost
        of GeostType:
            return constraint.geostState.cost
        of IrdcsType:
            return constraint.irdcsState.cost
        of CircuitType:
            return constraint.circuitState.cost
        of AllDifferentExcept0Type:
            return constraint.allDifferentExcept0State.cost
        of LexOrderType:
            return constraint.lexOrderState.cost
        of TableConstraintType:
            return constraint.tableConstraintState.cost
        of RegularType:
            return constraint.regularState.cost

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

    # AlgebraicExpression-to-AlgebraicExpression relations
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

    # StatefulAlgebraicExpression-to-constant relations
    func `rel`*[T](left: StatefulAlgebraicExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        let constraint = newRelationalConstraint[T](left.algebraicExpr, right, relEnum)
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
        of BooleanType:
            constraint.booleanState.initialize(assignment)
        of CumulativeType:
            constraint.cumulativeState.initialize(assignment)
        of GeostType:
            constraint.geostState.initialize(assignment)
        of IrdcsType:
            constraint.irdcsState.initialize(assignment)
        of CircuitType:
            constraint.circuitState.initialize(assignment)
        of AllDifferentExcept0Type:
            constraint.allDifferentExcept0State.initialize(assignment)
        of LexOrderType:
            constraint.lexOrderState.initialize(assignment)
        of TableConstraintType:
            constraint.tableConstraintState.initialize(assignment)
        of RegularType:
            constraint.regularState.initialize(assignment)


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
        of BooleanType:
            constraint.booleanState.moveDelta(position, oldValue, newValue)
        of CumulativeType:
            constraint.cumulativeState.moveDelta(position, oldValue, newValue)
        of GeostType:
            constraint.geostState.moveDelta(position, oldValue, newValue)
        of IrdcsType:
            constraint.irdcsState.moveDelta(position, oldValue, newValue)
        of CircuitType:
            constraint.circuitState.moveDelta(position, oldValue, newValue)
        of AllDifferentExcept0Type:
            constraint.allDifferentExcept0State.moveDelta(position, oldValue, newValue)
        of LexOrderType:
            constraint.lexOrderState.moveDelta(position, oldValue, newValue)
        of TableConstraintType:
            constraint.tableConstraintState.moveDelta(position, oldValue, newValue)
        of RegularType:
            constraint.regularState.moveDelta(position, oldValue, newValue)


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
        of BooleanType:
            constraint.booleanState.updatePosition(position, newValue)
        of CumulativeType:
            constraint.cumulativeState.updatePosition(position, newValue)
        of GeostType:
            constraint.geostState.updatePosition(position, newValue)
        of IrdcsType:
            constraint.irdcsState.updatePosition(position, newValue)
        of CircuitType:
            constraint.circuitState.updatePosition(position, newValue)
        of AllDifferentExcept0Type:
            constraint.allDifferentExcept0State.updatePosition(position, newValue)
        of LexOrderType:
            constraint.lexOrderState.updatePosition(position, newValue)
        of TableConstraintType:
            constraint.tableConstraintState.updatePosition(position, newValue)
        of RegularType:
            constraint.regularState.updatePosition(position, newValue)


func getAffectedPositions*[T](constraint: StatefulConstraint[T]): PackedSet[int] =
    ## Returns positions affected by the last updatePosition call.
    ## For most constraints, this is all positions in the constraint.
    ## For Cumulative and Geost constraints, returns a smarter subset.
    case constraint.stateType:
        of CumulativeType:
            return constraint.cumulativeState.getAffectedPositions()
        of GeostType:
            return constraint.geostState.getAffectedPositions()
        else:
            return constraint.positions


func getAffectedDomainValues*[T](constraint: StatefulConstraint[T], position: int): seq[T] =
    ## Returns domain values for `position` that need penalty recalculation after the last change.
    ## For most constraints, returns empty (meaning all values need recalculation).
    ## For Cumulative constraints, returns only values overlapping with the changed time range.
    case constraint.stateType:
        of CumulativeType:
            return constraint.cumulativeState.getAffectedDomainValues(position)
        else:
            return @[]

################################################################################
# Deep copy for StatefulConstraint
################################################################################

proc deepCopy*[T](constraint: StatefulConstraint[T]): StatefulConstraint[T] =
    ## Creates a deep copy of a stateful constraint for thread-safe parallel processing
    ## All constraints are reset to their initial state (cost = 0) for consistency
    case constraint.stateType:
        of AllDifferentType:
            # Create fresh AllDifferent constraint (initialize with cost: 0)
            case constraint.allDifferentState.evalMethod:
                of PositionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: AllDifferentType,
                        allDifferentState: newAllDifferentConstraint[T](constraint.positions.toSeq())
                    )
                of ExpressionBased:
                    # Deep copy expressions to ensure independence
                    var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.allDifferentState.expressions.len)
                    for i, expr in constraint.allDifferentState.expressions:
                        copiedExpressions[i] = expr.deepCopy()
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: AllDifferentType,
                        allDifferentState: newAllDifferentConstraint[T](copiedExpressions)
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
            case constraint.elementState.evalMethod:
                of PositionBased:
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
                of ExpressionBased:
                    if constraint.elementState.isConstantArrayEB:
                        result = StatefulConstraint[T](
                            positions: constraint.positions,
                            stateType: ElementType,
                            elementState: newElementStateExprBasedConst[T](
                                constraint.elementState.indexExpression,
                                constraint.elementState.constantArrayEB,
                                constraint.elementState.valueExpression
                            )
                        )
                    else:
                        result = StatefulConstraint[T](
                            positions: constraint.positions,
                            stateType: ElementType,
                            elementState: newElementStateExprBased[T](
                                constraint.elementState.indexExpression,
                                constraint.elementState.arrayExpressionsEB,
                                constraint.elementState.valueExpression
                            )
                        )
        of AlgebraicType:
            # Create fresh AlgebraicConstraint with deep copy of the expression (constructor sets cost: 0)
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: AlgebraicType,
                algebraicState: newAlgebraicConstraintState[T](
                    constraint.algebraicState.constraint.deepCopy()
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
                    # Deep copy expressions to ensure independence
                    var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.orderingState.expressions.len)
                    for i, expr in constraint.orderingState.expressions:
                        copiedExpressions[i] = expr.deepCopy()
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: OrderingType,
                        orderingState: OrderingConstraint[T](
                            orderingType: constraint.orderingState.orderingType,
                            currentAssignment: constraint.orderingState.currentAssignment,
                            cost: constraint.orderingState.cost,
                            evalMethod: ExpressionBased,
                            expressions: copiedExpressions,
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
                            # Deep copy expressions to ensure independence
                            var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.globalCardinalityState.expressions.len)
                            for i, expr in constraint.globalCardinalityState.expressions:
                                copiedExpressions[i] = expr.deepCopy()
                            result = StatefulConstraint[T](
                                positions: constraint.positions,
                                stateType: GlobalCardinalityType,
                                globalCardinalityState: GlobalCardinalityConstraint[T](
                                    currentAssignment: constraint.globalCardinalityState.currentAssignment,
                                    countTable: constraint.globalCardinalityState.countTable,
                                    cover: constraint.globalCardinalityState.cover,
                                    cost: constraint.globalCardinalityState.cost,
                                    evalMethod: ExpressionBased,
                                    expressions: copiedExpressions,
                                    expressionsAtPosition: constraint.globalCardinalityState.expressionsAtPosition,
                                    constraintType: ExactCounts,
                                    targetCounts: constraint.globalCardinalityState.targetCounts
                                )
                            )
                        of BoundedCounts:
                            # Deep copy expressions to ensure independence
                            var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.globalCardinalityState.expressions.len)
                            for i, expr in constraint.globalCardinalityState.expressions:
                                copiedExpressions[i] = expr.deepCopy()
                            result = StatefulConstraint[T](
                                positions: constraint.positions,
                                stateType: GlobalCardinalityType,
                                globalCardinalityState: GlobalCardinalityConstraint[T](
                                    currentAssignment: constraint.globalCardinalityState.currentAssignment,
                                    countTable: constraint.globalCardinalityState.countTable,
                                    cover: constraint.globalCardinalityState.cover,
                                    cost: constraint.globalCardinalityState.cost,
                                    evalMethod: ExpressionBased,
                                    expressions: copiedExpressions,
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
                    # Deep copy expressions to ensure independence
                    var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.multiknapsackState.expressions.len)
                    for i, expr in constraint.multiknapsackState.expressions:
                        copiedExpressions[i] = expr.deepCopy()
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
                            expressions: copiedExpressions,
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
                    # Deep copy expressions to ensure independence
                    var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.sequenceState.expressions.len)
                    for i, expr in constraint.sequenceState.expressions:
                        copiedExpressions[i] = expr.deepCopy()
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
                            expressions: copiedExpressions,
                            expressionsAtPosition: constraint.sequenceState.expressionsAtPosition
                        )
                    )
        of CumulativeType:
            # Create deep copy preserving all runtime state
            case constraint.cumulativeState.evalMethod:
                of PositionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: CumulativeType,
                        cumulativeState: CumulativeConstraint[T](
                            currentAssignment: constraint.cumulativeState.currentAssignment,
                            resourceProfile: constraint.cumulativeState.resourceProfile,
                            cost: constraint.cumulativeState.cost,
                            limit: constraint.cumulativeState.limit,
                            maxTime: constraint.cumulativeState.maxTime,
                            lastChangedPosition: constraint.cumulativeState.lastChangedPosition,
                            lastOldValue: constraint.cumulativeState.lastOldValue,
                            evalMethod: PositionBased,
                            originPositions: constraint.cumulativeState.originPositions,
                            durations: constraint.cumulativeState.durations,
                            heights: constraint.cumulativeState.heights,
                            positionToTask: constraint.cumulativeState.positionToTask
                        )
                    )
                of ExpressionBased:
                    # Deep copy expressions to ensure independence
                    var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.cumulativeState.originExpressions.len)
                    for i, expr in constraint.cumulativeState.originExpressions:
                        copiedExpressions[i] = expr.deepCopy()
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: CumulativeType,
                        cumulativeState: CumulativeConstraint[T](
                            currentAssignment: constraint.cumulativeState.currentAssignment,
                            resourceProfile: constraint.cumulativeState.resourceProfile,
                            cost: constraint.cumulativeState.cost,
                            limit: constraint.cumulativeState.limit,
                            maxTime: constraint.cumulativeState.maxTime,
                            lastChangedPosition: constraint.cumulativeState.lastChangedPosition,
                            lastOldValue: constraint.cumulativeState.lastOldValue,
                            evalMethod: ExpressionBased,
                            originExpressions: copiedExpressions,
                            durationsExpr: constraint.cumulativeState.durationsExpr,
                            heightsExpr: constraint.cumulativeState.heightsExpr,
                            expressionsAtPosition: constraint.cumulativeState.expressionsAtPosition
                        )
                    )
        of BooleanType:
            # Create deep copy of boolean constraint with deep copied children
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: BooleanType,
                booleanState: constraint.booleanState.deepCopy()
            )
        of GeostType:
            # Create deep copy of geost constraint
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: GeostType,
                geostState: constraint.geostState.deepCopy()
            )
        of IrdcsType:
            # Create deep copy of IRDCS constraint
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: IrdcsType,
                irdcsState: constraint.irdcsState.deepCopy()
            )
        of CircuitType:
            # Create deep copy of Circuit constraint
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: CircuitType,
                circuitState: constraint.circuitState.deepCopy()
            )
        of AllDifferentExcept0Type:
            case constraint.allDifferentExcept0State.evalMethod:
                of PositionBased:
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: AllDifferentExcept0Type,
                        allDifferentExcept0State: newAllDifferentExcept0Constraint[T](constraint.positions.toSeq())
                    )
                of ExpressionBased:
                    var copiedExpressions = newSeq[AlgebraicExpression[T]](constraint.allDifferentExcept0State.expressions.len)
                    for i, expr in constraint.allDifferentExcept0State.expressions:
                        copiedExpressions[i] = expr.deepCopy()
                    result = StatefulConstraint[T](
                        positions: constraint.positions,
                        stateType: AllDifferentExcept0Type,
                        allDifferentExcept0State: newAllDifferentExcept0Constraint[T](copiedExpressions)
                    )
        of LexOrderType:
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: LexOrderType,
                lexOrderState: newLexOrderConstraint[T](
                    constraint.lexOrderState.leftPositions,
                    constraint.lexOrderState.rightPositions,
                    constraint.lexOrderState.lexType
                )
            )
        of TableConstraintType:
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: TableConstraintType,
                tableConstraintState: newTableConstraint[T](
                    constraint.tableConstraintState.sortedPositions,
                    constraint.tableConstraintState.tuples,
                    constraint.tableConstraintState.mode
                )
            )
        of RegularType:
            result = StatefulConstraint[T](
                positions: constraint.positions,
                stateType: RegularType,
                regularState: newRegularConstraint[T](
                    constraint.regularState.sortedPositions,
                    constraint.regularState.nStates,
                    constraint.regularState.inputMin,
                    constraint.regularState.inputMax,
                    constraint.regularState.transition,
                    constraint.regularState.initialState,
                    constraint.regularState.finalStates.toSeq()
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

################################################################################
# Cumulative wrapper functions
################################################################################

func cumulative*[T](originPositions: openArray[int], durations: openArray[T], heights: openArray[T], limit: T): StatefulConstraint[T] =
    ## Creates a cumulative constraint for resource-constrained scheduling.
    ## - originPositions: Variable positions representing task start times
    ## - durations: Duration of each task (constant)
    ## - heights: Resource consumption of each task (constant)
    ## - limit: Maximum resource capacity
    ## Example: cumulative([0,1,2,3,4], [3,9,10,6,2], [1,2,1,1,3], 8) for project scheduling
    return StatefulConstraint[T](
        positions: toPackedSet[int](originPositions),
        stateType: CumulativeType,
        cumulativeState: newCumulativeConstraint[T](originPositions, durations, heights, limit)
    )

func cumulative*[T](originExpressions: seq[AlgebraicExpression[T]], durations: openArray[T], heights: openArray[T], limit: T): StatefulConstraint[T] =
    ## Returns cumulative constraint for the given origin expressions.
    let (allRefs, positions) = isAllRefs(originExpressions)

    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return cumulative[T](positions, durations, heights, limit)
    else:
        # Collect all positions from expressions for the constraint positions field
        var allPositions = toPackedSet[int]([])
        for exp in originExpressions:
            allPositions.incl(exp.positions)

        return StatefulConstraint[T](
            positions: allPositions,
            stateType: CumulativeType,
            cumulativeState: newCumulativeConstraint[T](originExpressions, durations, heights, limit)
        )

################################################################################
# Geost wrapper functions
################################################################################

func geost*[T](placementPositions: seq[int], cellsByPlacement: seq[seq[seq[int]]]): StatefulConstraint[T] =
    ## Creates a geost constraint for geometric non-overlap in placement problems.
    ## This is a local-search optimized implementation of the classic geost constraint.
    ##
    ## - placementPositions: Variable positions representing placement choice for each object
    ## - cellsByPlacement: cellsByPlacement[objectIdx][placementIdx] = cells covered by that placement
    ##
    ## Each object selects a placement from its domain, and the constraint ensures no two
    ## objects cover the same cell. Shapes are defined by cell lists (discrete grid cells)
    ## rather than shifted boxes.
    ##
    ## See: https://sofdem.github.io/gccat/gccat/Cgeost.html
    ##
    ## Example: For a puzzle with 5 pieces where each piece can be placed in various positions:
    ##   geost[int](@[0,1,2,3,4], cellsByPlacement)
    let geostConstraint = newGeostConstraint[T](placementPositions, cellsByPlacement)
    return StatefulConstraint[T](
        positions: geostConstraint.positions,
        stateType: GeostType,
        geostState: geostConstraint
    )

################################################################################
# IRDCS wrapper functions
################################################################################

func irdcs*[T](n: int, singletonPenalty: int = 1): StatefulConstraint[T] =
    ## Creates an IRDCS constraint for interval [1, n].
    ## An Incongruent Restricted Disjoint Covering System ensures:
    ## - Each position is assigned a modulus
    ## - All positions with the same modulus have the same residue (mod that modulus)
    ## - Each modulus used must cover at least 2 positions
    ##
    ## Variable positions are assumed to be 0 to n-1.
    ##
    ## See: "Odd Incongruent Restricted Disjoint Covering Systems" by Paul Robert Emanuel
    ## INTEGERS 12A (2012)
    let irdcsConstraint = newIrdcsConstraint[T](n, singletonPenalty)
    return StatefulConstraint[T](
        positions: irdcsConstraint.positions,
        stateType: IrdcsType,
        irdcsState: irdcsConstraint
    )

func irdcs*[T](positions: openArray[int], singletonPenalty: int = 1): StatefulConstraint[T] =
    ## Creates an IRDCS constraint for the given variable positions.
    ## The interval indices are derived from position order (first position = index 1, etc.)
    let irdcsConstraint = newIrdcsConstraint[T](positions.toSeq, singletonPenalty)
    return StatefulConstraint[T](
        positions: irdcsConstraint.positions,
        stateType: IrdcsType,
        irdcsState: irdcsConstraint
    )

################################################################################
# Circuit wrapper functions
################################################################################

func circuit*[T](positions: openArray[int]): StatefulConstraint[T] =
    ## Creates a Circuit constraint ensuring variables form a single Hamiltonian circuit.
    ## Uses 1-based convention: value j at position i means "from node i, go to node j."
    ##
    ## **Mathematical Form**: The successor function defined by the variables forms exactly
    ## one cycle visiting all n nodes.
    ##
    ## **Parameters**:
    ## - `positions`: Variable positions that define the successor function
    ##
    ## **Note**: Does NOT enforce allDifferent. Add both constraints:
    ##   sys.addConstraint(allDifferent(x))
    ##   sys.addConstraint(circuit(x))
    ##
    ## **Violation Cost**: max(0, numCycles - 1) + numTailNodes
    let circuitConstraint = newCircuitConstraint[T](positions)
    return StatefulConstraint[T](
        positions: circuitConstraint.positions,
        stateType: CircuitType,
        circuitState: circuitConstraint
    )

################################################################################
# AllDifferentExcept0 wrapper functions
################################################################################

func allDifferentExcept0*[T](positions: openArray[int]): StatefulConstraint[T] =
    ## Creates an AllDifferentExcept0 constraint ensuring all non-zero variables have distinct values.
    ## Zero values are ignored (any number of variables can be 0).
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AllDifferentExcept0Type,
        allDifferentExcept0State: newAllDifferentExcept0Constraint[T](positions)
    )

func allDifferentExcept0*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates an AllDifferentExcept0 constraint for algebraic expressions.
    let (allRefs, positions) = isAllRefs(expressions)
    if allRefs:
        return allDifferentExcept0[T](positions)
    else:
        var allPositions = toPackedSet[int]([])
        for exp in expressions:
            allPositions.incl(exp.positions)
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: AllDifferentExcept0Type,
            allDifferentExcept0State: newAllDifferentExcept0Constraint[T](expressions)
        )

################################################################################
# LexOrder wrapper functions
################################################################################

func lexLt*[T](leftPositions, rightPositions: openArray[int]): StatefulConstraint[T] =
    ## Creates a strict lexicographic ordering constraint: L < R
    let constraint = newLexOrderConstraint[T](leftPositions, rightPositions, Strict)
    return StatefulConstraint[T](
        positions: constraint.positions,
        stateType: LexOrderType,
        lexOrderState: constraint
    )

func lexLe*[T](leftPositions, rightPositions: openArray[int]): StatefulConstraint[T] =
    ## Creates a non-strict lexicographic ordering constraint: L <= R
    let constraint = newLexOrderConstraint[T](leftPositions, rightPositions, NonStrict)
    return StatefulConstraint[T](
        positions: constraint.positions,
        stateType: LexOrderType,
        lexOrderState: constraint
    )

func lexLt*[T](leftExprs, rightExprs: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates a strict lexicographic ordering constraint for expressions.
    let (allRefsL, positionsL) = isAllRefs(leftExprs)
    let (allRefsR, positionsR) = isAllRefs(rightExprs)
    if allRefsL and allRefsR:
        return lexLt[T](positionsL, positionsR)
    else:
        # Fall back to position-based using expression positions
        # For now, require ref nodes for lex ordering
        assert allRefsL and allRefsR, "lexLt currently requires simple variable references"
        return lexLt[T](positionsL, positionsR)

func lexLe*[T](leftExprs, rightExprs: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    ## Creates a non-strict lexicographic ordering constraint for expressions.
    let (allRefsL, positionsL) = isAllRefs(leftExprs)
    let (allRefsR, positionsR) = isAllRefs(rightExprs)
    if allRefsL and allRefsR:
        return lexLe[T](positionsL, positionsR)
    else:
        assert allRefsL and allRefsR, "lexLe currently requires simple variable references"
        return lexLe[T](positionsL, positionsR)

################################################################################
# Table constraint wrapper functions
################################################################################

func tableIn*[T](positions: openArray[int], tuples: seq[seq[T]]): StatefulConstraint[T] =
    ## Creates a table-in constraint: variable tuple must match one of the allowed tuples.
    let constraint = newTableConstraint[T](positions, tuples, TableIn)
    return StatefulConstraint[T](
        positions: constraint.positions,
        stateType: TableConstraintType,
        tableConstraintState: constraint
    )

func tableNotIn*[T](positions: openArray[int], tuples: seq[seq[T]]): StatefulConstraint[T] =
    ## Creates a table-not-in constraint: variable tuple must NOT match any forbidden tuple.
    let constraint = newTableConstraint[T](positions, tuples, TableNotIn)
    return StatefulConstraint[T](
        positions: constraint.positions,
        stateType: TableConstraintType,
        tableConstraintState: constraint
    )

func tableIn*[T](expressions: seq[AlgebraicExpression[T]], tuples: seq[seq[T]]): StatefulConstraint[T] =
    ## Creates a table-in constraint for expressions.
    let (allRefs, positions) = isAllRefs(expressions)
    if allRefs:
        return tableIn[T](positions, tuples)
    else:
        assert allRefs, "tableIn currently requires simple variable references"
        return tableIn[T](positions, tuples)

func tableNotIn*[T](expressions: seq[AlgebraicExpression[T]], tuples: seq[seq[T]]): StatefulConstraint[T] =
    ## Creates a table-not-in constraint for expressions.
    let (allRefs, positions) = isAllRefs(expressions)
    if allRefs:
        return tableNotIn[T](positions, tuples)
    else:
        assert allRefs, "tableNotIn currently requires simple variable references"
        return tableNotIn[T](positions, tuples)

################################################################################
# Regular constraint wrapper functions
################################################################################

func regular*[T](positions: openArray[int], nStates: int, inputMin, inputMax: T,
                  transition: seq[seq[int]], initialState: int,
                  finalStates: openArray[int]): StatefulConstraint[T] =
    ## Creates a regular constraint: sequence of variables must be accepted by a DFA.
    let constraint = newRegularConstraint[T](positions, nStates, inputMin, inputMax,
                                              transition, initialState, finalStates)
    return StatefulConstraint[T](
        positions: constraint.positions,
        stateType: RegularType,
        regularState: constraint
    )

func regular*[T](expressions: seq[AlgebraicExpression[T]], nStates: int, inputMin, inputMax: T,
                  transition: seq[seq[int]], initialState: int,
                  finalStates: openArray[int]): StatefulConstraint[T] =
    ## Creates a regular constraint for expressions.
    let (allRefs, positions) = isAllRefs(expressions)
    if allRefs:
        return regular[T](positions, nStates, inputMin, inputMax, transition, initialState, finalStates)
    else:
        assert allRefs, "regular currently requires simple variable references"
        return regular[T](positions, nStates, inputMin, inputMax, transition, initialState, finalStates)

################################################################################
# Boolean Operators for StatefulConstraint
################################################################################

template StatefulBooleanOp(op, opEnum: untyped) =
    func `op`*[T](left, right: StatefulConstraint[T]): StatefulConstraint[T] =
        ## Creates a boolean constraint combining two stateful constraints
        StatefulConstraint[T](
            positions: left.positions + right.positions,
            stateType: BooleanType,
            booleanState: newBooleanConstraint[T](left, right, opEnum)
        )

StatefulBooleanOp(`and`, And)
StatefulBooleanOp(`or`, Or)
StatefulBooleanOp(`xor`, Xor)
StatefulBooleanOp(`implies`, Implies)
StatefulBooleanOp(`iff`, Iff)

# More intuitive syntax for implies and iff
StatefulBooleanOp(`->`, Implies)   # Implies operator: A -> B means "if A then B"
StatefulBooleanOp(`<->`, Iff)      # If-and-only-if operator: A <-> B means "A iff B"

# NOT operator for StatefulConstraint
func `not`*[T](constraint: StatefulConstraint[T]): StatefulConstraint[T] =
    ## Creates a boolean NOT constraint for a stateful constraint
    StatefulConstraint[T](
        positions: constraint.positions,
        stateType: BooleanType,
        booleanState: newUnaryBooleanConstraint[T](constraint, Not)
    )

################################################################################
# AlgebraicConstraint to StatefulConstraint Conversion
################################################################################

func toStateful*[T](constraint: AlgebraicConstraint[T]): StatefulConstraint[T] =
    ## Converts an AlgebraicConstraint to a StatefulConstraint
    ## This enables mixing algebraic and stateful constraints in boolean operations
    StatefulConstraint[T](
        positions: constraint.positions,
        stateType: AlgebraicType,
        algebraicState: newAlgebraicConstraintState(constraint)
    )

################################################################################
# Mixed Constraint Type Boolean Operators
################################################################################

template MixedBooleanOp(op, opEnum: untyped) =
    # StatefulConstraint op AlgebraicConstraint
    func `op`*[T](left: StatefulConstraint[T], right: AlgebraicConstraint[T]): StatefulConstraint[T] =
        ## Boolean operator with automatic conversion of AlgebraicConstraint to StatefulConstraint
        StatefulConstraint[T](
            positions: left.positions + right.positions,
            stateType: BooleanType,
            booleanState: newBooleanConstraint[T](left, right.toStateful(), opEnum)
        )

    # AlgebraicConstraint op StatefulConstraint
    func `op`*[T](left: AlgebraicConstraint[T], right: StatefulConstraint[T]): StatefulConstraint[T] =
        ## Boolean operator with automatic conversion of AlgebraicConstraint to StatefulConstraint
        StatefulConstraint[T](
            positions: left.positions + right.positions,
            stateType: BooleanType,
            booleanState: newBooleanConstraint[T](left.toStateful(), right, opEnum)
        )

MixedBooleanOp(`and`, And)
MixedBooleanOp(`or`, Or)
MixedBooleanOp(`xor`, Xor)
MixedBooleanOp(`implies`, Implies)
MixedBooleanOp(`iff`, Iff)

# More intuitive syntax for implies and iff with mixed types
MixedBooleanOp(`->`, Implies)   # Implies operator: A -> B means "if A then B"
MixedBooleanOp(`<->`, Iff)      # If-and-only-if operator: A <-> B means "A iff B"
