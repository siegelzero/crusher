import std/[tables, sets, packedsets]
import ../expressions/expressions
import ../expressions/stateful
import constraintNode

################################################################################
# RelationalConstraint - Unified constraint for expression relations
################################################################################

type
    RelationalConstraint*[T] = ref object
        leftExpr*: Expression[T]               # Any expression type
        rightExpr*: Expression[T]              # Any expression type
        relation*: BinaryRelation              # Reuse existing ==, !=, <, <=, >, >=
        cost*: int                             # Cache current penalty
        positions*: PackedSet[int]         # Union of left + right positions
        # Cache for expression values
        leftValue*: T
        rightValue*: T
        # Track which positions were affected by last updatePosition
        lastAffectedPositions*: PackedSet[int]
        lastOldLeftValue*: T
        lastOldRightValue*: T

# Create a new RelationalConstraint with Expression wrappers
func newRelationalConstraint*[T](leftExpr, rightExpr: Expression[T],
                                  relation: BinaryRelation): RelationalConstraint[T] =
    result = RelationalConstraint[T](
        leftExpr: leftExpr,
        rightExpr: rightExpr,
        relation: relation,
        cost: 0,
        positions: leftExpr.positions + rightExpr.positions
    )

# Template-based constructor that accepts any expression types
template newRelationalConstraint*[T](leftExpr, rightExpr: typed,
                                     relation: BinaryRelation): RelationalConstraint[T] =
    newRelationalConstraint(newExpression[T](leftExpr), newExpression[T](rightExpr), relation)

# Initialize the constraint with an assignment
func initialize*[T](constraint: RelationalConstraint[T], assignment: seq[T]) =
    # Initialize both expressions
    constraint.leftExpr.initialize(assignment)
    constraint.rightExpr.initialize(assignment)

    # Cache values
    constraint.leftValue = constraint.leftExpr.getValue()
    constraint.rightValue = constraint.rightExpr.getValue()

    # Calculate initial cost
    constraint.cost = constraint.relation.penalty(constraint.leftValue, constraint.rightValue)

# Calculate the change in penalty for a position change
func moveDelta*[T](constraint: RelationalConstraint[T],
                   position: int, oldValue, newValue: T): int =
    # Early exit if position doesn't affect this constraint
    if position notin constraint.positions:
        return 0

    # Calculate deltas incrementally for affected expressions only
    var newLeftValue = constraint.leftValue
    var newRightValue = constraint.rightValue

    if position in constraint.leftExpr.positions:
        let leftDelta = constraint.leftExpr.moveDelta(position, oldValue, newValue)
        newLeftValue = constraint.leftValue + leftDelta

    if position in constraint.rightExpr.positions:
        let rightDelta = constraint.rightExpr.moveDelta(position, oldValue, newValue)
        newRightValue = constraint.rightValue + rightDelta

    # Return the change in penalty
    let newCost = constraint.relation.penalty(newLeftValue, newRightValue)
    return newCost - constraint.cost

# Update a position with a new value
func updatePosition*[T](constraint: RelationalConstraint[T],
                        position: int, newValue: T) =
    # Save old values for getAffectedPositions/getAffectedDomainValues
    constraint.lastOldLeftValue = constraint.leftValue
    constraint.lastOldRightValue = constraint.rightValue

    # Update expressions incrementally and get their new values directly
    # The expressions maintain their own values, so we don't need getValue()

    if position in constraint.leftExpr.positions:
        constraint.leftExpr.updatePosition(position, newValue)
        # Expression already updated its internal value during updatePosition
        constraint.leftValue = constraint.leftExpr.getValue()

    if position in constraint.rightExpr.positions:
        constraint.rightExpr.updatePosition(position, newValue)
        # Expression already updated its internal value during updatePosition
        constraint.rightValue = constraint.rightExpr.getValue()

    # Update cost based on new cached values
    constraint.cost = constraint.relation.penalty(constraint.leftValue, constraint.rightValue)

    # Track affected positions: only positions in expressions whose values changed
    constraint.lastAffectedPositions = initPackedSet[int]()
    if constraint.leftValue != constraint.lastOldLeftValue:
        constraint.lastAffectedPositions.incl(constraint.leftExpr.positions)
    if constraint.rightValue != constraint.lastOldRightValue:
        constraint.lastAffectedPositions.incl(constraint.rightExpr.positions)

# Get the current penalty
func penalty*[T](constraint: RelationalConstraint[T]): int =
    return constraint.cost

func getAffectedPositions*[T](constraint: RelationalConstraint[T]): PackedSet[int] =
    ## Returns positions affected by the last updatePosition call.
    ## Only includes positions of expressions whose values actually changed.
    return constraint.lastAffectedPositions

func getAffectedDomainValues*[T](constraint: RelationalConstraint[T], position: int): seq[T] =
    ## Returns empty (all values need recalculation) since expression-based
    ## constraints can have complex dependencies.
    return @[]

proc batchMovePenalty*[T](constraint: RelationalConstraint[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
    ## Compute penalty for ALL domain values at a position in a tight loop.
    ## For linear expressions (SumExpr/ConstantExpr), avoids per-value function call overhead.
    result = newSeq[int](domain.len)

    # Extract left coefficient for this position
    var leftCoeff: T = 0
    var leftOk = true
    case constraint.leftExpr.kind
    of SumExpr:
        let s = constraint.leftExpr.sumExpr
        if s.evalMethod == PositionBased:
            leftCoeff = s.coefficient.getOrDefault(position, T(0))
        else:
            leftOk = false
    of ConstantExpr:
        leftCoeff = 0
    else:
        leftOk = false

    # Extract right coefficient for this position
    var rightCoeff: T = 0
    var rightOk = true
    case constraint.rightExpr.kind
    of SumExpr:
        let s = constraint.rightExpr.sumExpr
        if s.evalMethod == PositionBased:
            rightCoeff = s.coefficient.getOrDefault(position, T(0))
        else:
            rightOk = false
    of ConstantExpr:
        rightCoeff = 0
    else:
        rightOk = false

    if leftOk and rightOk:
        # Batch evaluation: compute base values (with position contribution removed)
        let leftBase = constraint.leftValue - leftCoeff * currentValue
        let rightBase = constraint.rightValue - rightCoeff * currentValue
        let rel = constraint.relation
        let currentCost = constraint.cost

        for i in 0..<domain.len:
            let v = domain[i]
            let left = leftBase + leftCoeff * v
            let right = rightBase + rightCoeff * v
            result[i] = int(rel.penalty(left, right)) - currentCost
    else:
        # Fallback: individual computation
        for i, v in domain:
            result[i] = constraint.moveDelta(position, currentValue, v)
