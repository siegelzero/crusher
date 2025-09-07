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
        positions*: PackedSet[Natural]         # Union of left + right positions
        # Cache for expression values
        leftValue*: T
        rightValue*: T

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
    newRelationalConstraint(wrap[T](leftExpr), wrap[T](rightExpr), relation)

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
                   position: Natural, oldValue, newValue: T): int =
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
                        position: Natural, newValue: T) =
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

# Get the current penalty
func penalty*[T](constraint: RelationalConstraint[T]): int =
    return constraint.cost