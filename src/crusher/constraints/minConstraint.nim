import ../expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    MinConstraintType* = enum
        ConstantTarget,
        VariableTarget
        
    MinConstraint*[T] = ref object
        minExpr*: MinExpression[T]
        relation*: BinaryRelation
        cost*: int
        case constraintType*: MinConstraintType
        of ConstantTarget:
            target*: T
        of VariableTarget:
            targetPosition*: int
            targetValue*: T  # Cache of the current target value

################################################################################
# MinConstraint creation
################################################################################

func newMinConstraint*[T](minExpr: MinExpression[T],
                          relation: BinaryRelation,
                          target: T): MinConstraint[T] =
    result = MinConstraint[T](
        minExpr: minExpr,
        relation: relation,
        cost: 0,
        constraintType: ConstantTarget,
        target: target
    )

func newMinConstraintWithVariableTarget*[T](minExpr: MinExpression[T],
                          relation: BinaryRelation,
                          targetPosition: int): MinConstraint[T] =
    result = MinConstraint[T](
        minExpr: minExpr,
        relation: relation,
        cost: 0,
        constraintType: VariableTarget,
        targetPosition: targetPosition,
        targetValue: default(T)  # Will be set during initialize
    )

################################################################################
# MinConstraint initialization and updates
################################################################################

func initialize*[T](state: MinConstraint[T], assignment: seq[T]) =
    state.minExpr.initialize(assignment)
    case state.constraintType:
    of ConstantTarget:
        state.cost = state.relation.penalty(state.minExpr.value, state.target)
    of VariableTarget:
        state.targetValue = assignment[state.targetPosition]
        state.cost = state.relation.penalty(state.minExpr.value, state.targetValue)

func updatePosition*[T](state: MinConstraint[T], position: int, newValue: T, assignment: seq[T]) {.inline.} =
    state.minExpr.updatePosition(position, newValue)
    case state.constraintType:
    of ConstantTarget:
        state.cost = state.relation.penalty(state.minExpr.value, state.target)
    of VariableTarget:
        let targetValue = assignment[state.targetPosition]
        state.cost = state.relation.penalty(state.minExpr.value, targetValue)

# Keep the old signature for backward compatibility with constant targets
func updatePosition*[T](state: MinConstraint[T], position: int, newValue: T) {.inline.} =
    case state.constraintType:
    of ConstantTarget:
        state.minExpr.updatePosition(position, newValue)
        state.cost = state.relation.penalty(state.minExpr.value, state.target)
    of VariableTarget:
        # Update the min expression
        state.minExpr.updatePosition(position, newValue)
        
        # Update target value if the target position changed
        if position == state.targetPosition:
            state.targetValue = newValue
            
        # Recalculate cost with current target value
        state.cost = state.relation.penalty(state.minExpr.value, state.targetValue)

proc moveDelta*[T](state: MinConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let minDelta = state.minExpr.moveDelta(position, oldValue, newValue)
    let newMinValue = state.minExpr.value + minDelta
    
    case state.constraintType:
    of ConstantTarget:
        let newCost = int(state.relation.penalty(newMinValue, state.target))
        return newCost - oldCost
    of VariableTarget:
        # Handle case where target variable itself is changing
        let targetValue = if position == state.targetPosition: newValue else: state.targetValue
        let newCost = int(state.relation.penalty(newMinValue, targetValue))
        return newCost - oldCost

################################################################################
# MinExpression creation helpers for constraint syntax
################################################################################

func min*[T](expressions: seq[AlgebraicExpression[T]]): MinExpression[T] =
    # Check if all expressions are simple variable references (RefNodes)
    var allRefs = true
    var positions: seq[int] = @[]
    
    for exp in expressions:
        if exp.node.kind == RefNode:
            positions.add(exp.node.position)
        else:
            allRefs = false
    
    if allRefs:
        # Use efficient position-based approach if all expressions are simple variables
        return newMinExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newMinExpression[T](expressions)

# MinExpression operators are now defined in stateful.nim to create StatefulConstraints