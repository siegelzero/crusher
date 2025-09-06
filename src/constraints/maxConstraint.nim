import constraintNode
import ../expressions/maxExpression
import ../expressions/algebraic

################################################################################
# Type definitions
################################################################################

type
    MaxConstraintType* = enum
        ConstantTarget,
        VariableTarget

    MaxConstraint*[T] = ref object
        maxExpr*: MaxExpression[T]
        relation*: BinaryRelation
        cost*: int
        case constraintType*: MaxConstraintType
        of ConstantTarget:
            target*: T
        of VariableTarget:
            targetPosition*: int
            targetValue*: T  # Cache of the current target value

################################################################################
# MaxConstraint creation
################################################################################

func newMaxConstraint*[T](maxExpr: MaxExpression[T],
                          relation: BinaryRelation,
                          target: T): MaxConstraint[T] =
    result = MaxConstraint[T](
        maxExpr: maxExpr,
        relation: relation,
        cost: 0,
        constraintType: ConstantTarget,
        target: target
    )

func newMaxConstraintWithVariableTarget*[T](maxExpr: MaxExpression[T],
                          relation: BinaryRelation,
                          targetPosition: int): MaxConstraint[T] =
    result = MaxConstraint[T](
        maxExpr: maxExpr,
        relation: relation,
        cost: 0,
        constraintType: VariableTarget,
        targetPosition: targetPosition,
        targetValue: default(T)  # Will be set during initialize
    )

################################################################################
# MaxConstraint initialization and updates
################################################################################

func initialize*[T](state: MaxConstraint[T], assignment: seq[T]) =
    state.maxExpr.initialize(assignment)
    case state.constraintType:
    of ConstantTarget:
        state.cost = state.relation.penalty(state.maxExpr.value, state.target)
    of VariableTarget:
        state.targetValue = assignment[state.targetPosition]
        state.cost = state.relation.penalty(state.maxExpr.value, state.targetValue)

func updatePosition*[T](state: MaxConstraint[T], position: Natural, newValue: T) {.inline.} =
    case state.constraintType:
    of ConstantTarget:
        state.maxExpr.updatePosition(position, newValue)
        state.cost = state.relation.penalty(state.maxExpr.value, state.target)
    of VariableTarget:
        # Only update the max expression if the position is part of it
        if position in state.maxExpr.positions:
            state.maxExpr.updatePosition(position, newValue)

        # Update target value if the target position changed
        if position == state.targetPosition:
            state.targetValue = newValue

        # Recalculate cost with current target value
        state.cost = state.relation.penalty(state.maxExpr.value, state.targetValue)

func moveDelta*[T](state: MaxConstraint[T], position: Natural, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let maxDelta = state.maxExpr.moveDelta(position, oldValue, newValue)
    let newMaxValue = state.maxExpr.value + maxDelta

    case state.constraintType:
    of ConstantTarget:
        let newCost = state.relation.penalty(newMaxValue, state.target)
        return newCost - oldCost
    of VariableTarget:
        # Handle case where target variable itself is changing
        let targetValue = if position == state.targetPosition: newValue else: state.targetValue
        let newCost = state.relation.penalty(newMaxValue, targetValue)
        return newCost - oldCost

# MaxExpression operators are defined in maxExpression.nim and stateful.nim creates StatefulConstraints