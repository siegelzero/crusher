import ../expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    MaxConstraint*[T] = ref object
        maxExpr*: MaxExpression[T]
        relation*: BinaryRelation
        target*: T
        cost*: int

################################################################################
# MaxConstraint creation
################################################################################

func init*[T](state: MaxConstraint[T],
              maxExpr: MaxExpression[T],
              relation: BinaryRelation,
              target: T) =
    state.cost = 0
    state.maxExpr = maxExpr
    state.relation = relation
    state.target = target

func newMaxConstraint*[T](maxExpr: MaxExpression[T],
                          relation: BinaryRelation,
                          target: T): MaxConstraint[T] =
    new(result)
    result.init(maxExpr, relation, target)

################################################################################
# MaxConstraint initialization and updates
################################################################################

func initialize*[T](state: MaxConstraint[T], assignment: seq[T]) =
    state.maxExpr.initialize(assignment)
    state.cost = state.relation.penalty(state.maxExpr.value, state.target)

func updatePosition*[T](state: MaxConstraint[T], position: int, newValue: T) {.inline.} =
    state.maxExpr.updatePosition(position, newValue)
    state.cost = state.relation.penalty(state.maxExpr.value, state.target)

proc moveDelta*[T](state: MaxConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let maxDelta = state.maxExpr.moveDelta(position, oldValue, newValue)
    let newMaxValue = state.maxExpr.value + maxDelta
    let newCost = int(state.relation.penalty(newMaxValue, state.target))
    return newCost - oldCost

################################################################################
# MaxExpression creation helpers for constraint syntax
################################################################################

func max*[T](expressions: seq[AlgebraicExpression[T]]): MaxExpression[T] =
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
        return newMaxExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newMaxExpression[T](expressions)

# MaxExpression operators are now defined in stateful.nim to create StatefulConstraints