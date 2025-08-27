import ../expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    MinConstraint*[T] = ref object
        minExpr*: MinExpression[T]
        relation*: BinaryRelation
        target*: T
        cost*: int

################################################################################
# MinConstraint creation
################################################################################

func init*[T](state: MinConstraint[T],
              minExpr: MinExpression[T],
              relation: BinaryRelation,
              target: T) =
    state.cost = 0
    state.minExpr = minExpr
    state.relation = relation
    state.target = target

func newMinConstraint*[T](minExpr: MinExpression[T],
                          relation: BinaryRelation,
                          target: T): MinConstraint[T] =
    new(result)
    result.init(minExpr, relation, target)

################################################################################
# MinConstraint initialization and updates
################################################################################

func initialize*[T](state: MinConstraint[T], assignment: seq[T]) =
    state.minExpr.initialize(assignment)
    state.cost = state.relation.penalty(state.minExpr.value, state.target)

func updatePosition*[T](state: MinConstraint[T], position: int, newValue: T) {.inline.} =
    state.minExpr.updatePosition(position, newValue)
    state.cost = state.relation.penalty(state.minExpr.value, state.target)

proc moveDelta*[T](state: MinConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let minDelta = state.minExpr.moveDelta(position, oldValue, newValue)
    let newMinValue = state.minExpr.value + minDelta
    let newCost = int(state.relation.penalty(newMinValue, state.target))
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