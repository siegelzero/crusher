import ../expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    SumConstraint*[T] = ref object
        sumExpr*: SumExpression[T]
        relation*: BinaryRelation
        target*: T
        cost*: int

################################################################################
# SumConstraint creation
################################################################################

func init*[T](state: SumConstraint[T],
              sumExpr: SumExpression[T],
              relation: BinaryRelation,
              target: T) =
    state.cost = 0
    state.sumExpr = sumExpr
    state.relation = relation
    state.target = target

func newSumConstraint*[T](sumExpr: SumExpression[T],
                          relation: BinaryRelation,
                          target: T): SumConstraint[T] =
    new(result)
    result.init(sumExpr, relation, target)

################################################################################
# SumConstraint initialization and updates
################################################################################

func initialize*[T](state: SumConstraint[T], assignment: seq[T]) =
    state.sumExpr.initialize(assignment)
    state.cost = state.relation.penalty(state.sumExpr.value, state.target)

func updatePosition*[T](state: SumConstraint[T], position: int, newValue: T) {.inline.} =
    state.sumExpr.updatePosition(position, newValue)
    state.cost = state.relation.penalty(state.sumExpr.value, state.target)

proc moveDelta*[T](state: SumConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let sumDelta = state.sumExpr.moveDelta(position, oldValue, newValue)
    let newSumValue = state.sumExpr.value + sumDelta
    let newCost = int(state.relation.penalty(newSumValue, state.target))
    return newCost - oldCost