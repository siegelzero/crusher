import ../expressions/expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    SumExpressionConstraint*[T] = ref object
        sumExpr: SumExpression[T]
        relation*: BinaryRelation
        target*: T
        cost*: int

################################################################################
# SumExpressionConstraint creation
################################################################################

func init*[T](state: SumExpressionConstraint[T],
              sumExpr: SumExpression[T],
              relation: BinaryRelation,
              target: T) =
    state.cost = 0
    state.sumExpr = sumExpr
    state.relation = relation
    state.target = target


func newSumExpressionConstraint*[T](sumExpr: SumExpression[T],
                                    relation: BinaryRelation,
                                    target: T): SumExpressionConstraint[T] =
    new(result)
    result.init(sumExpr, relation, target)

################################################################################
# LinearCombinationState initialization and updates
################################################################################

func initialize*[T](state: SumExpressionConstraint[T], assignment: seq[T]) =
    state.sumExpr.initialize(assignment)
    state.cost = state.relation.penalty(state.sumExpr.value, state.target)


func updatePosition*[T](state: SumExpressionConstraint[T], position: int, newValue: T) {.inline.} =
    state.sumExpr.updatePosition(position, newValue)
    state.cost = state.relation.penalty(state.sumExpr.value, state.target)


proc moveDelta*[T](state: SumExpressionConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let delta = state.sumExpr.moveDelta(position, oldValue, newValue)
    return state.relation.penalty(state.sumExpr.value + delta, state.target)
