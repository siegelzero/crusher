import ../expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    LinearConstraint*[T] = ref object
        lincomb*: LinearCombination[T]
        relation*: BinaryRelation
        target*: T
        cost*: int

################################################################################
# LinearConstraint creation
################################################################################

func init*[T](state: LinearConstraint[T],
              lincomb: LinearCombination[T],
              relation: BinaryRelation,
              target: T) =
    state.cost = 0
    state.lincomb = lincomb
    state.relation = relation
    state.target = target


func newLinearConstraint*[T](lincomb: LinearCombination[T],
                             relation: BinaryRelation,
                             target: T): LinearConstraint[T] =
    new(result)
    result.init(lincomb, relation, target)

################################################################################
# LinearCombinationState initialization and updates
################################################################################

func initialize*[T](state: LinearConstraint[T], assignment: seq[T]) =
    state.lincomb.initialize(assignment)
    state.cost = state.relation.penalty(state.lincomb.value, state.target)


func updatePosition*[T](state: LinearConstraint[T], position: int, newValue: T) {.inline.} =
    state.lincomb.updatePosition(position, newValue)
    state.cost = state.relation.penalty(state.lincomb.value, state.target)


proc moveDelta*[T](state: LinearConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let delta = state.lincomb.moveDelta(position, oldValue, newValue)
    return state.relation.penalty(state.lincomb.value + delta, state.target)
