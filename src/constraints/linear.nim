import std/tables

import ../expressions
import ../utils
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    LinearConstraint*[T] = ref object
        lincomb: LinearCombination[T]
        relation*: BinaryRelation
        target*: T
        cost*: int

################################################################################
# LinearConstraint Creation
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
# LinearCombinationState Initialization
################################################################################

func computeCost(left, right: int, relation: BinaryRelation): int =
    case relation:
        of EqualTo:
            return if left == right: 0 else: 1
        of NotEqualTo:
            return if left != right: 0 else: 1
        of GreaterThan:
            return if left > right: 0 else: 1
        of GreaterThanEq:
            return if left >= right: 0 else: 1
        of LessThan:
            return if left < right: 0 else: 1
        of LessThanEq:
            return if left <= right: 0 else: 1
        of CommonFactor:
            return if gcd(left, right) > 1: 0 else: 1


func initialize*[T](state: LinearConstraint[T], assignment: seq[T]) =
    state.lincomb.initialize(assignment)
    state.cost = computeCost(state.lincomb.value, state.target, state.relation)

################################################################################
# LinearCombinationState Updates
################################################################################

func updatePosition*[T](state: LinearConstraint[T], position: int, newValue: T) {.inline.} =
    state.lincomb.updatePosition(position, newValue)
    state.cost = computeCost(state.lincomb.value, state.target, state.relation)


proc moveDelta*[T](state: LinearConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let delta = state.lincomb.coefficient[position]*(newValue - oldValue)
    return computeCost(state.lincomb.value + delta, state.target, state.relation)