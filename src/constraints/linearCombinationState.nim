import std/[packedsets, tables]

import ../expressions/expression

################################################################################
# Type definitions
################################################################################

type
    NonlinearExpressionError* = object of CatchableError

    LinearCombinationState*[T] = ref object
        value*: T
        constant*: T
        positions*: PackedSet[int]
        coefficient*: Table[int, T]
        currentAssignment*: Table[int, T]

################################################################################
# LinearCombinationState Creation
################################################################################

func init*[T](state: LinearCombinationState[T], positions: seq[T]) =
    state.value = 0
    state.constant = 0
    state.positions = toPackedSet[int](positions)
    state.coefficient = initTable[int, T]()
    state.currentAssignment = initTable[int, T]()

    for pos in positions:
        state.coefficient[pos] = 1

func init*[T](state: LinearCombinationState[T], coefficients: Table[int, T], constant: T) =
    state.value = constant
    state.constant = constant
    state.positions = initPackedSet[int]()
    state.coefficient = initTable[int, T]()
    state.currentAssignment = initTable[int, T]()

    for pos, coeff in coefficients:
        state.positions.incl(pos)
        state.coefficient[pos] = coeff

func newLinearCombinationState*[T](positions: seq[T]): LinearCombinationState[T] =
    new(result)
    result.init(positions)

func newLinearCombinationState*[T](coefficients: Table[int, T], constant: T = 0): LinearCombinationState[T] =
    new(result)
    result.init(coefficients, constant)

################################################################################
# LinearCombinationState Initialization
################################################################################

func initialize*[T](state: LinearCombinationState[T], assignment: seq[T]) =
    var value: T = state.constant
    for pos in state.positions:
        value = assignment[pos]
        state.value += state.coefficient[pos]*value
        state.currentAssignment[pos] = value

################################################################################
# LinearCombinationState Updates
################################################################################

func updatePosition*[T](state: LinearCombinationState[T], position: int, newValue: T) {.inline.} =
    let oldValue = state.currentAssignment[position]
    state.value += state.coefficient[position]*(newValue - oldValue)
    state.currentAssignment[position] = newValue

func moveDelta*[T](state: LinearCombinationState[T], position: int, oldValue, newValue: T): int {.inline.} =
    state.coefficient[position]*(newValue - oldValue)

################################################################################
# LinearCombinationState Updates
################################################################################

func linearize*[T](expression: Expression[T]): LinearCombinationState[T] =
    # Converts linear expression to a LinearCombinationState
    if not expression.linear:
        raise newException(NonlinearExpressionError, "Can't convert nonlinear expression to LinearCombinationState")

    var constant: T
    var coefficients, assignment: Table[int, T]

    # evaluate with all variables zero to get constant coefficient
    for pos in expression.positions:
        assignment[pos] = 0

    constant = expression.evaluate(assignment)

    # extract each coefficient
    for pos in expression.positions:
        assignment[pos] = 1
        coefficients[pos] = expression.evaluate(assignment) - constant
        assignment[pos] = 0

    return newLinearCombinationState(coefficients, constant)