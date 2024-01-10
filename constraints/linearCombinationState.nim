import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    LinearCombinationState*[T] = ref object
        value*: T
        positions*: PackedSet[int]
        coefficient*: Table[int, T]
        currentAssignment*: Table[int, T]

################################################################################
# LinearCombinationState Creation
################################################################################

func init*[T](state: LinearCombinationState[T], positions: openArray[T]) =
    state.value = 0
    state.positions = toPackedSet[int](positions)
    state.coefficient = initTable[int, T]()
    state.currentAssignment = initTable[int, T]()

    for pos in positions:
        state.coefficient[pos] = 1


func newLinearCombinationState*[T](positions: openArray[T] ): LinearCombinationState[T] =
    # Allocates and initializes new AllDifferentState[T]
    new(result)
    result.init(positions)

################################################################################
# LinearCombinationState Initialization
################################################################################

func initialize*[T](state: LinearCombinationState[T], assignment: seq[T]) =
    var value: T
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

func evaluate*[T](state: LinearCombinationState[T]): T {.inline.} =
    state.value