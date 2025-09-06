import std/[packedsets, tables]

################################################################################
# Type definitions for MinExpression
################################################################################

type
    MinExpression*[T] = ref object
        value*: T
        positions*: PackedSet[Natural]
        currentAssignment*: Table[int, T]

# MinExpression creation

func init*[T](state: MinExpression[T], positions: openArray[Natural]) =
    state.value = 0
    state.positions = toPackedSet[Natural](positions)
    state.currentAssignment = initTable[int, T]()

func newMinExpression*[T](positions: openArray[Natural]): MinExpression[T] =
    new(result)
    result.init(positions)

# MinExpression initialization

func initialize*[T](state: MinExpression[T], assignment: seq[T]) =
    # Initialize the MinExpression with the given assignment, and updates the value.
    var minValue: T = high(T)
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
        minValue = min(minValue, assignment[pos])
    state.value = minValue

func evaluate*[T](state: MinExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var minValue: T = high(T)
    for pos in state.positions:
        minValue = min(minValue, assignment[pos])
    return minValue

func `$`*[T](state: MinExpression[T]): string = $(state.value)

# MinExpression updates

func updatePosition*[T](state: MinExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    state.currentAssignment[position] = newValue
    state.value = state.currentAssignment.values.min()

func moveDelta*[T](state: MinExpression[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns the change in value obtained by reassigning position from oldValue to newValue.
    if newValue >= state.value:
        return 0
    else:
        return state.value - newValue
