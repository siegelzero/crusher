import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    ElementState*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        positions*: PackedSet[int]


proc initialize*[T](state: ElementState[T], assignment: seq[T]) =
    return

proc updatePosition*[T](state: ElementState[T], position: int, newValue: T) =
    return

proc moveDelta*[T](state: ElementState[T], position: int, oldValue, newValue: T): int =
    return 0