import std/[packedsets, tables]

import arrayState
import ../constrainedArray

################################################################################
# Type definitions
################################################################################

type
    TabuState*[T] = ref object of ArrayState[T]
        iteration*: int
        tabu*: seq[seq[int]]
        tenure*: int

################################################################################
# TabuState creation
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], tenure: int) =
    # Initializes fields and data for TabuState[T]
    state.init(carray) # Call init of parent class

    state.iteration = 0
    state.tenure = tenure
    state.tabu = newSeq[seq[int]](carray.len)

    for pos in carray.allPositions():
        state.tabu[pos] = newSeq[int](max(state.reducedDomain[pos]) + 1)


proc newTabuState*[T](carray: ConstrainedArray[T], tenure=6): TabuState[T] =
    # Allocates and initializes new TabuState[T]
    new(result)
    result.init(carray, tenure)
