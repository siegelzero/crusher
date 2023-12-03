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
        maxTenure*, minTenure*, tenure*: int

################################################################################
# TabuState methods
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], minTenure, maxTenure: int) =
    # Initializes fields and data for TabuState[T]
    state.init(carray) # Call init of parent class

    state.iteration = 0
    state.minTenure = minTenure
    state.maxTenure = maxTenure
    state.tenure = state.minTenure
    state.tabu = newSeq[seq[int]](carray.len)

    for pos in carray.allPositions():
        state.tabu[pos] = newSeq[int](max(state.reducedDomain[pos]) + 1)


proc newTabuState*[T](carray: ConstrainedArray[T], minTenure=2, maxTenure=100): TabuState[T] =
    # Allocates and initializes new TabuState[T]
    new(result)
    result.init(carray, minTenure, maxTenure)