import std/[packedsets, tables]

import arrayState
import ../constrainedArray

################################################################################
# Type definitions
################################################################################

type
    TabuState*[T] = ref object of ArrayState[T]
        iteration*: int
        tabu*: seq[Table[T, int]]
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
    state.tabu = newSeq[Table[T, int]](carray.len)

    for i in 0..<carray.len:
        state.tabu[i] = initTable[T, int]()
        for d in carray.domain[i]:
            state.tabu[i][d] = 0


func newTabuState*[T](carray: ConstrainedArray[T], minTenure=5, maxTenure=100): TabuState[T] =
    # Allocates and initializes new TabuState[T]
    new(result)
    result.init(carray, minTenure, maxTenure)