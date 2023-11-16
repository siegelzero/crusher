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
# ConstrainedArray Methods
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], minTenure, maxTenure: int) =
    state.init(carray)

    state.iteration = 0
    state.minTenure = minTenure
    state.maxTenure = maxTenure
    state.tenure = state.minTenure

    state.tabu = newSeq[Table[T, int]](carray.len)

    for i in 0..<carray.len:
        state.tabu[i] = initTable[T, int]()
        for d in carray.domain[i]:
            state.tabu[i][d] = 0


proc newTabuState*[T](carray: ConstrainedArray[T], minTenure=5, maxTenure=100): TabuState[T] =
    new(result)
    result.init(carray, minTenure, maxTenure)