import std/[packedsets, random, sequtils, tables]

import ../constraints/constraint
import ../constrainedArray

################################################################################
# Type definitions
################################################################################

type
    ArrayState*[T] = ref object of RootObj
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[Constraint[T]]]

        neighbors*: seq[seq[int]]

        penaltyMap*: seq[Table[T, int]]

        currentAssignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

################################################################################
# ArrayState methods
################################################################################

func updatePenaltiesForPosition[T](state: ArrayState[T], position: int) {.inline.} =
    # Computes penalties for all constraints involving the position, and updates penalty map
    let oldValue = state.currentAssignment[position]
    var penalty: int

    for newValue in state.carray.domain[position]:
        penalty = 0
        state.currentAssignment[position] = newValue
        for cons in state.constraintsAtPosition[position]:
            penalty += cons.penalty(state.currentAssignment)
        state.penaltyMap[position][newValue] = penalty

    state.currentAssignment[position] = oldValue

func updateNeighborPenalties*[T](state: ArrayState[T], position: int) {.inline.} =
    # Updates penalties for all neighboring positions to the given position
    for nbr in state.neighbors[position]:
        state.updatePenaltiesForPosition(nbr)


proc init*[T](state: ArrayState[T], carray: ConstrainedArray[T]) =
    # Initializes all structures and data for the state ArrayState[T]
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[Constraint[T]]](carray.len)
    state.neighbors = newSeq[seq[int]](carray.len)

    # Group constraints involving each position
    for constraint in carray.constraints:
        for pos in constraint.positions:
            state.constraintsAtPosition[pos].add(constraint)
    
    # Collect neighbors of each position
    var neighborSet: PackedSet[int] = toPackedSet[int]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for cons in state.constraintsAtPosition[pos]:
            neighborSet.incl(cons.positions)
        neighborSet.excl(pos)
        state.neighbors[pos] = toSeq(neighborSet)

    # Initialize with random assignment
    state.currentAssignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.currentAssignment[pos] = sample(carray.domain[pos])

    # Compute cost
    for cons in carray.constraints:
        state.cost += cons.penalty(state.currentAssignment)

    state.bestCost = state.cost
    state.bestAssignment = state.currentAssignment

    # Construct penalty map for each location and value
    state.penaltyMap = newSeq[Table[T, int]](state.carray.len)
    for pos in state.carray.allPositions():
        state.updatePenaltiesForPosition(pos)

proc newArrayState*[T](carray: ConstrainedArray[T]): ArrayState[T] =
    # Allocates and initializes new ArrayState[T]
    new(result)
    result.init(carray)