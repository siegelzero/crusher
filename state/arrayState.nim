import std/[packedsets, random, sequtils, tables]

import ../constraints/constraint
import ../constrainedArray
import domain

################################################################################
# Type definitions
################################################################################

type
    ArrayState*[T] = ref object of RootObj
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[int]]
        neighbors*: seq[seq[int]]
        penaltyMap*: seq[seq[int]]
        reducedDomain*: seq[seq[T]]

        currentAssignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

################################################################################
# Penalty Map Routines
################################################################################

func updatePenaltiesForPosition[T](state: ArrayState[T], position: int) {.inline.} =
    # Computes penalties for all constraints involving the position, and updates penalty map
    let oldValue = state.currentAssignment[position]
    var penalty: int

    for newValue in state.reducedDomain[position]:
        penalty = 0
        state.currentAssignment[position] = newValue
        for idx in state.constraintsAtPosition[position]:
            penalty += state.carray.constraints[idx].penalty(state.currentAssignment)
        state.penaltyMap[position][newValue] = penalty

    state.currentAssignment[position] = oldValue


func updateNeighborPenalties*[T](state: ArrayState[T], position: int) {.inline.} =
    # Updates penalties for all neighboring positions to the given position
    for nbr in state.neighbors[position]:
        state.updatePenaltiesForPosition(nbr)


func rebuildPenaltyMap*[T](state: ArrayState[T]) =
    for position in state.carray.allPositions():
        state.updatePenaltiesForPosition(position)

################################################################################
# ArrayState creation
################################################################################

proc init*[T](state: ArrayState[T], carray: ConstrainedArray[T]) =
    # Initializes all structures and data for the state ArrayState[T]
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[int]](carray.len)
    state.neighbors = newSeq[seq[int]](carray.len)
    state.reducedDomain = reduceDomain(state.carray)

    # Group constraints involving each position
    for idx, constraint in carray.constraints:
        for pos in constraint.positions:
            state.constraintsAtPosition[pos].add(idx)
    
    # Collect neighbors of each position
    var neighborSet: PackedSet[int] = toPackedSet[int]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for idx in state.constraintsAtPosition[pos]:
            neighborSet.incl(carray.constraints[idx].positions)
        neighborSet.excl(pos)
        state.neighbors[pos] = toSeq(neighborSet)

    # Initialize with random assignment
    state.currentAssignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.currentAssignment[pos] = sample(state.reducedDomain[pos])

    # Compute cost
    for cons in carray.constraints:
        state.cost += cons.penalty(state.currentAssignment)

    state.bestCost = state.cost
    state.bestAssignment = state.currentAssignment

    # Construct penalty map for each location and value
    state.penaltyMap = newSeq[seq[int]](state.carray.len)
    for pos in state.carray.allPositions():
        state.penaltyMap[pos] = newSeq[int](max(state.reducedDomain[pos]) + 1)

    for pos in state.carray.allPositions():
        state.updatePenaltiesForPosition(pos)


func newArrayState*[T](carray: ConstrainedArray[T]): ArrayState[T] =
    # Allocates and initializes new ArrayState[T]
    new(result)
    result.init(carray)

################################################################################
# Value Assignment
################################################################################

func assignValue*[T](state: ArrayState[T], position: int, value: T) =
    let penalty = state.penaltyMap[position][state.currentAssignment[position]]
    let delta = state.penaltyMap[position][value] - penalty
    state.currentAssignment[position] = value
    state.cost += delta
    state.updateNeighborPenalties(position)
