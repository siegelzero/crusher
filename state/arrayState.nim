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
# ConstrainedArray Methods
################################################################################

func updatePenaltyMap*[T](state: ArrayState[T], position: int) =
    var
        oldValue: T
        penalty: int

    for nbr in state.neighbors[position]:
        oldValue = state.currentAssignment[nbr]
        for newValue in state.carray.domain[nbr]:
            penalty = 0
            state.currentAssignment[nbr] = newValue
            for cons in state.constraintsAtPosition[nbr]:
                penalty += cons.penalty(state.currentAssignment)
            state.penaltyMap[nbr][newValue] = penalty
        state.currentAssignment[nbr] = oldValue


proc init*[T](state: ArrayState[T], carray: ConstrainedArray[T]) =
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

    # Random assignment
    state.currentAssignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.currentAssignment[pos] = sample(carray.domain[pos])

    # Compute cost
    for cons in carray.constraints:
        state.cost += cons.penalty(state.currentAssignment)

    state.bestCost = state.cost
    state.bestAssignment = state.currentAssignment

    state.penaltyMap = newSeq[Table[T, int]](state.carray.len)

    var penalty: int
    var oldValue: T

    # Construct penalty map for each location and value
    for pos in state.carray.allPositions():
        oldValue = state.currentAssignment[pos]
        for newValue in state.carray.domain[pos]:
            penalty = 0
            state.currentAssignment[pos] = newValue
            for cons in state.constraintsAtPosition[pos]:
                penalty += cons.penalty(state.currentAssignment)
            state.penaltyMap[pos][newValue] = penalty
        state.currentAssignment[pos] = oldValue


proc newArrayState*[T](carray: ConstrainedArray[T]): ArrayState[T] =
    new(result)
    result.init(carray)