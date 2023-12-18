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
        constraintsAtPosition*: seq[seq[Constraint[T]]]
        globalConstraints*: seq[Constraint[T]]
        neighbors*: seq[seq[int]]
        penaltyMap*: seq[seq[int]]
        reducedDomain*: seq[seq[T]]

        currentAssignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

################################################################################
# Penalty Routines
################################################################################

proc penalty*[T](state: ArrayState[T], constraint: Constraint[T]): int {.inline.} =
    return constraint.penalty(state.currentAssignment)


proc movePenalty*[T](state: ArrayState[T], constraint: Constraint[T], position: int, newValue: T): int {.inline.} =
    let oldValue = state.currentAssignment[position]
    case constraint.scope:
        of AlgebraicConstraint:
            state.currentAssignment[position] = newValue
            result = state.penalty(constraint)
            state.currentAssignment[position] = oldValue
        of AllDifferentConstraint:
            result = constraint.state.cost + constraint.state.moveDelta(position, oldValue, newValue)


################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: ArrayState[T], position: int) {.inline.} =
    # Computes penalties for all constraints involving the position, and updates penalty map
    var penalty: int
    for newValue in state.reducedDomain[position]:
        penalty = 0
        for constraint in state.constraintsAtPosition[position]:
            penalty += state.movePenalty(constraint, position, newValue)
        state.penaltyMap[position][newValue] = penalty


proc updateNeighborPenalties*[T](state: ArrayState[T], position: int) {.inline.} =
    # Updates penalties for all neighboring positions to the given position
    for nbr in state.neighbors[position]:
        state.updatePenaltiesForPosition(nbr)


proc rebuildPenaltyMap*[T](state: ArrayState[T]) =
    for position in state.carray.allPositions():
        state.updatePenaltiesForPosition(position)

################################################################################
# ArrayState creation
################################################################################

proc init*[T](state: ArrayState[T], carray: ConstrainedArray[T]) =
    # Initializes all structures and data for the state ArrayState[T]
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[Constraint[T]]](carray.len)
    state.neighbors = newSeq[seq[int]](carray.len)
    state.reducedDomain = reduceDomain(state.carray)

    # Group constraints involving each position
    for constraint in carray.constraints:
        for pos in constraint.positions:
            state.constraintsAtPosition[pos].add(constraint)
        if constraint.scope == AllDifferentConstraint:
            state.globalConstraints.add(constraint)
    
    # Collect neighbors of each position
    var neighborSet: PackedSet[int] = toPackedSet[int]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for constraint in state.constraintsAtPosition[pos]:
            neighborSet.incl(constraint.positions)
        neighborSet.excl(pos)
        state.neighbors[pos] = toSeq(neighborSet)

    # Initialize with random assignment
    state.currentAssignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.currentAssignment[pos] = sample(state.reducedDomain[pos])
    
    # Initialize global constraint states
    for cons in state.globalConstraints:
        cons.state.initialize(state.currentAssignment)

    # Compute cost
    for cons in carray.constraints:
        state.cost += state.penalty(cons)

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

proc assignValue*[T](state: ArrayState[T], position: int, value: T) =
    let penalty = state.penaltyMap[position][state.currentAssignment[position]]
    let delta = state.penaltyMap[position][value] - penalty
    state.currentAssignment[position] = value

    for cons in state.globalConstraints:
        if position in cons.positions:
            cons.state.updatePosition(position, value)

    state.cost += delta
    state.updateNeighborPenalties(position)
