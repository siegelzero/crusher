import std/[packedsets, random, sequtils, tables]

import ../constraints/[algebraic, stateful, allDifferent, sumConstraint]
import ../constrainedArray

################################################################################
# Type definitions
################################################################################

type
    TabuState*[T] = ref object of RootObj
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[StatefulConstraint[T]]]
        constraints*: seq[StatefulConstraint[T]]
        neighbors*: seq[seq[Natural]]
        penaltyMap*: seq[Table[T, int]]
        reducedDomain*: seq[seq[T]]

        assignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

        iteration*: int
        tabu*: seq[Table[T, int]]
        tenure*: int

################################################################################
# Penalty Routines
################################################################################

proc movePenalty*[T](state: TabuState[T], constraint: StatefulConstraint[T], position: int, newValue: T): int {.inline.} =
    let oldValue = state.assignment[position]
    case constraint.stateType:
        of AllDifferentType:
            result = constraint.allDifferentState.cost + constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            result = 0
        of SumExpressionType:
            result = constraint.sumExpressionConstraintState.cost + constraint.sumExpressionConstraintState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            result = constraint.algebraicConstraintState.cost + constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)

################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: TabuState[T], position: Natural) =
    # Computes penalties for all constraints involving the position, and updates penalty map
    var penalty: int
    for value in state.reducedDomain[position]:
        penalty = 0
        for constraint in state.constraintsAtPosition[position]:
            penalty += state.movePenalty(constraint, position, value)
        state.penaltyMap[position][value] = penalty


proc updateNeighborPenalties*[T](state: TabuState[T], position: Natural) =
    # Updates penalties for all neighboring positions to the given position
    for nbr in state.neighbors[position]:
        state.updatePenaltiesForPosition(nbr)


proc rebuildPenaltyMap*[T](state: TabuState[T]) =
    for position in state.carray.allPositions():
        state.updatePenaltiesForPosition(position)

################################################################################
# TabuState creation
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T]) =
    # Initializes all structures and data for the state TabuState[T]
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[StatefulConstraint[T]]](carray.len)
    state.neighbors = newSeq[seq[Natural]](carray.len)
    state.reducedDomain = reduceDomain(state.carray)

    state.iteration = 0
    state.tabu = newSeq[Table[T, int]](carray.len)

    for pos in carray.allPositions():
        state.tabu[pos] = initTable[T, int]()

    # Group constraints involving each position
    for constraint in carray.constraints:
        state.constraints.add(constraint)
        for pos in constraint.positions:
            state.constraintsAtPosition[pos].add(constraint)
    
    # Collect neighbors of each position
    var neighborSet: PackedSet[Natural] = toPackedSet[Natural]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for constraint in state.constraintsAtPosition[pos]:
            neighborSet.incl(constraint.positions)
        neighborSet.excl(pos)
        state.neighbors[pos] = toSeq(neighborSet)

    # Initialize with random assignment
    state.assignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.assignment[pos] = sample(state.reducedDomain[pos])
    
    # Initialize constraint states with current assignment
    for constraint in state.constraints:
        constraint.initialize(state.assignment)

    # Compute cost
    for cons in carray.constraints:
        state.cost += cons.penalty()

    state.bestCost = state.cost
    state.bestAssignment = state.assignment

    # Construct penalty map for each location and value
    state.penaltyMap = newSeq[Table[T, int]](state.carray.len)
    for pos in state.carray.allPositions():
        state.penaltyMap[pos] = initTable[T, int]()

    for pos in state.carray.allPositions():
        state.updatePenaltiesForPosition(pos)


proc newTabuState*[T](carray: ConstrainedArray[T]): TabuState[T] =
    # Allocates and initializes new TabuState[T]
    new(result)
    result.init(carray)

################################################################################
# Value Assignment
################################################################################

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    # Updates current assignment of state by setting value to the position
    let penalty = state.penaltyMap[position].getOrDefault(state.assignment[position], 0)
    let delta = state.penaltyMap[position].getOrDefault(value, 0) - penalty
    # Update assignment
    state.assignment[position] = value

    # Update all computed constraints that involve this position
    for constraint in state.constraintsAtPosition[position]:
        constraint.updatePosition(position, value)

    # Update cost of state for the given move
    state.cost += delta
    state.updateNeighborPenalties(position)
