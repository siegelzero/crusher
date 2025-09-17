import std/[packedsets, random, sequtils, tables, atomics]

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState]
import ../constrainedArray
import ../expressions/expressions

randomize()

################################################################################
# Type definitions
################################################################################

type
    TabuState*[T] = ref object of RootObj
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[StatefulConstraint[T]]]
        constraints*: seq[StatefulConstraint[T]]
        neighbors*: seq[seq[int]]
        penaltyMap*: seq[Table[T, int]]

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
        of AtLeastType:
            result = constraint.atLeastState.cost + constraint.atLeastState.moveDelta(position, oldValue, newValue)
        of AtMostType:
            result = constraint.atMostState.cost + constraint.atMostState.moveDelta(position, oldValue, newValue)
        of ElementType:
            result = constraint.elementState.cost + constraint.elementState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            result = constraint.algebraicState.cost + constraint.algebraicState.moveDelta(position, oldValue, newValue)
        of RelationalType:
            result = constraint.relationalState.cost + constraint.relationalState.moveDelta(position, oldValue, newValue)
        of OrderingType:
            result = constraint.orderingState.cost + constraint.orderingState.moveDelta(position, oldValue, newValue)
        of GlobalCardinalityType:
            result = constraint.globalCardinalityState.cost + constraint.globalCardinalityState.moveDelta(position, oldValue, newValue)
        of MultiknapsackType:
            result = constraint.multiknapsackState.cost + constraint.multiknapsackState.moveDelta(position, oldValue, newValue)
        of SequenceType:
            result = constraint.sequenceState.cost + constraint.sequenceState.moveDelta(position, oldValue, newValue)

################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: TabuState[T], position: int) =
    var penalty: int
    for value in state.carray.reducedDomain[position]:
        penalty = 0
        for constraint in state.constraintsAtPosition[position]:
            penalty += state.movePenalty(constraint, position, value)
        state.penaltyMap[position][value] = penalty


proc updateNeighborPenalties*[T](state: TabuState[T], position: int) =
    for nbr in state.neighbors[position]:
        state.updatePenaltiesForPosition(nbr)


proc rebuildPenaltyMap*[T](state: TabuState[T]) =
    for position in state.carray.allPositions():
        state.updatePenaltiesForPosition(position)

################################################################################
# TabuState creation
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T]) =
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[StatefulConstraint[T]]](carray.len)
    state.neighbors = newSeq[seq[int]](carray.len)

    state.iteration = 0
    state.tabu = newSeq[Table[T, int]](carray.len)

    for pos in carray.allPositions():
        state.tabu[pos] = initTable[T, int]()

    for constraint in carray.constraints:
        state.constraints.add(constraint)
        for pos in constraint.positions:
            state.constraintsAtPosition[pos].add(constraint)

    var neighborSet: PackedSet[int] = toPackedSet[int]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for constraint in state.constraintsAtPosition[pos]:
            neighborSet.incl(constraint.positions)
        neighborSet.excl(pos)
        state.neighbors[pos] = toSeq(neighborSet)

    state.assignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.assignment[pos] = sample(state.carray.reducedDomain[pos])

    for constraint in state.constraints:
        constraint.initialize(state.assignment)

    for cons in carray.constraints:
        state.cost += cons.penalty()

    state.bestCost = state.cost
    state.bestAssignment = state.assignment

    state.penaltyMap = newSeq[Table[T, int]](state.carray.len)
    for pos in state.carray.allPositions():
        state.penaltyMap[pos] = initTable[T, int]()

    for pos in state.carray.allPositions():
        state.updatePenaltiesForPosition(pos)


proc newTabuState*[T](carray: ConstrainedArray[T]): TabuState[T] =
    new(result)
    result.init(carray)

################################################################################
# Value Assignment
################################################################################

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    let penalty = state.penaltyMap[position].getOrDefault(state.assignment[position], 0)
    let delta = state.penaltyMap[position].getOrDefault(value, 0) - penalty
    state.assignment[position] = value

    for constraint in state.constraintsAtPosition[position]:
        constraint.updatePosition(position, value)

    state.cost += delta
    state.updateNeighborPenalties(position)

################################################################################
# Search Algorithm Implementation
################################################################################

proc bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    var
        delta: int
        bestMoveCost = high(int)
        oldPenalty: int
        oldValue: T

    for position in state.carray.allPositions():
        oldValue = state.assignment[position]
        oldPenalty = state.penaltyMap[position].getOrDefault(oldValue, 0)
        if oldPenalty == 0:
            continue

        for newValue in state.carray.reducedDomain[position]:
            if newValue == oldValue:
                continue
            delta = state.penaltyMap[position].getOrDefault(newValue, 0) - oldPenalty
            if state.tabu[position].getOrDefault(newValue, 0) <= state.iteration or state.cost + delta < state.bestCost:
                if state.cost + delta < bestMoveCost:
                    result = @[(position, newValue)]
                    bestMoveCost = state.cost + delta
                elif state.cost + delta == bestMoveCost:
                    result.add((position, newValue))


proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.assignment[position]
        state.assignValue(position, newValue)
        state.tabu[position][oldValue] = state.iteration + 1 + state.iteration mod 10


proc tabuImprove*[T](state: TabuState[T], threshold: int, shouldStop: ptr Atomic[bool] = nil): TabuState[T] =
    var lastImprovement = 0

    while state.iteration - lastImprovement < threshold:
        # Check for early termination signal
        if shouldStop != nil and shouldStop[].load():
            return state

        state.applyBestMove()
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
        if state.cost == 0:
            return state
        state.iteration += 1
    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int): TabuState[T] =
    var state = newTabuState[T](carray)
    return state.tabuImprove(threshold)