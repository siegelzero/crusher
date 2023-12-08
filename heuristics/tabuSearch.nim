import std/[packedsets, random, strformat, tables, times]

import ../constraints/constraint
import ../expressions/expression
import ../constrainedArray
import ../state/tabuState

randomize()


func bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    var
        delta: int
        bestMoveCost = high(int)
        oldPenalty: int
        oldValue: T

    for position in state.carray.allPositions():
        oldValue = state.currentAssignment[position]
        oldPenalty = state.penaltyMap[position][oldValue]
        if oldPenalty == 0:
            continue

        for newValue in state.reducedDomain[position]:
            if newValue == oldValue:
                continue

            delta = state.penaltyMap[position][newValue] - oldPenalty

            if state.tabu[position][newValue] <= state.iteration or state.cost + delta < state.bestCost:
                if state.cost + delta < bestMoveCost:
                    result = @[(position, newValue)]
                    bestMoveCost = state.cost + delta
                elif state.cost + delta == bestMoveCost:
                    result.add((position, newValue))


proc applyBestMove[T](state: TabuState[T]) =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.currentAssignment[position]
        state.assignValue(position, newValue)
        state.tabu[position][oldValue] = state.iteration + 1 + rand(state.tenure)


proc tabuImprove*[T](state: TabuState[T], threshold: int) =
    var lastImprovement = 0

    while state.iteration - lastImprovement < threshold:
        state.applyBestMove()

        if state.cost < state.bestCost:
            echo fmt"Improved from {state.bestCost} to {state.cost} on iteration {state.iteration}"
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.currentAssignment

        if state.cost == 0:
            break

        state.iteration += 1
    
    if state.cost != 0:
        state.cost = state.bestCost
        state.currentAssignment = state.bestAssignment
        state.rebuildPenaltyMap()


proc findAssignment*[T](carray: ConstrainedArray[T], threshold: int = 10000): seq[T] =
    var state = newTabuState(carray)
    state.tabuImprove(threshold)
    doAssert state.cost == 0
    return state.currentAssignment
