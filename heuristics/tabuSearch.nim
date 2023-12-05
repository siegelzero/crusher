import std/[packedsets, random, strformat, tables, times]

import ../constraints/constraint
import ../expressions/expression
import ../constrainedArray
import ../state/tabuState

randomize()


func bestMoves[T](state: TabuState[T]): seq[(int, T, T, int)] =
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
                    result = @[(position, oldValue, newValue, delta)]
                    bestMoveCost = state.cost + delta
                elif state.cost + delta == bestMoveCost:
                    result.add((position, oldValue, newValue, delta))


proc applyBestMove[T](state: TabuState[T]) =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, oldValue, newValue, delta) = sample(moves)
        state.assignValue(position, oldValue, newValue)
        state.tabu[position][oldValue] = state.iteration + 1 + rand(state.tenure)

        if delta > 0:
            state.tenure += 1
            if state.tenure == state.maxTenure:
                state.tenure = state.minTenure


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


proc tabuRestarts*[T](state: var TabuState[T], threshold, restarts: int) =
    var oldValue, newValue: T
    var delta: int

    for i in 0..<restarts:
        state.tabuImprove(threshold)
        if state.cost == 0:
            break
        echo "jiggling"
        state = newTabuState(state.carray)



proc findAssignment*[T](carray: ConstrainedArray[T], threshold: int = 10000, restarts: int = 10): seq[T] =
    var state = newTabuState(carray)
    state.tabuRestarts(threshold, restarts)
    doAssert state.cost == 0
    return state.currentAssignment