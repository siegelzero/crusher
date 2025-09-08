import std/[packedsets, random, tables]

import ../expressions/expressions
import ../constrainedArray
import tabuState

randomize()

proc bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    # Returns the best valid next moves for the state.
    # Evaluates the entire neighborhood to find best non-tabu or improving moves.
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

        for newValue in state.reducedDomain[position]:
            if newValue == oldValue:
                continue
            delta = state.penaltyMap[position].getOrDefault(newValue, 0) - oldPenalty
            # Allow the move if the new value is not tabu for the position
            # or if the new improved cost is better than the best seen so far (aspiration criterion)
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
        # state.tabu[position][oldValue] = state.iteration + state.cost + rand(11)
        state.tabu[position][oldValue] = state.iteration + 1 + state.iteration mod 10


proc tabuImprove*[T](state: TabuState[T], threshold: int): TabuState[T] =
    var lastImprovement = 0

    while state.iteration - lastImprovement < threshold:
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
