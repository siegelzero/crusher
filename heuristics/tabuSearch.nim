import std/[packedsets, random, strformat, tables, times]
import cpuinfo
import threadpool

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


proc tabuImprove*[T](state: TabuState[T], threshold: int): TabuState[T] =
    var lastImprovement = 0
    while state.iteration - lastImprovement < threshold:
        state.applyBestMove()
        if state.iteration mod 500 == 0:
            echo fmt"Have cost {state.bestCost} on iteration {state.iteration}"
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.currentAssignment
        if state.cost == 0:
            echo "Solution found!"
            return state
        state.iteration += 1
    if state.cost != 0:
        state.cost = state.bestCost
        state.currentAssignment = state.bestAssignment
        state.rebuildPenaltyMap()
    return state


proc batchImprove*[T](states: seq[TabuState[T]], tabuThreshold: int): seq[TabuState[T]] =
    var
        jobs: seq[FlowVarBase]
        idx: int
        res: TabuState[T]

    for state in states:
        jobs.add(spawn state.tabuImprove(tabuThreshold))

    sync()

    for job in jobs:
        result.add(^FlowVar[TabuState[T]](job))


proc parallelSearch*[T](carray: ConstrainedArray[T], threshold: int): TabuState[T] =
    let N = countProcessors()
    var initial: seq[TabuState[T]]
    var solutionFound = false

    for i in 0..<N:
        initial.add(newTabuState[T](carray))
    
    for improved in batchImprove(initial, threshold):
        if improved.cost == 0:
            solutionFound = true
            return improved
    
    doAssert solutionFound


proc findAssignment*[T](carray: ConstrainedArray[T], threshold: int = 10000): seq[T] =
    var state = newTabuState(carray)
    let improved = state.tabuImprove(threshold)
    doAssert improved.cost == 0
    return improved.currentAssignment
