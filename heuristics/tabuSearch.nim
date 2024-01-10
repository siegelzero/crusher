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
        firstImprovement = true

    for position in state.carray.allPositions():
        oldValue = state.currentAssignment[position]
        oldPenalty = state.penaltyMap[position][oldValue]
        if oldPenalty == 0:
            continue

        for newValue in state.reducedDomain[position]:
            if newValue == oldValue:
                continue

            delta = state.penaltyMap[position][newValue] - oldPenalty
            # if delta < 0 and firstImprovement:
            #     result = @[(position, newValue)]
            #     return result

            if state.tabu[position][newValue] <= state.iteration or state.cost + delta < state.bestCost:
                if state.cost + delta < bestMoveCost:
                    result = @[(position, newValue)]
                    bestMoveCost = state.cost + delta
                elif state.cost + delta == bestMoveCost:
                    result.add((position, newValue))


proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.currentAssignment[position]
        state.assignValue(position, newValue)
        state.tabu[position][oldValue] = state.iteration + state.cost + rand(state.tenure)


proc tabuImprove*[T](state: TabuState[T], threshold: int): TabuState[T] =
    var lastImprovement = 0
    let blockSize = 10000
    var now, rate: float
    var then = epochTime()
    var beginning = then


    while state.iteration - lastImprovement < threshold:
        state.applyBestMove()
        if state.iteration > 0 and state.iteration mod blockSize == 0:
            now = epochTime()
            rate = float(blockSize) / (now - then)
            then = now
            echo fmt"Iteration: {state.iteration}  Current: {state.cost}  Best: {state.bestCost}  Rate: {rate:.3f} moves/sec"
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.currentAssignment
        if state.cost == 0:
            echo fmt"Solution found on iteration {state.iteration} after {epochTime() - beginning:.3f} sec"
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


proc findAssignment*[T](carray: ConstrainedArray[T], tenure = 6, threshold = 10000): seq[T] =
    var state = newTabuState(carray, tenure)
    echo "Searching for Assignment:"
    echo fmt"  tenure: {tenure}"
    echo fmt"  tabuThreshold: {threshold}"
    echo fmt"  initial cost: {state.cost}"
    let improved = state.tabuImprove(threshold)
    doAssert improved.cost == 0
    return improved.currentAssignment
