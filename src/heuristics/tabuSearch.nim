import std/[packedsets, random, strformat, tables, times]
import cpuinfo
import threadpool

import ../constraints/constraint
import ../expressions/expression
import ../constrainedArray
import ../state/arrayState

randomize()


func bestMoves[T](state: ArrayState[T]): seq[(int, T)] =
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


proc applyBestMove[T](state: ArrayState[T]) {.inline.} =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.currentAssignment[position]
        state.assignValue(position, newValue)
        state.tabu[position][oldValue] = state.iteration + state.cost + rand(11)


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int): ArrayState[T] =
    var state = newArrayState[T](carray)
    # echo fmt"Searching for Assignment (thread {thread}):"
    # echo fmt"  tenure: {state.tenure}"
    # echo fmt"  tabuThreshold: {threshold}"
    # echo fmt"  initial cost: {state.cost}"
    var lastImprovement = 0
    let blockSize = 10000
    var now, rate: float
    var then = epochTime()
    var beginning = then

    while state.iteration - lastImprovement < threshold:
        now = epochTime()
        state.applyBestMove()
        if state.iteration > 0 and state.iteration mod blockSize == 0:
            rate = float(blockSize) / (now - then)
            then = now
            # echo fmt"Iteration: {state.iteration}  Current: {state.cost}  Best: {state.bestCost}  Rate: {rate:.3f} moves/sec"
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.currentAssignment
        if state.cost == 0:
            rate = float(state.iteration) / (now - beginning)
            echo fmt"Solution found on iteration {state.iteration} after {now - beginning:.3f} sec at {rate:.3f} moves/sec"
            return state
        state.iteration += 1
    if state.cost != 0:
        state.cost = state.bestCost
        state.currentAssignment = state.bestAssignment
        state.rebuildPenaltyMap()
    return state


iterator parallelSearch*[T](carray: ConstrainedArray[T], tabuThreshold: int): ArrayState[T] =
    let N = countProcessors()
    var jobs = newSeq[FlowVarBase](N)
    var idx: int
    var res: ArrayState[T]

    for i in 0..<N:
        jobs[i] = spawn carray.tabuImprove(tabuThreshold)
    
    while jobs.len > 0:
        idx = blockUntilAny(jobs)
        res = ^FlowVar[ArrayState[T]](jobs[idx])
        yield res
        jobs.del(idx)
        if res.cost == 0:
            break

proc resolve*[T](carray: ConstrainedArray[T], tabuThreshold = 10000): ArrayState[T] =
    for imp in carray.parallelSearch(tabuThreshold):
        if imp.cost == 0:
            return imp