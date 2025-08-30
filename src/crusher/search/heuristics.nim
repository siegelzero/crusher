import std/[random, os, times]

import ../constraints/stateful
import ../constrainedArray
import tabu

randomize()

# Sequential search iterator that performs multiple restarts
iterator sequentialSearch*[T](carray: ConstrainedArray[T], initialTabuThreshold: int, maxAttempts: int = 10, enableTiming: bool = false): TabuState[T] =
    var currentThreshold = initialTabuThreshold
    for attempt in 0..<maxAttempts:
        randomize(attempt * 1000 + int(epochTime()))
        let improved = carray.tabuImprove(currentThreshold, enableTiming)
        echo "DEBUG: Serial attempt ", attempt, " initial cost: ", improved.cost
        if attempt == 0:
            echo "DEBUG: Serial attempt 0 initial assignment (first 10): ", improved.assignment[0..<min(10, improved.assignment.len)]
        yield improved
        if improved.cost == 0:
            break
        currentThreshold = currentThreshold * 2


proc crossover*[T](carray: ConstrainedArray[T], A, B: TabuState[T]): TabuState[T] =
    result = newTabuState[T](carray)
    var penaltyA, penaltyB: int

    for constraint in carray.constraints:
        if rand(1.0) < 0.9:
            continue
        penaltyA = constraint.penalty(A.assignment)
        penaltyB = constraint.penalty(B.assignment)

        if penaltyA < penaltyB:
            for position in constraint.positions:
                result.assignValue(position, A.assignment[position])
        elif penaltyB < penaltyA:
            for position in constraint.positions:
                result.assignValue(position, B.assignment[position])
        else:
            for position in constraint.positions:
                result.assignValue(position, sample(A.reducedDomain[position]))


proc hybrid*[T](carray: ConstrainedArray[T], threshold, popSize, generations: int): TabuState[T] =
    var population: seq[TabuState[T]]
    # Create initial population using single-threaded search
    for i in 0..<popSize:
        let improved = carray.tabuImprove(threshold)
        if improved.cost == 0:
            return improved
        population.add(improved)
    
    var nextGeneration: seq[TabuState[T]]
    var improved, offspring: TabuState[T]

    for i in 0..<population.len:
        for j in 0..<i:
            offspring = carray.crossover(population[i], population[j])
            improved = offspring.tabuImprove(threshold)
            nextGeneration.add(improved)

    return nextGeneration[0]
