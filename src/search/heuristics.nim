import std/[cpuinfo, random, strformat, threadpool]

import ../constraints/stateful
import ../constrainedArray
import tabu

randomize()


iterator parallelSearch*[T](carray: ConstrainedArray[T], threshold: int, maxJobs=0): TabuState[T] =
    # Spawns N independent search threads, yielding results in order of completion.
    # Iteration stops if a solution is found.
    let N = countProcessors()

    # Spawn N threads
    var jobs = newSeq[FlowVarBase](N)
    var jobCount = 0
    for i in 0..<N:
        jobs[i] = spawn carray.tabuImprove(threshold)
        jobCount += 1

    # Yield each as it completes
    var result: TabuState[T]
    var idx: int
    while jobs.len > 0:
        idx = blockUntilAny(jobs)
        result = ^FlowVar[TabuState[T]](jobs[idx])

        yield result
        if result.cost == 0:
            break

        if jobCount < max(maxJobs, N):
            jobs[idx] = spawn carray.tabuImprove(threshold)
            jobCount += 1
        else:
            jobs.del(idx)


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
    for improved in carray.parallelSearch(threshold, popSize):
        if improved.cost == 0:
            return improved
        population.add(improved)

    echo fmt"Have population {population.len}"
    var nextGeneration: seq[TabuState[T]]
    var improved, offspring: TabuState[T]

    for i in 0..<population.len:
        for j in 0..<i:
            offspring = carray.crossover(population[i], population[j])
            echo fmt"child: {offspring.cost}"
            improved = offspring.tabuImprove(threshold)
            echo fmt"improved: {improved.cost}"
            nextGeneration.add(improved)

    return nextGeneration[0]