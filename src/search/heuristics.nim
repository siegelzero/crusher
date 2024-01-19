import std/[cpuinfo, random, strformat, threadpool]

import ../constraints/constraint
import ../constrainedArray
import ../state/arrayState
import tabuSearch

randomize()


iterator parallelSearch*[T](carray: ConstrainedArray[T], threshold: int, maxJobs=0): ArrayState[T] =
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
    var result: ArrayState[T]
    var idx: int
    while jobs.len > 0:
        idx = blockUntilAny(jobs)
        result = ^FlowVar[ArrayState[T]](jobs[idx])

        yield result
        if result.cost == 0:
            break

        if jobCount < max(maxJobs, N):
            jobs[idx] = spawn carray.tabuImprove(threshold)
            jobCount += 1
        else:
            jobs.del(idx)


proc crossover*[T](carray: ConstrainedArray[T], A, B: ArrayState[T]): ArrayState[T] =
    result = newArrayState[T](carray)
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


proc hybrid*[T](carray: ConstrainedArray[T], threshold, popSize, generations: int): ArrayState[T] =
    var population: seq[ArrayState[T]]
    for improved in carray.parallelSearch(threshold, popSize):
        if improved.cost == 0:
            return improved
        population.add(improved)
    
    echo fmt"Have population {population.len}"
    var nextGeneration: seq[ArrayState[T]]
    var improved, offspring: ArrayState[T]

    for i in 0..<population.len:
        for j in 0..<i:
            offspring = carray.crossover(population[i], population[j])
            echo fmt"child: {offspring.cost}"
            improved = offspring.tabuImprove(threshold)
            echo fmt"improved: {improved.cost}"
            nextGeneration.add(improved)

    return nextGeneration[0]