import std/[os, strformat]

import heuristics, tabuSearch
import ../constraintSystem


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T],
                 initialTabuThreshold=1024,
                 maxAttempts=100,
                 attemptThreshold=10) = 

    var lastImprovement = 0
    var bestAttempt = high(int)
    var bestSolution: seq[T]
    var attempt = 0
    var currentTabuThreshold = initialTabuThreshold

    for improved in system.baseArray.sequentialSearch(currentTabuThreshold, maxAttempts):
        attempt += 1

        if improved.cost < bestAttempt:
            bestAttempt = improved.cost
            bestSolution = improved.assignment
            lastImprovement = attempt
            echo fmt"Found better solution with cost {improved.cost}"

        if improved.cost == 0:
            system.assignment = improved.assignment
            return

        if attempt - lastImprovement > attemptThreshold:
            break

    # If no perfect solution found, use the best one found
    if bestSolution.len > 0:
        system.assignment = bestSolution
        return

    raise newException(NoSolutionFoundError, "Can't find satisfying solution")
