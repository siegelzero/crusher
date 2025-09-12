import std/os

import heuristics, tabu
import ../constraintSystem


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T],
                 parallel=false,
                 tabuThreshold=10000,
                 maxAttempts=1000,
                 attemptThreshold=100) =

    if not parallel:
        var improved = system.baseArray.tabuImprove(tabuThreshold)
        if improved.cost == 0:
            system.assignment = improved.assignment
            return
        raise newException(NoSolutionFoundError, "Can't find satisfying solution")
    else:
        var lastImprovement = 0
        var bestAttempt = high(int)
        var attempt = 0

        for improved in system.baseArray.parallelSearch(tabuThreshold, maxAttempts):
            attempt += 1

            if improved.cost < bestAttempt:
                bestAttempt = improved.cost
                lastImprovement = attempt

            if improved.cost == 0:
                system.assignment = improved.assignment
                return

            if attempt - lastImprovement > attemptThreshold:
                break

    raise newException(NoSolutionFoundError, "Can't find satisfying solution")
