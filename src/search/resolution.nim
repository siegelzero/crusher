import std/[os, strformat]

import heuristics, tabuSearch
import ../constraintSystem


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T],
                 parallel=true,
                 threshold=10000,
                 attempts=10) = 
    
    if not parallel:
        var improved = system.baseArray.tabuImprove(threshold)
        if improved.cost == 0:
            system.assignment = improved.assignment
            return
    else:
        for improved in system.baseArray.parallelSearch(threshold, attempts):
            if improved.cost == 0:
                system.assignment = improved.assignment
                return

    raise newException(NoSolutionFoundError, "Can't find satisfying solution")