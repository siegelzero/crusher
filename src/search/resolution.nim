import os

import heuristics
import ../constraintSystem


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T], threshold = 10000, attempts=10) = 
    for improved in system.baseArray.parallelSearch(threshold, attempts):
        if improved.cost == 0:
            system.assignment = improved.assignment
            return

    raise newException(NoSolutionFoundError, "Can't find satisfying solution")