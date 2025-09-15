import std/os

import tabu
import ../constraintSystem
import ../constrainedArray


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T], tabuThreshold=10000) =
    # Compute reduced domain once and cache it
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)

    var improved = system.baseArray.tabuImprove(tabuThreshold)
    if improved.cost == 0:
        system.assignment = improved.assignment
        return
    raise newException(NoSolutionFoundError, "Can't find satisfying solution")
