import std/[os, strformat]

import tabu
import ../constraintSystem
import ../constrainedArray

when compileOption("threads"):
    import parallelResolution

proc resolve*[T](system: ConstraintSystem[T],
                tabuThreshold: int = 10000,
                parallel: bool = false,
                populationSize: int = 32,
                numWorkers: int = 0,
                verbose: bool = true) =
    # Compute reduced domain once and cache it
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)

    if parallel:
        parallelResolve(system, populationSize, numWorkers, tabuThreshold, verbose)
        return
    else:
        var improved = system.baseArray.tabuImprove(tabuThreshold, verbose)
        if improved.cost == 0:
            system.initialize(improved.assignment)
            system.lastIterations = improved.iteration
            return
        if verbose:
            echo &"[Solve] Sequential failed: best cost={improved.cost}"
        raise newException(NoSolutionFoundError, "Can't find satisfying solution")
