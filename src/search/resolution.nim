import std/[os, strformat]

import tabu
import ../constraintSystem
import ../constrainedArray

when compileOption("threads"):
    import parallelResolution  # also exports candidatePool
    import scatterSearch

proc resolve*[T](system: ConstraintSystem[T],
                tabuThreshold: int = 10000,
                parallel: bool = false,
                populationSize: int = 32,
                numWorkers: int = 0,
                verbose: bool = true) =
    # Compute reduced domain once and cache it
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)

    # Check for empty domains (infeasible after domain reduction)
    for pos in system.baseArray.allPositions():
        if system.baseArray.reducedDomain[pos].len == 0:
            raise newException(NoSolutionFoundError, "Domain reduction found infeasibility")

    if parallel:
        var pool: CandidatePool[T]
        if parallelResolve(system, populationSize, numWorkers, tabuThreshold, verbose, pool):
            return

        # Parallel tabu failed — continue with scatter search using collected results
        if pool.entries.len > 0:
            let actualWorkers = if numWorkers == 0: getOptimalWorkerCount() else: numWorkers
            if verbose:
                echo &"[Solve] Continuing with scatter search (pool size={pool.entries.len}, best cost={pool.minCost})"
                pool.poolStatistics()
            if scatterImprove(system, pool, scatterThreshold = 1, tabuThreshold, tabuThreshold div 2, actualWorkers, verbose):
                return

        raise newException(NoSolutionFoundError, "Can't find satisfying solution with parallel search")
    else:
        var improved = system.baseArray.tabuImprove(tabuThreshold, verbose)
        if improved.cost == 0:
            system.initialize(improved.assignment)
            system.lastIterations = improved.iteration
            return
        if verbose:
            echo &"[Solve] Sequential failed: best cost={improved.cost}"
        raise newException(NoSolutionFoundError, "Can't find satisfying solution")
