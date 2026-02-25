import std/[os, strformat, times]

import tabu
import ../constraintSystem
import ../constrainedArray

when compileOption("threads"):
    import parallelResolution  # also exports candidatePool
    import scatterSearch

type
    ScatterStrategy* = enum
        PathRelinking,  ## Current approach: pairwise path relinking between pool members
        LNS             ## Constraint-group LNS: targeted perturbation guided by constraint topology

proc resolve*[T](system: ConstraintSystem[T],
                tabuThreshold: int = 10000,
                scatterThreshold: int = 5,
                parallel: bool = true,
                populationSize: int = 16,
                numWorkers: int = 0,
                scatterStrategy: ScatterStrategy = PathRelinking,
                verbose: bool = false,
                deadline: float = 0.0) =
    # Compute reduced domain once and cache it
    if system.baseArray.reducedDomain.len == 0:
        let drStart = epochTime()
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        if verbose:
            let drElapsed = epochTime() - drStart
            echo &"[Solve] Domain reduction took {drElapsed:.3f}s"
            var totalOriginal, totalReduced: int
            for pos in system.baseArray.allPositions():
                totalOriginal += system.baseArray.domain[pos].len
                totalReduced += system.baseArray.reducedDomain[pos].len
            if totalReduced < totalOriginal:
                echo &"[Solve] Domain reduction: {totalOriginal} -> {totalReduced} values ({100 - totalReduced * 100 div totalOriginal}% reduction)"

    # Check for empty domains (infeasible after domain reduction)
    for pos in system.baseArray.allPositions():
        if system.baseArray.reducedDomain[pos].len == 0:
            if verbose:
                echo &"[Solve] Empty domain at position {pos} (original domain size: {system.baseArray.domain[pos].len})"
            raise newException(InfeasibleError, "Domain reduction found infeasibility")

    # Shrink channel position domains to avoid expensive deepCopy of million-element seqs.
    # Channel positions are never searched, so their full domains are never needed again.
    for pos in system.baseArray.channelPositions.items:
        if system.baseArray.domain[pos].len > 1000:
            system.baseArray.domain[pos] = system.baseArray.reducedDomain[pos]

    if parallel:
        # Use persisted adapted threshold if available, otherwise caller's value
        let effectiveThreshold = if system.adaptedTabuThreshold > 0: system.adaptedTabuThreshold
                                 else: tabuThreshold
        if verbose and effectiveThreshold != tabuThreshold:
            echo &"[Solve] Using adapted threshold: {effectiveThreshold} (original: {tabuThreshold})"
        var pool: CandidatePool[T]
        var adaptedThreshold = effectiveThreshold
        if parallelResolve(system, populationSize, numWorkers, effectiveThreshold, verbose, pool, deadline, adaptedThreshold):
            system.adaptedTabuThreshold = adaptedThreshold
            return

        # Check deadline before continuing with scatter search
        if deadline > 0 and epochTime() > deadline:
            system.adaptedTabuThreshold = adaptedThreshold
            raise newException(TimeLimitExceededError, "Time limit exceeded")

        # Parallel tabu failed — continue with scatter search using collected results
        if pool.entries.len > 0:
            let actualWorkers = if numWorkers == 0: getOptimalWorkerCount() else: numWorkers
            if verbose:
                echo &"[Solve] Continuing with scatter search (pool size={pool.entries.len}, best cost={pool.minCost}, strategy={scatterStrategy}, adaptedThreshold={adaptedThreshold})"
                pool.poolStatistics()
            let improved = case scatterStrategy:
                of PathRelinking:
                    scatterImprove(system, pool, scatterThreshold, adaptedThreshold, adaptedThreshold, actualWorkers, verbose, deadline)
                of LNS:
                    lnsImprove(system, pool, scatterThreshold, adaptedThreshold, actualWorkers, verbose, deadline)
            # scatter/lns write final adaptedThreshold to system.adaptedTabuThreshold directly
            if improved:
                return

        if deadline > 0 and epochTime() > deadline:
            raise newException(TimeLimitExceededError, "Time limit exceeded")
        raise newException(NoSolutionFoundError, "Can't find satisfying solution with parallel search")
    else:
        var improved = system.baseArray.tabuImprove(tabuThreshold, verbose, deadline = deadline)
        if improved.cost == 0:
            system.initialize(improved.assignment)
            system.lastIterations = improved.iteration
            return
        if verbose:
            echo &"[Solve] Sequential failed: best cost={improved.cost}"
        if deadline > 0 and epochTime() > deadline:
            raise newException(TimeLimitExceededError, "Time limit exceeded")
        raise newException(NoSolutionFoundError, "Can't find satisfying solution")
