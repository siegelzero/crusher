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
                deadline: float = 0.0,
                seedAssignment: seq[T] = @[]) =
    # Detect element constraints that form inverse channel patterns
    system.baseArray.detectElementInverseChannels()

    # Compute reduced domain once and cache it
    if system.baseArray.reducedDomain.len == 0:
        let drStart = epochTime()
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain
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
    var nEmptyRestored = 0
    for pos in system.baseArray.allPositions():
        if system.baseArray.reducedDomain[pos].len == 0:
            if system.baseArray.domain[pos].len == 0:
                # Truly empty domain (even before reduction) — genuinely infeasible
                raise newException(InfeasibleError, "Domain reduction found infeasibility")
            else:
                # Domain reduction over-pruned this position — restore its original domain
                # but keep valid reductions for other positions
                if verbose:
                    echo &"[Solve] Empty domain at position {pos} (original domain size: {system.baseArray.domain[pos].len}), restoring"
                system.baseArray.reducedDomain[pos] = system.baseArray.domain[pos]
                inc nEmptyRestored
    if nEmptyRestored > 0 and verbose:
        echo &"[Solve] Restored {nEmptyRestored} over-pruned positions (keeping reductions for remaining positions)"

    # Remove constraints where all positions are fixed (singleton domain) or channel
    let constraintsBefore = system.baseArray.constraints.len
    system.baseArray.removeFixedConstraints()
    if verbose and system.baseArray.fixedPositions.len > 0:
        let removed = constraintsBefore - system.baseArray.constraints.len
        echo &"[Solve] Fixed positions: {system.baseArray.fixedPositions.len}, removed {removed} all-fixed constraints (of {constraintsBefore})"

    # Shrink channel position domains to avoid expensive deepCopy of million-element seqs.
    # Channel positions are never searched; for domain reduction only min/max are needed.
    # Use reducedDomain (the search-facing domain) as the shrunk version — it's already
    # created as @[first_value] for skipped positions. Keep the original domain intact
    # so bounds propagation can use the correct endpoints on subsequent optimization probes.
    # Note: reducedDomain is what gets deepCopied for each parallel state, not domain.

    if parallel:
        # Use persisted adapted threshold if available, otherwise caller's value
        let effectiveThreshold = if system.adaptedTabuThreshold > 0: system.adaptedTabuThreshold
                                 else: tabuThreshold
        if verbose and effectiveThreshold != tabuThreshold:
            echo &"[Solve] Using adapted threshold: {effectiveThreshold} (original: {tabuThreshold})"
        var pool: CandidatePool[T]
        var adaptedThreshold = effectiveThreshold
        if parallelResolve(system, populationSize, numWorkers, effectiveThreshold, verbose, pool, deadline, adaptedThreshold, seedAssignment):
            system.adaptedTabuThreshold = adaptedThreshold
            system.hasFeasibleSolution = true
            return

        # Check deadline before continuing with scatter search
        if deadline > 0 and epochTime() > deadline:
            system.adaptedTabuThreshold = adaptedThreshold
            raise newException(TimeLimitExceededError, "Time limit exceeded")

        # Parallel tabu failed — continue with scatter search using collected results
        if pool.entries.len > 0 and scatterThreshold > 0:
            let actualWorkers = if numWorkers == 0: getOptimalWorkerCount() else: numWorkers
            if verbose:
                echo &"[Solve] Continuing with scatter search (pool size={pool.entries.len}, best cost={pool.minCost}, strategy={scatterStrategy}, adaptedThreshold={adaptedThreshold})"
                flushFile(stdout)
                pool.poolStatistics()
            let improved = case scatterStrategy:
                of PathRelinking:
                    scatterImprove(system, pool, scatterThreshold, adaptedThreshold, adaptedThreshold, actualWorkers, verbose, deadline)
                of LNS:
                    lnsImprove(system, pool, scatterThreshold, adaptedThreshold, actualWorkers, verbose, deadline)
            # scatter/lns write final adaptedThreshold to system.adaptedTabuThreshold directly
            if improved:
                system.hasFeasibleSolution = true
                return

        if deadline > 0 and epochTime() > deadline:
            raise newException(TimeLimitExceededError, "Time limit exceeded")
        raise newException(NoSolutionFoundError, "Can't find satisfying solution with parallel search")
    else:
        var improved = system.baseArray.tabuImprove(tabuThreshold, verbose, deadline = deadline)
        if improved.bestCost == 0:
            system.initialize(improved.bestAssignment)
            system.lastIterations = improved.iteration
            system.hasFeasibleSolution = true
            return
        if verbose:
            echo &"[Solve] Sequential failed: best cost={improved.bestCost}"
        if deadline > 0 and epochTime() > deadline:
            raise newException(TimeLimitExceededError, "Time limit exceeded")
        raise newException(NoSolutionFoundError, "Can't find satisfying solution")

proc resolveFromAssignment*[T](system: ConstraintSystem[T],
                                assignment: seq[T],
                                tabuThreshold: int,
                                verbose: bool = false,
                                deadline: float = 0.0) =
    ## Sequential tabu search from a given starting assignment.
    ## Used by the optimizer when domain bound constraints are added after
    ## an initial feasible solution is found.
    ## Note: skips detectElementInverseChannels — already called by the
    ## initial resolve() before the optimizer adds bound constraints.
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain
    for pos in system.baseArray.allPositions():
        if system.baseArray.reducedDomain[pos].len == 0:
            raise newException(InfeasibleError, "Domain reduction found infeasibility")
    system.baseArray.removeFixedConstraints()
    var state = newTabuState[T](system.baseArray, assignment, verbose)
    let improved = state.tabuImprove(tabuThreshold, deadline = deadline)
    if improved.bestCost == 0:
        system.initialize(improved.bestAssignment)
        system.lastIterations = improved.iteration
        return
    if verbose:
        echo &"[Solve] Sequential from assignment failed: best cost={improved.bestCost}"
    if deadline > 0 and epochTime() > deadline:
        raise newException(TimeLimitExceededError, "Time limit exceeded")
    raise newException(NoSolutionFoundError, "Can't find satisfying solution from given assignment")
