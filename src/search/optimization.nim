
import resolution
from std/times import epochTime
from std/math import ceil
import ../expressions/expressions
import ../expressions/stateful
import ../expressions/sumExpression
import ../constraintSystem

type
    OptimizationDirection* = enum
        Minimize, Maximize



template optimizeImpl(ObjectiveType: typedesc, direction: OptimizationDirection, procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: ObjectiveType[T],
                      parallel=true,
                      tabuThreshold=1000,
                      scatterThreshold=1,
                      populationSize=8,
                      numWorkers=0,
                      scatterStrategy: ScatterStrategy = PathRelinking,
                      verbose=false,
                      multiplier=2,  # deprecated, ignored
                      lowerBound=low(int),
                      upperBound=high(int),
                      deadline: float = 0.0,
                      ) =
        # Find initial feasible solution: tabu-only first (fast, capped at 1000), scatter fallback
        try:
            system.resolve(parallel=parallel, tabuThreshold=min(tabuThreshold, 1000),
                          scatterThreshold=0,
                          populationSize=populationSize, numWorkers=numWorkers,
                          scatterStrategy=scatterStrategy, verbose=verbose,
                          deadline=deadline)
        except NoSolutionFoundError:
            if verbose:
                echo "[Opt] Tabu probe failed, retrying with scatter search"
            system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                          scatterThreshold=scatterThreshold,
                          populationSize=populationSize, numWorkers=numWorkers,
                          scatterStrategy=scatterStrategy, verbose=verbose,
                          deadline=deadline)
        objective.initialize(system.assignment)
        var currentCost = objective.value
        var hasBoundConstraint = false
        system.hasFeasibleSolution = true

        echo "[Opt] Initial solution: ", currentCost

        # Add domain bounds as permanent constraints (from FZN translator) and re-resolve
        # if the initial solution violates them. Both bounds are added together so the
        # solver sees the full feasible band at once.
        block:
            var boundsViolated = false
            if upperBound != high(int):
                system.addConstraint(objective <= upperBound)
                if currentCost > upperBound:
                    boundsViolated = true
            if lowerBound != low(int):
                system.addConstraint(objective >= lowerBound)
                if currentCost < lowerBound:
                    boundsViolated = true

            if boundsViolated:
                echo "[Opt] Objective ", currentCost, " outside domain [", lowerBound, "..", upperBound, "], constraining..."
                system.hasFeasibleSolution = false
                let savedAssignment = system.assignment
                var domainResolved = false
                # Try parallel resolve with scatter search, retrying with fresh seeds.
                # Don't pass internal deadline — let scatter stop at its stale limit
                # so each attempt completes quickly (~0.5-1s) for fresh restarts.
                for attempt in 1..5:
                    if deadline > 0 and epochTime() > deadline:
                        raise newException(TimeLimitExceededError, "Time limit exceeded")
                    system.baseArray.reducedDomain = @[]  # Force recomputation
                    system.adaptedTabuThreshold = 0  # Use full threshold
                    try:
                        system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                                      scatterThreshold=max(scatterThreshold, 3),
                                      populationSize=populationSize, numWorkers=numWorkers,
                                      scatterStrategy=scatterStrategy, verbose=verbose,
                                      deadline=0.0)
                        domainResolved = true
                        break
                    except NoSolutionFoundError:
                        if verbose:
                            echo "[Opt] Domain bound resolve attempt ", attempt, " failed"
                    except InfeasibleError:
                        raise
                if not domainResolved:
                    if verbose:
                        echo "[Opt] Trying sequential from saved assignment"
                    system.resolveFromAssignment(savedAssignment, tabuThreshold, verbose, deadline)
                objective.initialize(system.assignment)
                currentCost = objective.value
                system.hasFeasibleSolution = true
                echo "[Opt] Resolved within domain bounds: ", currentCost

        # Cache the base reduced domain (after any domain bound constraints).
        # Subsequent iterations only change the search bound — no need to recompute.
        let baseReducedDomain = system.baseArray.reducedDomain

        # Binary search bounds
        when direction == Minimize:
            var lo = if lowerBound != low(int): lowerBound else: 0
            var hi = currentCost - 1
            var loProven = true  # 0 is a genuine lower bound; user-provided also trusted
        else:
            var lo = currentCost + 1
            var hi = if upperBound != high(int): upperBound else: max(currentCost * 2, currentCost + 1)
            var hiProven = upperBound != high(int)  # user-provided bound is trusted

        # Phase 1: Binary search — fast tabu-only probes (no scatter)
        if verbose:
            echo "[Opt] Binary search [", lo, "..", hi, "]"

        while lo <= hi:
            if deadline > 0 and epochTime() > deadline:
                system.searchCompleted = false
                break

            let bestSolution = system.assignment
            # Binary search: try the midpoint
            let target = lo + (hi - lo) div 2

            if hasBoundConstraint:
                system.removeLastConstraint()

            when direction == Minimize:
                system.addConstraint(objective <= target)
            else:
                system.addConstraint(objective >= target)
            hasBoundConstraint = true
            system.baseArray.reducedDomain = baseReducedDomain

            if verbose:
                echo "[Opt] Trying ", target, " [", lo, "..", hi, "]"

            if deadline > 0 and deadline - epochTime() < 5.0:
                system.searchCompleted = false
                break

            try:
                system.resolve(
                    parallel=parallel,
                    tabuThreshold=tabuThreshold,
                    scatterThreshold=0,
                    populationSize=populationSize,
                    numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy,
                    verbose=verbose,
                    deadline=deadline,
                )
                objective.initialize(system.assignment)
                currentCost = objective.value
                echo "[Opt] Improved: ", objective.value
                if verbose:
                    echo "[Opt] iters=", system.lastIterations
                # Found solution at value currentCost — narrow toward better
                when direction == Minimize:
                    hi = currentCost - 1
                else:
                    lo = currentCost + 1
            except TimeLimitExceededError:
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                system.searchCompleted = false
                break
            except InfeasibleError:
                # Domain reduction proved no solution at this bound — narrow range
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                when direction == Minimize:
                    lo = target + 1
                    loProven = true
                else:
                    hi = target - 1
                    hiProven = true
            except NoSolutionFoundError:
                # Tabu-only couldn't find this target — stop binary search,
                # fall through to retry loop which uses scatter search
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                break

        # Retry: binary search used fast tabu-only probes until first failure.
        # Now try to beat the current best with full scatter search, deepening threshold on each failure.
        var retryThreshold = tabuThreshold
        block retryLoop:
            while true:
                # Check if current cost is already at the known bound.
                # Only claim proven optimal if the bound was established by
                # InfeasibleError (domain reduction proof) or user-provided.
                when direction == Minimize:
                    if currentCost <= lo:
                        if loProven:
                            system.optimalityProven = true
                        break retryLoop
                else:
                    if currentCost >= hi:
                        if hiProven:
                            system.optimalityProven = true
                            break retryLoop
                        else:
                            # hi was a heuristic guess — raise it and keep searching
                            hi = max(currentCost * 2, currentCost + 1)

                if deadline > 0 and epochTime() > deadline:
                    system.searchCompleted = false
                    break retryLoop

                let bestSolution = system.assignment
                if hasBoundConstraint:
                    system.removeLastConstraint()

                when direction == Minimize:
                    system.addConstraint(objective <= currentCost - 1)
                else:
                    system.addConstraint(objective >= currentCost + 1)
                hasBoundConstraint = true
                system.baseArray.reducedDomain = baseReducedDomain

                try:
                    system.resolve(
                        parallel=parallel,
                        tabuThreshold=retryThreshold,
                        scatterThreshold=scatterThreshold,
                        populationSize=populationSize,
                        numWorkers=numWorkers,
                        scatterStrategy=scatterStrategy,
                        verbose=verbose,
                        deadline=deadline,
                    )
                    objective.initialize(system.assignment)
                    currentCost = objective.value
                    echo "[Opt] Retry improved: ", currentCost
                    retryThreshold = tabuThreshold  # reset on success
                except TimeLimitExceededError:
                    system.initialize(bestSolution)
                    objective.initialize(system.assignment)
                    system.searchCompleted = false
                    break retryLoop
                except InfeasibleError:
                    # Domain reduction proved no better solution exists — provably optimal
                    system.optimalityProven = true
                    system.initialize(bestSolution)
                    objective.initialize(system.assignment)
                    break retryLoop
                except NoSolutionFoundError:
                    system.initialize(bestSolution)
                    objective.initialize(system.assignment)
                    retryThreshold = retryThreshold * 2
                    system.adaptedTabuThreshold = 0  # force using bumped threshold
                    if verbose:
                        echo "[Opt] Retry deepening threshold to ", retryThreshold
                    if deadline > 0 and epochTime() < deadline:
                        continue
                    break retryLoop

        # Clean up the bound constraint and restore best solution
        if hasBoundConstraint:
            system.removeLastConstraint()
        system.initialize(system.assignment)
        objective.initialize(system.assignment)
        if system.optimalityProven:
            echo "[Opt] Proven optimal: ", objective.value
        else:
            echo "[Opt] Done: ", objective.value

# Generate minimize and maximize procedures for all stateful expression types
optimizeImpl(SumExpression, Minimize, minimize)
optimizeImpl(MinExpression, Minimize, minimize)
optimizeImpl(MaxExpression, Minimize, minimize)
optimizeImpl(StatefulAlgebraicExpression, Minimize, minimize)

optimizeImpl(SumExpression, Maximize, maximize)
optimizeImpl(MinExpression, Maximize, maximize)
optimizeImpl(MaxExpression, Maximize, maximize)
optimizeImpl(StatefulAlgebraicExpression, Maximize, maximize)

# Template for AlgebraicExpression wrappers - convert to StatefulAlgebraicExpression
template algebraicWrapper(procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: AlgebraicExpression[T],
                      parallel=true,
                      tabuThreshold=1000,
                      scatterThreshold=1,
                      populationSize=32,
                      numWorkers=0,
                      scatterStrategy: ScatterStrategy = PathRelinking,
                      verbose=false,
                      multiplier=6,  # deprecated, ignored
                      lowerBound=low(int),
                      upperBound=high(int),
                      deadline: float = 0.0,
                      ) =
        if objective.linear:
            # Automatically linearize for O(1) incremental updates
            let linearizedObjective = linearize(objective)
            procName(system, linearizedObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                    scatterThreshold=scatterThreshold,
                    populationSize=populationSize, numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy, verbose=verbose,
                    lowerBound=lowerBound, upperBound=upperBound,
                    deadline=deadline)
        else:
            let statefulObjective = newStatefulAlgebraicExpression(objective)
            procName(system, statefulObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                    scatterThreshold=scatterThreshold,
                    populationSize=populationSize, numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy, verbose=verbose,
                    lowerBound=lowerBound, upperBound=upperBound,
                    deadline=deadline)

# Generate AlgebraicExpression wrappers
algebraicWrapper(minimize)
algebraicWrapper(maximize)
