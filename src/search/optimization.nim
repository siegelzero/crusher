
import resolution
from std/times import epochTime
import std/packedsets
import ../constraints/[types, circuitTimeProp]

when compileOption("threads"):
    import parallelResolution

proc copyPackedSet(src: PackedSet[int]): PackedSet[int] =
    ## Force a deep copy of a PackedSet to avoid shared Trunk refs under ARC.
    ## Nim 2.2.6's PackedSet.=copy is buggy: it doesn't clear dest.head before
    ## rebuilding the linked list, causing old and new trunks to chain together.
    result = initPackedSet[int]()
    for item in src.items:
        result.incl(item)

const BoundFloor = low(int) div 2
const BoundCeil = high(int) div 2

proc safeLowerBound(v: int): int {.inline.} =
    ## Compute a heuristic lower bound well below v, without overflow.
    if v <= BoundFloor: v
    else: min(0, v - abs(v) - 1)

proc safeUpperBound(v: int): int {.inline.} =
    ## Compute a heuristic upper bound well above v, without overflow.
    if v >= BoundCeil: v
    else: max(0, v + abs(v) + 1)
import ../expressions/expressions
import ../expressions/stateful
import ../expressions/sumExpression
import ../expressions/weightedSameValue
import ../constraintSystem
import ../constrainedArray

type
    OptimizationDirection* = enum
        Minimize, Maximize



template optimizeImpl(ObjectiveType: typedesc, direction: OptimizationDirection, procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: ObjectiveType[T],
                      parallel=true,
                      tabuThreshold=1000,
                      scatterThreshold=1,
                      populationSize=0,  # 0 = auto: 2 * worker threads
                      numWorkers=0,
                      scatterStrategy: ScatterStrategy = PathRelinking,
                      verbose=false,
                      multiplier=2,  # deprecated, ignored
                      lowerBound=low(int),
                      upperBound=high(int),
                      deadline: float = 0.0,
                      ) =
        # Compute effective population size: 0 means auto-detect (2 * worker threads)
        let effectivePopSize = when compileOption("threads"):
            if populationSize > 0: populationSize
            else:
                let workers = if numWorkers > 0: numWorkers else: getOptimalWorkerCount()
                workers * 2
        else:
            if populationSize > 0: populationSize else: 8

        # Find initial feasible solution: single unified resolve with tabu + scatter fallback.
        # Tabu probe runs first; if it fails, scatter search continues from the tabu pool
        # without re-initialization.
        system.resolve(parallel=parallel, tabuThreshold=min(tabuThreshold, 1000),
                      scatterThreshold=max(scatterThreshold, 3),
                      populationSize=effectivePopSize, numWorkers=numWorkers,
                      scatterStrategy=scatterStrategy, verbose=verbose,
                      deadline=deadline)
        objective.initialize(system.assignment)
        var currentCost = objective.value
        var hasBoundConstraint = false
        system.hasFeasibleSolution = true
        system.bestAssignmentValid = false
        system.bestFeasibleAssignment = system.assignment
        system.bestAssignmentValid = true

        echo "[Opt] Initial solution: ", currentCost
        flushFile(stdout)

        # Add domain bounds as permanent constraints only when the initial solution
        # violates them. Adding trivially-satisfied bounds wastes per-iteration work
        # (full penalty map rebuilds at all positions on every move).
        block:
            var boundsViolated = false
            if upperBound != high(int) and currentCost > upperBound:
                boundsViolated = true
            if lowerBound != low(int) and currentCost < lowerBound:
                boundsViolated = true

            if boundsViolated:
                if upperBound != high(int):
                    system.addConstraint(objective <= upperBound)
                if lowerBound != low(int):
                    system.addConstraint(objective >= lowerBound)
                echo "[Opt] Objective ", currentCost, " outside domain [", lowerBound, "..", upperBound, "], constraining..."
                flushFile(stdout)
                system.hasFeasibleSolution = false
                let savedAssignment = system.assignment
                var domainResolved = false
                # Try parallel resolve with scatter search, retrying with fresh seeds.
                for attempt in 1..5:
                    if deadline > 0 and epochTime() > deadline:
                        raise newException(TimeLimitExceededError, "Time limit exceeded")
                    system.baseArray.reducedDomain = @[]  # Force recomputation
                    system.adaptedTabuThreshold = 0  # Use full threshold
                    try:
                        system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                                      scatterThreshold=max(scatterThreshold, 3),
                                      populationSize=effectivePopSize, numWorkers=numWorkers,
                                      scatterStrategy=scatterStrategy, verbose=verbose,
                                      deadline=deadline)
                        domainResolved = true
                        break
                    except NoSolutionFoundError:
                        if verbose:
                            echo "[Opt] Domain bound resolve attempt ", attempt, " failed"
                        flushFile(stdout)
                    except InfeasibleError:
                        raise
                if not domainResolved:
                    if verbose:
                        echo "[Opt] Trying sequential from saved assignment"
                        flushFile(stdout)
                    system.resolveFromAssignment(savedAssignment, tabuThreshold, verbose, deadline)
                objective.initialize(system.assignment)
                currentCost = objective.value
                system.hasFeasibleSolution = true
                echo "[Opt] Resolved within domain bounds: ", currentCost
                flushFile(stdout)

        # Cache the base reduced domain and fixed positions (after any domain bound constraints).
        # Subsequent iterations only change the search bound — no need to recompute.
        # Use copyPackedSet for PackedSet to work around Nim 2.2.6 =copy bug under ARC.
        let baseReducedDomain = system.baseArray.reducedDomain
        let baseFixedPositions = copyPackedSet(system.baseArray.fixedPositions)

        # Binary search bounds
        when direction == Minimize:
            var lo = if lowerBound != low(int): lowerBound else: safeLowerBound(currentCost)
            var hi = currentCost - 1
            # loProven is ONLY set by InfeasibleError from domain reduction — the sole
            # mechanism by which a local search solver can prove a lower bound. Domain
            # bounds from variable declarations are hints, not proofs.
            var loProven = false
            let domainLoBound = if lowerBound != low(int): lowerBound else: low(int)
        else:
            var lo = currentCost + 1
            var hi = if upperBound != high(int): upperBound else: safeUpperBound(currentCost)
            var hiProven = false
            let domainHiBound = if upperBound != high(int): upperBound else: high(int)

        # Phase 1: Binary search — fast tabu-only probes (no scatter)
        if verbose:
            echo "[Opt] Binary search [", lo, "..", hi, "]"
            flushFile(stdout)

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
            # Set objective bound on CircuitTimeProp constraints (if any)
            for c in system.baseArray.constraints:
                if c.stateType == CircuitTimePropType:
                    when direction == Minimize:
                        c.circuitTimePropState.setObjectiveBound(target)
                    else:
                        c.circuitTimePropState.clearObjectiveBound()
            system.baseArray.reducedDomain = baseReducedDomain
            system.baseArray.fixedPositions = copyPackedSet(baseFixedPositions)
            system.baseArray.tightenReducedDomain()

            if verbose:
                echo "[Opt] Trying ", target, " [", lo, "..", hi, "]"
                flushFile(stdout)

            if deadline > 0 and deadline - epochTime() < 5.0:
                system.searchCompleted = false
                break

            # Save constraints/fixedPositions before resolve (which may mutate them
            # via removeFixedConstraints) so the optimizer can still add/remove bounds
            let savedConstraints = system.baseArray.constraints
            let savedFixed = copyPackedSet(system.baseArray.fixedPositions)

            try:
                system.resolve(
                    parallel=parallel,
                    tabuThreshold=tabuThreshold,
                    scatterThreshold=0,
                    populationSize=effectivePopSize,
                    numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy,
                    verbose=verbose,
                    deadline=deadline,
                    seedAssignment=bestSolution,
                )
                objective.initialize(system.assignment)
                currentCost = objective.value
                # Validate: reject solutions that violate the original domain bound.
                # This catches cases where disconnected variable arrays allow the
                # solver to find zero-penalty assignments with infeasible objectives.
                # Only checks against the ORIGINAL domain bound (immutable), not the
                # dynamic binary search lo/hi which ratchets during no-solution rounds.
                when direction == Minimize:
                    if lowerBound != low(int) and currentCost < domainLoBound:
                        if verbose:
                            echo "[Opt] Rejected infeasible solution: ", currentCost, " < domain lower bound ", domainLoBound
                            flushFile(stdout)
                        system.initialize(bestSolution)
                        objective.initialize(system.assignment)
                        currentCost = objective.value
                        lo = target + 1
                        continue
                else:
                    if upperBound != high(int) and currentCost > domainHiBound:
                        if verbose:
                            echo "[Opt] Rejected infeasible solution: ", currentCost, " > domain upper bound ", domainHiBound
                            flushFile(stdout)
                        system.initialize(bestSolution)
                        objective.initialize(system.assignment)
                        currentCost = objective.value
                        hi = target - 1
                        continue
                system.bestAssignmentValid = false
                system.bestFeasibleAssignment = system.assignment
                system.bestAssignmentValid = true
                echo "[Opt] Improved: ", objective.value
                flushFile(stdout)
                if verbose:
                    echo "[Opt] iters=", system.lastIterations
                    flushFile(stdout)
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
                # Tabu-only couldn't find — break to retry with scatter search
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                break
            finally:
                system.baseArray.constraints = savedConstraints
                system.baseArray.fixedPositions = copyPackedSet(savedFixed)

        # Retry: binary search used fast tabu-only probes until first failure.
        # Now try to beat the current best with full scatter search, deepening threshold on each failure.
        var retryThreshold = tabuThreshold
        block retryLoop:
            while true:
                # Check if current cost is already at the known bound.
                # Only claim proven optimal if the bound was established by
                # InfeasibleError (domain reduction proof) or user-provided.
                when direction == Minimize:
                    # Proven optimal if: (a) domain reduction proved lo, or
                    # (b) current cost matches the domain lower bound (no feasible
                    # solution can exist below it by definition of the variable domain).
                    if currentCost <= lo and loProven:
                        system.optimalityProven = true
                        break retryLoop
                    elif domainLoBound != low(int) and currentCost <= domainLoBound:
                        system.optimalityProven = true
                        break retryLoop
                    elif currentCost <= lo:
                        lo = min(safeLowerBound(currentCost), safeLowerBound(lo))
                else:
                    if currentCost >= hi and hiProven:
                        system.optimalityProven = true
                        break retryLoop
                    elif domainHiBound != high(int) and currentCost >= domainHiBound:
                        system.optimalityProven = true
                        break retryLoop
                    elif currentCost >= hi:
                        hi = max(safeUpperBound(currentCost), safeUpperBound(hi))

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
                # Set objective bound on CircuitTimeProp constraints (retry loop)
                for c in system.baseArray.constraints:
                    if c.stateType == CircuitTimePropType:
                        when direction == Minimize:
                            c.circuitTimePropState.setObjectiveBound(currentCost - 1)
                        else:
                            c.circuitTimePropState.clearObjectiveBound()
                system.baseArray.reducedDomain = baseReducedDomain
                system.baseArray.fixedPositions = copyPackedSet(baseFixedPositions)
                system.baseArray.tightenReducedDomain()

                let savedConstraints2 = system.baseArray.constraints
                let savedFixed2 = copyPackedSet(system.baseArray.fixedPositions)

                try:
                    if verbose:
                        echo "[Opt] Retry targeting ", (when direction == Minimize: currentCost - 1 else: currentCost + 1)
                        flushFile(stdout)

                    system.resolve(
                        parallel=parallel,
                        tabuThreshold=retryThreshold,
                        scatterThreshold=scatterThreshold,
                        populationSize=effectivePopSize,
                        numWorkers=numWorkers,
                        scatterStrategy=scatterStrategy,
                        verbose=verbose,
                        deadline=deadline,
                        seedAssignment=bestSolution,
                    )
                    objective.initialize(system.assignment)
                    currentCost = objective.value
                    # Reject solutions that violate the domain bound
                    # Reject solutions that violate the domain bound.
                    # Note: constraint/fixedPositions restore is handled by the finally block.
                    when direction == Minimize:
                        if domainLoBound != low(int) and currentCost < domainLoBound:
                            if verbose:
                                echo "[Opt] Rejected infeasible retry solution: ", currentCost, " < domain bound ", domainLoBound
                                flushFile(stdout)
                            system.initialize(bestSolution)
                            objective.initialize(system.assignment)
                            currentCost = objective.value
                            retryThreshold = min(retryThreshold + retryThreshold div 2, 100_000)
                            continue
                    else:
                        if domainHiBound != high(int) and currentCost > domainHiBound:
                            if verbose:
                                echo "[Opt] Rejected infeasible retry solution: ", currentCost, " > domain bound ", domainHiBound
                                flushFile(stdout)
                            system.initialize(bestSolution)
                            objective.initialize(system.assignment)
                            currentCost = objective.value
                            retryThreshold = min(retryThreshold + retryThreshold div 2, 100_000)
                            continue
                    system.bestAssignmentValid = false
                    system.bestFeasibleAssignment = system.assignment
                    system.bestAssignmentValid = true
                    echo "[Opt] Retry improved: ", currentCost
                    flushFile(stdout)
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
                        flushFile(stdout)
                    if deadline > 0 and epochTime() < deadline:
                        continue
                    break retryLoop
                finally:
                    system.baseArray.constraints = savedConstraints2
                    system.baseArray.fixedPositions = copyPackedSet(savedFixed2)

        # Clean up the bound constraint and restore best solution
        if hasBoundConstraint:
            system.removeLastConstraint()
        system.initialize(system.assignment)
        objective.initialize(system.assignment)
        if system.optimalityProven:
            echo "[Opt] Proven optimal: ", objective.value
        else:
            echo "[Opt] Done: ", objective.value
        flushFile(stdout)

# Generate minimize and maximize procedures for all stateful expression types
optimizeImpl(SumExpression, Minimize, minimize)
optimizeImpl(MinExpression, Minimize, minimize)
optimizeImpl(MaxExpression, Minimize, minimize)
optimizeImpl(StatefulAlgebraicExpression, Minimize, minimize)

optimizeImpl(SumExpression, Maximize, maximize)
optimizeImpl(MinExpression, Maximize, maximize)
optimizeImpl(MaxExpression, Maximize, maximize)
optimizeImpl(StatefulAlgebraicExpression, Maximize, maximize)

optimizeImpl(WeightedSameValueExpression, Minimize, minimize)
optimizeImpl(WeightedSameValueExpression, Maximize, maximize)

# Template for AlgebraicExpression wrappers - convert to StatefulAlgebraicExpression
template algebraicWrapper(procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: AlgebraicExpression[T],
                      parallel=true,
                      tabuThreshold=1000,
                      scatterThreshold=1,
                      populationSize=0,  # 0 = auto: 2 * worker threads
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
