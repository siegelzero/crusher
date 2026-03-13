
import resolution
from std/times import epochTime
from std/math import ceil
import std/packedsets

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
                                      populationSize=populationSize, numWorkers=numWorkers,
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
            var loProven = lowerBound != low(int)  # only proven if user-provided or domain-derived
        else:
            var lo = currentCost + 1
            var hi = if upperBound != high(int): upperBound else: safeUpperBound(currentCost)
            var hiProven = upperBound != high(int)  # user-provided bound is trusted

        # Adaptive binary search with escalating solve effort
        if verbose:
            echo "[Opt] Binary search [", lo, "..", hi, "]"
            flushFile(stdout)

        while lo <= hi:
            if deadline > 0 and epochTime() > deadline:
                system.searchCompleted = false
                break

            # Check if current cost is already at the proven bound
            when direction == Minimize:
                if currentCost <= lo and loProven:
                    system.optimalityProven = true
                    break
                elif currentCost <= lo:
                    # lo was heuristic — lower it conservatively
                    lo = max(lowerBound, currentCost div 2)
                    if lo > hi: break
            else:
                if currentCost >= hi and hiProven:
                    system.optimalityProven = true
                    break
                elif currentCost >= hi:
                    hi = currentCost + currentCost div 2
                    if lo > hi: break

            let bestSolution = system.assignment
            let target = lo + (hi - lo) div 2

            if hasBoundConstraint:
                system.removeLastConstraint()

            when direction == Minimize:
                system.addConstraint(objective <= target)
            else:
                system.addConstraint(objective >= target)
            hasBoundConstraint = true
            system.baseArray.reducedDomain = baseReducedDomain
            system.baseArray.fixedPositions = copyPackedSet(baseFixedPositions)
            system.baseArray.tightenReducedDomain()

            let remaining = if deadline > 0: deadline - epochTime() else: 120.0
            if remaining < 5.0:
                system.searchCompleted = false
                break

            if verbose:
                echo "[Opt] Trying ", target, " [", lo, "..", hi, "] (", int(remaining), "s left)"
                flushFile(stdout)

            let savedConstraints = system.baseArray.constraints
            let savedFixed = copyPackedSet(system.baseArray.fixedPositions)

            var probeSucceeded = false
            var probeInfeasible = false

            # Phase 1: Quick tabu-only probe
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
                probeSucceeded = true
            except TimeLimitExceededError:
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                system.searchCompleted = false
                break
            except InfeasibleError:
                probeInfeasible = true
            except NoSolutionFoundError:
                discard
            finally:
                system.baseArray.constraints = savedConstraints
                system.baseArray.fixedPositions = copyPackedSet(savedFixed)

            # Phase 2: If tabu failed, try scatter with fixed budget
            if not probeSucceeded and not probeInfeasible:
                let remaining2 = if deadline > 0: deadline - epochTime() else: 120.0
                if remaining2 >= 15.0:
                    # Fixed 30s budget, but no more than 60% of remaining time
                    let probeBudget = min(30.0, remaining2 * 0.6)
                    let probeDeadline = if deadline > 0:
                            epochTime() + probeBudget
                        else: 0.0
                    if verbose:
                        echo "[Opt] Scatter retry (budget: ", int(probeBudget), "s)"
                        flushFile(stdout)
                    let savedConstraints2 = system.baseArray.constraints
                    let savedFixed2 = copyPackedSet(system.baseArray.fixedPositions)
                    try:
                        system.resolve(
                            parallel=parallel,
                            tabuThreshold=tabuThreshold,
                            scatterThreshold=scatterThreshold,
                            populationSize=populationSize,
                            numWorkers=numWorkers,
                            scatterStrategy=scatterStrategy,
                            verbose=verbose,
                            deadline=probeDeadline,
                        )
                        probeSucceeded = true
                    except TimeLimitExceededError:
                        discard  # used up probe budget, continue to next target
                    except InfeasibleError:
                        probeInfeasible = true
                    except NoSolutionFoundError:
                        discard
                    finally:
                        system.baseArray.constraints = savedConstraints2
                        system.baseArray.fixedPositions = copyPackedSet(savedFixed2)

            if probeSucceeded:
                objective.initialize(system.assignment)
                currentCost = objective.value
                system.bestAssignmentValid = false
                system.bestFeasibleAssignment = system.assignment
                system.bestAssignmentValid = true
                echo "[Opt] Improved: ", objective.value
                flushFile(stdout)
                if verbose:
                    echo "[Opt] iters=", system.lastIterations
                    flushFile(stdout)
                when direction == Minimize:
                    hi = currentCost - 1
                    # If the new cost is below lo (which was heuristic), reset lo
                    if currentCost < lo and not loProven:
                        lo = max(lowerBound, currentCost div 2)
                else:
                    lo = currentCost + 1
                    if currentCost > hi and not hiProven:
                        hi = currentCost + currentCost div 2
            elif probeInfeasible:
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                when direction == Minimize:
                    lo = target + 1
                    loProven = true
                else:
                    hi = target - 1
                    hiProven = true
            else:
                # Both tabu and scatter failed — narrow range and continue
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                when direction == Minimize:
                    lo = target + 1
                    loProven = false
                else:
                    hi = target - 1
                    hiProven = false

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
