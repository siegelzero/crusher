
import resolution
from std/times import epochTime
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
        # Find initial solution (if this times out, re-raise — no feasible solution)
        system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                      scatterThreshold=scatterThreshold,
                      populationSize=populationSize, numWorkers=numWorkers,
                      scatterStrategy=scatterStrategy, verbose=verbose,
                      deadline=deadline)
        objective.initialize(system.assignment)
        var currentCost = objective.value
        var hasBoundConstraint = false

        echo "[Opt] Initial solution: ", currentCost

        # Binary search bounds
        when direction == Minimize:
            var lo = if lowerBound != low(int): lowerBound else: 0
            var hi = currentCost - 1
        else:
            var lo = currentCost + 1
            var hi = if upperBound != high(int): upperBound else: max(currentCost * 2, currentCost + 1)

        if verbose:
            echo "[Opt] Binary search: [", lo, ", ", hi, "]"

        while lo <= hi:
            # Check deadline before each binary search iteration
            if deadline > 0 and epochTime() > deadline:
                system.searchCompleted = false
                break

            let bestSolution = system.assignment
            let target = lo + (hi - lo) div 2

            if hasBoundConstraint:
                system.removeLastConstraint()

            when direction == Minimize:
                system.addConstraint(objective <= target)
            else:
                system.addConstraint(objective >= target)
            hasBoundConstraint = true

            if verbose:
                echo "[Opt] Trying ", target, " [", lo, "..", hi, "]"

            try:
                system.resolve(
                    parallel=parallel,
                    tabuThreshold=tabuThreshold,
                    scatterThreshold=scatterThreshold,
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
                when direction == Minimize:
                    hi = currentCost - 1
                else:
                    lo = currentCost + 1
            except TimeLimitExceededError:
                # Time limit hit during optimization — keep best known solution
                system.searchCompleted = false
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                break
            except NoSolutionFoundError:
                when direction == Minimize:
                    lo = target + 1
                else:
                    hi = target - 1
                # Restore best known solution
                system.initialize(bestSolution)
                objective.initialize(system.assignment)

        # Clean up the bound constraint and restore best solution
        if hasBoundConstraint:
            system.removeLastConstraint()
        system.initialize(system.assignment)
        objective.initialize(system.assignment)
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
