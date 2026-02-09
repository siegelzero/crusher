
import resolution
import ../expressions/expressions
import ../expressions/stateful
import ../constraintSystem

type
    OptimizationDirection* = enum
        Minimize, Maximize



template optimizeImpl(ObjectiveType: typedesc, direction: OptimizationDirection, procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: ObjectiveType[T],
                      parallel=true,
                      tabuThreshold=1000,
                      populationSize=8,
                      numWorkers=0,
                      verbose=false,
                      multiplier=2,
                      lowerBound=low(int),
                      upperBound=high(int),
                      ) =
        # Find initial solution
        system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                      populationSize=populationSize, numWorkers=numWorkers, verbose=verbose)
        objective.initialize(system.assignment)
        var currentCost = objective.value
        var currentTabuThreshold = max(system.lastIterations*multiplier, 1000)
        var hasBoundConstraint = false

        echo "Found initial solution with value ", currentCost

        # Binary search bounds
        when direction == Minimize:
            var lo = if lowerBound != low(int): lowerBound else: 0
            var hi = currentCost - 1
        else:
            var lo = currentCost + 1
            var hi = if upperBound != high(int): upperBound else: max(currentCost * 2, currentCost + 1)

        if verbose:
            echo "Initial iterations: ", system.lastIterations, ", next threshold: ", currentTabuThreshold
            echo "Binary search range: [", lo, ", ", hi, "]"

        while lo <= hi:
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
                echo "Trying target: ", target, " (range [", lo, ", ", hi, "])"

            # Use a capped threshold for probing to fail fast on infeasible targets
            let probeThreshold = min(currentTabuThreshold, tabuThreshold)

            try:
                system.resolve(
                    parallel=parallel,
                    tabuThreshold=probeThreshold,
                    populationSize=populationSize,
                    numWorkers=numWorkers,
                    verbose=verbose,
                )
                objective.initialize(system.assignment)
                currentCost = objective.value
                currentTabuThreshold = max(system.lastIterations * multiplier, 1000)
                echo "Found solution with objective ", objective.value
                if verbose:
                    echo "Iterations: ", system.lastIterations, ", next threshold: ", currentTabuThreshold
                when direction == Minimize:
                    hi = currentCost - 1
                else:
                    lo = currentCost + 1
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
        echo "Optimization complete. Final optimal value: ", objective.value

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
                      populationSize=32,
                      numWorkers=0,
                      verbose=false,
                      multiplier=6,
                      lowerBound=low(int),
                      upperBound=high(int),
                      ) =
        # Convert AlgebraicExpression to StatefulAlgebraicExpression
        let statefulObjective = newStatefulAlgebraicExpression(objective)

        # Forward all arguments to the template-generated function
        procName(system, statefulObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                populationSize=populationSize, numWorkers=numWorkers, verbose=verbose, multiplier=multiplier,
                lowerBound=lowerBound, upperBound=upperBound)

# Generate AlgebraicExpression wrappers
algebraicWrapper(minimize)
algebraicWrapper(maximize)
