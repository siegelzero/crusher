
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
                      populationSize=32,
                      numWorkers=0,
                      verbose=false,
                      multiplier=6,
                      ) =
        # Find initial solution
        system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                      populationSize=populationSize, numWorkers=numWorkers, verbose=verbose)
        objective.initialize(system.assignment)
        var currentCost = objective.value
        var currentTabuThreshold = max(system.lastIterations * multiplier, 1000)

        echo "Found initial solution with value ", currentCost
        if verbose:
            echo "Initial iterations: ", system.lastIterations, ", next threshold: ", currentTabuThreshold

        while true:
            # Store the best solution before attempting to find a better one
            let bestSolution = system.assignment

            when direction == Minimize:
                system.addConstraint(objective < currentCost)
            else:
                system.addConstraint(objective > currentCost)

            try:
                system.resolve(
                    parallel=parallel,
                    tabuThreshold=currentTabuThreshold,
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
            except NoSolutionFoundError:
                # Restore the best solution found so far and ensure objective state reflects it
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                echo "Optimization complete. Final optimal value: ", objective.value
                return

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
                      ) =
        # Convert AlgebraicExpression to StatefulAlgebraicExpression
        let statefulObjective = newStatefulAlgebraicExpression(objective)

        # Forward all arguments to the template-generated function
        procName(system, statefulObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                populationSize=populationSize, numWorkers=numWorkers, verbose=verbose, multiplier=multiplier)

# Generate AlgebraicExpression wrappers
algebraicWrapper(minimize)
algebraicWrapper(maximize)
