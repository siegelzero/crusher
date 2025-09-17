
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
                      ) =
        # Find initial solution
        system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                      populationSize=populationSize, numWorkers=numWorkers, verbose=verbose)
        objective.initialize(system.assignment)
        var currentCost = objective.value

        echo "Found initial solution with value ", currentCost

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
                    tabuThreshold=tabuThreshold,
                    populationSize=populationSize,
                    numWorkers=numWorkers,
                    verbose=verbose,
                )
                objective.initialize(system.assignment)
                currentCost = objective.value
                echo "Found solution with objective ", objective.value
            except NoSolutionFoundError:
                # Restore the best solution found so far and ensure objective state reflects it
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
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
                      ) =
        # Convert AlgebraicExpression to StatefulAlgebraicExpression
        let statefulObjective = newStatefulAlgebraicExpression(objective)

        # Forward all arguments to the template-generated function
        procName(system, statefulObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                populationSize=populationSize, numWorkers=numWorkers, verbose=verbose)

# Generate AlgebraicExpression wrappers
algebraicWrapper(minimize)
algebraicWrapper(maximize)
