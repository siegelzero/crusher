import std/[strformat]

import resolution
import ../expressions/expressions
import ../constraintSystem


proc minimize*[T](system: ConstraintSystem[T], objective: AlgebraicExpression[T]) =
    # Find initial solution
    system.resolve()
    var currentCost = objective.evaluate(system.assignment)
    echo fmt"Found solution with cost {currentCost}"

    while true:
        system.addConstraint(objective < currentCost)
        try:
            system.resolve()
            currentCost = objective.evaluate(system.assignment)
            echo fmt"Found solution with cost {currentCost}"
        except NoSolutionFoundError:
            return


proc minimize*[T](system: ConstraintSystem[T],
                  objective: SumExpression[T],
                  parallel=true,
                  tabuThreshold=1000,
                  maxAttempts=10,
                  attemptThreshold=10,
                  ) =
    # Find initial solution
    system.resolve(parallel=parallel)
    objective.initialize(system.assignment)
    var currentCost = objective.value

    echo fmt"Found initial solution with value {currentCost}"

    while true:
        system.addConstraint(objective < currentCost)

        try:
            system.resolve(
                parallel=parallel,
                tabuThreshold=tabuThreshold,
                maxAttempts=maxAttempts,
                attemptThreshold=attemptThreshold,
            )
            objective.initialize(system.assignment)
            currentCost = objective.value
            echo fmt"Found solution with objective {objective.value}"
        except NoSolutionFoundError:
            # Ensure objective state reflects the final best solution
            objective.initialize(system.assignment)
            return