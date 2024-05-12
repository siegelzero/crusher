import std/[strformat]

import resolution
import ../expressions/expression
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


proc minimize*[T](system: ConstraintSystem[T], objective: LinearCombination[T], parallel=true) =
    # Find initial solution
    system.resolve(parallel=parallel)
    objective.initialize(system.assignment)
    var currentCost = objective.value

    while true:
        system.addConstraint(objective < currentCost)

        try:
            system.resolve(parallel=parallel)
            objective.initialize(system.assignment)
            currentCost = objective.value
            echo fmt"Found solution with cost {currentCost}"
        except NoSolutionFoundError:
            return