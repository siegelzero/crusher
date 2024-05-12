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
    var vObjective = objective
    echo "Hello"
    system.resolve(parallel=parallel)
    vObjective.initialize(system.assignment)
    var currentCost = vObjective.value
    echo fmt"Found solution with cost {currentCost}"

    while true:
        system.addConstraint(vObjective < currentCost)

        try:
            system.resolve(parallel=parallel)
            vObjective.initialize(system.assignment)
            currentCost = vObjective.value
            echo fmt"Found solution with cost {currentCost}"
        except NoSolutionFoundError:
            return