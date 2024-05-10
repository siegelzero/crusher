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


proc minimize*[T](system: ConstraintSystem[T], objective: LinearCombination[T]) =
    # Find initial solution
    var vObjective = objective
    system.resolve()
    vObjective.initialize(system.assignment)
    var currentCost = vObjective.value
    echo fmt"Found solution with cost {currentCost}"

    while true:
        system.addConstraint(vObjective < currentCost)

        try:
            system.resolve()
            vObjective.initialize(system.assignment)
            currentCost = vObjective.value
            echo fmt"Found solution with cost {currentCost}"
        except NoSolutionFoundError:
            return