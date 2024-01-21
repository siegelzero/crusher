import std/[strformat]

import resolution
import ../constraints/constraint
import ../expressions/expression
import ../constraintSystem


proc minimize*[T](system: ConstraintSystem[T], objective: Expression[T]): seq[T] =
    # Find initial solution
    system.resolve()
    var currentCost = objective.evaluate(system.assignment)
    var bestAssignment = system.assignment
    echo fmt"Found solution {currentCost} with assignment {bestAssignment}"

    while true:
        system.addConstraint(objective < currentCost)
        try:
            system.resolve()
            currentCost = objective.evaluate(system.assignment)
            bestAssignment = system.assignment
            echo fmt"Found solution {currentCost} with assignment {system.assignment}"
        except NoSolutionFoundError:
            break
    
    return bestAssignment