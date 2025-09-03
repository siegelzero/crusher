import std/[strformat]

import resolution
import ../expressions
import ../constraintSystem


proc minimize*[T](system: ConstraintSystem[T], 
                  objective: AlgebraicExpression[T],
                  tabuThreshold=1000,
                  maxAttempts=5,
                  attemptThreshold=3,
                  parallel=true,
                  verbose=false) =
    # Find initial solution
    system.resolve(
        tabuThreshold=tabuThreshold,
        maxAttempts=maxAttempts,
        attemptThreshold=attemptThreshold,
        parallel=parallel,
        verbose=verbose
    )
    var currentCost = objective.evaluate(system.assignment)
    if verbose:
        echo fmt"Found initial solution with objective value: {currentCost}"

    while true:
        if verbose:
            echo fmt"Adding constraint: objective < {currentCost}"
        system.addConstraint(objective < currentCost)
        try:
            system.resolve(
                tabuThreshold=tabuThreshold,
                maxAttempts=maxAttempts,
                attemptThreshold=attemptThreshold,
                parallel=parallel,
                verbose=verbose
            )
            currentCost = objective.evaluate(system.assignment)
            if verbose:
                echo fmt"Found better solution with objective value: {currentCost}"
        except NoSolutionFoundError:
            return


proc minimize*[T](system: ConstraintSystem[T],
                  objective: LinearCombination[T],
                  tabuThreshold=1000,
                  maxAttempts=5,
                  attemptThreshold=3,
                  parallel=true,
                  verbose=false) =
    # Find initial solution
    system.resolve(
        tabuThreshold=tabuThreshold,
        maxAttempts=maxAttempts,
        attemptThreshold=attemptThreshold,
        parallel=parallel,
        verbose=verbose
    )
    objective.initialize(system.assignment)
    var currentCost = objective.value

    if verbose:
        echo fmt"Found initial solution with objective value: {currentCost}"

    while true:
        if verbose:
            echo fmt"Adding constraint: objective < {currentCost}"
        system.addConstraint(objective < currentCost)

        try:
            system.resolve(
                tabuThreshold=tabuThreshold,
                maxAttempts=maxAttempts,
                attemptThreshold=attemptThreshold,
                parallel=parallel,
                verbose=verbose
            )
            objective.initialize(system.assignment)
            currentCost = objective.value
            if verbose:
                echo fmt"Found better solution with objective value: {currentCost}"
        except NoSolutionFoundError:
            return


proc maximize*[T](system: ConstraintSystem[T], 
                  objective: AlgebraicExpression[T],
                  tabuThreshold=1000,
                  maxAttempts=5,
                  attemptThreshold=3,
                  parallel=true,
                  verbose=false) =
    # Find initial solution
    system.resolve(
        tabuThreshold=tabuThreshold,
        maxAttempts=maxAttempts,
        attemptThreshold=attemptThreshold,
        parallel=parallel,
        verbose=verbose
    )
    var currentCost = objective.evaluate(system.assignment)
    if verbose:
        echo fmt"Found initial solution with objective value: {currentCost}"

    while true:
        if verbose:
            echo fmt"Adding constraint: objective > {currentCost}"
        system.addConstraint(objective > currentCost)
        try:
            system.resolve(
                tabuThreshold=tabuThreshold,
                maxAttempts=maxAttempts,
                attemptThreshold=attemptThreshold,
                parallel=parallel,
                verbose=verbose
            )
            currentCost = objective.evaluate(system.assignment)
            if verbose:
                echo fmt"Found better solution with objective value: {currentCost}"
        except NoSolutionFoundError:
            return


proc maximize*[T](system: ConstraintSystem[T],
                  objective: LinearCombination[T],
                  tabuThreshold=1000,
                  maxAttempts=5,
                  attemptThreshold=3,
                  parallel=true,
                  verbose=false) =
    # Find initial solution
    system.resolve(
        tabuThreshold=tabuThreshold,
        maxAttempts=maxAttempts,
        attemptThreshold=attemptThreshold,
        parallel=parallel,
        verbose=verbose
    )
    objective.initialize(system.assignment)
    var currentCost = objective.value

    if verbose:
        echo fmt"Found initial solution with objective value: {currentCost}"

    while true:
        if verbose:
            echo fmt"Adding constraint: objective > {currentCost}"
        system.addConstraint(objective > currentCost)

        try:
            system.resolve(
                tabuThreshold=tabuThreshold,
                maxAttempts=maxAttempts,
                attemptThreshold=attemptThreshold,
                parallel=parallel,
                verbose=verbose
            )
            objective.initialize(system.assignment)
            currentCost = objective.value
            if verbose:
                echo fmt"Found better solution with objective value: {currentCost}"
        except NoSolutionFoundError:
            return