import std/[os, strformat, cpuinfo]

import heuristics, tabuSearch
import ../constraintSystem
import parallelResolutionWorking


type NoSolutionFoundError* = object of CatchableError


proc getOptimalWorkerCount(): int =
    ## Determine optimal number of workers based on CPU characteristics
    let cpuCount = countProcessors()
    # Use all logical cores but cap at reasonable maximum for constraint solving
    # Leave one core free for system/coordination tasks
    result = max(1, min(cpuCount - 1, 16))
    echo fmt"Detected {cpuCount} CPU cores, using {result} workers"

proc resolve*[T](system: ConstraintSystem[T],
                 initialTabuThreshold=32,
                 maxAttempts=10,
                 attemptThreshold=10,
                 useParallel=true) = 

    # Choose between serial and parallel resolution
    if useParallel:
        let numWorkers = getOptimalWorkerCount()
        echo fmt"Using parallel resolution with {numWorkers} workers"
        try:
            system.resolveParallelSimple(initialTabuThreshold, numWorkers)
        except Exception as e:
            echo fmt"Parallel resolution failed: {e.msg}, falling back to serial"
            # Fall back to serial resolution
            system.resolveSerial(initialTabuThreshold, maxAttempts, attemptThreshold)
    else:
        echo "Using serial resolution"
        system.resolveSerial(initialTabuThreshold, maxAttempts, attemptThreshold)

proc resolveSerial*[T](system: ConstraintSystem[T],
                      initialTabuThreshold=32,
                      maxAttempts=10,
                      attemptThreshold=10) = 
    ## Serial resolution implementation for constraint satisfaction
    ## Continues searching until a valid solution (cost = 0) is found

    var lastImprovement = 0
    var bestAttempt = high(int)
    var attempt = 0
    var currentTabuThreshold = initialTabuThreshold
    var totalIterations = 0

    # Keep trying with increasing effort until solution found
    while true:
        let batchMaxAttempts = maxAttempts * (1 + attempt div 5) # Increase attempts over time
        
        for improved in system.baseArray.sequentialSearch(currentTabuThreshold, batchMaxAttempts):
            totalIterations += 1

            if improved.cost < bestAttempt:
                bestAttempt = improved.cost
                lastImprovement = attempt
                echo fmt"Found better solution with cost {improved.cost} (iteration {totalIterations})"

            if improved.cost == 0:
                echo fmt"Perfect solution found after {totalIterations} iterations"
                system.assignment = improved.assignment
                return

        attempt += 1
        
        # Increase tabu threshold if no improvement for a while
        if attempt - lastImprovement > attemptThreshold:
            currentTabuThreshold += currentTabuThreshold div 4  # Increase by 25%
            echo fmt"No improvement for {attemptThreshold} batches, increasing threshold to {currentTabuThreshold}"
            lastImprovement = attempt  # Reset counter
