import std/[os, strformat, cpuinfo, atomics]
import std/typedthreads

import heuristics, tabu
import ../constraintSystem


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T],
                 initialTabuThreshold=1000,
                 maxAttempts=10,
                 attemptThreshold=10,
                 parallel=true) =
    if parallel:
        let cpuCount = countProcessors()
        let numWorkers = max(1, min(cpuCount - 1, 16))
        echo fmt"Using parallel resolution with {numWorkers} workers"
        system.resolveParallel(initialTabuThreshold, numWorkers)
    else:
        echo "Using serial resolution"
        system.resolveSerial(initialTabuThreshold, maxAttempts, attemptThreshold)

proc resolveSerial*[T](system: ConstraintSystem[T],
                      initialTabuThreshold=10000,
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

proc resolveParallel*[T](system: ConstraintSystem[T],
                        tabuThreshold=1000,
                        numWorkers=4) =
    ## Parallel version that runs multiple batches until solution found

    var attempt = 0
    var bestAttempt = high(int)
    var lastImprovement = 0
    var currentTabuThreshold = tabuThreshold

    # Keep running parallel batches until we find a solution
    while true:
        attempt += 1

        # Create shared result structure for this batch
        var sharedResult = SharedResult[T](assignment: @[])
        sharedResult.solved.store(false)
        sharedResult.solutionFound.store(false)
        sharedResult.bestCost.store(high(int))
        sharedResult.solutionWorkerId.store(-1)

        # Launch worker threads for this batch
        var threads: seq[Thread[WorkerParams[T]]]
        threads.setLen(numWorkers)

        for i in 0..<numWorkers:
            var systemCopy = system.deepCopy()

            let params = WorkerParams[T](
                systemCopy: systemCopy,
                threshold: currentTabuThreshold,
                result: sharedResult.addr,
                workerId: i
            )
            createThread(threads[i], tabuSearchWorker, params)

        # Wait for solution or all workers to complete
        while not sharedResult.solutionFound.load():
            var allDone = true
            for thread in threads:
                if running(thread):
                    allDone = false
                    break

            if allDone:
                break
            sleep(50)

        # Clean up threads
        for thread in threads:
            joinThread(thread)

        # Check if we found a solution
        if sharedResult.solutionFound.load():
            system.assignment = sharedResult.assignment
            return

        # Track best result from this batch
        let batchBestCost = sharedResult.bestCost.load()
        if batchBestCost < bestAttempt:
            bestAttempt = batchBestCost
            lastImprovement = attempt
            echo fmt"Batch {attempt} found better solution with cost {batchBestCost}"

        # Adaptive tabu threshold - increase if no improvement
        if attempt - lastImprovement > 2:
            currentTabuThreshold += currentTabuThreshold div 2
            echo fmt"No improvement for 5 batches, increasing threshold to {currentTabuThreshold}"
            lastImprovement = attempt
