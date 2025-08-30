import std/[os, strformat, cpuinfo, atomics, tables]
import std/typedthreads

import heuristics, tabu
import ../constraintSystem
import ../constrainedArray
import ../constraints/stateful


type NoSolutionFoundError* = object of CatchableError


proc resolve*[T](system: ConstraintSystem[T],
                 initialTabuThreshold=1000,
                 maxAttempts=10,
                 attemptThreshold=10,
                 parallel=true,
                 verbose=false) =
    if parallel:
        let cpuCount = countProcessors()
        let numWorkers = max(1, min(cpuCount - 1, 16))
        echo fmt"Using parallel resolution with {numWorkers} workers"
        # Work directly on the original system for parallel search  
        system.resolveParallel(initialTabuThreshold, numWorkers, verbose)
    else:
        echo "Using serial resolution"
        system.resolveSerial(initialTabuThreshold, maxAttempts, attemptThreshold, verbose)

proc resolveSerial*[T](system: ConstraintSystem[T],
                      initialTabuThreshold=10000,
                      maxAttempts=10,
                      attemptThreshold=10,
                      verbose=false) = 
    ## Serial resolution implementation for constraint satisfaction
    ## Continues searching until a valid solution (cost = 0) is found

    # Compute domain reduction once before search (same as parallel)
    echo "Computing domain reduction..."
    let preComputedDomains = system.baseArray.reduceDomain(verbose = false)
    echo "Domain reduction complete"
    
    # Check for empty domains before starting search
    for i, domain in preComputedDomains:
        if domain.len == 0:
            echo "Error: Variable at position ", i, " has empty reduced domain - problem is unsatisfiable"
            raise newException(NoSolutionFoundError, "Problem is unsatisfiable due to empty domains")
    
    # Set the pre-computed reduced domains on the system for serial search
    for pos in 0..<system.baseArray.len:
        system.baseArray.domain[pos] = preComputedDomains[pos]
    
    # DEBUG: Show first 10 domain sizes in serial path
    echo "DEBUG: Serial path domain sizes:"
    for i in 0..<min(10, preComputedDomains.len):
        echo "  Var ", i, ": ", preComputedDomains[i].len

    var lastImprovement = 0
    var bestAttempt = high(int)
    var attempt = 0
    var currentTabuThreshold = initialTabuThreshold
    var totalIterations = 0

    # Display constraint type information in verbose mode
    if verbose:
        echo "\n=== Constraint System Information ==="
        var constraintTypeCounts = initTable[string, int]()
        for constraint in system.baseArray.constraints:
            let typeName = constraint.getConstraintTypeName()
            constraintTypeCounts[typeName] = constraintTypeCounts.getOrDefault(typeName, 0) + 1
        
        echo fmt"Total constraints: {system.baseArray.constraints.len}"
        echo fmt"Total variables: {system.baseArray.len}"
        echo "Constraint types:"
        for constraintType, count in constraintTypeCounts.pairs:
            echo fmt"  {constraintType}: {count}"
        echo "=================================="

    # Keep trying with increasing effort until solution found
    while true:
        let batchMaxAttempts = maxAttempts * (1 + attempt div 5) # Increase attempts over time
        for improved in system.baseArray.sequentialSearch(currentTabuThreshold, batchMaxAttempts, verbose):
            totalIterations += 1

            if improved.cost < bestAttempt:
                bestAttempt = improved.cost
                lastImprovement = attempt
                echo fmt"Found better solution with cost {improved.cost} (iteration {totalIterations})"

            if improved.cost == 0:
                echo fmt"Perfect solution found after {totalIterations} iterations"
                system.assignment = improved.assignment
                # Display timing statistics in verbose mode
                if verbose:
                    improved.printTimingStats()
                return

        attempt += 1

        # Increase tabu threshold if no improvement for a while
        if attempt - lastImprovement > attemptThreshold:
            currentTabuThreshold += currentTabuThreshold div 4  # Increase by 25%
            echo fmt"No improvement for {attemptThreshold} batches, increasing threshold to {currentTabuThreshold}"
            lastImprovement = attempt  # Reset counter

proc resolveParallel*[T](system: ConstraintSystem[T],
                        tabuThreshold=1000,
                        numWorkers=4,
                        verbose=false) =
    ## Parallel version that runs multiple batches until solution found

    var attempt = 0
    var bestAttempt = high(int)
    var lastImprovement = 0
    var currentTabuThreshold = tabuThreshold

    # Display constraint type information in verbose mode
    if verbose:
        echo "\n=== Constraint System Information ==="
        var constraintTypeCounts = initTable[string, int]()
        for constraint in system.baseArray.constraints:
            let typeName = constraint.getConstraintTypeName()
            constraintTypeCounts[typeName] = constraintTypeCounts.getOrDefault(typeName, 0) + 1
        
        echo fmt"Total constraints: {system.baseArray.constraints.len}"
        echo fmt"Total variables: {system.baseArray.len}"
        echo "Constraint types:"
        for constraintType, count in constraintTypeCounts.pairs:
            echo fmt"  {constraintType}: {count}"
        echo "=================================="

    # Compute domain reduction once and share results with all workers
    echo "Computing domain reduction for parallel workers..."
    let preComputedDomains = system.baseArray.reduceDomain(verbose = false)
    echo "Domain reduction complete, sharing with all workers"
    
    # Check for empty domains before starting search
    for i, domain in preComputedDomains:
        if domain.len == 0:
            echo "Error: Variable at position ", i, " has empty reduced domain - problem is unsatisfiable"
            raise newException(NoSolutionFoundError, "Problem is unsatisfiable due to empty domains")
    
    # CRITICAL FIX: Set the reduced domains on the original system BEFORE deep copying
    # This ensures deep copies get the correct domains from the start
    for pos in 0..<system.baseArray.len:
        system.baseArray.domain[pos] = preComputedDomains[pos]

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
            
            # Domains should already be set correctly since we set them before deep copying
            if i == 0:
                echo "DEBUG: Worker 0 domains should now match original system"
                echo "DEBUG: Worker 0 first 10 domain sizes: "
                for j in 0..<min(10, systemCopy.baseArray.len):
                    echo "  Var ", j, ": ", systemCopy.baseArray.domain[j].len

            let params = WorkerParams[T](
                systemCopy: systemCopy,
                threshold: currentTabuThreshold,
                result: sharedResult.addr,
                workerId: i,
                verbose: verbose
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
