import std/[typedthreads, atomics, cpuinfo, locks, os, times, strformat]

import tabu
import ../constraintSystem
import ../constrainedArray

type
    BatchResult*[T] = object
        found*: bool
        bestCost*: int  # Store cost instead of full state
        bestSolution*: seq[T]  # Safe copy of solution values
        workerId*: int

    SharedResults*[T] = object
        results*: seq[BatchResult[T]]
        lock*: Lock
        completed*: Atomic[int]

    BatchWorkerData*[T] = object
        states*: ptr seq[TabuState[T]]  # Use pointer for mutability
        workerId*: int
        shouldStop*: ptr Atomic[bool]
        sharedResults*: ptr SharedResults[T]
        tabuThreshold*: int
        verbose*: bool

proc batchWorker*[T](data: BatchWorkerData[T]) {.thread.} =
    try:
        let startTime = epochTime()
        var bestState: TabuState[T] = nil
        var foundSolution = false
        var solutionCopy = newSeq[T]()  # Copy solution immediately when found

        if data.verbose:
            echo &"[Worker {data.workerId}] Starting with {data.states[].len} states, tabu threshold: {data.tabuThreshold}"

        # Process each state assigned to this worker
        for i, state in data.states[]:
            # Check for early termination before processing
            if data.shouldStop[].load():
                if data.verbose:
                    echo &"[Worker {data.workerId}] Early termination requested after processing {i} states"
                break

            let stateStartTime = epochTime()

            # Run tabu improvement on this state
            let improved = state.tabuImprove(data.tabuThreshold, data.shouldStop)

            let stateTime = epochTime() - stateStartTime

            if data.verbose:
                echo &"[Worker {data.workerId}] State {i}: cost {state.cost} -> {improved.bestCost} (time: {stateTime:.3f}s)"

            # Update the best state for this worker
            if bestState == nil or improved.bestCost < bestState.bestCost:
                bestState = improved
                if data.verbose:
                    echo &"[Worker {data.workerId}] New best cost: {bestState.bestCost}"

            # If we found a solution, notify and stop all workers
            if improved.bestCost == 0:
                data.shouldStop[].store(true)
                foundSolution = true
                bestState = improved
                # Copy solution immediately to avoid memory issues
                solutionCopy = newSeq[T](improved.bestAssignment.len)
                for i in 0..<improved.bestAssignment.len:
                    solutionCopy[i] = improved.bestAssignment[i]
                if data.verbose:
                    echo &"[Worker {data.workerId}] SOLUTION FOUND! Cost: 0, stopping all workers"
                    echo &"[Worker {data.workerId}] Solution: {solutionCopy}"
                break

        let totalTime = epochTime() - startTime

        # Always copy the best solution found (if any), not just perfect solutions
        if bestState != nil and solutionCopy.len == 0:
            solutionCopy = newSeq[T](bestState.bestAssignment.len)
            for i in 0..<bestState.bestAssignment.len:
                solutionCopy[i] = bestState.bestAssignment[i]

        # Send result back with safe copy of solution
        let result = BatchResult[T](
            found: foundSolution,
            bestCost: if bestState != nil: bestState.bestCost else: high(int),
            bestSolution: solutionCopy,
            workerId: data.workerId
        )

        if data.verbose:
            let bestCostStr = if bestState != nil: $bestState.bestCost else: "nil"
            echo &"[Worker {data.workerId}] Completed in {totalTime:.3f}s, best cost: {bestCostStr}, solution: {foundSolution}"

        # Thread-safe result storage
        withLock data.sharedResults[].lock:
            data.sharedResults[].results.add(result)
        discard data.sharedResults[].completed.fetchAdd(1)

    except CatchableError:
        # Send error result
        let result = BatchResult[T](
            found: false,
            bestCost: high(int),
            bestSolution: newSeq[T](),
            workerId: data.workerId
        )

        # Thread-safe result storage
        withLock data.sharedResults[].lock:
            data.sharedResults[].results.add(result)
        discard data.sharedResults[].completed.fetchAdd(1)

proc getOptimalWorkerCount*(): int =
    # Use CPU count, but cap at reasonable maximum
    min(countProcessors(), 8)

proc batchImprove*[T](population: var seq[TabuState[T]],
                     numWorkers: int = 0,
                     tabuThreshold: int = 10000,
                     verbose: bool = false): BatchResult[T] =
    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers

    if verbose:
        echo &"[BatchImprove] Starting with {population.len} states, {actualWorkers} workers, tabu threshold: {tabuThreshold}"

    if population.len == 0:
        raise newException(ValueError, "Empty population provided to batchImprove")

    # If only one state or one worker, process sequentially
    if population.len == 1 or actualWorkers == 1:
        if verbose:
            echo "[BatchImprove] Using sequential processing (single state or worker)"
        var improved = population[0].tabuImprove(tabuThreshold)
        if verbose:
            echo &"[BatchImprove] Sequential result: cost {improved.bestCost}"
        # Always copy the best solution found, regardless of cost
        var solutionCopy = newSeq[T](improved.bestAssignment.len)
        for i in 0..<improved.bestAssignment.len:
            solutionCopy[i] = improved.bestAssignment[i]
        return BatchResult[T](
            found: improved.bestCost == 0,
            bestCost: improved.bestCost,
            bestSolution: solutionCopy,
            workerId: 0
        )

    # Initialize shared state for coordination
    var shouldStop: Atomic[bool]
    shouldStop.store(false)

    var sharedResults = SharedResults[T](
        results: newSeq[BatchResult[T]](),
        completed: Atomic[int]()
    )
    initLock(sharedResults.lock)
    sharedResults.completed.store(0)

    # Distribute population among workers
    var workers = newSeq[Thread[BatchWorkerData[T]]](actualWorkers)
    var workerData = newSeq[BatchWorkerData[T]](actualWorkers)
    var workerStates = newSeq[seq[TabuState[T]]](actualWorkers)

    let statesPerWorker = population.len div actualWorkers
    let remainder = population.len mod actualWorkers

    if verbose:
        echo &"[BatchImprove] Distributing {population.len} states: {statesPerWorker} per worker, {remainder} remainder"

    var stateIndex = 0
    for i in 0..<actualWorkers:
        let startIdx = stateIndex
        let endIdx = stateIndex + statesPerWorker + (if i < remainder: 1 else: 0)

        # Create a copy for this worker
        workerStates[i] = population[startIdx..<endIdx]
        workerData[i] = BatchWorkerData[T](
            states: addr workerStates[i],
            workerId: i,
            shouldStop: addr shouldStop,
            sharedResults: addr sharedResults,
            tabuThreshold: tabuThreshold,
            verbose: verbose
        )

        if verbose:
            echo &"[BatchImprove] Starting worker {i} with {workerStates[i].len} states (indices {startIdx}..<{endIdx})"

        createThread(workers[i], batchWorker[T], workerData[i])
        stateIndex = endIdx

    let batchStartTime = epochTime()
    var lastProgressTime = batchStartTime

    # Wait for all workers to complete
    while sharedResults.completed.load() < actualWorkers:
        # Check if any worker found a solution
        var foundSolution = false
        withLock sharedResults.lock:
            for result in sharedResults.results:
                if result.found:
                    foundSolution = true
                    break

        if foundSolution:
            shouldStop.store(true)
            if verbose:
                echo "[BatchImprove] Solution found, signaling all workers to stop"

        # Progress reporting
        if verbose:
            let currentTime = epochTime()
            if currentTime - lastProgressTime > 5.0:  # Report every 5 seconds
                let completed = sharedResults.completed.load()
                let elapsed = currentTime - batchStartTime
                echo &"[BatchImprove] Progress: {completed}/{actualWorkers} workers completed (elapsed: {elapsed:.1f}s)"
                lastProgressTime = currentTime

        # Small delay to avoid busy waiting
        sleep(1)

    if verbose:
        echo "[BatchImprove] All workers completed, joining threads..."

    # Wait for all threads to complete
    joinThreads(workers)

    let totalTime = epochTime() - batchStartTime

    # Find best result
    var bestResult: BatchResult[T]
    var solutionFound = false
    var bestResultInitialized = false

    withLock sharedResults.lock:
        if verbose:
            echo &"[BatchImprove] Analyzing {sharedResults.results.len} worker results..."

        for result in sharedResults.results:
            if verbose:
                echo &"[BatchImprove] Worker {result.workerId}: cost={result.bestCost}, solution={result.found}"

            if result.found and not solutionFound:
                solutionFound = true
                bestResult = result
                bestResultInitialized = true
            elif not solutionFound and (not bestResultInitialized or result.bestCost < bestResult.bestCost):
                bestResult = result
                bestResultInitialized = true

    if verbose:
        echo &"[BatchImprove] Completed in {totalTime:.3f}s, best cost: {bestResult.bestCost}, solution found: {solutionFound}"

    deinitLock(sharedResults.lock)

    return bestResult

proc parallelResolve*[T](system: ConstraintSystem[T],
                        populationSize: int = 16,
                        numWorkers: int = 0,
                        tabuThreshold: int = 10000,
                        verbose: bool = false) =
    if verbose:
        let actualWorkers = if numWorkers == 0: getOptimalWorkerCount() else: numWorkers
        echo &"[ParallelResolve] Starting with population size: {populationSize}, workers: {actualWorkers}, tabu threshold: {tabuThreshold}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        if verbose:
            echo &"[ParallelResolve] Computed reduced domain size: {system.baseArray.reducedDomain.len}"

    # Create population of TabuStates from deepCopies
    let populationStartTime = epochTime()
    var population = newSeq[TabuState[T]](populationSize)
    for i in 0..<populationSize:
        let systemCopy = system.deepCopy()
        population[i] = newTabuState[T](systemCopy.baseArray)

    let populationTime = epochTime() - populationStartTime
    if verbose:
        echo &"[ParallelResolve] Created {populationSize} initial states in {populationTime:.3f}s"

    # Process population in parallel
    let bestResult = batchImprove(population, numWorkers, tabuThreshold, verbose)

    # Check if perfect solution was found (cost == 0 means all constraints satisfied)
    if bestResult.found and bestResult.bestSolution.len > 0:
        if verbose:
            echo &"[ParallelResolve] SUCCESS: Found solution with cost 0"
            echo &"[ParallelResolve] Solution length: {bestResult.bestSolution.len}"
        # Initialize the system with the found solution
        let solutionCopy = @(bestResult.bestSolution)
        system.initialize(solutionCopy)
    else:
        # No perfect solution found - reject partial solutions to match sequential behavior
        if verbose:
            if bestResult.bestSolution.len > 0:
                echo &"[ParallelResolve] FAILED: No valid solution found, best cost achieved was {bestResult.bestCost}"
            else:
                echo &"[ParallelResolve] FAILED: No solution found"
        raise newException(NoSolutionFoundError, "Can't find satisfying solution with parallel search")
