import std/[typedthreads, atomics, cpuinfo, locks, os, times, strformat, random]

import tabu
import ../constraintSystem
import ../constrainedArray

type
    BatchResult*[T] = object
        found*: bool
        cost*: int  # Store cost instead of full state
        assignment*: seq[T]  # Safe copy of solution values
        workerId*: int
        iterations*: int
        startTime*: float
        endTime*: float

    # Iterator-based approach types
    StatePool*[T] = object
        states*: seq[TabuState[T]]  # Pool of states to process
        nextTaskIndex*: Atomic[int]  # Index of next state to assign
        solutionFound*: Atomic[bool]  # Global solution flag
        tabuThreshold*: int
        verbose*: bool
        results*: seq[BatchResult[T]]  # Collected results
        resultsLock*: Lock  # Protect results array

    IterativeWorkerData*[T] = object
        workerId*: int
        pool*: ptr StatePool[T]

proc getOptimalWorkerCount*(): int =
    # Use CPU count, but cap at reasonable maximum
    min(countProcessors(), 8)

proc iterativeWorker*[T](data: IterativeWorkerData[T]) {.thread.} =
    try:
        randomize()
        let pool = data.pool

        while not pool.solutionFound.load():
            let taskIndex = pool.nextTaskIndex.fetchAdd(1)

            if taskIndex >= pool.states.len:
                break

            if pool.solutionFound.load():
                break

            discard  # Worker picks up task silently

            let state = pool.states[taskIndex]
            let startTime = epochTime()
            let improved = state.tabuImprove(pool.tabuThreshold, addr pool.solutionFound)
            let endTime = epochTime()

            let result = BatchResult[T](
                found: improved.bestCost == 0,
                cost: improved.bestCost,
                assignment: improved.assignment,
                workerId: data.workerId,
                iterations: improved.iteration,
                startTime: startTime,
                endTime: endTime
            )

            if result.found:
                pool.solutionFound.store(true)

            # Store result in shared array
            withLock pool.resultsLock:
                pool.results.add(result)

            if result.found:
                break

    except CatchableError:
        discard  # Worker error handled gracefully

iterator improveStates*[T](population: seq[TabuState[T]],
                           numWorkers: int = 0,
                           tabuThreshold: int = 10000,
                           verbose: bool = false): BatchResult[T] =
    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers

    discard

    if population.len > 0:
        # If only one state or one worker, process sequentially
        if population.len == 1 or actualWorkers == 1:
            for i, state in population:
                let startTime = epochTime()
                let improved = state.tabuImprove(tabuThreshold)
                let endTime = epochTime()
                let result = BatchResult[T](
                    found: improved.bestCost == 0,
                    cost: improved.bestCost,
                    assignment: improved.assignment,
                    workerId: 0,
                    iterations: improved.iteration,
                    startTime: startTime,
                    endTime: endTime
                )
                yield result
                if result.found:
                    break
        else:
            # Parallel processing setup
            var pool = StatePool[T](
                states: population,
                tabuThreshold: tabuThreshold,
                verbose: verbose,
                results: newSeq[BatchResult[T]]()
            )
            pool.nextTaskIndex.store(0)
            pool.solutionFound.store(false)
            initLock(pool.resultsLock)

            # Start workers
            var workers = newSeq[Thread[IterativeWorkerData[T]]](actualWorkers)
            var workerData = newSeq[IterativeWorkerData[T]](actualWorkers)

            for i in 0..<actualWorkers:
                workerData[i] = IterativeWorkerData[T](
                    workerId: i,
                    pool: addr pool
                )
                createThread(workers[i], iterativeWorker[T], workerData[i])

            # Monitor and yield results as they become available
            var yieldedResults = 0
            var lastResultCount = 0

            while yieldedResults < population.len and not pool.solutionFound.load():
                # Check for new results
                var currentResults: seq[BatchResult[T]]
                withLock pool.resultsLock:
                    currentResults = pool.results

                # Yield any new results
                for i in lastResultCount..<currentResults.len:
                    let result = currentResults[i]
                    yield result
                    inc yieldedResults

                    if result.found:
                        pool.solutionFound.store(true)
                        break

                lastResultCount = currentResults.len

                if yieldedResults >= population.len or pool.solutionFound.load():
                    break

                sleep(1)  # Small delay to avoid busy waiting

            # Signal all workers to stop if not already done
            if not pool.solutionFound.load():
                pool.solutionFound.store(true)

            # Wait for workers to complete
            for i in 0..<actualWorkers:
                joinThread(workers[i])

            # Small delay to ensure all worker cleanup is complete
            sleep(10)

            # Yield any remaining results after all workers are done
            withLock pool.resultsLock:
                for i in lastResultCount..<pool.results.len:
                    if yieldedResults < population.len:
                        yield pool.results[i]
                        inc yieldedResults

            # Clear the results array to prevent memory issues
            withLock pool.resultsLock:
                pool.results.setLen(0)

            deinitLock(pool.resultsLock)

            # Additional cleanup - ensure all worker data is cleared
            for i in 0..<workerData.len:
                workerData[i].pool = nil

proc dynamicImprove*[T](population: var seq[TabuState[T]],
                       numWorkers: int = 0,
                       tabuThreshold: int = 10000,
                       verbose: bool = false): BatchResult[T] =
    if population.len == 0:
        raise newException(ValueError, "Empty population provided to dynamicImprove")

    var bestResult: BatchResult[T]
    var solutionFound = false
    var bestResultInitialized = false

    # Use the iterator to process states one by one
    for result in improveStates(population, numWorkers, tabuThreshold, verbose):

        # Update best result
        if result.found and not solutionFound:
            solutionFound = true
            bestResult = result
            bestResultInitialized = true
            break
        elif not solutionFound and (not bestResultInitialized or result.cost < bestResult.cost):
            bestResult = result
            bestResultInitialized = true

    if not bestResultInitialized:
        # Fallback result if no results were produced
        bestResult = BatchResult[T](
            found: false,
            cost: high(int),
            assignment: newSeq[T](),
            workerId: -1,
            iterations: 0,
            startTime: 0.0,
            endTime: 0.0
        )

    return bestResult

proc parallelResolve*[T](system: ConstraintSystem[T],
                        populationSize: int = 16,
                        numWorkers: int = 0,
                        tabuThreshold: int = 10000,
                        verbose: bool = false) =
    let actualWorkers = if numWorkers == 0: getOptimalWorkerCount() else: numWorkers
    if verbose:
        echo &"[Solve] vars={system.baseArray.len} constraints={system.baseArray.constraints.len} pop={populationSize} workers={actualWorkers} threshold={tabuThreshold}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        let reducedDomainStart = epochTime()
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        if verbose:
            let reducedTime = epochTime() - reducedDomainStart
            echo &"[Solve] Domain reduction: {reducedTime:.3f}s"

    # Create population of TabuStates from deepCopies
    let populationStartTime = epochTime()
    var population = newSeq[TabuState[T]](populationSize)
    for i in 0..<populationSize:
        let systemCopy = system.deepCopy()
        population[i] = newTabuState[T](systemCopy.baseArray, verbose, id=i)

    if verbose:
        let populationTime = epochTime() - populationStartTime
        echo &"[Solve] Created {populationSize} states in {populationTime:.3f}s"

    # Process population in parallel using dynamic dispatcher
    let bestResult = dynamicImprove(population, numWorkers, tabuThreshold, verbose)

    # Check if perfect solution was found (cost == 0 means all constraints satisfied)
    if bestResult.found and bestResult.assignment.len > 0:
        if verbose:
            let elapsed = bestResult.endTime - bestResult.startTime
            let rate = if elapsed > 0: bestResult.iterations.float / elapsed else: 0.0
            echo &"[Solve] Solution found by S{bestResult.workerId} in {elapsed:.1f}s ({rate:.0f} iter/s)"
        let solutionCopy = @(bestResult.assignment)
        system.initialize(solutionCopy)
        system.lastIterations = bestResult.iterations
    else:
        if verbose:
            echo &"[Solve] Failed: best cost={bestResult.cost}"
        raise newException(NoSolutionFoundError, "Can't find satisfying solution with parallel search")
