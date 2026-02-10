import std/[typedthreads, atomics, cpuinfo, locks, os, times, strformat, random, algorithm]

import tabu
import candidatePool
import ../constraintSystem
import ../constrainedArray

export candidatePool

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

proc parallelResolve*[T](system: ConstraintSystem[T],
                        populationSize: int = 16,
                        numWorkers: int = 0,
                        tabuThreshold: int = 10000,
                        verbose: bool = false,
                        failedPool: var CandidatePool[T]): bool =
    ## Run parallel tabu search. Returns true if solution found (system initialized).
    ## On failure, populates failedPool with best results for scatter search continuation.
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
        population[i] = newTabuState[T](systemCopy.baseArray, verbose = false, id=i)

    if verbose:
        let populationTime = epochTime() - populationStartTime
        echo &"[Solve] Created {populationSize} states in {populationTime:.3f}s"

    # Collect all results from parallel tabu improvement
    var allResults: seq[PoolEntry[T]] = @[]

    for result in improveStates(population, numWorkers, tabuThreshold, verbose = false):
        if result.found:
            if verbose:
                let elapsed = result.endTime - result.startTime
                let rate = if elapsed > 0: result.iterations.float / elapsed else: 0.0
                echo &"[Solve] Solution found by S{result.workerId} in {elapsed:.1f}s ({rate:.0f} iter/s)"
            system.initialize(result.assignment)
            system.lastIterations = result.iterations
            return true
        allResults.add(PoolEntry[T](
            assignment: result.assignment,
            cost: result.cost
        ))

    # No solution found — build pool from results for scatter continuation
    if allResults.len > 0:
        let poolSize = min(populationSize, 10)
        allResults.sort(proc(a, b: PoolEntry[T]): int = cmp(a.cost, b.cost))
        let keepCount = min(poolSize, allResults.len)
        failedPool.entries = allResults[0..<keepCount]
        failedPool.updateBounds()

    if verbose:
        let bestCost = if allResults.len > 0: allResults[0].cost else: -1
        echo &"[Solve] Initial parallel search failed: best cost={bestCost}"

    return false
