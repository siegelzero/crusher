import std/[typedthreads, atomics, cpuinfo, locks, os, times, strformat, random, algorithm, sequtils]

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
        lastImprovement*: int  # Iteration of last bestCost improvement
        startTime*: float
        endTime*: float
        taskIndex*: int  # Index into carrays for eager slot freeing

    # Iterator-based approach types
    StatePool*[T] = object
        states*: seq[TabuState[T]]  # Pool of states to process
        nextTaskIndex*: Atomic[int]  # Index of next state to assign
        solutionFound*: Atomic[bool]  # Global solution flag
        tabuThreshold*: int
        deadline*: float
        verbose*: bool
        results*: seq[BatchResult[T]]  # Collected results
        resultsLock*: Lock  # Protect results array

    IterativeWorkerData*[T] = object
        workerId*: int
        pool*: ptr StatePool[T]

proc getOptimalWorkerCount*(): int =
    # Use CPU count, but cap at reasonable maximum
    min(countProcessors(), 8)

# Parallel state initialization (work-stealing pool)
type
    InitPool[T] = object
        carrays: ptr UncheckedArray[ConstrainedArray[T]]
        results: ptr UncheckedArray[TabuState[T]]
        nextTaskIndex: Atomic[int]
        totalTasks: int
        verbose: bool

    InitWorkerData[T] = object
        workerId: int
        pool: ptr InitPool[T]

proc initPoolWorker[T](data: InitWorkerData[T]) {.thread.} =
    {.cast(gcsafe).}:
        randomize()
        let pool = data.pool
        while true:
            let idx = pool.nextTaskIndex.fetchAdd(1)
            if idx >= pool.totalTasks:
                break
            try:
                pool.results[idx] = newTabuState[T](pool.carrays[idx],
                    verbose = pool.verbose and idx == 0, id = idx)
            except CatchableError as e:
                stderr.writeLine("[InitWorker " & $data.workerId & "] Error on state " & $idx & ": " & e.msg)
                stderr.writeLine("[InitWorker " & $data.workerId & "] Stack: " & e.getStackTrace())

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
            let improved = state.tabuImprove(pool.tabuThreshold, addr pool.solutionFound, pool.deadline)
            let endTime = epochTime()

            let result = BatchResult[T](
                found: improved.bestCost == 0,
                cost: improved.bestCost,
                assignment: improved.bestAssignment,
                workerId: data.workerId,
                iterations: improved.iteration,
                lastImprovement: improved.lastImprovementIter,
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

    except CatchableError as e:
        stderr.writeLine("[Worker " & $data.workerId & "] Error: " & e.msg)
        stderr.writeLine("[Worker " & $data.workerId & "] Stack: " & e.getStackTrace())

iterator improveStates*[T](population: seq[TabuState[T]],
                           numWorkers: int = 0,
                           tabuThreshold: int = 10000,
                           verbose: bool = false,
                           deadline: float = 0.0): BatchResult[T] =
    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers

    discard

    if population.len > 0:
        # If only one state or one worker, process sequentially
        if population.len == 1 or actualWorkers == 1:
            for i, state in population:
                let startTime = epochTime()
                let improved = state.tabuImprove(tabuThreshold, deadline = deadline)
                let endTime = epochTime()
                let result = BatchResult[T](
                    found: improved.bestCost == 0,
                    cost: improved.bestCost,
                    assignment: improved.bestAssignment,
                    workerId: 0,
                    iterations: improved.iteration,
                    lastImprovement: improved.lastImprovementIter,
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
                deadline: deadline,
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

            # Ensure threads are joined even if caller returns during a yield
            var threadsJoined = false
            defer:
                if not threadsJoined:
                    if not pool.solutionFound.load():
                        pool.solutionFound.store(true)
                    for i in 0..<actualWorkers:
                        joinThread(workers[i])
                    threadsJoined = true
                deinitLock(pool.resultsLock)
                for i in 0..<workerData.len:
                    workerData[i].pool = nil

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

                # Check deadline in monitor loop
                if deadline > 0 and epochTime() > deadline:
                    pool.solutionFound.store(true)
                    break

                sleep(1)  # Small delay to avoid busy waiting

            # Signal all workers to stop if not already done
            if not pool.solutionFound.load():
                pool.solutionFound.store(true)

            for i in 0..<actualWorkers:
                joinThread(workers[i])
            threadsJoined = true

            # Yield any remaining results after all workers are done
            withLock pool.resultsLock:
                for i in lastResultCount..<pool.results.len:
                    if yieldedResults < population.len:
                        yield pool.results[i]
                        inc yieldedResults

            withLock pool.resultsLock:
                pool.results.setLen(0)

# Combined init+improve work-stealing pool — no batch boundaries.
# Workers grab a task, create TabuState from pre-deepCopied array + assignment,
# run tabuImprove, and store the result. Results stream in as they complete.
type
    AssignmentPool*[T] = object
        carrays*: ptr UncheckedArray[ConstrainedArray[T]]
        assignments*: ptr UncheckedArray[seq[T]]
        nextTaskIndex*: Atomic[int]
        createdUpTo*: Atomic[int]  # How many carrays have been created (lazy creation)
        solutionFound*: Atomic[bool]
        totalTasks*: int
        tabuThreshold*: int
        deadline*: float
        results*: seq[BatchResult[T]]
        resultsLock*: Lock

    AssignmentWorkerData*[T] = object
        workerId*: int
        pool*: ptr AssignmentPool[T]

proc assignmentWorker*[T](data: AssignmentWorkerData[T]) {.thread.} =
    try:
        randomize()
        let pool = data.pool

        while not pool.solutionFound.load():
            let idx = pool.nextTaskIndex.fetchAdd(1)
            if idx >= pool.totalTasks:
                break
            if pool.solutionFound.load():
                break

            # Wait for main thread to create this carray (lazy creation)
            while pool.createdUpTo.load() <= idx:
                if pool.solutionFound.load(): return
                sleep(1)

            # Create TabuState from pre-deepCopied array + assignment, then improve
            let state = newTabuState[T](pool.carrays[idx], pool.assignments[idx],
                verbose = false, id = idx)
            let startTime = epochTime()
            let improved = state.tabuImprove(pool.tabuThreshold, addr pool.solutionFound, pool.deadline)
            let endTime = epochTime()

            let result = BatchResult[T](
                found: improved.bestCost == 0,
                cost: improved.bestCost,
                assignment: improved.bestAssignment,
                workerId: data.workerId,
                iterations: improved.iteration,
                lastImprovement: improved.lastImprovementIter,
                startTime: startTime,
                endTime: endTime,
                taskIndex: idx
            )

            if result.found:
                pool.solutionFound.store(true)

            withLock pool.resultsLock:
                pool.results.add(result)

            if result.found:
                break

    except CatchableError as e:
        stderr.writeLine("[AssignmentWorker " & $data.workerId & "] Error: " & e.msg)
        stderr.writeLine("[AssignmentWorker " & $data.workerId & "] Stack: " & e.getStackTrace())

iterator improveFromAssignments*[T](system: ConstraintSystem[T],
                                     assignments: seq[seq[T]],
                                     numWorkers: int = 0,
                                     tabuThreshold: int = 10000,
                                     deadline: float = 0.0): BatchResult[T] =
    ## Work-stealing iterator: pre-deepCopies arrays sequentially, then workers
    ## each grab a task, create TabuState + improve, yielding results as they complete.
    ## No batch boundaries — eliminates idle gaps and missed results at deadline.
    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers

    if assignments.len > 0:
        if assignments.len == 1 or actualWorkers == 1:
            # Sequential fallback
            for i in 0..<assignments.len:
                let sc = system.deepCopy()
                let state = newTabuState[T](sc.baseArray, assignments[i], verbose = false, id = i)
                let startTime = epochTime()
                let improved = state.tabuImprove(tabuThreshold, deadline = deadline)
                let endTime = epochTime()
                let result = BatchResult[T](
                    found: improved.bestCost == 0,
                    cost: improved.bestCost,
                    assignment: improved.bestAssignment,
                    workerId: 0,
                    iterations: improved.iteration,
                    lastImprovement: improved.lastImprovementIter,
                    startTime: startTime,
                    endTime: endTime
                )
                yield result
                if result.found:
                    break
        else:
            # Lazy creation: allocate the array but only create copies incrementally
            # to bound peak memory to ~workerCount*2 copies instead of all at once.
            # Workers wait for their slot via createdUpTo atomic.
            var carrays = newSeq[ConstrainedArray[T]](assignments.len)
            # Use a single template array for all copies (avoids full system.deepCopy overhead)
            var templateArray = system.baseArray.deepCopy()
            let bufferAhead = actualWorkers * 2
            let initialBatch = min(bufferAhead, assignments.len)
            for i in 0..<initialBatch:
                carrays[i] = templateArray.deepCopy()
            var createdSoFar = initialBatch

            # Set up work-stealing pool
            var assignmentsCopy = assignments  # Local copy for addr stability
            var pool = AssignmentPool[T](
                carrays: cast[ptr UncheckedArray[ConstrainedArray[T]]](addr carrays[0]),
                assignments: cast[ptr UncheckedArray[seq[T]]](addr assignmentsCopy[0]),
                totalTasks: assignments.len,
                tabuThreshold: tabuThreshold,
                deadline: deadline,
                results: newSeq[BatchResult[T]]()
            )
            pool.nextTaskIndex.store(0)
            pool.createdUpTo.store(createdSoFar)
            pool.solutionFound.store(false)
            initLock(pool.resultsLock)

            # Start workers
            let workerCount = min(actualWorkers, assignments.len)
            var workers = newSeq[Thread[AssignmentWorkerData[T]]](workerCount)
            var workerDatas = newSeq[AssignmentWorkerData[T]](workerCount)
            for i in 0..<workerCount:
                workerDatas[i] = AssignmentWorkerData[T](workerId: i, pool: addr pool)
                createThread(workers[i], assignmentWorker[T], workerDatas[i])

            # Ensure threads are joined even if caller returns during a yield
            var threadsJoined = false
            defer:
                if not threadsJoined:
                    if not pool.solutionFound.load():
                        pool.solutionFound.store(true)
                    for i in 0..<workerCount:
                        joinThread(workers[i])
                    threadsJoined = true
                deinitLock(pool.resultsLock)
                for i in 0..<workerDatas.len:
                    workerDatas[i].pool = nil

            # Monitor and yield results as they become available
            var yieldedResults = 0
            var lastResultCount = 0

            while yieldedResults < assignments.len and not pool.solutionFound.load():
                # Create more carrays ahead of workers (lazy, bounded buffer)
                let nextTask = pool.nextTaskIndex.load()
                let target = min(nextTask + bufferAhead, assignments.len)
                while createdSoFar < target and not pool.solutionFound.load():
                    carrays[createdSoFar] = templateArray.deepCopy()
                    createdSoFar += 1
                    pool.createdUpTo.store(createdSoFar)

                var currentResults: seq[BatchResult[T]]
                withLock pool.resultsLock:
                    currentResults = pool.results

                for i in lastResultCount..<currentResults.len:
                    let result = currentResults[i]
                    yield result
                    # Free the carray slot — worker already copied it into TabuState
                    reset(carrays[result.taskIndex])
                    inc yieldedResults
                    if result.found:
                        pool.solutionFound.store(true)
                        break

                lastResultCount = currentResults.len

                if yieldedResults >= assignments.len or pool.solutionFound.load():
                    break

                if deadline > 0 and epochTime() > deadline:
                    pool.solutionFound.store(true)
                    break

                sleep(1)

            if not pool.solutionFound.load():
                pool.solutionFound.store(true)

            for i in 0..<workerCount:
                joinThread(workers[i])
            threadsJoined = true

            # Yield any remaining results after workers complete
            withLock pool.resultsLock:
                for i in lastResultCount..<pool.results.len:
                    if yieldedResults < assignments.len:
                        yield pool.results[i]
                        reset(carrays[pool.results[i].taskIndex])
                        inc yieldedResults

            withLock pool.resultsLock:
                pool.results.setLen(0)

proc parallelResolve*[T](system: ConstraintSystem[T],
                        populationSize: int = 16,
                        numWorkers: int = 0,
                        tabuThreshold: int = 10000,
                        verbose: bool = false,
                        failedPool: var CandidatePool[T],
                        deadline: float = 0.0,
                        adaptedThreshold: var int): bool =
    ## Run parallel tabu search. Returns true if solution found (system initialized).
    ## On failure, populates failedPool with best results for scatter search continuation.
    let actualWorkers = if numWorkers == 0: getOptimalWorkerCount() else: numWorkers
    if verbose:
        echo &"[Solve] vars={system.baseArray.len} constraints={system.baseArray.constraints.len} pop={populationSize} workers={actualWorkers} threshold={tabuThreshold}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        let reducedDomainStart = epochTime()
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain
        if verbose:
            let reducedTime = epochTime() - reducedDomainStart
            echo &"[Solve] Domain reduction: {reducedTime:.3f}s"

    # Create population: deepCopy sequentially (safe), init in parallel (fast)
    let populationStartTime = epochTime()
    var population = newSeq[TabuState[T]](populationSize)
    var templateArray = system.baseArray.deepCopy()
    var carrays = newSeq[ConstrainedArray[T]](populationSize)
    for i in 0..<populationSize:
        carrays[i] = templateArray.deepCopy()

    # Initialize TabuStates in parallel using work-stealing pool.
    # Workers grab the next state to init via atomic counter — no batch boundaries.
    # SAFETY: population and carrays are pre-allocated to final size above and never
    # resized, so UncheckedArray access via indices remains valid through joinThreads.
    var initPool = InitPool[T](
        carrays: cast[ptr UncheckedArray[ConstrainedArray[T]]](addr carrays[0]),
        results: cast[ptr UncheckedArray[TabuState[T]]](addr population[0]),
        totalTasks: populationSize,
        verbose: verbose
    )
    initPool.nextTaskIndex.store(0)

    let initWorkerCount = min(actualWorkers, populationSize)
    var initThreads = newSeq[Thread[InitWorkerData[T]]](initWorkerCount)
    var initWorkerDatas = newSeq[InitWorkerData[T]](initWorkerCount)
    for i in 0..<initWorkerCount:
        initWorkerDatas[i] = InitWorkerData[T](workerId: i, pool: addr initPool)
        createThread(initThreads[i], initPoolWorker[T], initWorkerDatas[i])
    joinThreads(initThreads)

    # Free carrays — consumed by initPoolWorker to create TabuStates
    carrays.setLen(0)

    # Check for failed initializations (nil states from worker exceptions)
    var failedStates: seq[int]
    for i in 0..<populationSize:
        if population[i].isNil:
            failedStates.add(i)
    if failedStates.len > 0:
        stderr.writeLine(&"[Solve] WARNING: {failedStates.len}/{populationSize} states failed to initialize")
        population.keepItIf(not it.isNil)
        if population.len == 0:
            raise newException(CatchableError, "All TabuState initializations failed")

    if verbose:
        let populationTime = epochTime() - populationStartTime
        echo &"[Solve] Created {population.len} states in {populationTime:.3f}s"

    # Collect all results from parallel tabu improvement
    var allResults: seq[PoolEntry[T]] = @[]
    var maxLastImp = 0

    for result in improveStates(population, numWorkers, tabuThreshold, verbose = false, deadline = deadline):
        maxLastImp = max(maxLastImp, result.lastImprovement)
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

    # Set adapted threshold based on observed search depth
    if maxLastImp > 0:
        adaptedThreshold = max(maxLastImp, 500)
    else:
        adaptedThreshold = tabuThreshold

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
        flushFile(stdout)

    return false
