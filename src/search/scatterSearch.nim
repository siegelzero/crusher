import std/[random, math, sequtils, strformat, algorithm, atomics, tables, packedsets, typedthreads, locks, os]
import std/times

proc currentTime*(): float {.inline.} = epochTime()

import tabu
import candidatePool
import parallelResolution
import ../constraintSystem
import ../constrainedArray

randomize()

type
    PathEntry*[T] = object
        assignment*: seq[T]
        cost*: int

    RelinkTask*[T] = object
        sourceAssignment*: seq[T]
        targetAssignment*: seq[T]

    RelinkResult*[T] = object
        pathEntries*: seq[PathEntry[T]]
        taskIndex*: int

    RelinkPool*[T] = object
        carrays*: ptr UncheckedArray[ConstrainedArray[T]]
        tasks*: ptr UncheckedArray[RelinkTask[T]]
        nextTaskIndex*: Atomic[int]
        createdUpTo*: Atomic[int]
        solutionFound*: Atomic[bool]
        totalTasks*: int
        deadline*: float
        results*: seq[RelinkResult[T]]
        resultsLock*: Lock

    RelinkWorkerData*[T] = object
        workerId*: int
        pool*: ptr RelinkPool[T]

proc relinkPath*[T](state: TabuState[T], targetAssignment: seq[T]): seq[PathEntry[T]] =
    ## Path relinking: greedy walk from state's current assignment toward targetAssignment.
    ## Uses lean assignment (no penalty map updates) and computes cost deltas
    ## directly from constraint moveDelta for fast traversal.

    # Collect search positions where source and target differ
    # (channel positions auto-update and have no penalty maps)
    var moves: seq[int] = @[]
    for pos in state.carray.allSearchPositions():
        if state.assignment[pos] != targetAssignment[pos]:
            moves.add(pos)

    if moves.len == 0:
        return

    # Sample every ~sqrt(n) steps to get a reasonable number of path entries
    let sampleInterval = max(1, int(sqrt(moves.len.float)))
    var stepCount = 0
    var bestCost = state.cost
    var bestAssignment = state.assignment

    while moves.len > 0:
        # Evaluate all remaining moves using direct costDelta (no penalty maps needed)
        var
            bestDelta = high(int)
            bestMoveIndices: seq[int] = @[]

        for mi in 0..<moves.len:
            let pos = moves[mi]
            let targetVal = targetAssignment[pos]
            let delta = state.costDelta(pos, targetVal)

            if delta < bestDelta:
                bestDelta = delta
                bestMoveIndices = @[mi]
            elif delta == bestDelta:
                bestMoveIndices.add(mi)

        # Apply the best move (lean: no penalty map updates)
        let chosenIdx = sample(bestMoveIndices)
        let pos = moves[chosenIdx]
        let targetVal = targetAssignment[pos]
        state.assignValueLean(pos, targetVal)
        moves.del(chosenIdx)
        inc stepCount

        # Track best intermediate
        if state.cost < bestCost:
            bestCost = state.cost
            bestAssignment = state.assignment

        # Early exit on solution
        if state.cost == 0:
            result.add(PathEntry[T](
                assignment: state.assignment,
                cost: 0
            ))
            return

        # Sample at regular intervals
        if stepCount mod sampleInterval == 0:
            result.add(PathEntry[T](
                assignment: state.assignment,
                cost: state.cost
            ))

    # Always include final state
    result.add(PathEntry[T](
        assignment: state.assignment,
        cost: state.cost
    ))

    # Always include the best intermediate if it's better than final
    if bestCost < state.cost:
        result.add(PathEntry[T](
            assignment: bestAssignment,
            cost: bestCost
        ))


proc relinkWorker*[T](data: RelinkWorkerData[T]) {.thread.} =
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

            let task = pool.tasks[idx]
            var relinkState = newRelinkState[T](pool.carrays[idx], task.sourceAssignment, id = idx)
            let pathEntries = relinkPath(relinkState, task.targetAssignment)

            let result = RelinkResult[T](
                pathEntries: pathEntries,
                taskIndex: idx
            )

            # Check for solution
            if pathEntries.len > 0 and pathEntries[^1].cost == 0:
                pool.solutionFound.store(true)

            withLock pool.resultsLock:
                pool.results.add(result)

            if pool.solutionFound.load():
                break

    except CatchableError as e:
        stderr.writeLine("[RelinkWorker " & $data.workerId & "] Error: " & e.msg)
        stderr.writeLine("[RelinkWorker " & $data.workerId & "] Stack: " & e.getStackTrace())


proc buildInitialPopulation*[T](system: ConstraintSystem[T],
                                size: int,
                                tabuThreshold: int,
                                numWorkers: int,
                                verbose: bool,
                                maxLastImprovement: var int): CandidatePool[T] =
    ## Create random states, parallel tabu-improve, return best `size` as pool
    let createSize = size * 2

    if verbose:
        echo &"[Scatter] Building initial population: creating {createSize}, keeping {size}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain

    let popStart = currentTime()

    # Create population of random TabuStates
    var popTemplate = system.baseArray.deepCopy()
    var population = newSeq[TabuState[T]](createSize)
    for i in 0..<createSize:
        let arr = popTemplate.deepCopy()
        population[i] = newTabuState[T](arr, verbose = false, id = i)

    if verbose:
        echo &"[Scatter] Created {createSize} states in {currentTime() - popStart:.2f}s"

    let improveStart = currentTime()

    # Parallel tabu-improve all
    var results: seq[PoolEntry[T]] = @[]
    maxLastImprovement = 0
    for batchResult in improveStates(population, numWorkers, tabuThreshold, verbose = false):
        results.add(PoolEntry[T](
            assignment: batchResult.assignment,
            cost: batchResult.cost
        ))
        maxLastImprovement = max(maxLastImprovement, batchResult.lastImprovement)
        if batchResult.found:
            break

    if verbose:
        echo &"[Scatter] Improved {results.len} states in {currentTime() - improveStart:.2f}s"
        let costs = results.mapIt(it.cost).sorted()
        echo &"[Scatter] Cost distribution: {costs}"

    # Sort by cost and keep best `size`
    results.sort(proc(a, b: PoolEntry[T]): int = cmp(a.cost, b.cost))
    let keepCount = min(size, results.len)
    result.entries = results[0..<keepCount]
    result.updateBounds()

    if verbose:
        result.poolStatistics()


proc scatterImprove*[T](system: ConstraintSystem[T],
                        pool: var CandidatePool[T],
                        scatterThreshold: int = 3,
                        tabuThreshold: int = 10000,
                        relinkThreshold: int = 5000,
                        numWorkers: int = 0,
                        verbose: bool = false,
                        deadline: float = 0.0): bool =
    ## Run scatter search iterations on an existing pool.
    ## Returns true if solution found (system is initialized).
    ## Returns false after scatterThreshold iterations without improvement.

    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers
    let totalStart = currentTime()
    let poolSize = pool.entries.len
    var itersSinceImprovement = 0
    var iter = 0
    var effectiveThreshold = tabuThreshold
    template saveThreshold() =
        system.adaptedTabuThreshold = effectiveThreshold

    while itersSinceImprovement < scatterThreshold or (deadline > 0 and epochTime() < deadline):
        # Check deadline at start of each iteration
        if deadline > 0 and epochTime() > deadline:
            saveThreshold()
            return false

        let iterStart = currentTime()
        let prevBestCost = pool.minCost
        inc iter
        if verbose:
            echo &"[Scatter] === Iteration {iter} (stale={itersSinceImprovement}/{scatterThreshold}) ==="

        # a. PATH RELINKING: For each pair, relink both directions (parallel)
        let relinkStart = currentTime()
        var allPathEntries: seq[PathEntry[T]] = @[]
        var pairCount = 0
        var totalDiffPositions = 0

        # Pre-generate all relinking tasks
        var relinkTasks: seq[RelinkTask[T]] = @[]
        for (i, j) in pool.pairs():
            pairCount += 1
            let entryA = pool.entries[i]
            let entryB = pool.entries[j]
            let dist = distance(entryA, entryB)
            totalDiffPositions += dist
            # A -> B
            relinkTasks.add(RelinkTask[T](
                sourceAssignment: entryA.assignment,
                targetAssignment: entryB.assignment
            ))
            # B -> A
            relinkTasks.add(RelinkTask[T](
                sourceAssignment: entryB.assignment,
                targetAssignment: entryA.assignment
            ))

        if relinkTasks.len > 0:
            if actualWorkers <= 1 or relinkTasks.len == 1:
                # Sequential fallback
                var relinkTemplate = system.baseArray.deepCopy()
                for task in relinkTasks:
                    var relinkArray = relinkTemplate.deepCopy()
                    var relinkState = newRelinkState[T](relinkArray, task.sourceAssignment)
                    let pathEntries = relinkPath(relinkState, task.targetAssignment)
                    allPathEntries.add(pathEntries)
                    if pathEntries.len > 0 and pathEntries[^1].cost == 0:
                        break
                    if deadline > 0 and epochTime() > deadline:
                        break
            else:
                # Parallel path relinking with work-stealing pool
                var carrays = newSeq[ConstrainedArray[T]](relinkTasks.len)
                var templateArray = system.baseArray.deepCopy()
                let bufferAhead = actualWorkers * 2
                let initialBatch = min(bufferAhead, relinkTasks.len)
                for i in 0..<initialBatch:
                    carrays[i] = templateArray.deepCopy()
                var createdSoFar = initialBatch

                var relinkPool = RelinkPool[T](
                    carrays: cast[ptr UncheckedArray[ConstrainedArray[T]]](addr carrays[0]),
                    tasks: cast[ptr UncheckedArray[RelinkTask[T]]](addr relinkTasks[0]),
                    totalTasks: relinkTasks.len,
                    deadline: deadline,
                    results: newSeq[RelinkResult[T]]()
                )
                relinkPool.nextTaskIndex.store(0)
                relinkPool.createdUpTo.store(createdSoFar)
                relinkPool.solutionFound.store(false)
                initLock(relinkPool.resultsLock)

                let workerCount = min(actualWorkers, relinkTasks.len)
                var workers = newSeq[Thread[RelinkWorkerData[T]]](workerCount)
                var workerDatas = newSeq[RelinkWorkerData[T]](workerCount)
                for i in 0..<workerCount:
                    workerDatas[i] = RelinkWorkerData[T](workerId: i, pool: addr relinkPool)
                    createThread(workers[i], relinkWorker[T], workerDatas[i])

                var threadsJoined = false
                defer:
                    if not threadsJoined:
                        if not relinkPool.solutionFound.load():
                            relinkPool.solutionFound.store(true)
                        for i in 0..<workerCount:
                            joinThread(workers[i])
                        threadsJoined = true
                    deinitLock(relinkPool.resultsLock)
                    for i in 0..<workerDatas.len:
                        workerDatas[i].pool = nil

                # Monitor and collect results
                var collectedResults = 0
                var lastResultCount = 0

                while collectedResults < relinkTasks.len and not relinkPool.solutionFound.load():
                    # Create more carrays ahead of workers (lazy, bounded buffer)
                    let nextTask = relinkPool.nextTaskIndex.load()
                    let target = min(nextTask + bufferAhead, relinkTasks.len)
                    while createdSoFar < target and not relinkPool.solutionFound.load():
                        carrays[createdSoFar] = templateArray.deepCopy()
                        createdSoFar += 1
                        relinkPool.createdUpTo.store(createdSoFar)

                    var currentResults: seq[RelinkResult[T]]
                    withLock relinkPool.resultsLock:
                        currentResults = relinkPool.results

                    for i in lastResultCount..<currentResults.len:
                        let res = currentResults[i]
                        allPathEntries.add(res.pathEntries)
                        reset(carrays[res.taskIndex])
                        inc collectedResults
                        if res.pathEntries.len > 0 and res.pathEntries[^1].cost == 0:
                            relinkPool.solutionFound.store(true)
                            break

                    lastResultCount = currentResults.len

                    if collectedResults >= relinkTasks.len or relinkPool.solutionFound.load():
                        break

                    if deadline > 0 and epochTime() > deadline:
                        relinkPool.solutionFound.store(true)
                        break

                    sleep(1)

                if not relinkPool.solutionFound.load():
                    relinkPool.solutionFound.store(true)

                for i in 0..<workerCount:
                    joinThread(workers[i])
                threadsJoined = true

                # Collect any remaining results
                withLock relinkPool.resultsLock:
                    for i in lastResultCount..<relinkPool.results.len:
                        allPathEntries.add(relinkPool.results[i].pathEntries)
                        reset(carrays[relinkPool.results[i].taskIndex])

                withLock relinkPool.resultsLock:
                    relinkPool.results.setLen(0)

        if verbose:
            let relinkElapsed = currentTime() - relinkStart
            let avgDiff = if pairCount > 0: totalDiffPositions div pairCount else: 0
            echo &"[Scatter] Relinked {pairCount} pairs ({pairCount * 2} paths) in {relinkElapsed:.2f}s, avg_diff={avgDiff}, collected {allPathEntries.len} path entries"
            # Path entry cost distribution
            let pathCosts = allPathEntries.mapIt(it.cost).sorted()
            if pathCosts.len > 0:
                let p25 = pathCosts[pathCosts.len div 4]
                let p50 = pathCosts[pathCosts.len div 2]
                let p75 = pathCosts[pathCosts.len * 3 div 4]
                echo &"[Scatter] Path entry costs: min={pathCosts[0]} p25={p25} p50={p50} p75={p75} max={pathCosts[^1]}"

        # Select promising entries: best K by cost, scaled by estimated state memory
        var totalDomainValues = 0
        if system.baseArray.reducedDomain.len > 0:
            for rd in system.baseArray.reducedDomain:
                totalDomainValues += rd.len
        # Rough estimate: penalty maps + constraint overhead ≈ 16 bytes per domain value
        let estimatedStateMB = totalDomainValues * 16 div 1_000_000
        let memoryBudgetStates = max(10, min(100, 2000 div max(1, estimatedStateMB)))
        let maxPromising = min(memoryBudgetStates, max(poolSize, allPathEntries.len div 4))
        allPathEntries.sort(proc(a, b: PathEntry[T]): int = cmp(a.cost, b.cost))
        var promising: seq[PathEntry[T]] = @[]
        for pe in allPathEntries:
            if pe.cost == 0:
                system.initialize(pe.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during path relinking (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                saveThreshold()
                return true
            promising.add(pe)
            if promising.len >= maxPromising:
                break

        # Free path entries — promising has been extracted, allPathEntries is no longer needed.
        # This can reclaim >1 GB for large problems before batch improvement allocates new states.
        allPathEntries.setLen(0)

        if verbose:
            if promising.len > 0:
                echo &"[Scatter] Improving {promising.len} promising entries (best={promising[0].cost}, worst={promising[^1].cost})"
            else:
                echo &"[Scatter] No promising entries to improve"

        # Tabu-improve promising entries — streaming via work-stealing pool (no batching)
        let improveStart = currentTime()
        var improvements: seq[PoolEntry[T]] = @[]
        var improvedCount = 0
        var maxLastImp = 0
        if promising.len > 0:
            let promisingAssignments = promising.mapIt(it.assignment)
            for batchResult in improveFromAssignments(system, promisingAssignments, actualWorkers, relinkThreshold, deadline = deadline):
                inc improvedCount
                maxLastImp = max(maxLastImp, batchResult.lastImprovement)
                if batchResult.found:
                    system.initialize(batchResult.assignment)
                    if verbose:
                        echo &"[Scatter] Solution found during path relinking (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                    saveThreshold()
                    return true
                if batchResult.cost < pool.minCost:
                    improvements.add(PoolEntry[T](
                        assignment: batchResult.assignment,
                        cost: batchResult.cost
                    ))

        if verbose:
            let improveElapsed = currentTime() - improveStart
            echo &"[Scatter] Improved {improvedCount} path entries in {improveElapsed:.2f}s, found {improvements.len} better than pool min={pool.minCost}"
            if improvements.len > 0:
                let impCosts = improvements.mapIt(it.cost).sorted()
                echo &"[Scatter] Improvement costs: {impCosts}"

        # b. UPDATE POOL with improvements
        if improvements.len > 0:
            improvements.sort(proc(a, b: PoolEntry[T]): int = cmp(a.cost, b.cost))
            pool.update(improvements)
            if verbose:
                pool.poolStatistics()

        # Check for solution
        if pool.minCost == 0:
            for entry in pool.entries:
                if entry.cost == 0:
                    system.initialize(entry.assignment)
                    if verbose:
                        echo &"[Scatter] Solution found after pool update (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                    saveThreshold()
                    return true

        # c. DIVERSIFY: Generate fresh random tabu-improved states
        let diversifyCount = max(poolSize div 2, 2)
        let divStart = currentTime()
        if verbose:
            echo &"[Scatter] Diversifying with {diversifyCount} fresh states"

        var freshTemplate = system.baseArray.deepCopy()
        var freshPop = newSeq[TabuState[T]](diversifyCount)
        for i in 0..<diversifyCount:
            let arr = freshTemplate.deepCopy()
            freshPop[i] = newTabuState[T](arr, verbose = false, id = i)

        for batchResult in improveStates(freshPop, actualWorkers, effectiveThreshold, verbose = false, deadline = deadline):
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during diversification (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                saveThreshold()
                return true
            maxLastImp = max(maxLastImp, batchResult.lastImprovement)
            pool.replaceMaxCost(PoolEntry[T](
                assignment: batchResult.assignment,
                cost: batchResult.cost
            ))

        if verbose:
            echo &"[Scatter] Diversification took {currentTime() - divStart:.2f}s"

        # d. INTENSIFY: Re-optimize all pool members with tabu search
        let intStart = currentTime()
        if verbose:
            echo &"[Scatter] Intensifying pool"

        var intensifyTemplate = system.baseArray.deepCopy()
        var intensifyPop = newSeq[TabuState[T]](pool.entries.len)
        for i in 0..<pool.entries.len:
            let arr = intensifyTemplate.deepCopy()
            intensifyPop[i] = newTabuState[T](arr, pool.entries[i].assignment, verbose = false, id = i)

        var newEntries: seq[PoolEntry[T]] = @[]
        for batchResult in improveStates(intensifyPop, actualWorkers, effectiveThreshold, verbose = false, deadline = deadline):
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during intensification (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                saveThreshold()
                return true
            maxLastImp = max(maxLastImp, batchResult.lastImprovement)
            newEntries.add(PoolEntry[T](
                assignment: batchResult.assignment,
                cost: batchResult.cost
            ))

        # Update pool with intensified results
        pool.update(newEntries)

        if verbose:
            echo &"[Scatter] Intensification took {currentTime() - intStart:.2f}s"

        # Adapt threshold based on observed search depth (only increases)
        let prevThreshold = effectiveThreshold
        if maxLastImp > 0:
            effectiveThreshold = max(effectiveThreshold, max(maxLastImp, 500))
        if verbose and effectiveThreshold != prevThreshold:
            echo &"[Scatter] Adaptive threshold: {prevThreshold} -> {effectiveThreshold} (maxLastImp={maxLastImp})"

        # Track improvement
        if pool.minCost < prevBestCost:
            itersSinceImprovement = 0
        else:
            inc itersSinceImprovement
            if itersSinceImprovement >= scatterThreshold and deadline > 0:
                # Running past stale threshold due to deadline — deepen search to escape basin
                effectiveThreshold = effectiveThreshold + effectiveThreshold div 2
                if verbose:
                    echo &"[Scatter] Stale deepening threshold to {effectiveThreshold}"

        if verbose:
            let iterElapsed = currentTime() - iterStart
            pool.poolStatistics()
            echo &"[Scatter] Iteration {iter} completed in {iterElapsed:.1f}s ({currentTime() - totalStart:.1f}s total)"

    # No solution found
    if verbose:
        echo &"[Scatter] No solution after {iter} iterations (stale={scatterThreshold}): best cost={pool.minCost} ({currentTime() - totalStart:.1f}s total)"
    saveThreshold()
    return false


proc lnsImprove*[T](system: ConstraintSystem[T],
                    pool: var CandidatePool[T],
                    scatterThreshold: int = 3,
                    tabuThreshold: int = 10000,
                    numWorkers: int = 0,
                    verbose: bool = false,
                    deadline: float = 0.0): bool =
    ## Constraint-Group LNS: destroy positions covered by random compact constraints,
    ## then repair with tabu search. O(poolSize) per iteration instead of O(poolSize^2).
    ## Returns true if solution found (system is initialized).

    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers
    let totalStart = currentTime()
    let poolSize = pool.entries.len
    let totalPositions = system.baseArray.len
    let maxCompactSize = totalPositions div 3  # 33% threshold

    # Identify compact constraints (those spanning ≤33% of positions)
    var compactIndices: seq[int] = @[]
    for ci, c in system.baseArray.constraints:
        if c.positions.len <= maxCompactSize and c.positions.len > 0:
            compactIndices.add(ci)

    if verbose:
        echo &"[LNS] Compact constraints: {compactIndices.len}/{system.baseArray.constraints.len} (max size={maxCompactSize}/{totalPositions})"

    if compactIndices.len == 0:
        if verbose:
            echo &"[LNS] No compact constraints found, falling back to random perturbation"
        return false

    var itersSinceImprovement = 0
    var iter = 0
    var destroyCount = 1  # Start by destroying 1 constraint group
    var effectiveThreshold = tabuThreshold
    template saveLnsThreshold() =
        system.adaptedTabuThreshold = effectiveThreshold

    while itersSinceImprovement < scatterThreshold or (deadline > 0 and epochTime() < deadline):
        # Check deadline at start of each iteration
        if deadline > 0 and epochTime() > deadline:
            saveLnsThreshold()
            return false

        let iterStart = currentTime()
        let prevBestCost = pool.minCost
        inc iter
        if verbose:
            echo &"[LNS] === Iteration {iter} (stale={itersSinceImprovement}/{scatterThreshold}, destroy={destroyCount}) ==="

        # a. PERTURB: For each pool entry, create 3 variants with increasing destruction
        let perturbStart = currentTime()
        var perturbed: seq[seq[T]] = @[]

        for ei in 0..<poolSize:
            let baseAssignment = pool.entries[ei].assignment

            for sizeOffset in 0..2:
                let numDestroy = destroyCount + sizeOffset
                var destroyed: PackedSet[int]

                # Pick random compact constraints to destroy
                var chosen: seq[int] = @[]
                var candidates = compactIndices
                for d in 0..<min(numDestroy, candidates.len):
                    let idx = rand(candidates.len - 1)
                    chosen.add(candidates[idx])
                    candidates.del(idx)

                # Collect all positions from chosen constraints
                for ci in chosen:
                    for pos in system.baseArray.constraints[ci].positions.items:
                        destroyed.incl(pos)

                # Create perturbed assignment: randomize destroyed positions
                var newAssignment = baseAssignment
                for pos in destroyed.items:
                    if pos notin system.baseArray.channelPositions:
                        newAssignment[pos] = sample(system.baseArray.reducedDomain[pos])

                perturbed.add(newAssignment)

        if verbose:
            echo &"[LNS] Created {perturbed.len} perturbed states in {currentTime() - perturbStart:.2f}s"

        # b. REPAIR: Tabu-improve perturbed states — streaming via work-stealing pool
        let repairStart = currentTime()
        var improvements: seq[PoolEntry[T]] = @[]
        var repairedCount = 0
        var maxLastImp = 0

        if perturbed.len > 0:
            for batchResult in improveFromAssignments(system, perturbed, actualWorkers, effectiveThreshold, deadline = deadline):
                inc repairedCount
                maxLastImp = max(maxLastImp, batchResult.lastImprovement)
                if batchResult.found:
                    system.initialize(batchResult.assignment)
                    if verbose:
                        echo &"[LNS] Solution found during repair (iter {iter}, {currentTime() - totalStart:.2f}s total)"
                    saveLnsThreshold()
                    return true
                if batchResult.cost < pool.maxCost:
                    improvements.add(PoolEntry[T](
                        assignment: batchResult.assignment,
                        cost: batchResult.cost
                    ))

        if verbose:
            let repairElapsed = currentTime() - repairStart
            echo &"[LNS] Repaired {repairedCount} states in {repairElapsed:.2f}s, {improvements.len} better than pool max={pool.maxCost}"
            if improvements.len > 0:
                let impCosts = improvements.mapIt(it.cost).sorted()
                echo &"[LNS] Improvement costs: min={impCosts[0]} max={impCosts[^1]}"

        # Update pool with improvements
        if improvements.len > 0:
            improvements.sort(proc(a, b: PoolEntry[T]): int = cmp(a.cost, b.cost))
            for imp in improvements:
                pool.replaceMaxCost(imp)
            if verbose:
                pool.poolStatistics()

        # Check for solution
        if pool.minCost == 0:
            for entry in pool.entries:
                if entry.cost == 0:
                    system.initialize(entry.assignment)
                    if verbose:
                        echo &"[LNS] Solution found after pool update (iter {iter}, {currentTime() - totalStart:.2f}s total)"
                    saveLnsThreshold()
                    return true

        # c. DIVERSIFY: Fresh random states
        let diversifyCount = max(poolSize div 2, 2)
        let divStart = currentTime()
        if verbose:
            echo &"[LNS] Diversifying with {diversifyCount} fresh states"

        var lnsFreshTemplate = system.baseArray.deepCopy()
        var freshPop = newSeq[TabuState[T]](diversifyCount)
        for i in 0..<diversifyCount:
            let arr = lnsFreshTemplate.deepCopy()
            freshPop[i] = newTabuState[T](arr, verbose = false, id = i)

        for batchResult in improveStates(freshPop, actualWorkers, effectiveThreshold, verbose = false, deadline = deadline):
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[LNS] Solution found during diversification (iter {iter}, {currentTime() - totalStart:.2f}s total)"
                saveLnsThreshold()
                return true
            maxLastImp = max(maxLastImp, batchResult.lastImprovement)
            pool.replaceMaxCost(PoolEntry[T](
                assignment: batchResult.assignment,
                cost: batchResult.cost
            ))

        if verbose:
            echo &"[LNS] Diversification took {currentTime() - divStart:.2f}s"

        # Adapt threshold based on observed search depth (only increases)
        let prevThreshold = effectiveThreshold
        if maxLastImp > 0:
            effectiveThreshold = max(effectiveThreshold, max(maxLastImp, 500))
        if verbose and effectiveThreshold != prevThreshold:
            echo &"[LNS] Adaptive threshold: {prevThreshold} -> {effectiveThreshold} (maxLastImp={maxLastImp})"

        # Track improvement and adapt destroy count
        if pool.minCost < prevBestCost:
            itersSinceImprovement = 0
            destroyCount = 1  # Reset on improvement
        else:
            inc itersSinceImprovement
            destroyCount = min(destroyCount + 1, compactIndices.len div 2)  # Escalate
            if itersSinceImprovement >= scatterThreshold and deadline > 0:
                # Running past stale threshold due to deadline — deepen search to escape basin
                effectiveThreshold = effectiveThreshold + effectiveThreshold div 2
                if verbose:
                    echo &"[LNS] Stale deepening threshold to {effectiveThreshold}"

        if verbose:
            let iterElapsed = currentTime() - iterStart
            pool.poolStatistics()
            echo &"[LNS] Iteration {iter} completed in {iterElapsed:.1f}s ({currentTime() - totalStart:.1f}s total)"

    # No solution found
    if verbose:
        echo &"[LNS] No solution after {iter} iterations (stale={scatterThreshold}): best cost={pool.minCost} ({currentTime() - totalStart:.1f}s total)"
    saveLnsThreshold()
    return false


proc scatterResolve*[T](system: ConstraintSystem[T],
                        poolSize: int = 10,
                        scatterThreshold: int = 5,
                        tabuThreshold: int = 10000,
                        relinkThreshold: int = 5000,
                        numWorkers: int = 0,
                        verbose: bool = false) =
    ## Scatter search: population-based metaheuristic combining path relinking with tabu search.

    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers
    let totalStart = currentTime()

    if verbose:
        echo &"[Scatter] vars={system.baseArray.len} constraints={system.baseArray.constraints.len} pool={poolSize} scatterThreshold={scatterThreshold} threshold={tabuThreshold} relinkThreshold={relinkThreshold} workers={actualWorkers}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)
        system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain

    # 1. Build initial population
    let buildStart = currentTime()
    var maxLastImp = 0
    var pool = buildInitialPopulation[T](system, poolSize, tabuThreshold, actualWorkers, verbose, maxLastImp)

    if verbose:
        echo &"[Scatter] Initial population built in {currentTime() - buildStart:.2f}s"

    # Check if solution found during initial population
    if pool.minCost == 0:
        for entry in pool.entries:
            if entry.cost == 0:
                system.initialize(entry.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during initial population ({currentTime() - totalStart:.2f}s total)"
                return

    # 2. Run scatter search iterations
    if not scatterImprove(system, pool, scatterThreshold, tabuThreshold, relinkThreshold, actualWorkers, verbose):
        raise newException(NoSolutionFoundError, "Can't find satisfying solution with scatter search")
