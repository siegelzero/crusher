import std/[random, math, sequtils, strformat, algorithm, atomics, tables, packedsets]
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

proc relinkPath*[T](state: TabuState[T], targetAssignment: seq[T]): seq[PathEntry[T]] =
    ## Path relinking: greedy walk from state's current assignment toward targetAssignment.
    ## The state is mutated during relinking via assignValue (incremental updates).
    ## Samples every sampleInterval steps plus tracks the best intermediate state.

    # Collect positions where source and target differ
    var moves: seq[int] = @[]
    for pos in state.carray.allPositions():
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
        # Evaluate all remaining moves, pick the best
        var
            bestDelta = high(int)
            bestMoveIndices: seq[int] = @[]

        for mi in 0..<moves.len:
            let pos = moves[mi]
            let targetVal = targetAssignment[pos]
            let oldVal = state.assignment[pos]
            let oldPenalty = state.penaltyAt(pos, oldVal)
            let newPenalty = state.penaltyAt(pos, targetVal)
            let delta = newPenalty - oldPenalty

            if delta < bestDelta:
                bestDelta = delta
                bestMoveIndices = @[mi]
            elif delta == bestDelta:
                bestMoveIndices.add(mi)

        # Apply the best move
        let chosenIdx = sample(bestMoveIndices)
        let pos = moves[chosenIdx]
        let targetVal = targetAssignment[pos]
        state.assignValue(pos, targetVal)
        moves.del(chosenIdx)
        inc stepCount

        # Track best intermediate
        if state.cost < bestCost:
            bestCost = state.cost
            bestAssignment = state.assignment

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


proc buildInitialPopulation*[T](system: ConstraintSystem[T],
                                size: int,
                                tabuThreshold: int,
                                numWorkers: int,
                                verbose: bool): CandidatePool[T] =
    ## Create random states, parallel tabu-improve, return best `size` as pool
    let createSize = size * 2

    if verbose:
        echo &"[Scatter] Building initial population: creating {createSize}, keeping {size}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)

    let popStart = currentTime()

    # Create population of random TabuStates
    var population = newSeq[TabuState[T]](createSize)
    for i in 0..<createSize:
        let systemCopy = system.deepCopy()
        population[i] = newTabuState[T](systemCopy.baseArray, verbose = false, id = i)

    if verbose:
        echo &"[Scatter] Created {createSize} states in {currentTime() - popStart:.2f}s"

    let improveStart = currentTime()

    # Parallel tabu-improve all
    var results: seq[PoolEntry[T]] = @[]
    for batchResult in improveStates(population, numWorkers, tabuThreshold, verbose = false):
        results.add(PoolEntry[T](
            assignment: batchResult.assignment,
            cost: batchResult.cost
        ))
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
                        verbose: bool = true,
                        deadline: float = 0.0): bool =
    ## Run scatter search iterations on an existing pool.
    ## Returns true if solution found (system is initialized).
    ## Returns false after scatterThreshold iterations without improvement.

    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers
    let totalStart = currentTime()
    let poolSize = pool.entries.len
    var itersSinceImprovement = 0
    var iter = 0

    while itersSinceImprovement < scatterThreshold:
        # Check deadline at start of each iteration
        if deadline > 0 and epochTime() > deadline:
            return false

        let iterStart = currentTime()
        let prevBestCost = pool.minCost
        inc iter
        if verbose:
            echo &"[Scatter] === Iteration {iter} (stale={itersSinceImprovement}/{scatterThreshold}) ==="

        # a. PATH RELINKING: For each pair, relink both directions
        let relinkStart = currentTime()
        var allPathEntries: seq[PathEntry[T]] = @[]
        var pairCount = 0
        var totalDiffPositions = 0

        for (i, j) in pool.pairs():
            pairCount += 1
            let entryA = pool.entries[i]
            let entryB = pool.entries[j]

            let dist = distance(entryA, entryB)
            totalDiffPositions += dist

            # A -> B
            block:
                let systemCopy = system.deepCopy()
                var relinkState = newTabuState[T](systemCopy.baseArray, entryA.assignment, verbose = false)
                let pathEntries = relinkPath(relinkState, entryB.assignment)
                allPathEntries.add(pathEntries)

            # B -> A
            block:
                let systemCopy = system.deepCopy()
                var relinkState = newTabuState[T](systemCopy.baseArray, entryB.assignment, verbose = false)
                let pathEntries = relinkPath(relinkState, entryA.assignment)
                allPathEntries.add(pathEntries)

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

        # Select promising entries: best K by cost, where K scales with pool size
        let maxPromising = min(max(poolSize, allPathEntries.len div 4), 100)
        allPathEntries.sort(proc(a, b: PathEntry[T]): int = cmp(a.cost, b.cost))
        var promising: seq[PathEntry[T]] = @[]
        for pe in allPathEntries:
            if pe.cost == 0:
                system.initialize(pe.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during path relinking (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                return true
            promising.add(pe)
            if promising.len >= maxPromising:
                break

        if verbose:
            if promising.len > 0:
                echo &"[Scatter] Improving {promising.len} promising entries (best={promising[0].cost}, worst={promising[^1].cost})"
            else:
                echo &"[Scatter] No promising entries to improve"

        # Tabu-improve promising entries
        let improveStart = currentTime()
        var improvements: seq[PoolEntry[T]] = @[]
        var improvedCount = 0
        if promising.len > 0:
            var toImprove = newSeq[TabuState[T]](promising.len)
            for pi in 0..<promising.len:
                let sc = system.deepCopy()
                toImprove[pi] = newTabuState[T](sc.baseArray, promising[pi].assignment, verbose = false, id = pi)

            for batchResult in improveStates(toImprove, actualWorkers, relinkThreshold, verbose = false, deadline = deadline):
                inc improvedCount
                if batchResult.found:
                    system.initialize(batchResult.assignment)
                    if verbose:
                        echo &"[Scatter] Solution found during path relinking (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
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
                    return true

        # c. DIVERSIFY: Generate fresh random tabu-improved states
        let diversifyCount = max(poolSize div 2, 2)
        let divStart = currentTime()
        if verbose:
            echo &"[Scatter] Diversifying with {diversifyCount} fresh states"

        var freshPop = newSeq[TabuState[T]](diversifyCount)
        for i in 0..<diversifyCount:
            let sc = system.deepCopy()
            freshPop[i] = newTabuState[T](sc.baseArray, verbose = false, id = i)

        for batchResult in improveStates(freshPop, actualWorkers, tabuThreshold, verbose = false, deadline = deadline):
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during diversification (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                return true
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

        var intensifyPop = newSeq[TabuState[T]](pool.entries.len)
        for i in 0..<pool.entries.len:
            let sc = system.deepCopy()
            intensifyPop[i] = newTabuState[T](sc.baseArray, pool.entries[i].assignment, verbose = false, id = i)

        var newEntries: seq[PoolEntry[T]] = @[]
        for batchResult in improveStates(intensifyPop, actualWorkers, tabuThreshold, verbose = false, deadline = deadline):
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[Scatter] Solution found during intensification (iter {iter + 1}, {currentTime() - totalStart:.2f}s total)"
                return true
            newEntries.add(PoolEntry[T](
                assignment: batchResult.assignment,
                cost: batchResult.cost
            ))

        # Update pool with intensified results
        pool.update(newEntries)

        if verbose:
            echo &"[Scatter] Intensification took {currentTime() - intStart:.2f}s"

        # Track improvement
        if pool.minCost < prevBestCost:
            itersSinceImprovement = 0
        else:
            inc itersSinceImprovement

        if verbose:
            let iterElapsed = currentTime() - iterStart
            pool.poolStatistics()
            echo &"[Scatter] Iteration {iter} completed in {iterElapsed:.1f}s ({currentTime() - totalStart:.1f}s total)"

    # No solution found
    if verbose:
        echo &"[Scatter] No solution after {iter} iterations (stale={scatterThreshold}): best cost={pool.minCost} ({currentTime() - totalStart:.1f}s total)"
    return false


proc lnsImprove*[T](system: ConstraintSystem[T],
                    pool: var CandidatePool[T],
                    scatterThreshold: int = 3,
                    tabuThreshold: int = 10000,
                    numWorkers: int = 0,
                    verbose: bool = true,
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

    while itersSinceImprovement < scatterThreshold:
        # Check deadline at start of each iteration
        if deadline > 0 and epochTime() > deadline:
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

        # b. REPAIR: Tabu-improve all perturbed states
        let repairStart = currentTime()
        var improvements: seq[PoolEntry[T]] = @[]
        var repairedCount = 0

        var toRepair = newSeq[TabuState[T]](perturbed.len)
        for pi in 0..<perturbed.len:
            let sc = system.deepCopy()
            toRepair[pi] = newTabuState[T](sc.baseArray, perturbed[pi], verbose = false, id = pi)

        for batchResult in improveStates(toRepair, actualWorkers, tabuThreshold, verbose = false, deadline = deadline):
            inc repairedCount
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[LNS] Solution found during repair (iter {iter}, {currentTime() - totalStart:.2f}s total)"
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
                    return true

        # c. DIVERSIFY: Fresh random states
        let diversifyCount = max(poolSize div 2, 2)
        let divStart = currentTime()
        if verbose:
            echo &"[LNS] Diversifying with {diversifyCount} fresh states"

        var freshPop = newSeq[TabuState[T]](diversifyCount)
        for i in 0..<diversifyCount:
            let sc = system.deepCopy()
            freshPop[i] = newTabuState[T](sc.baseArray, verbose = false, id = i)

        for batchResult in improveStates(freshPop, actualWorkers, tabuThreshold, verbose = false, deadline = deadline):
            if batchResult.found:
                system.initialize(batchResult.assignment)
                if verbose:
                    echo &"[LNS] Solution found during diversification (iter {iter}, {currentTime() - totalStart:.2f}s total)"
                return true
            pool.replaceMaxCost(PoolEntry[T](
                assignment: batchResult.assignment,
                cost: batchResult.cost
            ))

        if verbose:
            echo &"[LNS] Diversification took {currentTime() - divStart:.2f}s"

        # Track improvement and adapt destroy count
        if pool.minCost < prevBestCost:
            itersSinceImprovement = 0
            destroyCount = 1  # Reset on improvement
        else:
            inc itersSinceImprovement
            destroyCount = min(destroyCount + 1, compactIndices.len div 2)  # Escalate

        if verbose:
            let iterElapsed = currentTime() - iterStart
            pool.poolStatistics()
            echo &"[LNS] Iteration {iter} completed in {iterElapsed:.1f}s ({currentTime() - totalStart:.1f}s total)"

    # No solution found
    if verbose:
        echo &"[LNS] No solution after {iter} iterations (stale={scatterThreshold}): best cost={pool.minCost} ({currentTime() - totalStart:.1f}s total)"
    return false


proc scatterResolve*[T](system: ConstraintSystem[T],
                        poolSize: int = 10,
                        scatterThreshold: int = 5,
                        tabuThreshold: int = 10000,
                        relinkThreshold: int = 5000,
                        numWorkers: int = 0,
                        verbose: bool = true) =
    ## Scatter search: population-based metaheuristic combining path relinking with tabu search.

    let actualWorkers = if numWorkers <= 0: getOptimalWorkerCount() else: numWorkers
    let totalStart = currentTime()

    if verbose:
        echo &"[Scatter] vars={system.baseArray.len} constraints={system.baseArray.constraints.len} pool={poolSize} scatterThreshold={scatterThreshold} threshold={tabuThreshold} relinkThreshold={relinkThreshold} workers={actualWorkers}"

    # Compute reduced domain once
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)

    # 1. Build initial population
    let buildStart = currentTime()
    var pool = buildInitialPopulation[T](system, poolSize, tabuThreshold, actualWorkers, verbose)

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
