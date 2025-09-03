import std/[packedsets, random, sequtils, tables, atomics, strformat, strutils, os, times, algorithm]
import ../expressions
import ../constrainedArray
import ../constraintSystem
import ../constraints/[algebraic, stateful, allDifferent, linear, minConstraint, maxConstraint, sumConstraint, elementState, globalCardinality]

randomize()

################################################################################
# Type definitions
################################################################################

type
    ConstraintTiming* = object
        totalTime*: float
        callCount*: int
        constraintType*: string

    TabuState*[T] = ref object of RootObj
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[StatefulConstraint[T]]]
        constraints*: seq[StatefulConstraint[T]]
        neighbors*: seq[seq[int]]
        penaltyMap*: seq[seq[int]]
        domain*: seq[seq[T]]

        assignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

        iteration*: int
        tabu*: seq[seq[int]]

        # Timing statistics for profiling
        constraintTimings*: Table[string, ConstraintTiming]
        enableTiming*: bool

################################################################################
# Penalty Routines
################################################################################

proc movePenalty*[T](state: TabuState[T], constraint: StatefulConstraint[T], position: int, newValue: T): int {.inline.} =
    let oldValue = state.assignment[position]

    # Time the operation if timing is enabled
    var startTime: float
    if state.enableTiming:
        startTime = epochTime()

    case constraint.stateType:
        of AllDifferentType:
            result = constraint.allDifferentState.cost + constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            result = 0
        of LinearType:
            result = constraint.linearConstraintState.cost + constraint.linearConstraintState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            result = constraint.algebraicConstraintState.cost + constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)
        of ReifiedLinearType:
            result = constraint.reifiedLinearState.cost + constraint.reifiedLinearState.moveDelta(position, oldValue, newValue)
        of MinType:
            result = constraint.minConstraintState.cost + constraint.minConstraintState.moveDelta(position, oldValue, newValue)
        of MaxType:
            result = constraint.maxConstraintState.cost + constraint.maxConstraintState.moveDelta(position, oldValue, newValue)
        of SumType:
            result = constraint.sumConstraintState.cost + constraint.sumConstraintState.moveDelta(position, oldValue, newValue)
        of GlobalCardinalityType:
            result = constraint.globalCardinalityState.cost + constraint.globalCardinalityState.moveDelta(position, oldValue, newValue)
        of RegularType:
            result = constraint.regularState.cost + constraint.moveDelta(position, oldValue, newValue)

    # Record timing if enabled
    if state.enableTiming:
        let elapsed = epochTime() - startTime
        let constraintType = constraint.getConstraintTypeName()
        if constraintType in state.constraintTimings:
            state.constraintTimings[constraintType].totalTime += elapsed
            state.constraintTimings[constraintType].callCount += 1
        else:
            state.constraintTimings[constraintType] = ConstraintTiming(
                totalTime: elapsed,
                callCount: 1,
                constraintType: constraintType
            )

################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: TabuState[T], position: int) =
    # Computes penalties for all constraints involving the position, and updates penalty map
    var penalty: int
    for value in state.domain[position]:
        penalty = 0
        for constraint in state.constraintsAtPosition[position]:
            penalty += state.movePenalty(constraint, position, value)
        state.penaltyMap[position][value] = penalty


proc updateNeighborPenalties*[T](state: TabuState[T], position: int) =
    # Updates penalties for all neighboring positions to the given position
    for nbr in state.neighbors[position]:
        state.updatePenaltiesForPosition(nbr)


proc rebuildPenaltyMap*[T](state: TabuState[T]) =
    for position in state.carray.allPositions():
        state.updatePenaltiesForPosition(position)

################################################################################
# TabuState creation
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], enableTiming: bool = false) =
    # Initializes all structures and data for the state TabuState[T]
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[StatefulConstraint[T]]](carray.len)
    state.neighbors = newSeq[seq[int]](carray.len)
    # Use the current domain (should already be pre-computed)
    state.domain = newSeq[seq[T]](carray.len)
    for pos in carray.allPositions():
        state.domain[pos] = carray.domain[pos]

    state.iteration = 0
    state.tabu = newSeq[seq[int]](carray.len)

    # Initialize timing
    state.enableTiming = enableTiming
    state.constraintTimings = initTable[string, ConstraintTiming]()

    for pos in carray.allPositions():
        if state.domain[pos].len > 0:
            state.tabu[pos] = newSeq[int](max(state.domain[pos]) + 1)
        else:
            # Handle empty domain - this indicates inconsistent constraints
            echo "Warning: Variable at position ", pos, " has empty domain"
            state.tabu[pos] = newSeq[int](1)  # Minimal tabu array

    # Group constraints involving each position
    for constraint in carray.constraints:
        state.constraints.add(constraint)
        for pos in constraint.positions:
            state.constraintsAtPosition[pos].add(constraint)

    # Collect neighbors of each position
    var neighborSet: PackedSet[int] = toPackedSet[int]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for constraint in state.constraintsAtPosition[pos]:
            neighborSet.incl(constraint.positions)
        neighborSet.excl(pos)
        state.neighbors[pos] = toSeq(neighborSet)

    # Initialize with random assignment  
    state.assignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        if state.domain[pos].len > 0:
            state.assignment[pos] = sample(state.domain[pos])
        else:
            # Handle empty domain - use original domain as fallback
            # This shouldn't happen with well-formed problems, but provides robustness
            if carray.domain[pos].len > 0:
                state.assignment[pos] = sample(carray.domain[pos])
            else:
                # Last resort: use default value
                state.assignment[pos] = T(0)

    # Initialize constraint states with current assignment
    for constraint in state.constraints:
        constraint.initialize(state.assignment)

    # Compute cost
    for cons in carray.constraints:
        state.cost += cons.penalty()

    state.bestCost = state.cost
    state.bestAssignment = state.assignment

    # Construct penalty map for each location and value
    state.penaltyMap = newSeq[seq[int]](state.carray.len)
    for pos in state.carray.allPositions():
        state.penaltyMap[pos] = newSeq[int](max(state.domain[pos]) + 1)

    for pos in state.carray.allPositions():
        state.updatePenaltiesForPosition(pos)


proc newTabuState*[T](carray: ConstrainedArray[T], enableTiming: bool = false): TabuState[T] =
    # Allocates and initializes new TabuState[T]
    new(result)
    result.init(carray, enableTiming)

proc printTimingStats*[T](state: TabuState[T]) =
    # Print timing statistics for constraint types
    if not state.enableTiming or state.constraintTimings.len == 0:
        return

    echo "\n=== Constraint Timing Statistics ==="
    echo "Type                 Calls    Total(s)   Avg(μs)    %"

    # Calculate total time across all constraints
    var totalTime = 0.0
    for timing in state.constraintTimings.values:
        totalTime += timing.totalTime

    # Sort by total time descending 
    var timingItems: seq[(string, ConstraintTiming)] = @[]
    for constraintType, timing in state.constraintTimings.pairs:
        timingItems.add((constraintType, timing))

    algorithm.sort(timingItems, proc(x, y: (string, ConstraintTiming)): int = 
        if x[1].totalTime > y[1].totalTime: -1 
        elif x[1].totalTime < y[1].totalTime: 1 
        else: 0)

    for (constraintType, timing) in timingItems:
        let avgMicros = (timing.totalTime * 1_000_000.0) / timing.callCount.float
        let percentage = (timing.totalTime / totalTime) * 100.0
        echo fmt"{constraintType:<20} {timing.callCount:<8} {timing.totalTime:<10.3f} {avgMicros:<10.1f} {percentage:<6.1f}"

################################################################################
# Value Assignment
################################################################################

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    # Updates current assignment of state by setting value to the position
    let oldValue = state.assignment[position]

    # Calculate cost delta BEFORE updating constraint states using moveDelta
    var delta = 0
    for constraint in state.constraintsAtPosition[position]:
        case constraint.stateType:
            of AllDifferentType:
                delta += constraint.allDifferentState.moveDelta(position, oldValue, value)
            of ElementConstraint:
                delta += constraint.elementState.moveDelta(position, oldValue, value)
            of LinearType:
                delta += constraint.linearConstraintState.moveDelta(position, oldValue, value)
            of AlgebraicType:
                delta += constraint.algebraicConstraintState.moveDelta(position, oldValue, value)
            of ReifiedLinearType:
                delta += constraint.reifiedLinearState.moveDelta(position, oldValue, value)
            of MinType:
                delta += constraint.minConstraintState.moveDelta(position, oldValue, value)
            of MaxType:
                delta += constraint.maxConstraintState.moveDelta(position, oldValue, value)
            of SumType:
                delta += constraint.sumConstraintState.moveDelta(position, oldValue, value)
            of GlobalCardinalityType:
                delta += constraint.globalCardinalityState.moveDelta(position, oldValue, value)
            of RegularType:
                delta += constraint.moveDelta(position, oldValue, value)

    # Update assignment
    state.assignment[position] = value

    # Update all constraint states that involve this position
    for constraint in state.constraintsAtPosition[position]:
        constraint.updatePosition(position, value)

    # Apply the pre-calculated cost delta
    state.cost += delta

    # Rebuild penalty maps for this position and neighbors (since constraint states changed)
    state.updateNeighborPenalties(position)

################################################################################
# Neighborhood evaluation
################################################################################

proc bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    # Returns the best valid next moves for the state.
    # Evaluates the entire neighborhood to find best non-tabu or improving moves.
    var
        delta: int
        bestMoveCost = high(int)
        oldPenalty: int
        oldValue: T

    for position in state.carray.allPositions():
        oldValue = state.assignment[position]
        oldPenalty = state.penaltyMap[position][oldValue]
        if oldPenalty == 0:
            continue

        for newValue in state.domain[position]:
            if newValue == oldValue:
                continue
            delta = state.penaltyMap[position][newValue] - oldPenalty
            # Allow the move if the new value is not tabu for the position
            # or if the new improved cost is better than the best seen so far (aspiration criterion)
            if state.tabu[position][newValue] <= state.iteration or state.cost + delta < state.bestCost:
                if state.cost + delta < bestMoveCost:
                    result = @[(position, newValue)]
                    bestMoveCost = state.cost + delta
                elif state.cost + delta == bestMoveCost:
                    result.add((position, newValue))


proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.assignment[position]
        state.assignValue(position, newValue)
        state.tabu[position][oldValue] = state.iteration + 1 + state.iteration mod 10

################################################################################
# Normal tabu search
################################################################################

proc tabuImprove*[T](state: TabuState[T], threshold: int): TabuState[T] =
    let startTime = epochTime()
    var lastImprovement = 0

    while state.iteration - lastImprovement < threshold:
        state.applyBestMove()
        if state.cost < state.bestCost:
            # echo "Found better solution with cost ", state.cost
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
        if state.cost == 0:
            break
        state.iteration += 1
    
    # Don't report timing here - let the caller handle it
    
    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int, enableTiming: bool = false): TabuState[T] =
    var state = newTabuState[T](carray, enableTiming)
    return state.tabuImprove(threshold)

################################################################################
# Tabu search with message passing for early termination
################################################################################

proc tabuImproveWithTermination*[T](state: TabuState[T], threshold: int, shouldTerminate: proc(): bool {.gcsafe.}): TabuState[T] {.gcsafe.} =
    var lastImprovement = 0

    while state.iteration - lastImprovement < threshold:
        if shouldTerminate():
            break
        state.applyBestMove()
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
        if state.cost == 0:
            return state
        state.iteration += 1

    return state

proc tabuImproveWithTermination*[T](carray: ConstrainedArray[T], threshold: int, shouldTerminate: proc(): bool {.gcsafe.}, enableTiming: bool = false): TabuState[T] {.gcsafe.} =
    var state = newTabuState[T](carray, enableTiming)
    return state.tabuImproveWithTermination(threshold, shouldTerminate)

################################################################################
# Parallel tabu search types and worker
################################################################################

type
    SharedResult*[T] = object
        solved*: Atomic[bool]
        solutionFound*: Atomic[bool] 
        bestCost*: Atomic[int]
        solutionWorkerId*: Atomic[int]
        assignment*: seq[T]  # Protected by solved flag

    BatchSharedResult*[T] = object
        solutionFound*: Atomic[bool]
        bestCost*: Atomic[int]
        solutionWorkerId*: Atomic[int]
        solutionAssignment*: seq[T]
        # Storage for all improved states
        improvedStates*: seq[TabuState[T]]

    WorkerParams*[T] = object
        systemCopy*: ConstraintSystem[T]
        threshold*: int
        result*: ptr SharedResult[T]
        workerId*: int
        verbose*: bool

proc tabuSearchWorker*[T](params: WorkerParams[T]) {.thread.} =
    ## Worker thread that performs tabu search and updates shared result
    # Create termination check function
    proc shouldTerminate(): bool {.gcsafe.} = params.result.solutionFound.load()

    # Set different random seeds for each worker
    randomize(params.workerId * 1000 + int(epochTime()))

    let startTime = epochTime()
    # Enable timing only for worker 0 and only in verbose mode to avoid too much overhead
    let enableTiming = params.verbose and params.workerId == 0

    # Domains are already set by the main thread - no need for domain reduction

    # Use the same multi-restart logic as sequentialSearch iterator
    var bestResult: TabuState[T]
    var found = false
    var currentThreshold = params.threshold

    for attempt in 0..<10:  # Same as sequentialSearch maxAttempts
        # Check if another worker found a solution
        if shouldTerminate():
            if params.verbose:
                echo "DEBUG: Worker ", params.workerId, " terminating early - solution found by another worker"
            return

        randomize(attempt * 1000 + int(epochTime()))  # Same seed pattern as sequentialSearch
        let attemptStartTime = epochTime()
        let improved = params.systemCopy.baseArray.tabuImproveWithTermination(currentThreshold, shouldTerminate)
        let attemptEndTime = epochTime()
        let attemptDuration = attemptEndTime - attemptStartTime
        let iterationsPerSec = if attemptDuration > 0:
            improved.iteration.float / attemptDuration
        else:
            0.0
        if params.verbose:
            echo "DEBUG: Worker ", params.workerId, " attempt ", attempt, " cost: ", improved.cost, 
                 " (", improved.iteration, " iters @ ", int(iterationsPerSec), " iters/sec)"

        # DEBUG: Show the first few assignment values for worker 0
        if params.workerId == 0 and attempt == 0 and params.verbose:
            echo "DEBUG: Worker 0 initial assignment (first 10): ", improved.assignment[0..<min(10, improved.assignment.len)]

        if not found or improved.cost < bestResult.cost:
            bestResult = improved
            found = true

        if improved.cost == 0:
            bestResult = improved
            break

        currentThreshold = currentThreshold * 2  # Same threshold doubling as sequentialSearch

    let improved = if found: bestResult else: params.systemCopy.baseArray.tabuImproveWithTermination(params.threshold, shouldTerminate)
    let elapsed = epochTime() - startTime

    # Log profiling info for this worker
    if elapsed > 0:
        let totalIterations = improved.iteration
        let iterationsPerSecond = totalIterations.float / elapsed
        if params.verbose:
            echo fmt"  Worker {params.workerId}: {totalIterations} iterations in {elapsed:.2f}s ({iterationsPerSecond:.0f} iter/s)"

        # Print constraint timing statistics for worker 0
        if enableTiming:
            improved.printTimingStats()

    # Check if we found a perfect solution
    if improved.cost == 0:
        # Try to claim the solution using solutionFound flag
        let wasAlreadyFound = params.result.solutionFound.exchange(true)
        if not wasAlreadyFound:  # We're the first to find a perfect solution
            if params.verbose:
                echo fmt"Worker {params.workerId} found solution!"

            # Atomically update the assignment
            params.result.assignment = improved.assignment
            params.result.bestCost.store(0)
            params.result.solutionWorkerId.store(params.workerId)
            params.result.solved.store(true)
            return

    # Update best cost if we found an improvement
    var currentBest = params.result.bestCost.load()
    while improved.cost < currentBest:
        let swapped = params.result.bestCost.compareExchange(currentBest, improved.cost)
        if swapped:
            echo fmt"Worker {params.workerId} found new best cost: {improved.cost}"
            break
        currentBest = params.result.bestCost.load()

################################################################################
# Batch improvement methods
################################################################################

type
    BatchWorkerParams*[T] = object
        systemCopy*: ConstraintSystem[T]
        threshold*: int
        result*: ptr BatchSharedResult[T]
        workerId*: int
        verbose*: bool

proc batchImproveWorker*[T](params: BatchWorkerParams[T]) {.thread.} =
    ## Worker thread that improves a single ConstraintSystem in a batch
    # Create termination check function
    proc shouldTerminate(): bool {.gcsafe.} = params.result.solutionFound.load()
    
    # Set different random seeds for each worker to ensure diversity
    randomize(params.workerId * 1000 + int(epochTime()))

    let startTime = epochTime()
    let enableTiming = params.verbose and params.workerId == 0
    
    # Improve using the system's baseArray (same pattern as existing parallel search)
    let improved = params.systemCopy.baseArray.tabuImproveWithTermination(params.threshold, shouldTerminate, enableTiming)
    let elapsed = epochTime() - startTime
    
    # Log profiling info for this worker
    if elapsed > 0:
        let totalIterations = improved.iteration
        let iterationsPerSecond = totalIterations.float / elapsed
        if params.verbose:
            echo fmt"  Batch Worker {params.workerId}: {totalIterations} iterations in {elapsed:.2f}s ({iterationsPerSecond:.0f} iter/s), final cost: {improved.cost}"
        
        # Print constraint timing statistics for worker 0
        if enableTiming:
            improved.printTimingStats()

    # Store the improved state in the shared result (always, regardless of solution status)
    # Note: This is not thread-safe for concurrent writes, but since each worker writes to its own index, it should be fine
    if params.workerId < params.result.improvedStates.len:
        params.result.improvedStates[params.workerId] = improved

    # Check if we found a perfect solution
    if improved.cost == 0:
        # Try to claim the solution using solutionFound flag
        let wasAlreadyFound = params.result.solutionFound.exchange(true)
        if not wasAlreadyFound:  # We're the first to find a perfect solution
            if params.verbose:
                echo fmt"Batch Worker {params.workerId} found solution!"

            # Atomically update the solution
            params.result.solutionAssignment = improved.assignment
            params.result.bestCost.store(0)
            params.result.solutionWorkerId.store(params.workerId)
            return

    # Update best cost if we found an improvement
    var currentBest = params.result.bestCost.load()
    while improved.cost < currentBest:
        let swapped = params.result.bestCost.compareExchange(currentBest, improved.cost)
        if swapped:
            if params.verbose:
                echo fmt"Batch Worker {params.workerId} found new best cost: {improved.cost}"
            break
        currentBest = params.result.bestCost.load()

proc batchImprove*[T](systems: seq[ConstraintSystem[T]], threshold: int, verbose: bool = false): seq[TabuState[T]] =
    ## Improves a batch of ConstraintSystems in parallel using tabu search
    ## Returns improved TabuStates, terminating early if any solution found (cost == 0)
    
    if systems.len == 0:
        return @[]
    
    let numWorkers = systems.len
    if verbose:
        echo fmt"Starting batch improvement with {numWorkers} systems"
    
    # Create batch shared result structure
    var batchResult = BatchSharedResult[T]()
    batchResult.solutionFound.store(false)
    batchResult.bestCost.store(high(int))
    batchResult.solutionWorkerId.store(-1)
    batchResult.solutionAssignment = @[]
    batchResult.improvedStates = newSeq[TabuState[T]](numWorkers)
    
    # Launch worker threads - each gets a deep copy of a system
    var threads: seq[Thread[BatchWorkerParams[T]]]
    threads.setLen(numWorkers)
    
    for i in 0..<numWorkers:
        var systemCopy = systems[i].deepCopy()
        
        let params = BatchWorkerParams[T](
            systemCopy: systemCopy,
            threshold: threshold,
            result: batchResult.addr,
            workerId: i,
            verbose: verbose
        )
        createThread(threads[i], batchImproveWorker, params)
    
    # Wait for solution or all workers to complete
    while not batchResult.solutionFound.load():
        var allDone = true
        for thread in threads:
            if running(thread):
                allDone = false
                break
        
        if allDone:
            break
        sleep(50)
    
    # Clean up threads
    for i in 0..<threads.len:
        joinThread(threads[i])
    
    # Report results and return improved states
    if batchResult.solutionFound.load():
        let solutionWorkerId = batchResult.solutionWorkerId.load()
        if verbose:
            echo fmt"Batch improvement found solution via worker {solutionWorkerId}"
    else:
        let bestCost = batchResult.bestCost.load()
        if verbose and bestCost < high(int):
            echo fmt"Batch improvement completed, best cost: {bestCost}"
    
    # Return all improved states (whether solution found or not)
    return batchResult.improvedStates

proc batchImprove*[T](carrays: seq[ConstrainedArray[T]], threshold: int, verbose: bool = false): seq[TabuState[T]] =
    ## Convenience overload that creates ConstraintSystems from ConstrainedArrays
    var systems: seq[ConstraintSystem[T]] = @[]
    
    for carray in carrays:
        # Create a constraint system from the constrained array
        var system = initConstraintSystem[T]()
        system.baseArray = carray
        systems.add(system)
    
    return batchImprove(systems, threshold, verbose)
