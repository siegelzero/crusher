import std/[packedsets, random, sequtils, tables, atomics, strformat, os, times, algorithm]
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
        reducedDomain*: seq[seq[T]]

        assignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

        iteration*: int
        tabu*: seq[seq[int]]
        tenure*: int

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
    for value in state.reducedDomain[position]:
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
    # Use the current domain as the reduced domain (should already be pre-computed)
    state.reducedDomain = newSeq[seq[T]](carray.len)
    for pos in carray.allPositions():
        state.reducedDomain[pos] = carray.domain[pos]

    state.iteration = 0
    state.tabu = newSeq[seq[int]](carray.len)

    # Initialize timing
    state.enableTiming = enableTiming
    state.constraintTimings = initTable[string, ConstraintTiming]()

    for pos in carray.allPositions():
        if state.reducedDomain[pos].len > 0:
            state.tabu[pos] = newSeq[int](max(state.reducedDomain[pos]) + 1)
        else:
            # Handle empty reduced domain - this indicates inconsistent constraints
            echo "Warning: Variable at position ", pos, " has empty reduced domain"
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
        if state.reducedDomain[pos].len > 0:
            state.assignment[pos] = sample(state.reducedDomain[pos])
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
        state.penaltyMap[pos] = newSeq[int](max(state.reducedDomain[pos]) + 1)

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

        for newValue in state.reducedDomain[position]:
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
    var lastImprovement = 0

    while state.iteration - lastImprovement < threshold:
        state.applyBestMove()
        if state.cost < state.bestCost:
            # echo "Found better solution with cost ", state.cost
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
        if state.cost == 0:
            return state
        state.iteration += 1
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
    echo "Worker ", params.workerId, " starting search with pre-computed domains"
    
    # Use the same multi-restart logic as sequentialSearch iterator
    var bestResult: TabuState[T]
    var found = false
    var currentThreshold = params.threshold
    
    for attempt in 0..<10:  # Same as sequentialSearch maxAttempts
        # Check if another worker found a solution
        if shouldTerminate():
            echo "DEBUG: Worker ", params.workerId, " terminating early - solution found by another worker"
            return
            
        randomize(attempt * 1000 + int(epochTime()))  # Same seed pattern as sequentialSearch
        let improved = params.systemCopy.baseArray.tabuImproveWithTermination(currentThreshold, shouldTerminate)
        echo "DEBUG: Worker ", params.workerId, " attempt ", attempt, " cost: ", improved.cost
        
        # DEBUG: Show the first few assignment values for worker 0
        if params.workerId == 0 and attempt == 0:
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
        echo fmt"  Worker {params.workerId}: {totalIterations} iterations in {elapsed:.2f}s ({iterationsPerSecond:.0f} iter/s)"
        
        # Print constraint timing statistics for worker 0
        if enableTiming:
            improved.printTimingStats()

    # Check if we found a perfect solution
    if improved.cost == 0:
        # Try to claim the solution using solutionFound flag
        let wasAlreadyFound = params.result.solutionFound.exchange(true)
        if not wasAlreadyFound:  # We're the first to find a perfect solution
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
