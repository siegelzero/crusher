import std/[packedsets, random, sequtils, tables, atomics, strformat]
from std/times import epochTime, cpuTime

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState, types, cumulative, geost]
import ../constrainedArray
import ../expressions/expressions

randomize()

# Logging configuration
const LogInterval* = 5000  # Log every N iterations
const ProfileMoveDelta* = false  # Enable moveDelta profiling (disable for performance)

################################################################################
# Type definitions
################################################################################

type
    # Profiling stats per constraint type
    ConstraintProfile* = object
        calls*: int64
        totalTime*: float  # in seconds

    TabuState*[T] = ref object of RootObj
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[StatefulConstraint[T]]]
        constraints*: seq[StatefulConstraint[T]]
        neighbors*: seq[seq[int]]
        penaltyMap*: seq[Table[T, int]]
        constraintPenalties*: seq[seq[Table[T, int]]]  # [pos][local_constraint_idx][value]

        assignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

        iteration*: int
        tabu*: seq[Table[T, int]]
        tenure*: int

        # Stats tracking
        startTime*: float
        lastLogTime*: float
        lastLogIteration*: int
        movesExplored*: int  # Track number of moves explored per iteration
        verbose*: bool

        # Profiling per constraint type
        profileByType*: array[StatefulConstraintType, ConstraintProfile]
        lastProfileLogTime*: float

################################################################################
# Penalty Routines
################################################################################

proc movePenalty*[T](state: TabuState[T], constraint: StatefulConstraint[T], position: int, newValue: T): int {.inline.} =
    let oldValue = state.assignment[position]
    when ProfileMoveDelta:
        let startT = cpuTime()
    case constraint.stateType:
        of AllDifferentType:
            result = constraint.allDifferentState.cost + constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of AtLeastType:
            result = constraint.atLeastState.cost + constraint.atLeastState.moveDelta(position, oldValue, newValue)
        of AtMostType:
            result = constraint.atMostState.cost + constraint.atMostState.moveDelta(position, oldValue, newValue)
        of ElementType:
            result = constraint.elementState.cost + constraint.elementState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            result = constraint.algebraicState.cost + constraint.algebraicState.moveDelta(position, oldValue, newValue)
        of RelationalType:
            result = constraint.relationalState.cost + constraint.relationalState.moveDelta(position, oldValue, newValue)
        of OrderingType:
            result = constraint.orderingState.cost + constraint.orderingState.moveDelta(position, oldValue, newValue)
        of GlobalCardinalityType:
            result = constraint.globalCardinalityState.cost + constraint.globalCardinalityState.moveDelta(position, oldValue, newValue)
        of MultiknapsackType:
            result = constraint.multiknapsackState.cost + constraint.multiknapsackState.moveDelta(position, oldValue, newValue)
        of SequenceType:
            result = constraint.sequenceState.cost + constraint.sequenceState.moveDelta(position, oldValue, newValue)
        of BooleanType:
            result = constraint.booleanState.cost + constraint.booleanState.moveDelta(position, oldValue, newValue)
        of CumulativeType:
            result = constraint.cumulativeState.cost + constraint.cumulativeState.moveDelta(position, oldValue, newValue)
        of GeostType:
            result = constraint.geostState.cost + constraint.geostState.moveDelta(position, oldValue, newValue)
        of IrdcsType:
            result = constraint.irdcsState.cost + constraint.irdcsState.moveDelta(position, oldValue, newValue)
        of CircuitType:
            result = constraint.circuitState.cost + constraint.circuitState.moveDelta(position, oldValue, newValue)
    when ProfileMoveDelta:
        let elapsed = cpuTime() - startT
        state.profileByType[constraint.stateType].calls += 1
        state.profileByType[constraint.stateType].totalTime += elapsed

################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: TabuState[T], position: int) =
    ## Full rebuild of penalty map at position, including per-constraint cache.
    for value in state.carray.reducedDomain[position]:
        var total = 0
        for ci, constraint in state.constraintsAtPosition[position]:
            let p = state.movePenalty(constraint, position, value)
            state.constraintPenalties[position][ci][value] = p
            total += p
        state.penaltyMap[position][value] = total


proc updateConstraintAtPosition[T](state: TabuState[T], position: int, localIdx: int) =
    ## Incrementally update penalty map at position for a single constraint.
    ## Only recomputes that constraint's contribution and adjusts the total.
    let constraint = state.constraintsAtPosition[position][localIdx]
    for value in state.carray.reducedDomain[position]:
        let newP = state.movePenalty(constraint, position, value)
        let oldP = state.constraintPenalties[position][localIdx].getOrDefault(value, 0)
        state.penaltyMap[position][value] += (newP - oldP)
        state.constraintPenalties[position][localIdx][value] = newP


proc updateConstraintAtPositionValues[T](state: TabuState[T], position: int, localIdx: int, values: seq[T]) =
    ## Incrementally update penalty map for specific domain values at position for a single constraint.
    ## Only updates values that exist in the penalty map (i.e., in the reduced domain).
    let constraint = state.constraintsAtPosition[position][localIdx]
    for value in values:
        if value notin state.penaltyMap[position]:
            continue
        let newP = state.movePenalty(constraint, position, value)
        let oldP = state.constraintPenalties[position][localIdx].getOrDefault(value, 0)
        state.penaltyMap[position][value] += (newP - oldP)
        state.constraintPenalties[position][localIdx][value] = newP


proc findLocalConstraintIdx[T](state: TabuState[T], position: int, constraint: StatefulConstraint[T]): int {.inline.} =
    ## Find the local index of a constraint at a position by reference identity.
    for i, c in state.constraintsAtPosition[position]:
        if cast[pointer](c) == cast[pointer](constraint):
            return i
    return -1


proc updateNeighborPenalties*[T](state: TabuState[T], position: int) =
    ## Update penalty map for positions affected by a change at `position`.
    ## Only recomputes the specific constraint(s) that changed at each neighbor,
    ## not all constraints at that position.

    for constraint in state.constraintsAtPosition[position]:
        let affectedPositions = constraint.getAffectedPositions()
        for pos in affectedPositions.items:
            if pos == position:
                continue
            let localIdx = state.findLocalConstraintIdx(pos, constraint)
            let affectedVals = constraint.getAffectedDomainValues(pos)
            if affectedVals.len == 0:
                state.updateConstraintAtPosition(pos, localIdx)
            else:
                state.updateConstraintAtPositionValues(pos, localIdx, affectedVals)


proc rebuildPenaltyMap*[T](state: TabuState[T]) =
    for position in state.carray.allPositions():
        state.updatePenaltiesForPosition(position)


proc logProfileStats*[T](state: TabuState[T]) =
    ## Log moveDelta profiling statistics by constraint type
    when ProfileMoveDelta:
        echo "[Profile] moveDelta stats by constraint type:"
        var totalCalls: int64 = 0
        var totalTime: float = 0.0
        for ctype in StatefulConstraintType:
            let profile = state.profileByType[ctype]
            if profile.calls > 0:
                let avgNs = if profile.calls > 0: (profile.totalTime * 1e9) / profile.calls.float else: 0.0
                echo &"[Profile]   {ctype}: calls={profile.calls:>10} time={profile.totalTime:>8.3f}s avg={avgNs:>8.1f}ns"
                totalCalls += profile.calls
                totalTime += profile.totalTime
        if totalCalls > 0:
            let avgNs = (totalTime * 1e9) / totalCalls.float
            echo &"[Profile]   TOTAL: calls={totalCalls:>10} time={totalTime:>8.3f}s avg={avgNs:>8.1f}ns"


proc resetProfileStats*[T](state: TabuState[T]) =
    ## Reset profiling counters
    when ProfileMoveDelta:
        for ctype in StatefulConstraintType:
            state.profileByType[ctype].calls = 0
            state.profileByType[ctype].totalTime = 0.0

################################################################################
# TabuState creation
################################################################################

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], verbose: bool = false) =
    state.carray = carray
    state.constraintsAtPosition = newSeq[seq[StatefulConstraint[T]]](carray.len)
    state.neighbors = newSeq[seq[int]](carray.len)

    state.iteration = 0
    state.tabu = newSeq[Table[T, int]](carray.len)

    # Initialize stats
    state.startTime = epochTime()
    state.lastLogTime = state.startTime
    state.lastLogIteration = 0
    state.movesExplored = 0
    state.verbose = verbose

    var initStart = epochTime()

    for pos in carray.allPositions():
        state.tabu[pos] = initTable[T, int]()

    for constraint in carray.constraints:
        state.constraints.add(constraint)

    for constraint in state.constraints:
        for pos in constraint.positions.items:
            state.constraintsAtPosition[pos].add(constraint)

    if verbose:
        echo "[TabuState] Built constraintsAtPosition in " & $(epochTime() - initStart) & "s"
        # Log constraint stats
        var maxPositions = 0
        var totalPositions = 0
        for c in state.constraints:
            let pcount = c.positions.len
            totalPositions += pcount
            if pcount > maxPositions:
                maxPositions = pcount
        echo "[TabuState] Constraints: " & $state.constraints.len & " total, max positions=" & $maxPositions & " avg=" & $(totalPositions div max(1, state.constraints.len))
        initStart = epochTime()

    # Skip expensive neighbor precomputation - compute lazily during search
    # Just initialize empty neighbor lists for now
    for pos in carray.allPositions():
        state.neighbors[pos] = @[]

    if verbose:
        echo "[TabuState] Initialized neighbors (lazy) in " & $(epochTime() - initStart) & "s"
        initStart = epochTime()

    state.assignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        state.assignment[pos] = sample(carray.reducedDomain[pos])

    for constraint in state.constraints:
        constraint.initialize(state.assignment)

    if verbose:
        echo "[TabuState] Initialized constraints in " & $(epochTime() - initStart) & "s"
        initStart = epochTime()

    for cons in state.constraints:
        state.cost += cons.penalty()

    state.bestCost = state.cost
    state.bestAssignment = state.assignment

    state.penaltyMap = newSeq[Table[T, int]](state.carray.len)
    state.constraintPenalties = newSeq[seq[Table[T, int]]](state.carray.len)
    for pos in carray.allPositions():
        state.penaltyMap[pos] = initTable[T, int]()
        state.constraintPenalties[pos] = newSeq[Table[T, int]](state.constraintsAtPosition[pos].len)
        for ci in 0..<state.constraintsAtPosition[pos].len:
            state.constraintPenalties[pos][ci] = initTable[T, int]()

    if verbose:
        echo "[TabuState] Starting penalty map computation for " & $carray.len & " positions..."
        var totalDomainSize = 0
        for pos in carray.allPositions():
            totalDomainSize += carray.reducedDomain[pos].len
        echo "[TabuState] Total domain values to compute: " & $totalDomainSize

    var penaltyStart = epochTime()
    for pos in carray.allPositions():
        state.updatePenaltiesForPosition(pos)
        if verbose and pos mod 500 == 0 and pos > 0:
            let elapsed = epochTime() - penaltyStart
            let rate = pos.float / max(elapsed, 0.001)
            let eta = (carray.len - pos).float / max(rate, 0.001)
            echo "[TabuState] Penalties: " & $pos & "/" & $carray.len & " rate=" & $rate.int & "/s eta=" & $eta.int & "s"

    if verbose:
        echo "[TabuState] Built penalty map in " & $(epochTime() - initStart) & "s"
        state.logProfileStats()
        state.resetProfileStats()  # Reset for search phase


proc newTabuState*[T](carray: ConstrainedArray[T], verbose: bool = false): TabuState[T] =
    new(result)
    result.init(carray, verbose)

################################################################################
# Value Assignment
################################################################################

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    let oldValue = state.assignment[position]

    # Compute delta directly from moveDelta (avoids stale penaltyMap values)
    var delta = 0
    for constraint in state.constraintsAtPosition[position]:
        delta += constraint.moveDelta(position, oldValue, value)

    state.assignment[position] = value

    for constraint in state.constraintsAtPosition[position]:
        constraint.updatePosition(position, value)

    state.cost += delta

    state.updatePenaltiesForPosition(position)
    state.updateNeighborPenalties(position)

################################################################################
# Search Algorithm Implementation
################################################################################

proc bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    var
        delta: int
        bestMoveCost = high(int)
        oldPenalty: int
        oldValue: T
        movesEvaluated = 0

    for position in state.carray.allPositions():
        oldValue = state.assignment[position]
        oldPenalty = state.penaltyMap[position].getOrDefault(oldValue, 0)
        if oldPenalty == 0:
            continue

        for newValue in state.carray.reducedDomain[position]:
            if newValue == oldValue:
                continue
            inc movesEvaluated
            delta = state.penaltyMap[position].getOrDefault(newValue, 0) - oldPenalty
            if state.tabu[position].getOrDefault(newValue, 0) <= state.iteration or state.cost + delta < state.bestCost:
                if state.cost + delta < bestMoveCost:
                    result = @[(position, newValue)]
                    bestMoveCost = state.cost + delta
                elif state.cost + delta == bestMoveCost:
                    result.add((position, newValue))

    state.movesExplored = movesEvaluated


proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.assignment[position]
        state.assignValue(position, newValue)
        state.tabu[position][oldValue] = state.iteration + 1 + state.iteration mod 10


proc logProgress[T](state: TabuState[T], lastImprovement: int) =
    ## Log search progress periodically
    let now = epochTime()
    let elapsed = now - state.lastLogTime
    let itersSinceLog = state.iteration - state.lastLogIteration
    let totalElapsed = now - state.startTime
    let iterRate = if elapsed > 0: itersSinceLog.float / elapsed else: 0.0
    let overallRate = if totalElapsed > 0: state.iteration.float / totalElapsed else: 0.0
    let stagnation = state.iteration - lastImprovement

    echo &"[Tabu] iter={state.iteration:>7} cost={state.cost:>5} best={state.bestCost:>5} " &
         &"moves={state.movesExplored:>6} rate={iterRate:>7.0f}/s overall={overallRate:>7.0f}/s stag={stagnation:>5}"

    state.lastLogTime = now
    state.lastLogIteration = state.iteration


proc tabuImprove*[T](state: TabuState[T], threshold: int, shouldStop: ptr Atomic[bool] = nil): TabuState[T] =
    var lastImprovement = 0

    # Reset timing for this run
    state.startTime = epochTime()
    state.lastLogTime = state.startTime
    state.lastLogIteration = 0

    if state.verbose:
        echo &"[Tabu] Starting search: vars={state.carray.len} constraints={state.constraints.len} threshold={threshold}"
        echo &"[Tabu] Initial cost={state.cost}"

    while state.iteration - lastImprovement < threshold:
        # Check for early termination signal
        if shouldStop != nil and shouldStop[].load():
            return state

        state.applyBestMove()
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
            if state.verbose and state.bestCost > 0:
                let elapsed = epochTime() - state.startTime
                echo &"[Tabu] IMPROVED at iter={state.iteration} cost={state.bestCost} elapsed={elapsed:.1f}s"
            if state.cost == 0:
                if state.verbose:
                    let elapsed = epochTime() - state.startTime
                    let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
                    echo &"[Tabu] SOLUTION FOUND at iter={state.iteration} elapsed={elapsed:.2f}s rate={rate:.0f}/s"
                return state
        state.iteration += 1

        # Periodic logging
        if state.verbose and state.iteration mod LogInterval == 0:
            state.logProgress(lastImprovement)

    if state.verbose:
        let elapsed = epochTime() - state.startTime
        echo &"[Tabu] Search ended: best_cost={state.bestCost} iterations={state.iteration} elapsed={elapsed:.2f}s"
        state.logProfileStats()

    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int, verbose: bool = false): TabuState[T] =
    var state = newTabuState[T](carray, verbose)
    return state.tabuImprove(threshold)
