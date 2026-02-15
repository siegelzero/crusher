import std/[packedsets, random, sequtils, tables, atomics, strformat]
from std/times import epochTime, cpuTime

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState, types, cumulative, geost]
import ../constrainedArray
import ../expressions/expressions

randomize()

# Logging configuration
const LogInterval* = 50000  # Log every N iterations
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
        id*: int  # Identifies this state in parallel runs
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[StatefulConstraint[T]]]
        constraintIdxAt*: seq[Table[pointer, int]]  # [position][constraint_ptr] -> localIdx
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
        of AllDifferentExcept0Type:
            result = constraint.allDifferentExcept0State.cost + constraint.allDifferentExcept0State.moveDelta(position, oldValue, newValue)
        of LexOrderType:
            result = constraint.lexOrderState.cost + constraint.lexOrderState.moveDelta(position, oldValue, newValue)
        of TableConstraintType:
            result = constraint.tableConstraintState.cost + constraint.tableConstraintState.moveDelta(position, oldValue, newValue)
        of RegularType:
            result = constraint.regularState.cost + constraint.regularState.moveDelta(position, oldValue, newValue)
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
    ## Find the local index of a constraint at a position via O(1) lookup.
    return state.constraintIdxAt[position][cast[pointer](constraint)]


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

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], verbose: bool = false, id: int = 0, initialAssignment: seq[T] = @[]) =
    state.id = id
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

    # Build O(1) constraint index lookup
    state.constraintIdxAt = newSeq[Table[pointer, int]](carray.len)
    for pos in carray.allPositions():
        state.constraintIdxAt[pos] = initTable[pointer, int]()
        for i, c in state.constraintsAtPosition[pos]:
            state.constraintIdxAt[pos][cast[pointer](c)] = i

    if verbose and id == 0:
        echo "[Init] Built constraintsAtPosition in " & $(epochTime() - initStart) & "s"
        var maxPositions = 0
        var totalPositions = 0
        for c in state.constraints:
            let pcount = c.positions.len
            totalPositions += pcount
            if pcount > maxPositions:
                maxPositions = pcount
        echo "[Init] Constraints: " & $state.constraints.len & " total, max_pos=" & $maxPositions & " avg_pos=" & $(totalPositions div max(1, state.constraints.len))
        var maxConsAtPos = 0
        var totalConsAtPos = 0
        for pos in carray.allPositions():
            let cnt = state.constraintsAtPosition[pos].len
            totalConsAtPos += cnt
            if cnt > maxConsAtPos:
                maxConsAtPos = cnt
        echo "[Init] Constraints per position: max=" & $maxConsAtPos & " avg=" & $(totalConsAtPos div max(1, carray.len))
        initStart = epochTime()

    # Skip expensive neighbor precomputation - compute lazily during search
    # Just initialize empty neighbor lists for now
    for pos in carray.allPositions():
        state.neighbors[pos] = @[]

    if verbose and id == 0:
        initStart = epochTime()

    state.assignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        if initialAssignment.len > 0:
            state.assignment[pos] = initialAssignment[pos]
        else:
            state.assignment[pos] = sample(carray.reducedDomain[pos])

    for constraint in state.constraints:
        constraint.initialize(state.assignment)

    if verbose and id == 0:
        echo "[Init] Initialized constraints in " & $(epochTime() - initStart) & "s"
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

    if verbose and id == 0:
        var totalDomainSize = 0
        for pos in carray.allPositions():
            totalDomainSize += carray.reducedDomain[pos].len
        echo "[Init] Building penalty map: " & $carray.len & " positions, " & $totalDomainSize & " domain values"

    var penaltyStart = epochTime()
    for pos in carray.allPositions():
        state.updatePenaltiesForPosition(pos)
        if verbose and id == 0 and pos mod 500 == 0 and pos > 0:
            let elapsed = epochTime() - penaltyStart
            let rate = pos.float / max(elapsed, 0.001)
            let eta = (carray.len - pos).float / max(rate, 0.001)
            echo "[Init] Penalties: " & $pos & "/" & $carray.len & " rate=" & $rate.int & "/s eta=" & $eta.int & "s"

    if verbose and id == 0:
        echo "[Init] Built penalty map in " & $(epochTime() - initStart) & "s"
        state.logProfileStats()
        state.resetProfileStats()


proc newTabuState*[T](carray: ConstrainedArray[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id)

proc newTabuState*[T](carray: ConstrainedArray[T], assignment: seq[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id, initialAssignment = assignment)

################################################################################
# Value Assignment
################################################################################

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    state.assignment[position] = value

    for constraint in state.constraintsAtPosition[position]:
        constraint.updatePosition(position, value)

    # Recompute true cost from constraint penalties (avoids accumulated moveDelta errors
    # with expression-based constraints where multiple expressions share a position)
    state.cost = 0
    for constraint in state.constraints:
        state.cost += constraint.penalty()

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
    let totalElapsed = now - state.startTime
    let overallRate = if totalElapsed > 0: state.iteration.float / totalElapsed else: 0.0
    let stagnation = state.iteration - lastImprovement

    echo &"[Tabu S{state.id}] iter={state.iteration:>7} cost={state.bestCost:>5} " &
         &"rate={overallRate:>7.0f}/s stag={stagnation:>5} elapsed={totalElapsed:>5.1f}s"

    state.lastLogTime = now
    state.lastLogIteration = state.iteration


proc tabuImprove*[T](state: TabuState[T], threshold: int, shouldStop: ptr Atomic[bool] = nil): TabuState[T] =
    var lastImprovement = 0

    # Reset timing for this run
    state.startTime = epochTime()
    state.lastLogTime = state.startTime
    state.lastLogIteration = 0

    if state.verbose:
        echo &"[Tabu S{state.id}] Starting: vars={state.carray.len} constraints={state.constraints.len} threshold={threshold} cost={state.cost}"

    while state.iteration - lastImprovement < threshold:
        # Check for early termination signal
        if shouldStop != nil and shouldStop[].load():
            return state

        state.applyBestMove()
        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
            if state.cost == 0:
                if state.verbose:
                    let elapsed = epochTime() - state.startTime
                    let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
                    echo &"[Tabu S{state.id}] Solution found at iter={state.iteration} elapsed={elapsed:.2f}s rate={rate:.0f}/s"
                return state
        state.iteration += 1

        # Periodic logging
        if state.verbose and state.iteration mod LogInterval == 0:
            state.logProgress(lastImprovement)

    if state.verbose:
        let elapsed = epochTime() - state.startTime
        let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
        echo &"[Tabu S{state.id}] Exhausted: best={state.bestCost} iters={state.iteration} elapsed={elapsed:.1f}s rate={rate:.0f}/s"
        state.logProfileStats()

    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int, verbose: bool = false): TabuState[T] =
    var state = newTabuState[T](carray, verbose)
    return state.tabuImprove(threshold)
