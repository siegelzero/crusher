import std/[math, hashes, packedsets, random, sequtils, sets, tables, atomics, strformat]
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

        # Dense array penalty tracking (indexed by domain-local index)
        domainIndex*: seq[Table[T, int]]  # [position][value] -> index in reducedDomain
        penaltyMap*: seq[seq[int]]  # [position][domainIdx] -> total penalty
        constraintPenalties*: seq[seq[seq[int]]]  # [pos][local_constraint_idx][domainIdx]
        tabu*: seq[seq[int]]  # [position][domainIdx] -> tabu expiration iteration

        assignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

        iteration*: int

        # Stats tracking
        startTime*: float
        lastLogTime*: float
        lastLogIteration*: int
        movesExplored*: int  # Track number of moves explored per iteration
        verbose*: bool

        # Profiling per constraint type
        profileByType*: array[StatefulConstraintType, ConstraintProfile]
        lastProfileLogTime*: float

        # Swap neighborhoods: groups of search positions in the same AllDifferent
        swapGroups*: seq[seq[int]]

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
        of CountEqType:
            result = constraint.countEqState.cost + constraint.countEqState.moveDelta(position, oldValue, newValue)
        of DiffnType:
            result = constraint.diffnState.cost + constraint.diffnState.moveDelta(position, oldValue, newValue)
        of MatrixElementType:
            result = constraint.matrixElementState.cost + constraint.matrixElementState.moveDelta(position, oldValue, newValue)
    when ProfileMoveDelta:
        let elapsed = cpuTime() - startT
        state.profileByType[constraint.stateType].calls += 1
        state.profileByType[constraint.stateType].totalTime += elapsed

################################################################################
# Dense Array Penalty Lookup
################################################################################

proc penaltyAt*[T](state: TabuState[T], position: int, value: T): int {.inline.} =
    ## Look up penalty for a (position, value) pair using dense arrays.
    let idx = state.domainIndex[position].getOrDefault(value, -1)
    if idx >= 0: state.penaltyMap[position][idx] else: 0

################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: TabuState[T], position: int) =
    ## Full rebuild of penalty map at position, including per-constraint cache.
    ## Uses batch computation for cumulative constraints (prefix-sum approach).
    let domain = state.carray.reducedDomain[position]
    let dLen = domain.len
    if dLen == 0: return

    # Zero out penalty map
    for i in 0..<dLen:
        state.penaltyMap[position][i] = 0

    for ci, constraint in state.constraintsAtPosition[position]:
        if constraint.stateType == CumulativeType and
           constraint.cumulativeState.evalMethod == PositionBased:
            # Batch computation via prefix sums — O(maxTime + domainSize)
            let penalties = constraint.cumulativeState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == RelationalType:
            # Batch computation for relational constraints — tight arithmetic loop
            let penalties = constraint.relationalState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        else:
            # Individual computation for other constraints
            for i in 0..<dLen:
                let value = domain[i]
                let p = state.movePenalty(constraint, position, value)
                state.constraintPenalties[position][ci][i] = p
                state.penaltyMap[position][i] += p


proc updateConstraintAtPosition[T](state: TabuState[T], position: int, localIdx: int) =
    ## Incrementally update penalty map at position for a single constraint.
    ## Only recomputes that constraint's contribution and adjusts the total.
    ## Uses batch prefix-sum method for cumulative constraints.
    let constraint = state.constraintsAtPosition[position][localIdx]
    let domain = state.carray.reducedDomain[position]

    if constraint.stateType == CumulativeType and
       constraint.cumulativeState.evalMethod == PositionBased:
        # Batch computation via prefix sums
        let penalties = constraint.cumulativeState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == RelationalType:
        # Batch computation for relational constraints
        let penalties = constraint.relationalState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    else:
        for i in 0..<domain.len:
            let value = domain[i]
            let newP = state.movePenalty(constraint, position, value)
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP


proc updateConstraintAtPositionValues[T](state: TabuState[T], position: int, localIdx: int, values: seq[T]) =
    ## Incrementally update penalty map for specific domain values at position for a single constraint.
    ## Only updates values that exist in the domain index.
    let constraint = state.constraintsAtPosition[position][localIdx]
    for value in values:
        let idx = state.domainIndex[position].getOrDefault(value, -1)
        if idx < 0:
            continue
        let newP = state.movePenalty(constraint, position, value)
        let oldP = state.constraintPenalties[position][localIdx][idx]
        state.penaltyMap[position][idx] += newP - oldP
        state.constraintPenalties[position][localIdx][idx] = newP


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

    # Initialize stats
    state.startTime = epochTime()
    state.lastLogTime = state.startTime
    state.lastLogIteration = 0
    state.movesExplored = 0
    state.verbose = verbose

    var initStart = epochTime()

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
        elif pos in carray.channelPositions:
            # Channel variables get a placeholder; computed below
            state.assignment[pos] = carray.reducedDomain[pos][0]
        else:
            state.assignment[pos] = sample(carray.reducedDomain[pos])

    # Compute channel variable initial values from their defining element constraints
    for binding in carray.channelBindings:
        let idxVal = binding.indexExpression.evaluate(state.assignment)
        if idxVal >= 0 and idxVal < binding.arrayElements.len:
            let elem = binding.arrayElements[idxVal]
            state.assignment[binding.channelPosition] =
                if elem.isConstant: elem.constantValue
                else: state.assignment[elem.variablePosition]

    for constraint in state.constraints:
        constraint.initialize(state.assignment)

    if verbose and id == 0:
        echo "[Init] Initialized constraints in " & $(epochTime() - initStart) & "s"
        initStart = epochTime()

    for cons in state.constraints:
        state.cost += cons.penalty()

    state.bestCost = state.cost
    state.bestAssignment = state.assignment

    # Build domain index: value -> local array index
    state.domainIndex = newSeq[Table[T, int]](carray.len)
    for pos in carray.allPositions():
        state.domainIndex[pos] = initTable[T, int]()
        for i, v in carray.reducedDomain[pos]:
            state.domainIndex[pos][v] = i

    # Initialize dense penalty arrays
    state.penaltyMap = newSeq[seq[int]](carray.len)
    state.constraintPenalties = newSeq[seq[seq[int]]](carray.len)
    state.tabu = newSeq[seq[int]](carray.len)
    for pos in carray.allPositions():
        let dsize = carray.reducedDomain[pos].len
        state.penaltyMap[pos] = newSeq[int](dsize)
        state.tabu[pos] = newSeq[int](dsize)
        state.constraintPenalties[pos] = newSeq[seq[int]](state.constraintsAtPosition[pos].len)
        for ci in 0..<state.constraintsAtPosition[pos].len:
            state.constraintPenalties[pos][ci] = newSeq[int](dsize)

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

    # Build swap groups from AllDifferent constraints
    # Only create swap groups when ALL constraints on the group's positions are
    # AllDifferent, Element, Relational, or Algebraic (swap-friendly types).
    # Skip when positions participate in Circuit, Regular, etc. where swaps hurt.
    # Also skip channel positions and singleton-domain positions (constants).
    for constraint in state.constraints:
        if constraint.stateType == AllDifferentType and
           constraint.allDifferentState.evalMethod == PositionBased:
            var positions: seq[int]
            for pos in constraint.positions.items:
                if pos notin carray.channelPositions and
                   carray.reducedDomain[pos].len > 1:
                    positions.add(pos)
            if positions.len >= 2:
                # Check that no position in this group is in a swap-unfriendly constraint
                var swapSafe = true
                for pos in positions:
                    for c in state.constraintsAtPosition[pos]:
                        if c.stateType notin {AllDifferentType, ElementType,
                                              AlgebraicType, RelationalType,
                                              BooleanType, MatrixElementType,
                                              AtLeastType, AtMostType,
                                              GlobalCardinalityType, CountEqType}:
                            swapSafe = false
                            break
                    if not swapSafe:
                        break
                if swapSafe:
                    state.swapGroups.add(positions)

    if verbose and id == 0 and state.swapGroups.len > 0:
        echo "[Init] Built " & $state.swapGroups.len & " swap groups"


proc newTabuState*[T](carray: ConstrainedArray[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id)

proc newTabuState*[T](carray: ConstrainedArray[T], assignment: seq[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id, initialAssignment = assignment)

################################################################################
# Value Assignment
################################################################################

proc propagateChannels[T](state: TabuState[T], position: int) =
    ## Propagate channel variable values after a change at `position`.
    if position notin state.carray.channelsAtPosition:
        return
    for bi in state.carray.channelsAtPosition[position]:
        let binding = state.carray.channelBindings[bi]
        let idxVal = binding.indexExpression.evaluate(state.assignment)
        var newVal: T
        if idxVal >= 0 and idxVal < binding.arrayElements.len:
            let elem = binding.arrayElements[idxVal]
            newVal = if elem.isConstant: elem.constantValue
                     else: state.assignment[elem.variablePosition]
        else:
            continue  # out of bounds, leave as-is

        if newVal != state.assignment[binding.channelPosition]:
            state.assignment[binding.channelPosition] = newVal
            for c in state.constraintsAtPosition[binding.channelPosition]:
                c.updatePosition(binding.channelPosition, newVal)
            state.updatePenaltiesForPosition(binding.channelPosition)
            state.updateNeighborPenalties(binding.channelPosition)

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    state.assignment[position] = value

    for constraint in state.constraintsAtPosition[position]:
        constraint.updatePosition(position, value)

    # Propagate channel variables affected by this position change
    state.propagateChannels(position)

    # Recompute true cost from constraint penalties (avoids accumulated moveDelta errors
    # with expression-based constraints where multiple expressions share a position)
    state.cost = 0
    for constraint in state.constraints:
        state.cost += constraint.penalty()

    state.updatePenaltiesForPosition(position)
    state.updateNeighborPenalties(position)

################################################################################
# Swap Move Infrastructure
################################################################################

proc swapMoveDelta[T](state: TabuState[T], posA, posB: int): int =
    ## Compute the cost delta for swapping values at posA and posB.
    let valA = state.assignment[posA]
    let valB = state.assignment[posB]
    if valA == valB: return 0

    var delta = 0
    var seen: HashSet[pointer]

    # Constraints involving posA
    for c in state.constraintsAtPosition[posA]:
        seen.incl(cast[pointer](c))
        if posB in c.positions:
            # Constraint covers both — need swap-aware eval
            if c.stateType == AllDifferentType:
                delta += 0  # swap preserves allDifferent cost
            else:
                let oldP = c.penalty()
                c.updatePosition(posA, valB)
                c.updatePosition(posB, valA)
                delta += c.penalty() - oldP
                c.updatePosition(posB, valB)
                c.updatePosition(posA, valA)
        else:
            delta += c.moveDelta(posA, valA, valB)

    # Constraints involving only posB
    for c in state.constraintsAtPosition[posB]:
        if cast[pointer](c) notin seen:
            delta += c.moveDelta(posB, valB, valA)

    return delta


proc bestSwapMoves[T](state: TabuState[T]): seq[(int, int)] =
    ## Find the best swap moves across all swap groups.
    var bestDelta = high(int)

    for group in state.swapGroups:
        for i in 0..<group.len:
            let posA = group[i]
            let valA = state.assignment[posA]
            for j in (i+1)..<group.len:
                let posB = group[j]
                let valB = state.assignment[posB]
                if valA == valB:
                    continue

                # Domain check: only swap if each value is in the other's domain
                let idxA = state.domainIndex[posA].getOrDefault(valB, -1)
                let idxB = state.domainIndex[posB].getOrDefault(valA, -1)
                if idxA < 0 or idxB < 0:
                    continue  # swap would place out-of-domain value

                let delta = state.swapMoveDelta(posA, posB)
                let newCost = state.cost + delta

                # Tabu check: a swap is tabu only if BOTH positions are tabu for their new values
                var isTabu = state.tabu[posA][idxA] > state.iteration and
                             state.tabu[posB][idxB] > state.iteration

                if isTabu and newCost >= state.bestCost:
                    continue

                if newCost < bestDelta:
                    result = @[(posA, posB)]
                    bestDelta = newCost
                elif newCost == bestDelta:
                    result.add((posA, posB))


proc assignSwap[T](state: TabuState[T], posA, posB: int) =
    ## Swap the values at posA and posB and update all constraint states.
    let valA = state.assignment[posA]
    let valB = state.assignment[posB]

    state.assignment[posA] = valB
    state.assignment[posB] = valA

    # Update constraint states for both positions
    for constraint in state.constraintsAtPosition[posA]:
        constraint.updatePosition(posA, valB)
    for constraint in state.constraintsAtPosition[posB]:
        constraint.updatePosition(posB, valA)

    # Propagate channel variables affected by both positions
    state.propagateChannels(posA)
    state.propagateChannels(posB)

    # Recompute true cost
    state.cost = 0
    for constraint in state.constraints:
        state.cost += constraint.penalty()

    # Update penalty maps for both positions and their neighbors
    state.updatePenaltiesForPosition(posA)
    state.updatePenaltiesForPosition(posB)
    state.updateNeighborPenalties(posA)
    state.updateNeighborPenalties(posB)


################################################################################
# Search Algorithm Implementation
################################################################################

proc bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    const MAX_CANDIDATES_PER_POS = 500

    var
        delta: int
        bestMoveCost = high(int)
        oldPenalty: int
        movesEvaluated = 0

    for position in state.carray.allPositions():
        if position in state.carray.channelPositions:
            continue
        let oldValue = state.assignment[position]
        let oldIdx = state.domainIndex[position].getOrDefault(oldValue, -1)
        if oldIdx < 0:
            continue
        oldPenalty = state.penaltyMap[position][oldIdx]
        if oldPenalty == 0:
            continue

        let domain = state.carray.reducedDomain[position]
        let dLen = domain.len

        if dLen <= MAX_CANDIDATES_PER_POS:
            # Small domain: evaluate all values
            for i in 0..<dLen:
                if i == oldIdx:
                    continue
                inc movesEvaluated
                delta = state.penaltyMap[position][i] - oldPenalty
                let newCost = state.cost + delta
                if state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                    if newCost < bestMoveCost:
                        result = @[(position, domain[i])]
                        bestMoveCost = newCost
                    elif newCost == bestMoveCost:
                        result.add((position, domain[i]))
        else:
            # Large domain: evaluate a random sample of candidates
            for s in 0..<MAX_CANDIDATES_PER_POS:
                let i = rand(dLen - 1)
                if i == oldIdx:
                    continue
                inc movesEvaluated
                delta = state.penaltyMap[position][i] - oldPenalty
                let newCost = state.cost + delta
                if state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                    if newCost < bestMoveCost:
                        result = @[(position, domain[i])]
                        bestMoveCost = newCost
                    elif newCost == bestMoveCost:
                        result.add((position, domain[i]))

    state.movesExplored = movesEvaluated


proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    # Alternate between swap and regular moves when swap groups exist
    if state.swapGroups.len > 0 and state.iteration mod 2 == 0:
        let swaps = state.bestSwapMoves()
        if swaps.len > 0:
            let (posA, posB) = sample(swaps)
            let oldValA = state.assignment[posA]
            let oldValB = state.assignment[posB]
            state.assignSwap(posA, posB)
            # Set tabu on old values
            let oldIdxA = state.domainIndex[posA].getOrDefault(oldValA, -1)
            if oldIdxA >= 0:
                state.tabu[posA][oldIdxA] = state.iteration + 1 + state.iteration mod 10
            let oldIdxB = state.domainIndex[posB].getOrDefault(oldValB, -1)
            if oldIdxB >= 0:
                state.tabu[posB][oldIdxB] = state.iteration + 1 + state.iteration mod 10
            return

    let moves = state.bestMoves()

    if moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.assignment[position]
        state.assignValue(position, newValue)
        let oldIdx = state.domainIndex[position].getOrDefault(oldValue, -1)
        if oldIdx >= 0:
            state.tabu[position][oldIdx] = state.iteration + 1 + state.iteration mod 10


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
