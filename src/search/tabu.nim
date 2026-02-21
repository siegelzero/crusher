import std/[math, packedsets, random, sequtils, tables, atomics, strformat]
from std/times import epochTime, cpuTime

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState, types, cumulative, geost, matrixElement, constraintNode, tableConstraint]
import ../constrainedArray
import ../expressions/expressions

randomize()

# Logging configuration
const LogInterval* = 50000  # Log every N iterations
const ProfileMoveDelta* = false  # Enable moveDelta profiling (disable for performance)
const ProfileIteration* = false  # Enable per-iteration phase profiling

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

        # Per-position count of violated constraints (penalty > 0)
        violationCount*: seq[int]

        # Cached search metadata
        searchPositions*: seq[int]  # Non-channel positions (precomputed)
        totalDomainSize*: int  # Sum of domain sizes across search positions

        # Swap move structures for binary variables
        swapEnabled*: bool
        binaryPositions*: seq[int]           # positions with domain {0,1}
        binaryPosIndex*: Table[int, int]     # position -> index in binaryPositions
        swapNeighbors*: seq[seq[int]]        # [binaryIdx] -> neighbor binary indices (by binaryIdx)
        sharedConstraints*: Table[(int,int), seq[StatefulConstraint[T]]]  # (min_pos,max_pos) -> shared constraints

        # Ejection chain / flow network structure
        flowEnabled*: bool
        flowNodePositions*: seq[seq[(int, int)]]  # [flowNodeIdx] -> [(position, coeff)]
        posFlowNodes*: seq[seq[(int, int)]]       # [position] -> [(flowNodeIdx, coeff)]
        edgeObjectiveWeight*: Table[int, int]     # position -> objective coefficient for guided chains

        # Profiling per constraint type
        profileByType*: array[StatefulConstraintType, ConstraintProfile]
        lastProfileLogTime*: float

        # Iteration phase profiling
        when ProfileIteration:
            timeBestMoves*: float
            timeAssignConstraints*: float
            timeUpdatePenalties*: float
            timeNeighborPenalties*: float
            neighborUpdates*: int64
            neighborBatchCalls*: int64
            positionsScanned*: int64
            affectedPosTotal*: int64
            affectedPosSkipped*: int64


# Forward declarations
proc initSwapStructures[T](state: TabuState[T])
proc initFlowStructure[T](state: TabuState[T])
proc assignValue*[T](state: TabuState[T], position: int, value: T)

################################################################################
# Penalty Routines
################################################################################

proc movePenalty*[T](state: TabuState[T], constraint: StatefulConstraint[T], position: int, newValue: T): int {.inline.} =
    ## Returns the moveDelta for assigning newValue at position under this constraint.
    ## The penalty map caches these deltas (not absolute costs) so that targeted
    ## neighbor updates remain correct when a constraint's base cost changes.
    let oldValue = state.assignment[position]
    when ProfileMoveDelta:
        let startT = cpuTime()
    case constraint.stateType:
        of AllDifferentType:
            result = constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of AtLeastType:
            result = constraint.atLeastState.moveDelta(position, oldValue, newValue)
        of AtMostType:
            result = constraint.atMostState.moveDelta(position, oldValue, newValue)
        of ElementType:
            result = constraint.elementState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            result = constraint.algebraicState.moveDelta(position, oldValue, newValue)
        of RelationalType:
            result = constraint.relationalState.moveDelta(position, oldValue, newValue)
        of OrderingType:
            result = constraint.orderingState.moveDelta(position, oldValue, newValue)
        of GlobalCardinalityType:
            result = constraint.globalCardinalityState.moveDelta(position, oldValue, newValue)
        of MultiknapsackType:
            result = constraint.multiknapsackState.moveDelta(position, oldValue, newValue)
        of SequenceType:
            result = constraint.sequenceState.moveDelta(position, oldValue, newValue)
        of BooleanType:
            result = constraint.booleanState.moveDelta(position, oldValue, newValue)
        of CumulativeType:
            result = constraint.cumulativeState.moveDelta(position, oldValue, newValue)
        of GeostType:
            result = constraint.geostState.moveDelta(position, oldValue, newValue)
        of IrdcsType:
            result = constraint.irdcsState.moveDelta(position, oldValue, newValue)
        of CircuitType:
            result = constraint.circuitState.moveDelta(position, oldValue, newValue)
        of AllDifferentExcept0Type:
            result = constraint.allDifferentExcept0State.moveDelta(position, oldValue, newValue)
        of LexOrderType:
            result = constraint.lexOrderState.moveDelta(position, oldValue, newValue)
        of TableConstraintType:
            result = constraint.tableConstraintState.moveDelta(position, oldValue, newValue)
        of RegularType:
            result = constraint.regularState.moveDelta(position, oldValue, newValue)
        of CountEqType:
            result = constraint.countEqState.moveDelta(position, oldValue, newValue)
        of DiffnType:
            result = constraint.diffnState.moveDelta(position, oldValue, newValue)
        of MatrixElementType:
            result = constraint.matrixElementState.moveDelta(position, oldValue, newValue)
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
                position, state.assignment[position], domain, state.assignment)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == MatrixElementType:
            # Batch computation for matrixElement constraints
            let penalties = constraint.matrixElementState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == TableConstraintType:
            # Batch computation for table constraints — O(nTuples + domainSize)
            let penalties = constraint.tableConstraintState.batchMovePenalty(
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
            position, state.assignment[position], domain, state.assignment)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == MatrixElementType:
        # Batch computation for matrixElement constraints
        let penalties = constraint.matrixElementState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == TableConstraintType:
        # Batch computation for table constraints
        let penalties = constraint.tableConstraintState.batchMovePenalty(
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
            when ProfileIteration:
                state.neighborUpdates += 1
            let localIdx = state.findLocalConstraintIdx(pos, constraint)
            let affectedVals = constraint.getAffectedDomainValues(pos)
            if affectedVals.len == 0:
                when ProfileIteration:
                    state.neighborBatchCalls += 1
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

    # Build violation count: for each position, how many touching constraints have penalty > 0
    state.violationCount = newSeq[int](carray.len)
    for constraint in state.constraints:
        if constraint.penalty() > 0:
            for pos in constraint.positions.items:
                state.violationCount[pos] += 1

    state.bestCost = state.cost
    state.bestAssignment = state.assignment

    # Cache search positions and total domain size
    state.searchPositions = @[]
    state.totalDomainSize = 0
    for pos in carray.allSearchPositions():
        state.searchPositions.add(pos)
        state.totalDomainSize += carray.reducedDomain[pos].len

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

    # Initialize swap move structures for binary variables
    state.initSwapStructures()
    state.initFlowStructure()


proc newTabuState*[T](carray: ConstrainedArray[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id)

proc newTabuState*[T](carray: ConstrainedArray[T], assignment: seq[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id, initialAssignment = assignment)

################################################################################
# Swap Move Initialization
################################################################################

proc initSwapStructures[T](state: TabuState[T]) =
    ## Detect binary (0/1) positions and build swap neighbor adjacency.
    ## Two binary positions are swap neighbors if they share at least one constraint.
    state.swapEnabled = false
    state.binaryPositions = @[]
    state.binaryPosIndex = initTable[int, int]()
    state.swapNeighbors = @[]
    state.sharedConstraints = initTable[(int,int), seq[StatefulConstraint[T]]]()

    # Find all search positions with domain exactly {0, 1}
    for pos in state.searchPositions:
        let domain = state.carray.reducedDomain[pos]
        if domain.len == 2 and
           ((domain[0] == 0 and domain[1] == 1) or (domain[0] == 1 and domain[1] == 0)):
            state.binaryPosIndex[pos] = state.binaryPositions.len
            state.binaryPositions.add(pos)

    if state.binaryPositions.len < 2:
        return

    # For each constraint, collect binary positions it covers
    # Then build swap neighbor pairs from positions sharing a constraint
    let binaryPosSet = block:
        var s = initPackedSet[int]()
        for p in state.binaryPositions: s.incl(p)
        s

    state.swapNeighbors = newSeq[seq[int]](state.binaryPositions.len)

    # Use a set per binary index to avoid duplicate neighbors
    var neighborSets = newSeq[PackedSet[int]](state.binaryPositions.len)
    for i in 0..<state.binaryPositions.len:
        neighborSets[i] = initPackedSet[int]()

    for constraint in state.constraints:
        # Collect binary positions in this constraint
        var binaryInConstraint: seq[int] = @[]
        for pos in constraint.positions.items:
            if pos in binaryPosSet:
                binaryInConstraint.add(pos)

        if binaryInConstraint.len < 2:
            continue

        # Add all pairs as swap neighbors and record shared constraints
        for i in 0..<binaryInConstraint.len:
            for j in (i+1)..<binaryInConstraint.len:
                let p1 = binaryInConstraint[i]
                let p2 = binaryInConstraint[j]
                let bi1 = state.binaryPosIndex[p1]
                let bi2 = state.binaryPosIndex[p2]
                neighborSets[bi1].incl(bi2)
                neighborSets[bi2].incl(bi1)

                let key = if p1 < p2: (p1, p2) else: (p2, p1)
                if key notin state.sharedConstraints:
                    state.sharedConstraints[key] = @[constraint]
                else:
                    state.sharedConstraints[key].add(constraint)

    # Convert neighbor sets to seqs
    var totalPairs = 0
    for bi in 0..<state.binaryPositions.len:
        state.swapNeighbors[bi] = @[]
        for nbi in neighborSets[bi].items:
            state.swapNeighbors[bi].add(nbi)
        totalPairs += state.swapNeighbors[bi].len

    totalPairs = totalPairs div 2  # each pair counted twice

    if totalPairs > 0:
        state.swapEnabled = true
        if state.verbose and state.id == 0:
            echo "[Init] Swap moves: " & $state.binaryPositions.len & " binary positions, " & $totalPairs & " swap pairs"


################################################################################
# Flow Structure Initialization
################################################################################

proc initFlowStructure[T](state: TabuState[T]) =
    ## Detect flow network structure for ejection chain moves.
    ## A "flow node" is an EqualTo RelationalConstraint with PositionBased SumExpr
    ## where all coefficients are ±1 and all positions are binary.
    state.flowEnabled = false
    state.flowNodePositions = @[]
    state.posFlowNodes = newSeq[seq[(int, int)]](state.carray.len)

    if not state.swapEnabled:
        return

    let binaryPosSet = block:
        var s = initPackedSet[int]()
        for p in state.binaryPositions: s.incl(p)
        s

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo:
            continue
        if rc.leftExpr.kind != SumExpr:
            continue
        let sumExpr = rc.leftExpr.sumExpr
        if sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue

        # Check all coefficients are ±1 and all positions are binary
        var allValid = true
        var posCoeffs: seq[(int, int)] = @[]
        for pos, coeff in sumExpr.coefficient.pairs:
            if (coeff != 1 and coeff != -1) or pos notin binaryPosSet:
                allValid = false
                break
            posCoeffs.add((pos, coeff))

        if not allValid or posCoeffs.len < 2:
            continue

        # This is a flow node
        let fnIdx = state.flowNodePositions.len
        state.flowNodePositions.add(posCoeffs)
        for (pos, coeff) in posCoeffs:
            state.posFlowNodes[pos].add((fnIdx, coeff))

    if state.flowNodePositions.len > 0:
        var flowEdgeCount = 0
        for pos in state.binaryPositions:
            if state.posFlowNodes[pos].len >= 2:
                flowEdgeCount += 1
        if flowEdgeCount > 0:
            state.flowEnabled = true
            if state.verbose and state.id == 0:
                echo "[Init] Flow structure: " & $state.flowNodePositions.len &
                     " flow nodes, " & $flowEdgeCount & " flow edges"

    # Extract objective coefficients for guided chain construction.
    # Look for LessThanEq/GreaterThanEq RelationalConstraint with PositionBased SumExpr
    # covering many binary positions — this is the objective bound constraint.
    state.edgeObjectiveWeight = initTable[int, int]()
    if state.flowEnabled:
        var bestObjConstraint: RelationalConstraint[T] = nil
        var bestObjCoverage = 0
        for constraint in state.constraints:
            if constraint.stateType != RelationalType:
                continue
            let rc = constraint.relationalState
            if rc.relation notin {LessThanEq, GreaterThanEq}:
                continue
            if rc.leftExpr.kind != SumExpr:
                continue
            let sumExpr = rc.leftExpr.sumExpr
            if sumExpr.evalMethod != PositionBased:
                continue
            # Count how many binary positions this constraint covers
            var coverage = 0
            for pos in sumExpr.coefficient.keys:
                if pos in binaryPosSet:
                    coverage += 1
            if coverage > bestObjCoverage:
                bestObjCoverage = coverage
                bestObjConstraint = rc
        if bestObjConstraint != nil and bestObjCoverage >= 4:
            let sumExpr = bestObjConstraint.leftExpr.sumExpr
            for pos, coeff in sumExpr.coefficient.pairs:
                if pos in binaryPosSet:
                    state.edgeObjectiveWeight[pos] = coeff
            if state.verbose and state.id == 0:
                echo "[Init] Objective weights: " & $state.edgeObjectiveWeight.len &
                     " binary edges with objective coefficients"


################################################################################
# Negative-Cost Cycle Detection (Bellman-Ford on Residual Graph)
################################################################################

type
    ResidualEdge = object
        src, dst: int       # flow node indices
        cost: int           # residual cost (negative = improving)
        pos: int            # original position (edge variable)
        newVal: int         # value to assign (0 or 1) when using this edge

proc findNegativeCycle[T](state: TabuState[T]): (seq[(int, T)], int) =
    ## Find a negative-cost cycle in the residual flow graph using Bellman-Ford.
    ## Returns (chain, cycleCost) where chain is a list of (position, newValue)
    ## flips and cycleCost is the sum of residual edge costs in the cycle.
    ## Each binary edge variable maps to a residual edge:
    ##   - Currently ON (1): reverse edge with cost = -weight (removing saves weight)
    ##   - Currently OFF (0): forward edge with cost = +weight (adding costs weight)
    ## A negative cycle corresponds to a set of edge flips that improve the objective
    ## while maintaining flow conservation.
    if state.edgeObjectiveWeight.len == 0:
        return (@[], 0)

    let n = state.flowNodePositions.len  # number of flow nodes
    if n == 0:
        return (@[], 0)

    # Build residual edges
    var edges: seq[ResidualEdge] = @[]
    for pos in state.binaryPositions:
        let flowNodes = state.posFlowNodes[pos]
        if flowNodes.len != 2:
            continue
        let w = state.edgeObjectiveWeight.getOrDefault(pos, 0)
        let val = int(state.assignment[pos])

        # Determine direction: +1 coeff = outgoing from that node, -1 = incoming
        var srcNode, dstNode: int
        if flowNodes[0][1] > 0:
            srcNode = flowNodes[0][0]
            dstNode = flowNodes[1][0]
        else:
            srcNode = flowNodes[1][0]
            dstNode = flowNodes[0][0]

        if val == 1:
            # ON edge: residual goes backward (dst→src) with negative cost
            edges.add(ResidualEdge(src: dstNode, dst: srcNode, cost: -w, pos: pos, newVal: 0))
        else:
            # OFF edge: residual goes forward (src→dst) with positive cost
            edges.add(ResidualEdge(src: srcNode, dst: dstNode, cost: w, pos: pos, newVal: 1))

    if edges.len == 0:
        return (@[], 0)

    # Bellman-Ford: detect negative-cost cycle
    var dist = newSeq[int](n)
    var pred = newSeq[int](n)    # predecessor edge index
    for i in 0..<n:
        dist[i] = 0
        pred[i] = -1

    # Relax edges n times; on the n-th pass, any relaxation indicates a negative cycle
    var lastRelaxed = -1
    for iter in 0..<n:
        lastRelaxed = -1
        for ei in 0..<edges.len:
            let e = edges[ei]
            if dist[e.src] + e.cost < dist[e.dst]:
                dist[e.dst] = dist[e.src] + e.cost
                pred[e.dst] = ei
                lastRelaxed = e.dst

    if lastRelaxed < 0:
        return (@[], 0)  # No negative cycle

    # Trace back to find the cycle
    var node = lastRelaxed
    # Walk back n steps to ensure we're in the cycle
    for i in 0..<n:
        node = edges[pred[node]].src

    # Now trace the cycle from this node
    let cycleStart = node
    var cycle: seq[ResidualEdge] = @[]
    var current = cycleStart
    var visited = initPackedSet[int]()
    while true:
        let ei = pred[current]
        if ei < 0:
            return (@[], 0)  # broken chain
        cycle.add(edges[ei])
        visited.incl(current)
        current = edges[ei].src
        if current == cycleStart:
            break
        if current in visited:
            return (@[], 0)  # unexpected loop structure

    if cycle.len < 2:
        return (@[], 0)

    # Compute cycle cost and convert to position flips
    var cycleCost = 0
    var chain: seq[(int, T)] = @[]
    for e in cycle:
        cycleCost += e.cost
        chain.add((e.pos, T(e.newVal)))
    return (chain, cycleCost)


proc tryChainMoves*[T](state: TabuState[T]): bool =
    ## Find and apply negative-cost cycles in the flow residual graph.
    ## Returns true if an improving cycle was applied.
    if not state.flowEnabled:
        return false

    let (chain, cycleCost) = state.findNegativeCycle()
    if chain.len < 2:
        return false

    # Skip cycles that aren't negative in the flow subproblem — these can't
    # improve the full cost and applying+restoring them wastes penalty rebuilds.
    if cycleCost >= 0:
        return false

    # Apply chain and measure actual delta (may differ from cycleCost due to
    # non-flow constraints like cardinality bounds or side constraints).
    let costBefore = state.cost
    var oldValues: seq[T] = @[]
    for (pos, newVal) in chain:
        oldValues.add(state.assignment[pos])
        state.assignValue(pos, newVal)
    let delta = state.cost - costBefore

    if delta < 0:
        if state.verbose:
            echo &"[Chain S{state.id}] Applying negative cycle: len={chain.len} delta={delta} cycleCost={cycleCost} (cost {costBefore} -> {costBefore + delta})"
        # Set tabu for all flipped positions
        for i in 0..<chain.len:
            let (pos, _) = chain[i]
            let oldVal = oldValues[i]
            let oldIdx = state.domainIndex[pos].getOrDefault(oldVal, -1)
            if oldIdx >= 0:
                state.tabu[pos][oldIdx] = state.iteration + 1 + state.iteration mod 10
        return true
    else:
        # Restore — cycle wasn't actually improving (due to non-flow constraints)
        if state.verbose:
            echo &"[Chain S{state.id}] Negative cycle not improving: len={chain.len} delta={delta} cycleCost={cycleCost}"
        for i in countdown(chain.len - 1, 0):
            state.assignValue(chain[i][0], oldValues[i])
        return false


################################################################################
# Value Assignment
################################################################################

proc propagateChannels[T](state: TabuState[T], position: int) =
    ## Propagate channel variable values after a change at `position`.
    ## Uses a worklist to handle transitive channel dependencies.
    var worklist = @[position]
    var visited: PackedSet[int]
    visited.incl(position)

    while worklist.len > 0:
        let pos = worklist.pop()
        if pos notin state.carray.channelsAtPosition:
            continue
        for bi in state.carray.channelsAtPosition[pos]:
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
                    let oldPenalty = c.penalty()
                    c.updatePosition(binding.channelPosition, newVal)
                    let newPenalty = c.penalty()
                    state.cost += newPenalty - oldPenalty
                    if oldPenalty > 0 and newPenalty == 0:
                        for pos in c.positions.items:
                            state.violationCount[pos] -= 1
                    elif oldPenalty == 0 and newPenalty > 0:
                        for pos in c.positions.items:
                            state.violationCount[pos] += 1
                state.updatePenaltiesForPosition(binding.channelPosition)
                state.updateNeighborPenalties(binding.channelPosition)
                # If this channel position triggers further channels, enqueue it
                if binding.channelPosition notin visited:
                    visited.incl(binding.channelPosition)
                    worklist.add(binding.channelPosition)

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    when ProfileIteration:
        let t0 = epochTime()

    state.assignment[position] = value

    for constraint in state.constraintsAtPosition[position]:
        let oldPenalty = constraint.penalty()
        constraint.updatePosition(position, value)
        let newPenalty = constraint.penalty()
        state.cost += newPenalty - oldPenalty
        # Update violation count for transitions to/from zero
        if oldPenalty > 0 and newPenalty == 0:
            for pos in constraint.positions.items:
                state.violationCount[pos] -= 1
        elif oldPenalty == 0 and newPenalty > 0:
            for pos in constraint.positions.items:
                state.violationCount[pos] += 1

    # Propagate channel variables affected by this position change
    state.propagateChannels(position)

    when ProfileIteration:
        let t1 = epochTime()
        state.timeAssignConstraints += t1 - t0

    state.updatePenaltiesForPosition(position)

    when ProfileIteration:
        let t2 = epochTime()
        state.timeUpdatePenalties += t2 - t1

    state.updateNeighborPenalties(position)

    when ProfileIteration:
        state.timeNeighborPenalties += epochTime() - t2


################################################################################
# Search Algorithm Implementation
################################################################################

proc bestMoves[T](state: TabuState[T]): seq[(int, T)] =
    const MAX_CANDIDATES_PER_POS = 500
    const FIRST_IMPROVEMENT_THRESHOLD = 100_000

    var
        bestMoveCost = high(int)
        movesEvaluated = 0

    # For large search spaces, use first-improvement: pick a small random
    # subset of violated positions and accept the first improving move.
    let useFirstImprovement = state.totalDomainSize > FIRST_IMPROVEMENT_THRESHOLD

    if useFirstImprovement:
        # First-improvement: check a limited number of random violated positions,
        # sample domain values randomly, and accept the first improving move.
        # Random sampling adds diversity that helps escape local optima.
        shuffle(state.searchPositions)
        var positionsChecked = 0
        const MAX_POS_FIRST_IMPROVEMENT = 30

        for position in state.searchPositions:
            when ProfileIteration:
                state.positionsScanned += 1

            let oldValue = state.assignment[position]
            let oldIdx = state.domainIndex[position].getOrDefault(oldValue, -1)
            if oldIdx < 0:
                continue

            if state.violationCount[position] == 0:
                continue

            inc positionsChecked

            let domain = state.carray.reducedDomain[position]
            let dLen = domain.len

            # Sample random domain values, break on first improving move
            for s in 0..<min(dLen, MAX_CANDIDATES_PER_POS):
                let i = rand(dLen - 1)
                if i == oldIdx:
                    continue
                inc movesEvaluated
                let newCost = state.cost + state.penaltyMap[position][i]
                if state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                    if newCost < bestMoveCost:
                        result = @[(position, domain[i])]
                        bestMoveCost = newCost
                    if bestMoveCost < state.cost:
                        break  # Found improving value, stop domain scan

            # Stop after finding an improving move or checking enough positions
            if bestMoveCost < state.cost:
                break
            if positionsChecked >= MAX_POS_FIRST_IMPROVEMENT:
                break
    else:
        for position in state.searchPositions:
            when ProfileIteration:
                state.positionsScanned += 1

            let oldValue = state.assignment[position]
            let oldIdx = state.domainIndex[position].getOrDefault(oldValue, -1)
            if oldIdx < 0:
                continue

            if state.violationCount[position] == 0:
                continue

            let domain = state.carray.reducedDomain[position]
            let dLen = domain.len

            if dLen <= MAX_CANDIDATES_PER_POS:
                for i in 0..<dLen:
                    if i == oldIdx:
                        continue
                    inc movesEvaluated
                    let newCost = state.cost + state.penaltyMap[position][i]
                    if state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                        if newCost < bestMoveCost:
                            result = @[(position, domain[i])]
                            bestMoveCost = newCost
                        elif newCost == bestMoveCost:
                            result.add((position, domain[i]))
            else:
                for s in 0..<MAX_CANDIDATES_PER_POS:
                    let i = rand(dLen - 1)
                    if i == oldIdx:
                        continue
                    inc movesEvaluated
                    let newCost = state.cost + state.penaltyMap[position][i]
                    if state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                        if newCost < bestMoveCost:
                            result = @[(position, domain[i])]
                            bestMoveCost = newCost
                        elif newCost == bestMoveCost:
                            result.add((position, domain[i]))

    state.movesExplored = movesEvaluated


################################################################################
# Swap Move Evaluation
################################################################################

proc swapDelta[T](state: TabuState[T], p1, p2: int, newVal1, newVal2: T): int =
    ## Compute the cost delta for simultaneously assigning p1→newVal1 and p2→newVal2.
    ## Uses penalty maps for independent contributions and corrects for shared constraints.
    let newIdx1 = state.domainIndex[p1].getOrDefault(newVal1, -1)
    let newIdx2 = state.domainIndex[p2].getOrDefault(newVal2, -1)
    if newIdx1 < 0 or newIdx2 < 0:
        return high(int)

    # Start with sum of independent single-move deltas from penalty maps
    result = state.penaltyMap[p1][newIdx1] + state.penaltyMap[p2][newIdx2]

    # Correct for shared constraints where independent deltas double-count
    let key = if p1 < p2: (p1, p2) else: (p2, p1)
    if key in state.sharedConstraints:
        for constraint in state.sharedConstraints[key]:
            # Get independent deltas from per-constraint penalty cache
            let localIdx1 = state.findLocalConstraintIdx(p1, constraint)
            let localIdx2 = state.findLocalConstraintIdx(p2, constraint)
            let indep1 = state.constraintPenalties[p1][localIdx1][newIdx1]
            let indep2 = state.constraintPenalties[p2][localIdx2][newIdx2]

            # Compute joint delta for both changes simultaneously
            var jointDelta: int
            if constraint.stateType == RelationalType:
                let rc = constraint.relationalState
                # Fast path for relational constraints with linear expressions
                var leftOk = true
                var rightOk = true
                var leftCoeff1, leftCoeff2, rightCoeff1, rightCoeff2: T

                case rc.leftExpr.kind
                of SumExpr:
                    let s = rc.leftExpr.sumExpr
                    if s.evalMethod == PositionBased:
                        leftCoeff1 = s.coefficient.getOrDefault(p1, T(0))
                        leftCoeff2 = s.coefficient.getOrDefault(p2, T(0))
                    else:
                        leftOk = false
                of ConstantExpr:
                    leftCoeff1 = 0
                    leftCoeff2 = 0
                else:
                    leftOk = false

                case rc.rightExpr.kind
                of SumExpr:
                    let s = rc.rightExpr.sumExpr
                    if s.evalMethod == PositionBased:
                        rightCoeff1 = s.coefficient.getOrDefault(p1, T(0))
                        rightCoeff2 = s.coefficient.getOrDefault(p2, T(0))
                    else:
                        rightOk = false
                of ConstantExpr:
                    rightCoeff1 = 0
                    rightCoeff2 = 0
                else:
                    rightOk = false

                if leftOk and rightOk:
                    let oldVal1 = state.assignment[p1]
                    let oldVal2 = state.assignment[p2]
                    let newLeft = rc.leftValue + leftCoeff1 * (newVal1 - oldVal1) + leftCoeff2 * (newVal2 - oldVal2)
                    let newRight = rc.rightValue + rightCoeff1 * (newVal1 - oldVal1) + rightCoeff2 * (newVal2 - oldVal2)
                    jointDelta = rc.relation.penalty(newLeft, newRight) - rc.cost
                else:
                    # Fallback: simulate both changes
                    let oldVal1 = state.assignment[p1]
                    let oldVal2 = state.assignment[p2]
                    let delta1 = constraint.relationalState.moveDelta(p1, oldVal1, newVal1)
                    # Temporarily apply first change to get joint delta
                    constraint.relationalState.updatePosition(p1, newVal1)
                    let delta2 = constraint.relationalState.moveDelta(p2, oldVal2, newVal2)
                    # Restore
                    constraint.relationalState.updatePosition(p1, oldVal1)
                    jointDelta = delta1 + delta2
            else:
                # Generic fallback: simulate and restore
                let oldVal1 = state.assignment[p1]
                let oldVal2 = state.assignment[p2]
                let costBefore = constraint.penalty()
                constraint.updatePosition(p1, newVal1)
                constraint.updatePosition(p2, newVal2)
                let costAfter = constraint.penalty()
                # Restore original state
                constraint.updatePosition(p2, oldVal2)
                constraint.updatePosition(p1, oldVal1)
                jointDelta = costAfter - costBefore

            # Correction: replace independent sum with joint delta
            result += jointDelta - indep1 - indep2


proc bestSwapMoves[T](state: TabuState[T]): (seq[(int, int, T, T)], int) =
    ## Find the best swap move among binary variable pairs.
    ## Returns (moves, bestCost) where moves is a list of equally-best
    ## (p1, p2, newVal1, newVal2) tuples and bestCost is the projected cost.
    ## Only active when flow structure is detected (swap moves are designed for
    ## network flow problems; for non-flow binary variables like channeling
    ## indicators, swapping without coordinating linked variables is counterproductive).
    if not state.flowEnabled:
        return (@[], high(int))

    const MAX_SWAP_EVALUATIONS = 2000

    var
        bestSwapCost = high(int)
        moves: seq[(int, int, T, T)] = @[]
        swapsEvaluated = 0

    # Iterate binary positions, prefer violated ones
    for bi1 in 0..<state.binaryPositions.len:
        let p1 = state.binaryPositions[bi1]
        if state.violationCount[p1] == 0:
            continue

        let val1 = state.assignment[p1]
        let newVal1 = 1 - val1  # flip: 0→1 or 1→0

        for bi2 in state.swapNeighbors[bi1]:
            let p2 = state.binaryPositions[bi2]
            let val2 = state.assignment[p2]

            # Only swap if they have different values (one 0→1, one 1→0)
            if val1 == val2:
                continue

            # Avoid evaluating (p2,p1) when we already evaluated (p1,p2)
            if p2 < p1:
                continue

            let newVal2 = 1 - val2

            let delta = state.swapDelta(p1, p2, newVal1, newVal2)
            let newCost = state.cost + delta
            inc swapsEvaluated

            # Tabu check: swap is tabu only if BOTH legs are tabu AND no aspiration
            let newIdx1 = state.domainIndex[p1].getOrDefault(newVal1, -1)
            let newIdx2 = state.domainIndex[p2].getOrDefault(newVal2, -1)
            let tabu1 = newIdx1 >= 0 and state.tabu[p1][newIdx1] > state.iteration
            let tabu2 = newIdx2 >= 0 and state.tabu[p2][newIdx2] > state.iteration
            let isTabu = tabu1 and tabu2
            let aspiration = newCost < state.bestCost

            if isTabu and not aspiration:
                continue

            if newCost < bestSwapCost:
                moves = @[(p1, p2, newVal1, newVal2)]
                bestSwapCost = newCost
            elif newCost == bestSwapCost:
                moves.add((p1, p2, newVal1, newVal2))

            if swapsEvaluated >= MAX_SWAP_EVALUATIONS:
                return (moves, bestSwapCost)

            # Early exit on improvement
            if bestSwapCost < state.cost:
                return (moves, bestSwapCost)

    return (moves, bestSwapCost)


################################################################################
# Move Application
################################################################################

proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    when ProfileIteration:
        let tBM = epochTime()
    let moves = state.bestMoves()
    let (swapMoves, swapCost) = state.bestSwapMoves()
    when ProfileIteration:
        state.timeBestMoves += epochTime() - tBM

    # Determine best single move cost
    var singleCost = high(int)
    if moves.len > 0:
        let (pos, val) = moves[0]
        let idx = state.domainIndex[pos].getOrDefault(val, -1)
        if idx >= 0:
            singleCost = state.cost + state.penaltyMap[pos][idx]

    if swapMoves.len > 0 and swapCost < singleCost:
        # Apply swap move
        let (p1, p2, newVal1, newVal2) = sample(swapMoves)
        let oldVal1 = state.assignment[p1]
        let oldVal2 = state.assignment[p2]
        state.assignValue(p1, newVal1)
        state.assignValue(p2, newVal2)
        let tabuTenure = state.iteration + 1 + state.iteration mod 10
        let oldIdx1 = state.domainIndex[p1].getOrDefault(oldVal1, -1)
        if oldIdx1 >= 0:
            state.tabu[p1][oldIdx1] = tabuTenure
        let oldIdx2 = state.domainIndex[p2].getOrDefault(oldVal2, -1)
        if oldIdx2 >= 0:
            state.tabu[p2][oldIdx2] = tabuTenure
    elif moves.len > 0:
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

    when ProfileIteration:
        let iters = max(1, state.iteration).float
        echo &"[Profile S{state.id}] bestMoves={state.timeBestMoves:.3f}s ({state.timeBestMoves/max(totalElapsed,0.001)*100:.1f}%) " &
             &"assignConstr={state.timeAssignConstraints:.3f}s ({state.timeAssignConstraints/max(totalElapsed,0.001)*100:.1f}%) " &
             &"updatePen={state.timeUpdatePenalties:.3f}s ({state.timeUpdatePenalties/max(totalElapsed,0.001)*100:.1f}%) " &
             &"neighborPen={state.timeNeighborPenalties:.3f}s ({state.timeNeighborPenalties/max(totalElapsed,0.001)*100:.1f}%)"
        echo &"[Profile S{state.id}] neighborUpdates={state.neighborUpdates} ({state.neighborUpdates.float/iters:.1f}/iter) " &
             &"batchCalls={state.neighborBatchCalls} ({state.neighborBatchCalls.float/iters:.1f}/iter) " &
             &"posScanned={state.positionsScanned} ({state.positionsScanned.float/iters:.1f}/iter)"

    state.lastLogTime = now
    state.lastLogIteration = state.iteration


proc tabuImprove*[T](state: TabuState[T], threshold: int, shouldStop: ptr Atomic[bool] = nil, deadline: float = 0.0): TabuState[T] =
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

        # Check deadline every 1024 iterations
        if deadline > 0 and (state.iteration and 0x3FF) == 0 and epochTime() > deadline:
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
                    when ProfileIteration:
                        let iters = max(1, state.iteration).float
                        echo &"[Profile S{state.id}] bestMoves={state.timeBestMoves:.3f}s ({state.timeBestMoves/max(elapsed,0.001)*100:.1f}%) " &
                             &"assignConstr={state.timeAssignConstraints:.3f}s ({state.timeAssignConstraints/max(elapsed,0.001)*100:.1f}%) " &
                             &"updatePen={state.timeUpdatePenalties:.3f}s ({state.timeUpdatePenalties/max(elapsed,0.001)*100:.1f}%) " &
                             &"neighborPen={state.timeNeighborPenalties:.3f}s ({state.timeNeighborPenalties/max(elapsed,0.001)*100:.1f}%)"
                        echo &"[Profile S{state.id}] neighborUpdates={state.neighborUpdates} ({state.neighborUpdates.float/iters:.1f}/iter) " &
                             &"batchCalls={state.neighborBatchCalls} ({state.neighborBatchCalls.float/iters:.1f}/iter)"
                return state

        # Try ejection chain moves periodically during stagnation
        if state.flowEnabled and
           state.iteration - lastImprovement >= 50 and
           (state.iteration - lastImprovement) mod 50 == 0:
            if state.tryChainMoves():
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            let elapsed = epochTime() - state.startTime
                            let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
                            echo &"[Tabu S{state.id}] Solution found via chain at iter={state.iteration} elapsed={elapsed:.2f}s rate={rate:.0f}/s"
                        return state

        state.iteration += 1

        # Periodic logging
        if state.verbose and state.iteration mod LogInterval == 0:
            state.logProgress(lastImprovement)

    if state.verbose:
        let elapsed = epochTime() - state.startTime
        let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
        echo &"[Tabu S{state.id}] Exhausted: best={state.bestCost} iters={state.iteration} elapsed={elapsed:.1f}s rate={rate:.0f}/s"
        when ProfileIteration:
            let iters = max(1, state.iteration).float
            echo &"[Profile S{state.id}] bestMoves={state.timeBestMoves:.3f}s ({state.timeBestMoves/elapsed*100:.1f}%) " &
                 &"assignConstr={state.timeAssignConstraints:.3f}s ({state.timeAssignConstraints/elapsed*100:.1f}%) " &
                 &"updatePen={state.timeUpdatePenalties:.3f}s ({state.timeUpdatePenalties/elapsed*100:.1f}%) " &
                 &"neighborPen={state.timeNeighborPenalties:.3f}s ({state.timeNeighborPenalties/elapsed*100:.1f}%)"
            echo &"[Profile S{state.id}] neighborUpdates={state.neighborUpdates} ({state.neighborUpdates.float/iters:.1f}/iter) " &
                 &"batchCalls={state.neighborBatchCalls} ({state.neighborBatchCalls.float/iters:.1f}/iter)"
        state.logProfileStats()

    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int, verbose: bool = false, deadline: float = 0.0): TabuState[T] =
    var state = newTabuState[T](carray, verbose)
    return state.tabuImprove(threshold, deadline = deadline)
