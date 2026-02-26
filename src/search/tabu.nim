import std/[math, packedsets, random, sequtils, tables, atomics, strformat]
from std/times import epochTime, cpuTime

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState, types, cumulative, geost, matrixElement, constraintNode, tableConstraint, diffn]
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

    FlatMinMaxBinding*[T] = object
        channelPosition*: int
        isMin*: bool
        # All inputs stored as linear terms: value = sum(coeffs[j] * assignment[positions[j]]) + offsets[j]
        # positions/coeffs/offsets have one entry per ref, inputBounds marks input boundaries
        linearPositions*: seq[int]   # concatenated positions for all inputs
        linearCoeffs*: seq[T]        # concatenated coefficients
        linearOffsets*: seq[T]       # one offset per input
        inputBounds*: seq[int]       # inputBounds[i] = start index into linearPositions for input i
        # Pre-evaluated constant: min/max of all constant inputs (inputs with 0 positions)
        constantVal*: T
        hasConstant*: bool
        # Complex inputs requiring expression evaluation (fallback, should be rare)
        complexExprs*: seq[AlgebraicExpression[T]]

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
        lastImprovementIter*: int  # Iteration of last bestCost improvement

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

        # Per-constraint search position cache (excludes channel positions)
        constraintSearchPos*: Table[pointer, PackedSet[int]]

        # Channel-dependent constraint support
        hasChannelDeps*: bool
        channelDepConstraints*: seq[StatefulConstraint[T]]
        channelDepPenalties*: seq[seq[int]]  # [position][domainIdx] -> channel-dep delta
        channelDepSearchPositions*: seq[int]  # search positions with channel bindings
        channelDepConstraintsForPos*: Table[int, seq[StatefulConstraint[T]]]  # pos -> relevant channel-dep constraints
        # One-hot channel fast path: maps source position to array of change entries.
        # For each domain value (array index = value - lo), stores which channel positions
        # change and what their transitions are when the source enters/leaves that value.
        # Each entry: (channelPos, valueWhenActive) — valueWhenActive=1 for eq_reif, 0 for ne_reif
        oneHotChanges*: Table[int, seq[seq[tuple[chanPos: int, activeVal: int]]]]
        oneHotLo*: Table[int, int]  # source pos -> lo offset from index expression
        # Reusable buffers for computeChannelDepDelta (avoid per-call heap allocation).
        # NOTE: these make computeChannelDepDelta non-reentrant within a single state.
        cdInUse: bool  # debug guard against reentrant calls
        cdChanges: seq[(int, T, T)]
        cdWorklist: seq[int]
        cdVisited: PackedSet[int]  # reusable visited set for worklist propagation
        cdProcessed: PackedSet[int]  # reusable dedup set for constraint penalty loop
        changedChannelsBuf: seq[int]  # buffer for propagateChannels output
        cdTargetedUpdates: Table[int, PackedSet[int]]  # reusable buffer for recomputeAffectedChannelDepPenalties
        # Reverse index: channel position → which search positions' channel-dep penalties are affected
        channelDepPosForChannel: Table[int, seq[int]]
        # Two-level reverse index for targeted channel-dep recomputation:
        # Level 1: channel position → indices into channelDepConstraints
        chanPosToDepConstraintIdx: Table[int, seq[int]]
        # Level 2: per constraint, list of one-hot (searchPos, domainIdx) entries it touches
        depConstraintOneHotEntries: seq[seq[tuple[pos: int, domainIdx: int]]]

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

        # Flat min/max channel bindings for fast evaluation (avoids DAG expression tree traversal)
        flatMinMaxBindings*: seq[FlatMinMaxBinding[T]]

        # Element implied move structures
        elementImpliedEnabled*: bool
        elementImpliedMoves*: Table[int, seq[StatefulConstraint[T]]]
            # index position -> element constraints where this pos affects the index
        elementImpliedDiscount*: Table[int, seq[int]]
            # index position -> per-domainIdx discount from implied fixes

        # Inverse group compound move structures
        inverseEnabled*: bool
        inverseGroups*: seq[InverseGroup[int]]
        posToInverseGroup*: seq[int]              # [position] -> group index (-1 if not in any group)
        posToGroupLocalIdx*: seq[int]             # [position] -> local index within group (-1 if not in any group)
        inverseDelta*: seq[seq[int]]              # [pos][domainIdx] -> compound delta from forced changes
        inverseForcedChanges*: seq[(int, int, int)]  # buffer: (pos, oldVal, newVal)
        inverseSavedBuf*: seq[(int, T)]           # reusable buffer for computeChannelDepDelta
        forcedChannelsBuf2*: seq[int]             # reusable buffer for forced position channel propagation

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
            cdTotalCalls*: int64
            cdTargetedPos*: int64
            cdFullPos*: int64
            cdNonOneHotPos*: int64
            cdMovedCalls*: int64
            affectedPosSkipped*: int64


# Forward declarations
proc initSwapStructures[T](state: TabuState[T])
proc initFlowStructure[T](state: TabuState[T])
proc initElementImpliedStructures[T](state: TabuState[T])
proc initInverseStructures[T](state: TabuState[T])
proc assignValue*[T](state: TabuState[T], position: int, value: T)
proc computeChannelDepDelta[T](state: TabuState[T], pos: int, candidateValue: T): int
proc computeInverseForcedChanges[T](state: TabuState[T], position: int, newValue: T, oldValue: T = T(0), oldValueProvided: bool = false)
proc computeInverseDeltaAt[T](state: TabuState[T], position: int, candidateValue: T): int
proc recomputeAllInverseDeltas[T](state: TabuState[T])

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
        of SubcircuitType:
            result = constraint.subcircuitState.moveDelta(position, oldValue, newValue)
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

proc costDelta*[T](state: TabuState[T], position: int, newValue: T): int =
    ## Compute the total cost change for assigning newValue at position by
    ## summing moveDelta across all constraints. O(constraints_at_pos) but
    ## doesn't require penalty maps to be up-to-date.
    ## Includes indirect cost changes through channel propagation and inverse group moves.
    for constraint in state.constraintsAtPosition[position]:
        result += state.movePenalty(constraint, position, newValue)
    if state.hasChannelDeps:
        result += state.computeChannelDepDelta(position, newValue)
    if state.inverseEnabled and state.posToInverseGroup[position] >= 0:
        result += state.computeInverseDeltaAt(position, newValue)

################################################################################
# Penalty Map Routines
################################################################################

proc recomputeElementImpliedDiscounts[T](state: TabuState[T]) =
    ## Recompute the penalty discount for all element index positions.
    ## For each candidate value of an index position, estimates how many element
    ## constraints can be fixed by implied moves and discounts the penalty by -1 each.
    ## This makes the solver see the benefit of compound moves before selecting them.
    if not state.elementImpliedEnabled:
        return

    let channelPos = state.carray.channelPositions

    for idxPos, constraints in state.elementImpliedMoves.pairs:
        let domain = state.carray.reducedDomain[idxPos]
        let dLen = domain.len
        if dLen == 0: continue

        # Initialize or reset discount seq
        if idxPos notin state.elementImpliedDiscount:
            state.elementImpliedDiscount[idxPos] = newSeq[int](dLen)
        else:
            for i in 0..<dLen:
                state.elementImpliedDiscount[idxPos][i] = 0

        for i in 0..<dLen:
            let candidateValue = domain[i]
            var discount = 0
            for constraint in constraints:
                let es = constraint.elementState
                # Evaluate what index the candidate value would produce
                var newIdx: int
                case es.evalMethod:
                of PositionBased:
                    newIdx = candidateValue
                of ExpressionBased:
                    let oldVal = es.currentAssignment.getOrDefault(idxPos, candidateValue)
                    es.currentAssignment[idxPos] = candidateValue
                    newIdx = es.indexExpression.evaluate(es.currentAssignment)
                    es.currentAssignment[idxPos] = oldVal

                let arraySize = es.getArraySize()
                if newIdx < 0 or newIdx >= arraySize:
                    continue

                # Would this element constraint be violated?
                let targetValue = es.getValueValue()
                let currentArrayValue = es.getArrayValue(newIdx)
                if currentArrayValue == targetValue:
                    continue  # Already satisfied, no discount needed

                # Can we fix it? Check if target position is a fixable variable
                var targetPos = -1
                case es.evalMethod:
                of PositionBased:
                    if es.isConstantArray: continue
                    let elem = es.arrayElements[newIdx]
                    if elem.isConstant: continue
                    targetPos = elem.variablePosition
                of ExpressionBased:
                    if es.isConstantArrayEB: continue
                    let expr = es.arrayExpressionsEB[newIdx]
                    if expr.node.kind != RefNode: continue
                    targetPos = expr.node.position

                if targetPos < 0 or targetPos in channelPos or targetPos == idxPos:
                    continue

                if targetValue in state.domainIndex[targetPos]:
                    discount -= 1

            state.elementImpliedDiscount[idxPos][i] = discount

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
        elif constraint.stateType == DiffnType:
            # Batch computation for diffn — pre-caches fixed rect coords
            let penalties = constraint.diffnState.batchMovePenalty(
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

    # Add channel-dep penalties (indirect cost through channel propagation)
    if state.hasChannelDeps and state.channelDepPenalties[position].len > 0:
        for i in 0..<dLen:
            state.penaltyMap[position][i] += state.channelDepPenalties[position][i]

    # Apply element implied discount
    if state.elementImpliedEnabled and position in state.elementImpliedDiscount:
        for i in 0..<dLen:
            state.penaltyMap[position][i] += state.elementImpliedDiscount[position][i]


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
    elif constraint.stateType == DiffnType:
        # Batch computation for diffn — pre-caches fixed rect coords
        let penalties = constraint.diffnState.batchMovePenalty(
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
    ## Uses precomputed search-only positions to skip channels efficiently.

    for constraint in state.constraintsAtPosition[position]:
        let cptr = cast[pointer](constraint)
        let searchPos = state.constraintSearchPos.getOrDefault(cptr)
        if searchPos.len == 0:
            continue  # Constraint has no search positions — skip entirely
        let affectedPositions = constraint.getAffectedPositions()

        # Fast path: binary broadcast for PositionBased SumExpr + ConstantExpr
        # For binary domains {0,1}, the flip penalty at every neighbor can be computed
        # with a single computeCost call per distinct coefficient, instead of calling
        # batchMovePenalty (which allocates a seq and does per-value computation).
        if constraint.stateType == RelationalType:
            let rc = constraint.relationalState
            var canBroadcast = false
            var sumOnLeft = false
            var sumRef: SumExpression[T]
            if rc.leftExpr.kind == SumExpr and
               rc.leftExpr.sumExpr.evalMethod == PositionBased and
               rc.rightExpr.kind == ConstantExpr:
                canBroadcast = true
                sumOnLeft = true
                sumRef = rc.leftExpr.sumExpr
            elif rc.rightExpr.kind == SumExpr and
                 rc.rightExpr.sumExpr.evalMethod == PositionBased and
                 rc.leftExpr.kind == ConstantExpr:
                canBroadcast = true
                sumOnLeft = false
                sumRef = rc.rightExpr.sumExpr

            if canBroadcast and affectedPositions.len > 0:
                let currentCost = rc.cost
                let leftV = rc.leftValue
                let rightV = rc.rightValue

                for pos in searchPos.items:
                    if pos == position:
                        continue
                    # For EqualTo with PositionBased SumExpr + ConstantExpr:
                    # when leftValue changed, ALL positions in leftExpr are affected.
                    # For inequality relations, slack-based skip may reduce this set,
                    # so we still need the check for non-EqualTo.
                    if rc.relation != EqualTo and pos notin affectedPositions:
                        continue

                    let domain = state.carray.reducedDomain[pos]
                    if domain.len != 2 or domain[0] != T(0) or domain[1] != T(1):
                        # Non-binary: fall back to standard update
                        if pos notin affectedPositions:
                            continue
                        when ProfileIteration:
                            state.neighborUpdates += 1
                            state.neighborBatchCalls += 1
                        let localIdx = state.findLocalConstraintIdx(pos, constraint)
                        state.updateConstraintAtPosition(pos, localIdx)
                        continue

                    when ProfileIteration:
                        state.neighborUpdates += 1
                    let localIdx = state.findLocalConstraintIdx(pos, constraint)
                    let x = int(state.assignment[pos])
                    let coeff = sumRef.coefficient.getOrDefault(pos, T(0))

                    # For binary domain: keeping current value always gives moveDelta = 0.
                    # Flip penalty: computeCost(leftV + flipDelta, rightV) - currentCost
                    let flipDelta = if x == 0: coeff else: -coeff
                    let newFlip = if sumOnLeft:
                        rc.computeCost(leftV + flipDelta, rightV) - currentCost
                    else:
                        rc.computeCost(leftV, rightV + flipDelta) - currentCost

                    # Binary domain sorted [0,1]: domainIndex maps 0→0, 1→1
                    # keepIdx = x, flipIdx = 1-x
                    let oldKeep = state.constraintPenalties[pos][localIdx][x]
                    let oldFlip = state.constraintPenalties[pos][localIdx][1-x]
                    state.penaltyMap[pos][x] -= oldKeep  # newKeep = 0
                    state.penaltyMap[pos][1-x] += newFlip - oldFlip
                    state.constraintPenalties[pos][localIdx][x] = 0
                    state.constraintPenalties[pos][localIdx][1-x] = newFlip

                continue  # Done with this constraint via broadcast

        # Standard path
        for pos in searchPos.items:
            if pos == position:
                continue
            if pos notin affectedPositions:
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
    for position in state.carray.allSearchPositions():
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
# Channel-Dependent Constraint Penalty Routines
################################################################################

proc channelDepConstraintDelta[T](c: StatefulConstraint[T], cdChanges: seq[(int, T, T)]): int =
    ## Compute the penalty delta for a single channel-dep constraint given a set of
    ## channel value changes. Uses fast arithmetic for RelationalConstraint+SumExpr,
    ## falls back to simulate-restore for other constraint types.
    if c.stateType == RelationalType:
        let rc = c.relationalState
        var newLeft = rc.leftValue
        var newRight = rc.rightValue
        var canFastPath = true

        case rc.leftExpr.kind
        of SumExpr:
            if rc.leftExpr.sumExpr.evalMethod == PositionBased:
                for (cp, oldV, newV) in cdChanges:
                    let coeff = rc.leftExpr.sumExpr.coefficient.getOrDefault(cp, T(0))
                    if coeff != 0:
                        newLeft += coeff * (newV - oldV)
            else: canFastPath = false
        of ConstantExpr: discard
        else: canFastPath = false

        if canFastPath:
            case rc.rightExpr.kind
            of SumExpr:
                if rc.rightExpr.sumExpr.evalMethod == PositionBased:
                    for (cp, oldV, newV) in cdChanges:
                        let coeff = rc.rightExpr.sumExpr.coefficient.getOrDefault(cp, T(0))
                        if coeff != 0:
                            newRight += coeff * (newV - oldV)
                else: canFastPath = false
            of ConstantExpr: discard
            else: canFastPath = false

        if canFastPath:
            return rc.computeCost(newLeft, newRight) - rc.cost

    # Fallback: simulate-restore on the constraint
    let oldPenalty = c.penalty()
    for (cp, _, newV) in cdChanges:
        if cp in c.positions:
            c.updatePosition(cp, newV)
    let newPenalty = c.penalty()
    for j in countdown(cdChanges.len - 1, 0):
        let (cp, oldV, _) = cdChanges[j]
        if cp in c.positions:
            c.updatePosition(cp, oldV)
    return newPenalty - oldPenalty

type LinearTerm[T] = tuple[pos: int, coeff: T]

proc tryExtractLinear[T](node: ExpressionNode[T]): tuple[ok: bool, terms: seq[LinearTerm[T]], offset: T] =
    ## Recursively decompose an expression tree into sum(coeff_i * assignment[pos_i]) + offset.
    ## Non-linear subtrees (min/max/abs) are only treated as constants when their
    ## children are purely constant (no variable references). If they depend on
    ## variables, we return ok=false so the entire input expression falls through
    ## to complexExprs for correct runtime evaluation.
    case node.kind
    of LiteralNode:
        return (true, @[], node.value)
    of RefNode:
        return (true, @[(pos: node.position, coeff: T(1))], T(0))
    of BinaryOpNode:
        case node.binaryOp
        of Addition:
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            return (true, lterms & rterms, loff + roff)
        of Subtraction:
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            var negTerms = newSeq[LinearTerm[T]](rterms.len)
            for i, t in rterms: negTerms[i] = (pos: t.pos, coeff: -t.coeff)
            return (true, lterms & negTerms, loff - roff)
        of Multiplication:
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            if lterms.len == 0 and rterms.len == 0:
                return (true, @[], loff * roff)
            if lterms.len == 0:
                var scaled = newSeq[LinearTerm[T]](rterms.len)
                for i, t in rterms: scaled[i] = (pos: t.pos, coeff: loff * t.coeff)
                return (true, scaled, loff * roff)
            if rterms.len == 0:
                var scaled = newSeq[LinearTerm[T]](lterms.len)
                for i, t in lterms: scaled[i] = (pos: t.pos, coeff: roff * t.coeff)
                return (true, scaled, roff * loff)
            return (false, @[], T(0))
        of Maximum, Minimum:
            # Only fold as constant if both children are purely constant (no terms).
            # Otherwise the result depends on variable values and would go stale.
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            if lterms.len == 0 and rterms.len == 0:
                let v = if node.binaryOp == Maximum: max(loff, roff) else: min(loff, roff)
                return (true, @[], v)
            return (false, @[], T(0))
    of UnaryOpNode:
        if node.unaryOp == Negation:
            let (ok, terms, off) = tryExtractLinear[T](node.target)
            if ok:
                var negTerms = newSeq[LinearTerm[T]](terms.len)
                for i, t in terms: negTerms[i] = (pos: t.pos, coeff: -t.coeff)
                return (true, negTerms, -off)
        elif node.unaryOp == AbsoluteValue:
            # Only fold as constant if the child is purely constant (no terms).
            let (ok, terms, off) = tryExtractLinear[T](node.target)
            if ok and terms.len == 0:
                return (true, @[], abs(off))
        return (false, @[], T(0))

proc evaluateFlatMinMax[T](fb: FlatMinMaxBinding[T], assignment: seq[T]): T {.inline.} =
    ## Evaluate a min/max channel binding using flat data (no tree traversal).
    let nInputs = fb.linearOffsets.len
    if fb.isMin:
        result = if fb.hasConstant: fb.constantVal else: high(T)
        for i in 0..<nInputs:
            var v = fb.linearOffsets[i]
            let start = fb.inputBounds[i]
            let stop = if i + 1 < nInputs: fb.inputBounds[i + 1] else: fb.linearPositions.len
            for j in start..<stop:
                v += fb.linearCoeffs[j] * assignment[fb.linearPositions[j]]
            if v < result: result = v
        for expr in fb.complexExprs:
            let v = expr.evaluate(assignment)
            if v < result: result = v
    else:
        result = if fb.hasConstant: fb.constantVal else: low(T)
        for i in 0..<nInputs:
            var v = fb.linearOffsets[i]
            let start = fb.inputBounds[i]
            let stop = if i + 1 < nInputs: fb.inputBounds[i + 1] else: fb.linearPositions.len
            for j in start..<stop:
                v += fb.linearCoeffs[j] * assignment[fb.linearPositions[j]]
            if v > result: result = v
        for expr in fb.complexExprs:
            let v = expr.evaluate(assignment)
            if v > result: result = v

proc computeChannelDepDelta[T](state: TabuState[T], pos: int, candidateValue: T): int =
    ## Compute the total penalty delta from channel-dep constraints if we were
    ## to assign candidateValue at pos. Simulates channel propagation via worklist,
    ## then uses fast arithmetic for RelationalConstraint+SumExpr, falling back
    ## to simulate-restore for other constraint types.
    if pos notin state.carray.channelsAtPosition and
       pos notin state.carray.minMaxChannelsAtPosition:
        return 0

    assert not state.cdInUse, "computeChannelDepDelta is not reentrant"
    state.cdInUse = true
    defer: state.cdInUse = false

    # Clear reusable buffers from previous call
    state.cdVisited.clear()
    state.cdChanges.setLen(0)
    let savedPos = state.assignment[pos]
    state.assignment[pos] = candidateValue

    # Apply inverse group forced changes for simulation
    state.inverseSavedBuf.setLen(0)
    if state.inverseEnabled and state.posToInverseGroup[pos] >= 0:
        state.computeInverseForcedChanges(pos, candidateValue, savedPos, oldValueProvided = true)
        for (fPos, fOld, fNew) in state.inverseForcedChanges:
            state.inverseSavedBuf.add((fPos, state.assignment[fPos]))
            state.assignment[fPos] = T(fNew)

    # Fast path for one-hot source positions: directly compute the few changes
    # instead of evaluating all bindings through the worklist
    if pos in state.oneHotChanges:
        let changes = state.oneHotChanges[pos]
        let lo = state.oneHotLo[pos]
        let oldIdx = savedPos - lo
        let newIdx = candidateValue - lo

        if oldIdx == newIdx:
            state.assignment[pos] = savedPos
            return 0

        # Source leaving oldIdx: channels at oldIdx transition away from their active value
        if oldIdx >= 0 and oldIdx < changes.len:
            for (chanPos, activeVal) in changes[oldIdx]:
                # Was at activeVal (source matched), now goes to 1-activeVal (source no longer matches)
                let toVal = T(1 - activeVal)
                if state.assignment[chanPos] != toVal:
                    state.cdChanges.add((chanPos, state.assignment[chanPos], toVal))
                    state.assignment[chanPos] = toVal
        # Source entering newIdx: channels at newIdx transition to their active value
        if newIdx >= 0 and newIdx < changes.len:
            for (chanPos, activeVal) in changes[newIdx]:
                # Source now matches, so channel goes to activeVal
                let toVal = T(activeVal)
                if state.assignment[chanPos] != toVal:
                    state.cdChanges.add((chanPos, state.assignment[chanPos], toVal))
                    state.assignment[chanPos] = toVal

        # Propagate downstream from the changed channel positions
        state.cdWorklist.setLen(0)
        for (chanPos, _, _) in state.cdChanges:
            state.cdWorklist.add(chanPos)
        state.cdVisited.incl(pos)
        for (chanPos, _, _) in state.cdChanges:
            state.cdVisited.incl(chanPos)
        # Add inverse forced positions to the worklist for channel propagation
        for (fPos, savedVal) in state.inverseSavedBuf:
            if fPos notin state.cdVisited:
                state.cdVisited.incl(fPos)
                state.cdWorklist.add(fPos)

        while state.cdWorklist.len > 0:
            let p = state.cdWorklist.pop()
            if p in state.carray.channelsAtPosition:
                for bi in state.carray.channelsAtPosition[p]:
                    let binding = state.carray.channelBindings[bi]
                    let idxVal = binding.indexExpression.evaluate(state.assignment)
                    if idxVal < 0 or idxVal >= binding.arrayElements.len: continue
                    let elem = binding.arrayElements[idxVal]
                    let newChanVal = if elem.isConstant: elem.constantValue
                                     else: state.assignment[elem.variablePosition]
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.cdChanges.add((chanPos, state.assignment[chanPos], newChanVal))
                        state.assignment[chanPos] = newChanVal
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.minMaxChannelsAtPosition:
                for bi in state.carray.minMaxChannelsAtPosition[p]:
                    let fb = state.flatMinMaxBindings[bi]
                    let newChanVal = evaluateFlatMinMax(fb, state.assignment)
                    let chanPos = fb.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.cdChanges.add((chanPos, state.assignment[chanPos], newChanVal))
                        state.assignment[chanPos] = newChanVal
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
    else:
        # General worklist propagation
        state.cdWorklist.setLen(0)
        state.cdWorklist.add(pos)
        state.cdVisited.incl(pos)
        # Add inverse forced positions to the worklist for channel propagation
        for (fPos, savedVal) in state.inverseSavedBuf:
            if fPos notin state.cdVisited:
                state.cdVisited.incl(fPos)
                state.cdWorklist.add(fPos)

        while state.cdWorklist.len > 0:
            let p = state.cdWorklist.pop()
            if p in state.carray.channelsAtPosition:
                for bi in state.carray.channelsAtPosition[p]:
                    let binding = state.carray.channelBindings[bi]
                    let idxVal = binding.indexExpression.evaluate(state.assignment)
                    if idxVal < 0 or idxVal >= binding.arrayElements.len: continue
                    let elem = binding.arrayElements[idxVal]
                    let newChanVal = if elem.isConstant: elem.constantValue
                                     else: state.assignment[elem.variablePosition]
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.cdChanges.add((chanPos, state.assignment[chanPos], newChanVal))
                        state.assignment[chanPos] = newChanVal
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.minMaxChannelsAtPosition:
                for bi in state.carray.minMaxChannelsAtPosition[p]:
                    let fb = state.flatMinMaxBindings[bi]
                    let newChanVal = evaluateFlatMinMax(fb, state.assignment)
                    let chanPos = fb.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.cdChanges.add((chanPos, state.assignment[chanPos], newChanVal))
                        state.assignment[chanPos] = newChanVal
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)

    # Restore all modified assignment values (reverse order for cdChanges because a
    # channel position can be modified multiple times when it depends on both the
    # primary position and an inverse forced position — only the first entry has
    # the true original value).
    state.assignment[pos] = savedPos
    for (fPos, savedVal) in state.inverseSavedBuf:
        state.assignment[fPos] = savedVal
    for i in countdown(state.cdChanges.len - 1, 0):
        let (chanPos, oldVal, _) = state.cdChanges[i]
        state.assignment[chanPos] = oldVal

    if state.cdChanges.len == 0:
        return 0

    # Compute penalty delta for affected channel-dep constraints only.
    # Look up affected constraints directly from changed channels instead of
    # iterating all relevant constraints (O(cdChanges * constraints_per_channel)
    # instead of O(all_relevant_constraints * cdChanges)).
    if state.chanPosToDepConstraintIdx.len > 0:
        # Clear reusable dedup set
        state.cdProcessed.clear()
        for (chanPos, _, _) in state.cdChanges:
            if chanPos in state.chanPosToDepConstraintIdx:
                for ci in state.chanPosToDepConstraintIdx[chanPos]:
                    if ci in state.cdProcessed: continue
                    state.cdProcessed.incl(ci)
                    result += channelDepConstraintDelta(state.channelDepConstraints[ci], state.cdChanges)
    else:
        # Fallback: iterate all relevant constraints (no reverse index)
        let relevantConstraints = state.channelDepConstraintsForPos.getOrDefault(pos, @[])
        for c in relevantConstraints:
            var affected = false
            for (chanPos, _, _) in state.cdChanges:
                if chanPos in c.positions:
                    affected = true
                    break
            if not affected: continue
            result += channelDepConstraintDelta(c, state.cdChanges)


proc computeChannelDepPenaltiesAt[T](state: TabuState[T], pos: int) =
    ## Compute channelDepPenalties[pos] for all domain values.
    let domain = state.carray.reducedDomain[pos]
    for i in 0..<domain.len:
        state.channelDepPenalties[pos][i] = state.computeChannelDepDelta(pos, domain[i])


proc recomputeAllChannelDepPenalties[T](state: TabuState[T]) =
    ## Recompute channel-dep penalties at all relevant search positions and
    ## adjust penaltyMap by the delta (new - old). Called after propagateChannels
    ## when channel-dep constraint state has changed.
    for pos in state.channelDepSearchPositions:
        let domain = state.carray.reducedDomain[pos]
        for i in 0..<domain.len:
            let newDep = state.computeChannelDepDelta(pos, domain[i])
            let oldDep = state.channelDepPenalties[pos][i]
            if newDep != oldDep:
                state.penaltyMap[pos][i] += newDep - oldDep
                state.channelDepPenalties[pos][i] = newDep

proc recomputeAffectedChannelDepPenalties[T](state: TabuState[T], changedChannels: seq[int], movedPosition: int = -1) =
    ## Targeted recomputation: update channel-dep penalties at search positions
    ## affected by the given changed channel positions.
    ## Uses constraint-based reverse index to find ALL affected (pos, domainIdx) pairs
    ## across all search positions sharing constraints with changed channels.
    ## For one-hot positions, only recomputes the 2-3 domain values per position.
    ## The movedPosition is skipped (its penalty map is fully rebuilt by updatePenaltiesForPosition).

    if state.depConstraintOneHotEntries.len > 0:
        # Find affected constraint indices from changed channels
        var affectedConstraintIds: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.chanPosToDepConstraintIdx:
                for ci in state.chanPosToDepConstraintIdx[chanPos]:
                    affectedConstraintIds.incl(ci)

        # Collect targeted (pos, domainIdx) pairs from affected constraints
        # This finds ALL one-hot positions sharing constraints with changed channels
        state.cdTargetedUpdates.clear()
        for ci in affectedConstraintIds.items:
            for entry in state.depConstraintOneHotEntries[ci]:
                if entry.pos == movedPosition: continue
                if entry.pos notin state.cdTargetedUpdates:
                    state.cdTargetedUpdates[entry.pos] = initPackedSet[int]()
                state.cdTargetedUpdates[entry.pos].incl(entry.domainIdx)

        for pos, affectedIndices in state.cdTargetedUpdates.pairs:
            # Check if current value is among affected indices
            # (leaving cost baseline changed → all candidates affected)
            let currentVal = state.assignment[pos]
            let currentIdx = state.domainIndex[pos].getOrDefault(currentVal, -1)
            if currentIdx >= 0 and currentIdx in affectedIndices:
                # Full recomputation — current value's leaving channels affect all candidates
                when ProfileIteration: state.cdFullPos += 1
                let domain = state.carray.reducedDomain[pos]
                for i in 0..<domain.len:
                    when ProfileIteration: state.cdTotalCalls += 1
                    let newDep = state.computeChannelDepDelta(pos, domain[i])
                    let oldDep = state.channelDepPenalties[pos][i]
                    if newDep != oldDep:
                        state.penaltyMap[pos][i] += newDep - oldDep
                        state.channelDepPenalties[pos][i] = newDep
            else:
                # Targeted recomputation — only affected domain values
                when ProfileIteration: state.cdTargetedPos += 1
                let domain = state.carray.reducedDomain[pos]
                for i in affectedIndices.items:
                    when ProfileIteration: state.cdTotalCalls += 1
                    let newDep = state.computeChannelDepDelta(pos, domain[i])
                    let oldDep = state.channelDepPenalties[pos][i]
                    if newDep != oldDep:
                        state.penaltyMap[pos][i] += newDep - oldDep
                        state.channelDepPenalties[pos][i] = newDep

        # Also handle non-one-hot positions via channelDepPosForChannel
        var nonOneHotPositions: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.channelDepPosForChannel:
                for pos in state.channelDepPosForChannel[chanPos]:
                    if pos != movedPosition and pos notin state.cdTargetedUpdates:
                        nonOneHotPositions.incl(pos)
        for pos in nonOneHotPositions.items:
            when ProfileIteration: state.cdNonOneHotPos += 1
            let domain = state.carray.reducedDomain[pos]
            for i in 0..<domain.len:
                when ProfileIteration: state.cdTotalCalls += 1
                let newDep = state.computeChannelDepDelta(pos, domain[i])
                let oldDep = state.channelDepPenalties[pos][i]
                if newDep != oldDep:
                    state.penaltyMap[pos][i] += newDep - oldDep
                    state.channelDepPenalties[pos][i] = newDep
    else:
        # No reverse index — fall back to channelDepPosForChannel (original behavior)
        var affectedPositions: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.channelDepPosForChannel:
                for pos in state.channelDepPosForChannel[chanPos]:
                    affectedPositions.incl(pos)
        for pos in affectedPositions.items:
            let domain = state.carray.reducedDomain[pos]
            for i in 0..<domain.len:
                let newDep = state.computeChannelDepDelta(pos, domain[i])
                let oldDep = state.channelDepPenalties[pos][i]
                if newDep != oldDep:
                    state.penaltyMap[pos][i] += newDep - oldDep
                    state.channelDepPenalties[pos][i] = newDep


################################################################################
# TabuState creation
################################################################################

proc balanceBinarySums[T](state: TabuState[T]) =
    ## Adjusts initial assignment for binary variables to match equality-sum targets.
    ## For constraints of the form sum(binary_vars) == target, randomly flips
    ## variables so the sum matches the target exactly. Runs before constraint
    ## initialization so no state corruption.
    var fixed = initPackedSet[int]()  # positions already adjusted by earlier constraints

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo:
            continue
        # Left must be a position-based sum, right must be a constant
        if rc.leftExpr.kind != SumExpr or rc.rightExpr.kind != ConstantExpr:
            continue
        let s = rc.leftExpr.sumExpr
        if s.evalMethod != PositionBased:
            continue
        let target = rc.rightExpr.constantValue

        # Check all positions are binary {0,1} with coefficient 1
        var allBinaryUnitCoeff = true
        var positions: seq[int] = @[]
        for pos in s.positions.items:
            let dom = state.carray.reducedDomain[pos]
            let coeff = s.coefficient.getOrDefault(pos, T(0))
            if coeff != 1 or dom.len != 2 or dom[0] != 0 or dom[1] != 1:
                allBinaryUnitCoeff = false
                break
            positions.add(pos)
        if not allBinaryUnitCoeff or positions.len == 0:
            continue

        # Count current ones (only among unfixed positions)
        var currentOnes = 0
        var unfixedPositions: seq[int] = @[]
        for pos in positions:
            if pos in fixed:
                currentOnes += int(state.assignment[pos])
            else:
                unfixedPositions.add(pos)
                currentOnes += int(state.assignment[pos])

        # Compute how many ones we need among unfixed positions
        let fixedOnes = currentOnes - (block:
            var cnt = 0
            for pos in unfixedPositions:
                cnt += int(state.assignment[pos])
            cnt)
        let neededOnes = target - fixedOnes
        let n = unfixedPositions.len

        if neededOnes < 0 or neededOnes > n:
            continue  # infeasible given fixed positions, skip

        # Shuffle unfixed positions and assign exactly neededOnes ones
        shuffle(unfixedPositions)
        for i in 0..<n:
            state.assignment[unfixedPositions[i]] = if i < neededOnes: T(1) else: T(0)

        # Mark these positions as fixed for subsequent constraints
        for pos in positions:
            fixed.incl(pos)

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

    # Auto-detect graduated equality: if the system has inequality constraints
    # (which use graduated penalties), enable graduated penalty on EqualTo
    # constraints so they compete on the same scale as the inequalities.
    # This is especially important when channels are present, as the solver
    # needs smooth gradient to navigate through channel-mediated effects.
    block:
        var hasInequality = false
        for c in state.constraints:
            if c.stateType == RelationalType and
               c.relationalState.relation in {LessThan, LessThanEq, GreaterThan, GreaterThanEq}:
                hasInequality = true
                break
        if hasInequality:
            for c in state.constraints:
                if c.stateType == RelationalType and c.relationalState.relation == EqualTo:
                    c.relationalState.graduated = true

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

    # Collect positions belonging to inverse groups so we skip them in normal random init
    var inverseGroupPositions: PackedSet[int]
    for group in carray.inverseGroups:
        for pos in group.positions:
            inverseGroupPositions.incl(pos)

    for pos in carray.allPositions():
        if initialAssignment.len > 0:
            state.assignment[pos] = initialAssignment[pos]
        elif pos in carray.channelPositions:
            # Channel variables get a placeholder; computed below
            state.assignment[pos] = carray.reducedDomain[pos][0]
        elif pos in inverseGroupPositions:
            # Inverse group positions are initialized below as involutions
            state.assignment[pos] = carray.reducedDomain[pos][0]
        else:
            state.assignment[pos] = sample(carray.reducedDomain[pos])

    # Generate random involutions for inverse group positions
    if initialAssignment.len == 0 and carray.inverseGroups.len > 0:
        for group in carray.inverseGroups:
            let n = group.positions.len
            let offset = group.valueOffset
            # Generate a random involution (self-inverse permutation) via shuffle+pair
            # Retry until we get a valid involution that respects all domains
            var valid = false
            for attempt in 0..<1000:
                var perm = newSeq[int](n)
                var indices = toSeq(0..<n)
                shuffle(indices)
                var used = newSeq[bool](n)
                var ok = true
                var j = 0
                while j < n:
                    if used[indices[j]]:
                        j += 1
                        continue
                    # Try to pair indices[j] with next unpaired index
                    var paired = false
                    for k in (j+1)..<n:
                        if not used[indices[k]]:
                            let a = indices[j]
                            let b = indices[k]
                            # Check domain compatibility:
                            # position[a] must accept value (b - offset) and
                            # position[b] must accept value (a - offset)
                            let valA = T(b - offset)  # value at position a = b's 1-based index
                            let valB = T(a - offset)  # value at position b = a's 1-based index
                            let domA = carray.reducedDomain[group.positions[a]]
                            let domB = carray.reducedDomain[group.positions[b]]
                            if valA in domA and valB in domB:
                                perm[a] = b
                                perm[b] = a
                                used[a] = true
                                used[b] = true
                                paired = true
                                break
                    if not paired:
                        # If n is odd, the last element is a fixed point
                        let a = indices[j]
                        let valA = T(a - offset)
                        let domA = carray.reducedDomain[group.positions[a]]
                        if valA in domA:
                            perm[a] = a
                            used[a] = true
                        else:
                            ok = false
                            break
                    j += 1
                if ok:
                    # Verify all paired
                    var allUsed = true
                    for u in used:
                        if not u:
                            allUsed = false
                            break
                    if allUsed:
                        for i in 0..<n:
                            state.assignment[group.positions[i]] = T(perm[i] - offset)
                        valid = true
                        break
            if not valid and verbose and id == 0:
                echo "[Init] Warning: could not generate valid involution for group of size " & $n

    # Balance binary sums to match equality targets (before channel propagation)
    if initialAssignment.len == 0:
        state.balanceBinarySums()

    # Compute channel variable initial values from their defining element constraints
    for binding in carray.channelBindings:
        let idxVal = binding.indexExpression.evaluate(state.assignment)
        if idxVal >= 0 and idxVal < binding.arrayElements.len:
            let elem = binding.arrayElements[idxVal]
            state.assignment[binding.channelPosition] =
                if elem.isConstant: elem.constantValue
                else: state.assignment[elem.variablePosition]

    # Build flat min/max bindings: decompose expression trees into flat operations.
    # Expression trees can be DAGs (shared subtrees) causing exponential re-evaluation.
    # Flat bindings use O(1) position lookups and pre-evaluated constants instead.
    if carray.minMaxChannelBindings.len > 0:
        if verbose and id == 0:
            var totalInputs = 0
            var maxInputs = 0
            for binding in carray.minMaxChannelBindings:
                totalInputs += binding.inputExprs.len
                if binding.inputExprs.len > maxInputs:
                    maxInputs = binding.inputExprs.len
            echo "[Init] Min/max bindings: " & $carray.minMaxChannelBindings.len &
                 " total inputs=" & $totalInputs & " max=" & $maxInputs &
                 " avg=" & $(totalInputs div carray.minMaxChannelBindings.len)
            echo "[Init] Pre min/max: assignment+elem took " & $(epochTime() - initStart) & "s"
            initStart = epochTime()

        state.flatMinMaxBindings = newSeq[FlatMinMaxBinding[T]](carray.minMaxChannelBindings.len)
        let buildStart = epochTime()
        var nComplex = 0
        for i, binding in carray.minMaxChannelBindings:
            state.flatMinMaxBindings[i].channelPosition = binding.channelPosition
            state.flatMinMaxBindings[i].isMin = binding.isMin
            state.flatMinMaxBindings[i].hasConstant = false
            for expr in binding.inputExprs:
                let (ok, terms, offset) = tryExtractLinear[T](expr.node)
                if ok and terms.len > 0:
                    # Linear combination: sum(coeff_i * assignment[pos_i]) + offset
                    state.flatMinMaxBindings[i].inputBounds.add(state.flatMinMaxBindings[i].linearPositions.len)
                    state.flatMinMaxBindings[i].linearOffsets.add(offset)
                    for t in terms:
                        state.flatMinMaxBindings[i].linearPositions.add(t.pos)
                        state.flatMinMaxBindings[i].linearCoeffs.add(t.coeff)
                elif ok:
                    # Pure constant (pos == -1)
                    let v = offset
                    if not state.flatMinMaxBindings[i].hasConstant:
                        state.flatMinMaxBindings[i].constantVal = v
                        state.flatMinMaxBindings[i].hasConstant = true
                    elif binding.isMin:
                        if v < state.flatMinMaxBindings[i].constantVal:
                            state.flatMinMaxBindings[i].constantVal = v
                    else:
                        if v > state.flatMinMaxBindings[i].constantVal:
                            state.flatMinMaxBindings[i].constantVal = v
                else:
                    # Can't decompose — keep expression for runtime evaluation
                    state.flatMinMaxBindings[i].complexExprs.add(expr)
                    inc nComplex

        if verbose and id == 0:
            let buildElapsed = epochTime() - buildStart
            var totalLinear, totalConstants: int
            for fb in state.flatMinMaxBindings:
                totalLinear += fb.linearOffsets.len
                if fb.hasConstant: inc totalConstants
            echo "[Init] Min/max flat: " & $totalConstants & " constant, " &
                 $totalLinear & " linear, " & $nComplex & " complex (built in " &
                 $buildElapsed & "s)"
            initStart = epochTime()

        # Worklist-based fixed-point for chained min/max dependencies.
        var worklist: seq[int]  # indices into flatMinMaxBindings
        for i in 0..<state.flatMinMaxBindings.len:
            worklist.add(i)
        var inWorklist = newSeq[bool](state.flatMinMaxBindings.len)
        for i in 0..<inWorklist.len: inWorklist[i] = true

        # Build reverse index: position → binding indices that use this position as input
        var posToBindings = initTable[int, seq[int]]()
        for bi, fb in state.flatMinMaxBindings:
            for j in 0..<fb.linearPositions.len:
                let pos = fb.linearPositions[j]
                if pos notin posToBindings:
                    posToBindings[pos] = @[]
                posToBindings[pos].add(bi)

        var fpEvals = 0
        while worklist.len > 0:
            let bi = worklist.pop()
            inWorklist[bi] = false
            inc fpEvals
            let fb = state.flatMinMaxBindings[bi]
            let newVal = evaluateFlatMinMax(fb, state.assignment)
            if newVal != state.assignment[fb.channelPosition]:
                state.assignment[fb.channelPosition] = newVal
                # Enqueue downstream bindings that use this channel as input
                if fb.channelPosition in posToBindings:
                    for downstream in posToBindings[fb.channelPosition]:
                        if not inWorklist[downstream]:
                            inWorklist[downstream] = true
                            worklist.add(downstream)
        if verbose and id == 0:
            echo "[Init] Min/max channel fixed-point: " & $fpEvals & " evals, " &
                 $carray.minMaxChannelBindings.len & " bindings, took " & $(epochTime() - initStart) & "s"
            initStart = epochTime()

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

    # Precompute search-only positions per constraint (excluding channels)
    state.constraintSearchPos = initTable[pointer, PackedSet[int]]()
    for c in state.constraints:
        var searchPos: PackedSet[int]
        for pos in c.positions.items:
            if pos notin carray.channelPositions:
                searchPos.incl(pos)
        state.constraintSearchPos[cast[pointer](c)] = searchPos

    # Identify channel-dep constraints (those with no search positions)
    state.hasChannelDeps = false
    state.channelDepConstraints = @[]
    state.channelDepSearchPositions = @[]
    for c in state.constraints:
        let cptr = cast[pointer](c)
        let searchPos = state.constraintSearchPos.getOrDefault(cptr)
        if searchPos.len == 0:
            state.channelDepConstraints.add(c)
    if state.channelDepConstraints.len > 0:
        state.hasChannelDeps = true
        # Find search positions that have channel bindings (can affect channel-dep constraints)
        for pos in state.searchPositions:
            if pos in carray.channelsAtPosition or pos in carray.minMaxChannelsAtPosition:
                state.channelDepSearchPositions.add(pos)

        # Build inverse index: channel position -> channel-dep constraints at that position
        var channelDepAtPos = initTable[int, seq[StatefulConstraint[T]]]()
        for c in state.channelDepConstraints:
            for p in c.positions.items:
                if p in carray.channelPositions:
                    if p notin channelDepAtPos:
                        channelDepAtPos[p] = @[c]
                    else:
                        channelDepAtPos[p].add(c)

        # Precompute per search-position: which channel-dep constraints can it affect?
        # Simulate channel propagation topology (value-independent) from each position
        state.channelDepConstraintsForPos = initTable[int, seq[StatefulConstraint[T]]]()
        state.channelDepPosForChannel = initTable[int, seq[int]]()
        for pos in state.channelDepSearchPositions:
            var reachable: PackedSet[int]
            var worklist = @[pos]
            var visited: PackedSet[int]
            visited.incl(pos)
            while worklist.len > 0:
                let p = worklist.pop()
                # Element channel bindings
                if p in carray.channelsAtPosition:
                    for bi in carray.channelsAtPosition[p]:
                        let binding = carray.channelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Min/max channel bindings
                if p in carray.minMaxChannelsAtPosition:
                    for bi in carray.minMaxChannelsAtPosition[p]:
                        let binding = carray.minMaxChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
            # Collect channel-dep constraints reachable from this position
            var seen: PackedSet[int]  # dedup by constraint pointer
            var relevant: seq[StatefulConstraint[T]] = @[]
            for chanPos in reachable.items:
                if chanPos in channelDepAtPos:
                    for c in channelDepAtPos[chanPos]:
                        let cid = cast[int](cast[pointer](c))
                        if cid notin seen:
                            seen.incl(cid)
                            relevant.add(c)
            state.channelDepConstraintsForPos[pos] = relevant
            # Build reverse index: channel pos -> affected search positions
            for chanPos in reachable.items:
                if chanPos in channelDepAtPos:  # only channels with channel-dep constraints
                    if chanPos notin state.channelDepPosForChannel:
                        state.channelDepPosForChannel[chanPos] = @[]
                    state.channelDepPosForChannel[chanPos].add(pos)

        if verbose and id == 0:
            var totalRelevant = 0
            var maxRelevant = 0
            for pos in state.channelDepSearchPositions:
                let n = state.channelDepConstraintsForPos[pos].len
                totalRelevant += n
                if n > maxRelevant: maxRelevant = n
            echo "[Init] Channel-dep constraints: " & $state.channelDepConstraints.len &
                 " (reachable through " & $state.channelDepSearchPositions.len & " search positions" &
                 ", avg=" & $(totalRelevant div max(1, state.channelDepSearchPositions.len)) &
                 " max=" & $maxRelevant & " per pos)"

    # Build one-hot value→channel mapping for fast channel-dep propagation.
    # For positions where all channel bindings are one-hot (constant element arrays
    # with exactly one 1 and rest 0), precompute an array mapping:
    #   oneHotChanges[pos][arrayIdx] = [(chanPos, activeVal), ...]
    # This avoids evaluating all bindings during channel-dep delta — only the 2 that change.
    state.oneHotChanges = initTable[int, seq[seq[tuple[chanPos: int, activeVal: int]]]]()
    state.oneHotLo = initTable[int, int]()
    if state.hasChannelDeps:
        for pos in state.channelDepSearchPositions:
            if pos notin carray.channelsAtPosition: continue
            let bindingIndices = carray.channelsAtPosition[pos]
            if bindingIndices.len < 3: continue  # Only worth optimizing for large sets

            # All bindings must share the same index expression (pos - lo) or just (pos)
            # Extract lo from the first binding's indexExpression
            let firstBinding = carray.channelBindings[bindingIndices[0]]
            let node = firstBinding.indexExpression.node
            var lo = 0
            if node.kind == RefNode and node.position == pos:
                lo = 0
            elif node.kind == BinaryOpNode and node.binaryOp == Subtraction and
               node.left.kind == RefNode and node.left.position == pos and
               node.right.kind == LiteralNode:
                lo = node.right.value
            else:
                continue  # Not a simple pos or pos - lo pattern

            # Build: for each binding, check it's one-hot or inverted one-hot
            # Normal one-hot: exactly one 1, rest 0 → key = position of the 1, activeVal=1
            # Inverted one-hot: exactly one 0, rest 1 → key = position of the 0, activeVal=0
            let arrayLen = firstBinding.arrayElements.len
            var changesByIdx = newSeq[seq[tuple[chanPos: int, activeVal: int]]](arrayLen)

            var isOneHot = true
            for bi in bindingIndices:
                let binding = carray.channelBindings[bi]
                # Verify this binding uses the same index expression (same lo) as the first
                let bNode = binding.indexExpression.node
                var bLo = -1  # sentinel: doesn't match
                if bNode.kind == RefNode and bNode.position == pos:
                    bLo = 0
                elif bNode.kind == BinaryOpNode and bNode.binaryOp == Subtraction and
                   bNode.left.kind == RefNode and bNode.left.position == pos and
                   bNode.right.kind == LiteralNode:
                    bLo = bNode.right.value
                if bLo != lo:
                    isOneHot = false
                    break
                if binding.arrayElements.len != arrayLen:
                    isOneHot = false
                    break
                var oneCount = 0
                var zeroCount = 0
                var firstOneIdx = -1
                var firstZeroIdx = -1
                var valid = true
                for j, elem in binding.arrayElements:
                    if not elem.isConstant:
                        valid = false
                        break
                    if elem.constantValue == 1:
                        oneCount += 1
                        if firstOneIdx < 0: firstOneIdx = j
                    elif elem.constantValue == 0:
                        zeroCount += 1
                        if firstZeroIdx < 0: firstZeroIdx = j
                    else:
                        valid = false
                        break
                if not valid:
                    isOneHot = false
                    break
                if oneCount == 1 and zeroCount == arrayLen - 1:
                    # Normal one-hot: when source == (key+lo), channel = 1
                    changesByIdx[firstOneIdx].add((binding.channelPosition, 1))
                elif zeroCount == 1 and oneCount == arrayLen - 1:
                    # Inverted one-hot: when source == (key+lo), channel = 0
                    changesByIdx[firstZeroIdx].add((binding.channelPosition, 0))
                else:
                    isOneHot = false
                    break

            if isOneHot:
                state.oneHotChanges[pos] = changesByIdx
                state.oneHotLo[pos] = lo

        if verbose and id == 0:
            var failNoChannels = 0
            var failFewBindings = 0
            var failIndexExpr = 0
            var failArrayCheck = 0
            for pos in state.channelDepSearchPositions:
                if pos in state.oneHotChanges: continue
                if pos notin carray.channelsAtPosition:
                    failNoChannels += 1
                    continue
                let bi0 = carray.channelsAtPosition[pos]
                if bi0.len < 3:
                    failFewBindings += 1
                    continue
                let fb = carray.channelBindings[bi0[0]]
                let n = fb.indexExpression.node
                if not (n.kind == BinaryOpNode and n.binaryOp == Subtraction and
                        n.left.kind == RefNode and n.left.position == pos and
                        n.right.kind == LiteralNode) and
                   not (n.kind == RefNode and n.position == pos):
                    failIndexExpr += 1
                    continue
                failArrayCheck += 1

            echo "[Init] One-hot fast path: " & $state.oneHotChanges.len & " source positions" &
                 " (noCh=" & $failNoChannels & " fewBind=" & $failFewBindings &
                 " badIdx=" & $failIndexExpr & " badArr=" & $failArrayCheck & ")"

    # Build domain index: value -> local array index
    state.domainIndex = newSeq[Table[T, int]](carray.len)
    for pos in carray.allPositions():
        state.domainIndex[pos] = initTable[T, int]()
        for i, v in carray.reducedDomain[pos]:
            state.domainIndex[pos][v] = i

    # Build reverse index: channel position → channel-dep constraint indices
    # Used both for targeted recomputation and for fast constraint lookup in computeChannelDepDelta
    if state.hasChannelDeps:
        state.chanPosToDepConstraintIdx = initTable[int, seq[int]]()
        for ci, c in state.channelDepConstraints:
            for p in c.positions.items:
                if p notin state.chanPosToDepConstraintIdx:
                    state.chanPosToDepConstraintIdx[p] = @[ci]
                else:
                    state.chanPosToDepConstraintIdx[p].add(ci)

    # Build level-2 reverse index for targeted channel-dep recomputation
    if state.hasChannelDeps and state.oneHotChanges.len > 0:
        # For each constraint, which one-hot (pos, domainIdx) entries touch it
        state.depConstraintOneHotEntries = newSeq[seq[tuple[pos: int, domainIdx: int]]](state.channelDepConstraints.len)
        for pos in state.channelDepSearchPositions:
            if pos notin state.oneHotChanges: continue
            let changes = state.oneHotChanges[pos]
            let lo = state.oneHotLo[pos]
            for arrayIdx in 0..<changes.len:
                let val = T(arrayIdx + lo)
                let domIdx = state.domainIndex[pos].getOrDefault(val, -1)
                if domIdx < 0: continue
                var seenConstraints: PackedSet[int]
                for (chanPos, _) in changes[arrayIdx]:
                    if chanPos in state.chanPosToDepConstraintIdx:
                        for ci in state.chanPosToDepConstraintIdx[chanPos]:
                            if ci notin seenConstraints:
                                seenConstraints.incl(ci)
                                state.depConstraintOneHotEntries[ci].add((pos: pos, domainIdx: domIdx))
        if verbose and id == 0:
            var totalEntries = 0
            for ci in 0..<state.depConstraintOneHotEntries.len:
                totalEntries += state.depConstraintOneHotEntries[ci].len
            echo "[Init] Channel-dep reverse index: " & $state.chanPosToDepConstraintIdx.len &
                 " channel positions, " & $state.depConstraintOneHotEntries.len &
                 " constraints, " & $totalEntries & " one-hot entries"

    # Initialize dense penalty arrays — only for search positions (not channels)
    state.penaltyMap = newSeq[seq[int]](carray.len)
    state.constraintPenalties = newSeq[seq[seq[int]]](carray.len)
    state.tabu = newSeq[seq[int]](carray.len)
    state.channelDepPenalties = newSeq[seq[int]](carray.len)
    for pos in carray.allPositions():
        if pos in carray.channelPositions:
            continue
        let dsize = carray.reducedDomain[pos].len
        state.penaltyMap[pos] = newSeq[int](dsize)
        state.tabu[pos] = newSeq[int](dsize)
        state.constraintPenalties[pos] = newSeq[seq[int]](state.constraintsAtPosition[pos].len)
        for ci in 0..<state.constraintsAtPosition[pos].len:
            state.constraintPenalties[pos][ci] = newSeq[int](dsize)
        if state.hasChannelDeps:
            state.channelDepPenalties[pos] = newSeq[int](dsize)

    # Compute initial channel-dep penalties (before penalty map build)
    state.cdInUse = false
    if state.hasChannelDeps:
        let cdStart = epochTime()
        var cdBinaryCount = 0
        var cdLargeCount = 0
        var cdTotalEvals = 0
        for pos in state.channelDepSearchPositions:
            let dlen = carray.reducedDomain[pos].len
            cdTotalEvals += dlen
            if dlen <= 2: cdBinaryCount += 1
            else: cdLargeCount += 1
            state.computeChannelDepPenaltiesAt(pos)
        if verbose and id == 0:
            echo "[Init] Channel-dep penalties computed in " & $(epochTime() - cdStart) & "s" &
                 " (binary=" & $cdBinaryCount & " large=" & $cdLargeCount & " totalEvals=" & $cdTotalEvals & ")"

    # Initialize element implied structures before penalty map so discounts are included
    state.initElementImpliedStructures()
    state.recomputeElementImpliedDiscounts()

    if verbose and id == 0:
        let searchCount = state.searchPositions.len
        echo "[Init] Building penalty map: " & $searchCount & " search positions (skipping " & $(carray.len - searchCount) & " channels)"

    var penaltyStart = epochTime()
    var penaltyCount = 0
    for pos in carray.allSearchPositions():
        state.updatePenaltiesForPosition(pos)
        penaltyCount += 1
        if verbose and id == 0 and penaltyCount mod 500 == 0:
            let elapsed = epochTime() - penaltyStart
            let rate = penaltyCount.float / max(elapsed, 0.001)
            let eta = (state.searchPositions.len - penaltyCount).float / max(rate, 0.001)
            echo "[Init] Penalties: " & $penaltyCount & "/" & $state.searchPositions.len & " rate=" & $rate.int & "/s eta=" & $eta.int & "s"

    if verbose and id == 0:
        echo "[Init] Built penalty map in " & $(epochTime() - initStart) & "s"
        state.logProfileStats()
        state.resetProfileStats()

    # Initialize swap move structures for binary variables
    state.initSwapStructures()
    state.initFlowStructure()
    state.initInverseStructures()


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

    const maxBinaryPerConstraint = 350  # skip constraints with too many binary positions
    for constraint in state.constraints:
        # Collect binary positions in this constraint
        var binaryInConstraint: seq[int] = @[]
        for pos in constraint.positions.items:
            if pos in binaryPosSet:
                binaryInConstraint.add(pos)

        if binaryInConstraint.len < 2:
            continue

        # Skip constraints with too many binary positions (O(n^2) pair explosion)
        if binaryInConstraint.len > maxBinaryPerConstraint:
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
# Inverse Group Compound Move Support
################################################################################

proc computeInverseForcedChanges[T](state: TabuState[T], position: int, newValue: T, oldValue: T = T(0), oldValueProvided: bool = false) =
    ## Compute the 3 forced changes for assigning newValue at position within an inverse group.
    ## Populates state.inverseForcedChanges with (pos, oldVal, newVal) triples.
    ## Does NOT modify the assignment.
    ## If oldValueProvided is true, uses oldValue instead of reading assignment[position].
    state.inverseForcedChanges.setLen(0)
    let gi = state.posToInverseGroup[position]
    let group = state.inverseGroups[gi]
    let offset = group.valueOffset
    let localIdx = state.posToGroupLocalIdx[position]  # i

    let prevValue = if oldValueProvided: oldValue else: state.assignment[position]
    let newJ = int(newValue) + offset   # new partner local index
    let oldJ = int(prevValue) + offset   # old partner local index

    if newJ == localIdx:
        # Assigning self-match (fixed point). Old partner becomes unpaired.
        # Old partner oldJ needs a new value. Set it to itself (fixed point).
        if oldJ != localIdx and oldJ >= 0 and oldJ < group.positions.len:
            let partnerPos = group.positions[oldJ]
            let partnerOld = state.assignment[partnerPos]
            let partnerNew = T(oldJ - offset)  # self-match
            if partnerOld != partnerNew:
                state.inverseForcedChanges.add((partnerPos, int(partnerOld), int(partnerNew)))
    elif oldJ == localIdx:
        # Was a fixed point, now pairing with newJ.
        # newJ's old partner needs to become a fixed point.
        if newJ >= 0 and newJ < group.positions.len:
            let newPartnerPos = group.positions[newJ]
            let newPartnerOld = state.assignment[newPartnerPos]
            # Set newJ to point back to us
            let newPartnerNew = T(localIdx - offset)
            if newPartnerOld != newPartnerNew:
                state.inverseForcedChanges.add((newPartnerPos, int(newPartnerOld), int(newPartnerNew)))
                # newJ's old partner (if not us and not itself) becomes a fixed point
                let newPartnerOldIdx = int(newPartnerOld) + offset
                if newPartnerOldIdx != newJ and newPartnerOldIdx != localIdx and
                   newPartnerOldIdx >= 0 and newPartnerOldIdx < group.positions.len:
                    let thirdPos = group.positions[newPartnerOldIdx]
                    let thirdOld = state.assignment[thirdPos]
                    let thirdNew = T(newPartnerOldIdx - offset)  # self-match
                    if thirdOld != thirdNew:
                        state.inverseForcedChanges.add((thirdPos, int(thirdOld), int(thirdNew)))
    else:
        # General case: was paired with oldJ, now pairing with newJ.
        # Need: position[newJ] → localIdx, position[oldJ] → old_partner_of_newJ
        if newJ >= 0 and newJ < group.positions.len and
           oldJ >= 0 and oldJ < group.positions.len:
            let newPartnerPos = group.positions[newJ]
            let oldPartnerPos = group.positions[oldJ]
            let newPartnerOld = state.assignment[newPartnerPos]
            let newPartnerOldIdx = int(newPartnerOld) + offset  # who newJ was pointing to

            # newJ now points to us (localIdx)
            let newPartnerNew = T(localIdx - offset)
            if newPartnerOld != newPartnerNew:
                state.inverseForcedChanges.add((newPartnerPos, int(newPartnerOld), int(newPartnerNew)))

            # oldJ now points to newJ's old partner (completing the swap)
            let oldPartnerOld = state.assignment[oldPartnerPos]
            if newPartnerOldIdx >= 0 and newPartnerOldIdx < group.positions.len and
               newPartnerOldIdx != localIdx and newPartnerOldIdx != newJ:
                let oldPartnerNew = T(newPartnerOldIdx - offset)
                if oldPartnerOld != oldPartnerNew:
                    state.inverseForcedChanges.add((oldPartnerPos, int(oldPartnerOld), int(oldPartnerNew)))
                # newJ's old partner now points to oldJ
                if newPartnerOldIdx != oldJ:
                    let thirdPos = group.positions[newPartnerOldIdx]
                    let thirdOld = state.assignment[thirdPos]
                    let thirdNew = T(oldJ - offset)
                    if thirdOld != thirdNew:
                        state.inverseForcedChanges.add((thirdPos, int(thirdOld), int(thirdNew)))
            else:
                # newJ was pointing to localIdx (meaning newJ was our "new" partner already)
                # oldJ just needs to become a fixed point
                let oldPartnerNew = T(oldJ - offset)
                if oldPartnerOld != oldPartnerNew:
                    state.inverseForcedChanges.add((oldPartnerPos, int(oldPartnerOld), int(oldPartnerNew)))


proc computeInverseDeltaAt[T](state: TabuState[T], position: int, candidateValue: T): int =
    ## Compute the cost delta from the forced changes of an inverse group compound move
    ## at the given position with candidateValue.
    ## Uses movePenalty at each forced position (independent of primary position changes).
    state.computeInverseForcedChanges(position, candidateValue)
    for (fPos, fOld, fNew) in state.inverseForcedChanges:
        for constraint in state.constraintsAtPosition[fPos]:
            result += state.movePenalty(constraint, fPos, T(fNew))


proc recomputeAllInverseDeltas[T](state: TabuState[T]) =
    ## Recompute inverseDelta[pos][domainIdx] for all inverse group positions.
    ## Used only during initialization.
    for group in state.inverseGroups:
        for pos in group.positions:
            if pos in state.carray.channelPositions:
                continue
            let domain = state.carray.reducedDomain[pos]
            for i in 0..<domain.len:
                state.inverseDelta[pos][i] = state.computeInverseDeltaAt(pos, domain[i])


proc recomputeInverseDeltasTargeted[T](state: TabuState[T],
                                        movedPosition: int,
                                        localForced: openArray[(int, int, int)]) =
    ## Targeted recomputation of inverseDelta after an inverse group move.
    ## Only recomputes entries within the moved group that could have changed:
    ##   - Changed positions (primary + forced): full domain recompute
    ##   - Positions whose current partner is a changed position: full recompute
    ##   - Other positions: only domain values mapping to a changed local index
    let gi = state.posToInverseGroup[movedPosition]
    let group = state.inverseGroups[gi]
    let offset = group.valueOffset

    # Collect changed local indices (primary + forced positions)
    var changedLocalIdxs: PackedSet[int]
    changedLocalIdxs.incl(state.posToGroupLocalIdx[movedPosition])
    for (fPos, _, _) in localForced:
        if state.posToGroupLocalIdx[fPos] >= 0:
            changedLocalIdxs.incl(state.posToGroupLocalIdx[fPos])

    for pos in group.positions:
        if pos in state.carray.channelPositions:
            continue
        let domain = state.carray.reducedDomain[pos]
        let localIdx = state.posToGroupLocalIdx[pos]
        let oldJ = int(state.assignment[pos]) + offset

        if localIdx in changedLocalIdxs or oldJ in changedLocalIdxs:
            # This position's assignment changed, or its partner's assignment changed
            # → full recompute since forced changes depend on both
            for i in 0..<domain.len:
                state.inverseDelta[pos][i] = state.computeInverseDeltaAt(pos, domain[i])
        else:
            # Only recompute the few domain values whose candidate maps to a changed position.
            # Convert changed local indices → domain values → domain indices via domainIndex.
            for cl in changedLocalIdxs.items:
                let targetValue = T(cl - offset)
                let domIdx = state.domainIndex[pos].getOrDefault(targetValue, -1)
                if domIdx >= 0:
                    state.inverseDelta[pos][domIdx] = state.computeInverseDeltaAt(pos, targetValue)


proc initInverseStructures[T](state: TabuState[T]) =
    ## Initialize inverse group compound move structures.
    state.inverseEnabled = false
    state.inverseGroups = state.carray.inverseGroups
    state.posToInverseGroup = newSeq[int](state.carray.len)
    state.posToGroupLocalIdx = newSeq[int](state.carray.len)
    for i in 0..<state.carray.len:
        state.posToInverseGroup[i] = -1
        state.posToGroupLocalIdx[i] = -1
    state.inverseForcedChanges = @[]
    state.inverseSavedBuf = @[]
    state.forcedChannelsBuf2 = @[]

    if state.inverseGroups.len == 0:
        return

    state.inverseEnabled = true

    # Build position lookup tables (flat arrays for O(1) access in hot paths)
    for gi, group in state.inverseGroups:
        for li, pos in group.positions:
            state.posToInverseGroup[pos] = gi
            state.posToGroupLocalIdx[pos] = li

    # Allocate inverseDelta arrays for inverse group positions
    state.inverseDelta = newSeq[seq[int]](state.carray.len)
    for group in state.inverseGroups:
        for pos in group.positions:
            if pos in state.carray.channelPositions:
                continue
            let dsize = state.carray.reducedDomain[pos].len
            state.inverseDelta[pos] = newSeq[int](dsize)

    # Compute initial inverse deltas
    state.recomputeAllInverseDeltas()

    if state.verbose and state.id == 0:
        var totalPositions = 0
        for group in state.inverseGroups:
            totalPositions += group.positions.len
        echo "[Init] Inverse groups: " & $state.inverseGroups.len &
             " groups, " & $totalPositions & " positions"


################################################################################
# Element Implied Move Initialization
################################################################################

proc initElementImpliedStructures[T](state: TabuState[T]) =
    ## Detect element constraints with non-channel index positions and build
    ## a map from index positions to their element constraints, enabling
    ## compound moves that greedily fix array element targets after index changes.
    state.elementImpliedEnabled = false
    state.elementImpliedMoves = initTable[int, seq[StatefulConstraint[T]]]()

    let channelPos = state.carray.channelPositions

    for constraint in state.constraints:
        if constraint.stateType != ElementType:
            continue
        let es = constraint.elementState

        case es.evalMethod:
        of PositionBased:
            # Skip if the array is all constants (no variable target to fix)
            if es.isConstantArray:
                continue
            # Check that at least one array element is a variable
            var hasVariable = false
            for elem in es.arrayElements:
                if not elem.isConstant:
                    hasVariable = true
                    break
            if not hasVariable:
                continue

            let idxPos = es.indexPosition
            if idxPos in channelPos:
                continue
            if idxPos notin state.elementImpliedMoves:
                state.elementImpliedMoves[idxPos] = @[]
            state.elementImpliedMoves[idxPos].add(constraint)

        of ExpressionBased:
            # Skip if the array is all constants
            if es.isConstantArrayEB:
                continue
            # For expression-based, add each position in indexExprPositions if it's a search position
            for pos in es.indexExprPositions.keys:
                if pos in channelPos:
                    continue
                if pos notin state.elementImpliedMoves:
                    state.elementImpliedMoves[pos] = @[]
                state.elementImpliedMoves[pos].add(constraint)

    # Pre-allocate discount and old-discount buffers
    state.elementImpliedDiscount = initTable[int, seq[int]]()
    if state.elementImpliedMoves.len > 0:
        state.elementImpliedEnabled = true
        for idxPos in state.elementImpliedMoves.keys:
            let dLen = state.carray.reducedDomain[idxPos].len
            state.elementImpliedDiscount[idxPos] = newSeq[int](dLen)
        if state.verbose and state.id == 0:
            var totalConstraints = 0
            for constraints in state.elementImpliedMoves.values:
                totalConstraints += constraints.len
            echo "[Init] Element implied moves: " & $state.elementImpliedMoves.len &
                 " index positions, " & $totalConstraints & " element constraints"


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

proc propagateChannels[T](state: TabuState[T], position: int, changedChannels: var seq[int]): bool =
    ## Propagate channel variable values after a change at `position`.
    ## Uses a worklist to handle transitive channel dependencies.
    ## Returns true if any channel values actually changed.
    ## Populates changedChannels with positions of channels whose values changed.
    changedChannels.setLen(0)
    var worklist = @[position]
    var visited: PackedSet[int]
    visited.incl(position)

    while worklist.len > 0:
        let pos = worklist.pop()
        # Element channel bindings
        if pos in state.carray.channelsAtPosition:
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
                    result = true
                    changedChannels.add(binding.channelPosition)
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
                    state.updateNeighborPenalties(binding.channelPosition)
                    if binding.channelPosition notin visited:
                        visited.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Min/max channel bindings
        if pos in state.carray.minMaxChannelsAtPosition:
            for bi in state.carray.minMaxChannelsAtPosition[pos]:
                let fb = state.flatMinMaxBindings[bi]
                let newVal = evaluateFlatMinMax(fb, state.assignment)
                if newVal != state.assignment[fb.channelPosition]:
                    result = true
                    changedChannels.add(fb.channelPosition)
                    state.assignment[fb.channelPosition] = newVal
                    for c in state.constraintsAtPosition[fb.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(fb.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                        if oldPenalty > 0 and newPenalty == 0:
                            for pos in c.positions.items:
                                state.violationCount[pos] -= 1
                        elif oldPenalty == 0 and newPenalty > 0:
                            for pos in c.positions.items:
                                state.violationCount[pos] += 1
                    state.updateNeighborPenalties(fb.channelPosition)
                    if fb.channelPosition notin visited:
                        visited.incl(fb.channelPosition)
                        worklist.add(fb.channelPosition)

proc propagateChannelsLean[T](state: TabuState[T], position: int) =
    ## Lightweight channel propagation: updates constraint state and cost
    ## but skips penalty map updates entirely. For use during path relinking.
    var worklist = @[position]
    var visited: PackedSet[int]
    visited.incl(position)

    while worklist.len > 0:
        let pos = worklist.pop()
        # Element channel bindings
        if pos in state.carray.channelsAtPosition:
            for bi in state.carray.channelsAtPosition[pos]:
                let binding = state.carray.channelBindings[bi]
                let idxVal = binding.indexExpression.evaluate(state.assignment)
                var newVal: T
                if idxVal >= 0 and idxVal < binding.arrayElements.len:
                    let elem = binding.arrayElements[idxVal]
                    newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition]
                else:
                    continue
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin visited:
                        visited.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Min/max channel bindings
        if pos in state.carray.minMaxChannelsAtPosition:
            for bi in state.carray.minMaxChannelsAtPosition[pos]:
                let fb = state.flatMinMaxBindings[bi]
                let newVal = evaluateFlatMinMax(fb, state.assignment)
                if newVal != state.assignment[fb.channelPosition]:
                    state.assignment[fb.channelPosition] = newVal
                    for c in state.constraintsAtPosition[fb.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(fb.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if fb.channelPosition notin visited:
                        visited.incl(fb.channelPosition)
                        worklist.add(fb.channelPosition)

proc assignValueLean*[T](state: TabuState[T], position: int, value: T) =
    ## Lightweight assignment: updates constraint state and cost but skips
    ## penalty map updates. Used during path relinking for fast traversal.
    let oldValueLean = state.assignment[position]
    state.assignment[position] = value

    for constraint in state.constraintsAtPosition[position]:
        let oldPenalty = constraint.penalty()
        constraint.updatePosition(position, value)
        let newPenalty = constraint.penalty()
        state.cost += newPenalty - oldPenalty

    # Apply forced changes from inverse group compound move
    if state.inverseEnabled and state.posToInverseGroup[position] >= 0:
        state.computeInverseForcedChanges(position, value, oldValueLean, oldValueProvided = true)
        # Safe to iterate inverseForcedChanges directly: propagateChannelsLean doesn't modify it
        for (fPos, fOld, fNew) in state.inverseForcedChanges:
            state.assignment[fPos] = T(fNew)
            for constraint in state.constraintsAtPosition[fPos]:
                let oldPenalty = constraint.penalty()
                constraint.updatePosition(fPos, T(fNew))
                let newPenalty = constraint.penalty()
                state.cost += newPenalty - oldPenalty
            state.propagateChannelsLean(fPos)

    state.propagateChannelsLean(position)

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    when ProfileIteration:
        let t0 = epochTime()

    let oldValueAssign = state.assignment[position]
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

    # Apply forced changes from inverse group compound move
    let hasInverseMove = state.inverseEnabled and state.posToInverseGroup[position] >= 0
    var localForced: seq[(int, int, int)]  # local copy to avoid re-entrancy
    if hasInverseMove:
        state.computeInverseForcedChanges(position, value, oldValueAssign, oldValueProvided = true)
        for fc in state.inverseForcedChanges:
            localForced.add(fc)
        for (fPos, fOld, fNew) in localForced:
            state.assignment[fPos] = T(fNew)
            for constraint in state.constraintsAtPosition[fPos]:
                let oldPenalty = constraint.penalty()
                constraint.updatePosition(fPos, T(fNew))
                let newPenalty = constraint.penalty()
                state.cost += newPenalty - oldPenalty
                if oldPenalty > 0 and newPenalty == 0:
                    for p in constraint.positions.items:
                        state.violationCount[p] -= 1
                elif oldPenalty == 0 and newPenalty > 0:
                    for p in constraint.positions.items:
                        state.violationCount[p] += 1

    # Propagate channel variables affected by this position change
    let channelsChanged = state.propagateChannels(position, state.changedChannelsBuf)

    # Also propagate channels for forced positions (using pre-allocated buffer)
    if hasInverseMove:
        for (fPos, fOld, fNew) in localForced:
            let forcedChanged = state.propagateChannels(fPos, state.forcedChannelsBuf2)
            if forcedChanged:
                for ch in state.forcedChannelsBuf2:
                    state.changedChannelsBuf.add(ch)

    let anyChannelsChanged = state.changedChannelsBuf.len > 0

    # Recompute channel-dep penalties only for affected search positions
    if state.hasChannelDeps and anyChannelsChanged:
        state.recomputeAffectedChannelDepPenalties(state.changedChannelsBuf, position)
        # Refresh moved position's channel-dep cache before updatePenaltiesForPosition reads it
        if state.channelDepPenalties[position].len > 0:
            when ProfileIteration: state.cdMovedCalls += state.carray.reducedDomain[position].len
            state.computeChannelDepPenaltiesAt(position)
        if hasInverseMove:
            for (fPos, fOld, fNew) in localForced:
                if state.channelDepPenalties[fPos].len > 0:
                    state.computeChannelDepPenaltiesAt(fPos)

    when ProfileIteration:
        let t1 = epochTime()
        state.timeAssignConstraints += t1 - t0

    # Recompute element implied discounts before penalty rebuild if this is an index position.
    # The discount depends on current array values (updated above via constraint.updatePosition).
    if state.elementImpliedEnabled and position in state.elementImpliedMoves:
        state.recomputeElementImpliedDiscounts()

    state.updatePenaltiesForPosition(position)

    # Also rebuild penalty maps for forced positions
    if hasInverseMove:
        for (fPos, fOld, fNew) in localForced:
            state.updatePenaltiesForPosition(fPos)

    when ProfileIteration:
        let t2 = epochTime()
        state.timeUpdatePenalties += t2 - t1

    state.updateNeighborPenalties(position)

    # Also update neighbor penalties for forced positions
    if hasInverseMove:
        for (fPos, fOld, fNew) in localForced:
            state.updateNeighborPenalties(fPos)

    # Recompute inverse deltas for affected positions in the moved group
    if hasInverseMove:
        state.recomputeInverseDeltasTargeted(position, localForced)

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
            let hasInverse1 = state.inverseEnabled and state.posToInverseGroup[position] >= 0
            for s in 0..<min(dLen, MAX_CANDIDATES_PER_POS):
                let i = rand(dLen - 1)
                if i == oldIdx:
                    continue
                inc movesEvaluated
                var newCost = state.cost + state.penaltyMap[position][i]
                if hasInverse1:
                    newCost += state.inverseDelta[position][i]
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
            let hasInverse2 = state.inverseEnabled and state.posToInverseGroup[position] >= 0

            if dLen <= MAX_CANDIDATES_PER_POS:
                for i in 0..<dLen:
                    if i == oldIdx:
                        continue
                    inc movesEvaluated
                    var newCost = state.cost + state.penaltyMap[position][i]
                    if hasInverse2:
                        newCost += state.inverseDelta[position][i]
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
                    var newCost = state.cost + state.penaltyMap[position][i]
                    if hasInverse2:
                        newCost += state.inverseDelta[position][i]
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
                    jointDelta = rc.computeCost(newLeft, newRight) - rc.cost
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


proc tryGeneralSwapMoves[T](state: TabuState[T]): bool =
    ## Try value-exchange swaps between search positions.
    ## Uses assignValueLean simulation for exact delta computation.
    ## Returns true if an improving swap was found and applied.
    const MAX_SWAP_EVALS = 2000

    var bestDelta = 0
    var bestSwaps: seq[(int, int)] = @[]
    var evalsCount = 0

    for i in 0..<state.searchPositions.len:
        let p1 = state.searchPositions[i]
        if state.violationCount[p1] == 0:
            continue
        let val1 = state.assignment[p1]

        for j in (i+1)..<state.searchPositions.len:
            let p2 = state.searchPositions[j]
            let val2 = state.assignment[p2]
            if val1 == val2:
                continue

            # Check both values are in each other's domain
            let idx1 = state.domainIndex[p1].getOrDefault(val2, -1)
            let idx2 = state.domainIndex[p2].getOrDefault(val1, -1)
            if idx1 < 0 or idx2 < 0:
                continue
            let tabu1 = state.tabu[p1][idx1] > state.iteration
            let tabu2 = state.tabu[p2][idx2] > state.iteration

            # Simulate swap via 4x assignValueLean
            let origCost = state.cost
            state.assignValueLean(p1, val2)
            state.assignValueLean(p2, val1)
            let delta = state.cost - origCost
            # Restore (reverse order)
            state.assignValueLean(p2, val2)
            state.assignValueLean(p1, val1)

            inc evalsCount

            let aspiration = origCost + delta < state.bestCost
            if tabu1 and tabu2 and not aspiration:
                continue

            if delta < bestDelta:
                bestDelta = delta
                bestSwaps = @[(p1, p2)]
            elif delta == bestDelta and delta < 0:
                bestSwaps.add((p1, p2))

            if evalsCount >= MAX_SWAP_EVALS:
                break
        if evalsCount >= MAX_SWAP_EVALS:
            break

    if bestSwaps.len == 0:
        return false

    # Apply the best swap
    let (p1, p2) = sample(bestSwaps)
    let oldVal1 = state.assignment[p1]
    let oldVal2 = state.assignment[p2]
    state.assignValue(p1, oldVal2)
    state.assignValue(p2, oldVal1)

    # Set tabu on old values
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    let oldIdx1 = state.domainIndex[p1].getOrDefault(oldVal1, -1)
    if oldIdx1 >= 0:
        state.tabu[p1][oldIdx1] = tabuTenure
    let oldIdx2 = state.domainIndex[p2].getOrDefault(oldVal2, -1)
    if oldIdx2 >= 0:
        state.tabu[p2][oldIdx2] = tabuTenure
    return true


################################################################################
# Move Application
################################################################################

proc applyElementImpliedMoves[T](state: TabuState[T], movedPosition: int) =
    ## After a primary move at movedPosition, check if it's an element index position.
    ## If so, greedily apply follow-up moves at array element positions that produce
    ## a net cost improvement (strict delta < 0).
    if not state.elementImpliedEnabled:
        return
    if movedPosition notin state.elementImpliedMoves:
        return

    let channelPos = state.carray.channelPositions

    for constraint in state.elementImpliedMoves[movedPosition]:
        let es = constraint.elementState

        # Get current index value (reflects primary move)
        let newIdx = es.getIndexValue()
        let arraySize = es.getArraySize()
        if newIdx < 0 or newIdx >= arraySize:
            continue

        # What does the constraint need the array value to be?
        let targetValue = es.getValueValue()

        # What is the array currently holding at that index?
        let currentArrayValue = es.getArrayValue(newIdx)
        if currentArrayValue == targetValue:
            continue  # Already satisfied

        # Extract the target position from the array element at new index
        var targetPos = -1
        case es.evalMethod:
        of PositionBased:
            if es.isConstantArray:
                continue  # Can't change a constant
            let elem = es.arrayElements[newIdx]
            if elem.isConstant:
                continue  # Can't change a constant element
            targetPos = elem.variablePosition
        of ExpressionBased:
            if es.isConstantArrayEB:
                continue
            let expr = es.arrayExpressionsEB[newIdx]
            if expr.node.kind != RefNode:
                continue  # Only handle simple variable references
            targetPos = expr.node.position

        if targetPos < 0:
            continue
        if targetPos in channelPos:
            continue
        if targetPos == movedPosition:
            continue

        # Check if target value is in the domain
        let domIdx = state.domainIndex[targetPos].getOrDefault(targetValue, -1)
        if domIdx < 0:
            continue

        # Apply if net improvement or neutral (delta <= 0).
        # The element constraint contributes -1, so we apply even if other constraints
        # contribute +1 (net 0), since we're completing a compound move.
        var delta = state.penaltyMap[targetPos][domIdx]
        if state.hasChannelDeps and state.channelDepPenalties[targetPos].len > 0:
            delta += state.channelDepPenalties[targetPos][domIdx]
        if delta > 0:
            continue
        let oldValue = state.assignment[targetPos]
        state.assignValue(targetPos, targetValue)
        # Set tabu on the old value to prevent undoing
        let oldIdx = state.domainIndex[targetPos].getOrDefault(oldValue, -1)
        if oldIdx >= 0:
            state.tabu[targetPos][oldIdx] = state.iteration + 1 + state.iteration mod 10

proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    when ProfileIteration:
        let tBM = epochTime()
    let moves = state.bestMoves()
    let (swapMoves, swapCost) = state.bestSwapMoves()
    when ProfileIteration:
        state.timeBestMoves += epochTime() - tBM

    # Determine best single move cost (including inverse delta if applicable)
    var singleCost = high(int)
    if moves.len > 0:
        let (pos, val) = moves[0]
        let idx = state.domainIndex[pos].getOrDefault(val, -1)
        if idx >= 0:
            singleCost = state.cost + state.penaltyMap[pos][idx]
            if state.inverseEnabled and state.posToInverseGroup[pos] >= 0:
                singleCost += state.inverseDelta[pos][idx]

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
        state.applyElementImpliedMoves(p1)
        state.applyElementImpliedMoves(p2)
    elif moves.len > 0:
        let (position, newValue) = sample(moves)
        let oldValue = state.assignment[position]
        # Compute forced changes BEFORE assignValue to capture old values for tabu
        var forcedOldValues: seq[(int, T)]
        if state.inverseEnabled and state.posToInverseGroup[position] >= 0:
            state.computeInverseForcedChanges(position, newValue)
            for (fPos, fOld, fNew) in state.inverseForcedChanges:
                forcedOldValues.add((fPos, T(fOld)))
        state.assignValue(position, newValue)
        let tabuTenure = state.iteration + 1 + state.iteration mod 10
        let oldIdx = state.domainIndex[position].getOrDefault(oldValue, -1)
        if oldIdx >= 0:
            state.tabu[position][oldIdx] = tabuTenure
        # Set tabu on forced positions' old values
        for (fPos, fOldVal) in forcedOldValues:
            let fOldIdx = state.domainIndex[fPos].getOrDefault(fOldVal, -1)
            if fOldIdx >= 0:
                state.tabu[fPos][fOldIdx] = tabuTenure
        state.applyElementImpliedMoves(position)


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
        echo &"[Profile S{state.id}] cdCalls={state.cdTotalCalls} ({state.cdTotalCalls.float/iters:.1f}/iter) " &
             &"cdMoved={state.cdMovedCalls} ({state.cdMovedCalls.float/iters:.1f}/iter) " &
             &"targeted={state.cdTargetedPos} full={state.cdFullPos} nonOneHot={state.cdNonOneHotPos}"

    state.lastLogTime = now
    state.lastLogIteration = state.iteration


proc logExitStats[T](state: TabuState[T], label: string) =
    let elapsed = epochTime() - state.startTime
    let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
    echo &"[Tabu S{state.id}] {label}: best={state.bestCost} iters={state.iteration} elapsed={elapsed:.1f}s rate={rate:.0f}/s"
    when ProfileIteration:
        let iters = max(1, state.iteration).float
        echo &"[Profile S{state.id}] bestMoves={state.timeBestMoves:.3f}s ({state.timeBestMoves/max(elapsed,0.001)*100:.1f}%) " &
             &"assignConstr={state.timeAssignConstraints:.3f}s ({state.timeAssignConstraints/max(elapsed,0.001)*100:.1f}%) " &
             &"updatePen={state.timeUpdatePenalties:.3f}s ({state.timeUpdatePenalties/max(elapsed,0.001)*100:.1f}%) " &
             &"neighborPen={state.timeNeighborPenalties:.3f}s ({state.timeNeighborPenalties/max(elapsed,0.001)*100:.1f}%)"
        echo &"[Profile S{state.id}] neighborUpdates={state.neighborUpdates} ({state.neighborUpdates.float/iters:.1f}/iter) " &
             &"batchCalls={state.neighborBatchCalls} ({state.neighborBatchCalls.float/iters:.1f}/iter) " &
             &"posScanned={state.positionsScanned} ({state.positionsScanned.float/iters:.1f}/iter)"
        echo &"[Profile S{state.id}] cdCalls={state.cdTotalCalls} ({state.cdTotalCalls.float/iters:.1f}/iter) " &
             &"cdMoved={state.cdMovedCalls} ({state.cdMovedCalls.float/iters:.1f}/iter) " &
             &"targeted={state.cdTargetedPos} full={state.cdFullPos} nonOneHot={state.cdNonOneHotPos}"
    state.logProfileStats()


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
            if state.verbose:
                state.logExitStats("Stopped")
            state.lastImprovementIter = lastImprovement
            return state

        # Check deadline every 1024 iterations
        if deadline > 0 and (state.iteration and 0x3FF) == 0 and epochTime() > deadline:
            if state.verbose:
                state.logExitStats("Deadline")
            state.lastImprovementIter = lastImprovement
            return state

        state.applyBestMove()

        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.bestCost = state.cost
            state.bestAssignment = state.assignment
            if state.cost == 0:
                if state.verbose:
                    state.logExitStats("Solution found")
                state.lastImprovementIter = lastImprovement
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
                            state.logExitStats("Solution found via chain")
                        state.lastImprovementIter = lastImprovement
                        return state

        # Try general swap moves periodically during stagnation
        if state.searchPositions.len <= 200 and
           state.iteration - lastImprovement >= 20 and
           (state.iteration - lastImprovement) mod 20 == 0:
            if state.tryGeneralSwapMoves():
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via swap")
                        state.lastImprovementIter = lastImprovement
                        return state

        state.iteration += 1

        # Periodic logging
        if state.verbose and state.iteration mod LogInterval == 0:
            state.logProgress(lastImprovement)

    if state.verbose:
        state.logExitStats("Exhausted")

    state.lastImprovementIter = lastImprovement
    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int, verbose: bool = false, deadline: float = 0.0): TabuState[T] =
    var state = newTabuState[T](carray, verbose)
    return state.tabuImprove(threshold, deadline = deadline)
