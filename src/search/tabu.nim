import std/[algorithm, math, packedsets, random, sequtils, tables, atomics, strformat]
from std/times import epochTime, cpuTime

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState, types, cumulative, geost, matrixElement, constraintNode, tableConstraint, diffn, noOverlapFixedBox, conditionalCumulative, conditionalNoOverlap, conditionalDayCapacity]
from ../constraints/globalCardinality import ExactCounts, BoundedCounts
import ../constrainedArray
import ../expressions/expressions

randomize()

# Logging configuration
const LogInterval* = 50000  # Log every N iterations
const ProfileMoveDelta* = false  # Enable moveDelta profiling (disable for performance)
const ProfileIteration* = false  # Enable per-iteration phase profiling
const LazyThreshold* = 1000  # Positions with domain > this use on-demand costDelta instead of penalty maps
const BatchLazyMax* = 10000  # Lazy positions with domain <= this use batch evaluation in bestMoves

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
        sharedDomain*: ptr seq[seq[T]]  # Points to shared reducedDomain (never copied per state)
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
        isLazy*: seq[bool]  # [position] -> true if domain > LazyThreshold (uses costDelta, no penalty map)

        # Per-constraint search position cache (excludes channel positions)
        constraintSearchPos*: Table[pointer, PackedSet[int]]

        # Channel-dependent constraint support
        hasChannelDeps*: bool
        channelDepConstraints*: seq[StatefulConstraint[T]]
        channelDepConstraintActive*: seq[bool]  # per-constraint: false if tautological (penalty always 0)
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
        cdTrackPerConstraint: bool  # when true, track per-constraint max delta during init
        cdPerConstraintMaxDelta: seq[int]  # [constraintIdx] -> max |delta| seen during init
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

        # GCC-preserving swap structures
        gccGroupPositions*: seq[seq[int]]  # search positions per GCC constraint (for GCC-preserving swaps)

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

        # Channel-dep optimized simulation state (position-indexed arrays instead of hash tables)
        cdIsChanged: seq[bool]           # position-indexed, true if changed during simulation
        cdSavedVal: seq[T]               # position-indexed, original value before simulation
        cdDirtyPositions: seq[int]       # unique positions changed during simulation (for cleanup)

        # Precomputed coefficient lists for channel-dep constraints (flat arrays, no hash lookups)
        cdConstraintCoeffs: seq[seq[tuple[pos: int, coeff: T]]]   # [constraintIdx][j] = (position, coefficient) - left side
        cdConstraintCoeffsR: seq[seq[tuple[pos: int, coeff: T]]]  # right side coefficients
        cdConstraintCanFast: seq[bool]                             # can use fast path (both sides PositionBased/Constant)

        # Precomputed cascade tables: topology + optional precomputed values.
        # For ALL channel-dep positions, we precompute the topology (channel order, bindings, constraints).
        # For positions with constant-array bindings, we also precompute absolute channel values.
        # This enables batch evaluation: walk topology once, evaluate all domain values at once.
        cdCascadePos: Table[int, int]             # source position -> index into cdCascade*
        cdCascadeChans: seq[seq[int]]             # [cascadeIdx] -> channel positions in topological order
        cdCascadeBindings: seq[seq[int]]          # [cascadeIdx] -> binding index for each channel position (element or flatMinMax index)
        cdCascadeIsMinMax: seq[seq[bool]]         # [cascadeIdx][entryIdx] -> true if entry is a min/max binding
        cdCascadeExternalDeps: seq[PackedSet[int]]    # [cascadeIdx] -> ALL external dependency positions
        cdCascadeElemExtDeps: seq[PackedSet[int]]     # [cascadeIdx] -> external deps from element entries only
        cdCascadeMinMaxIdx: seq[seq[int]]             # [cascadeIdx] -> indices into topoOrder that are min/max entries
        # Min/max fast-path: cached cascade values and precomputed input mapping
        cdCascadeCachedValues: seq[seq[seq[T]]]      # [cascadeIdx][chanIdx][domainIdx] -> cached from last full eval
        cdCascadeMinMaxInputs: seq[seq[seq[tuple[linearIdx: int, topoIdx: int]]]] # [cascadeIdx][mmLocalIdx] -> (linearPositions index, cascade topoIdx)
        # Incremental cascade evaluation: forward deps and per-entry external inputs
        cdCascadeForwardDeps: seq[seq[seq[int]]]    # [cascadeIdx][ci] -> downstream entry indices that read from chans[ci]
        cdCascadeExtPosToEntries: seq[Table[int, seq[int]]]  # [cascadeIdx] -> extPos -> [entry indices that read extPos]
        cdCascadeDirtyBase: seq[bool]               # reusable buffer for incremental eval dirty tracking
        cdCascadeDirtyDV: seq[bool]                 # reusable buffer for per-domain-value dirty tracking
        cdCascadeInWorkList: seq[bool]              # reusable buffer for work list membership
        cdCascadeWorkList: seq[int]                 # reusable buffer for work list indices
        cdCascadeValues: seq[seq[seq[T]]]         # [cascadeIdx][chanIdx][domainIdx] -> absolute channel value (empty for dynamic)
        cdCascadeIsStatic: seq[bool]              # true if values are precomputed (constant arrays)
        # Per-constraint mapping into cascade channels (for fast penalty computation)
        cdCascadeConstraintL: seq[seq[seq[tuple[cascadeIdx: int, coeff: T]]]]  # [cascadeIdx][constraintLocalIdx][j] = (chanIdx in cascade, coeff)
        cdCascadeConstraintR: seq[seq[seq[tuple[cascadeIdx: int, coeff: T]]]]  # right side
        cdCascadeConstraintIds: seq[seq[int]]     # [cascadeIdx][constraintLocalIdx] -> index into channelDepConstraints
        # Reusable buffers for dynamic batch evaluation (avoid per-call allocation)
        cdBatchValues: seq[seq[T]]                # [chanIdx][domainIdx] -> channel value (resized as needed)
        cdBatchSaved: seq[T]                      # saved channel values during batch evaluation
        # Uniform delta: saved constraint costs before propagation
        cdSavedConstraintCosts: seq[int]          # [constraintIdx] -> saved cost before propagateChannels

        # Dormancy support: positions that are don't-care based on a selector variable's value
        hasDormancy*: bool
        isDormant*: seq[bool]  # [position] -> currently dormant (don't-care)
        dormancyBindings*: seq[tuple[dormantPos: int, selectorPos: int, activeValue: int]]
        dormancyAtSelector*: Table[int, seq[int]]  # selector_pos -> [binding indices]

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
            cdWorklistTime*: float   # time in worklist propagation
            cdPenaltyTime*: float    # time in penalty computation
            cdTargetedPos*: int64
            cdFullPos*: int64
            cdNonOneHotPos*: int64
            cdMovedCalls*: int64
            affectedPosSkipped*: int64
            neighborByType*: array[StatefulConstraintType, int64]
            neighborTimeByType*: array[StatefulConstraintType, float]
            timePropagateChannels*: float
            timeChannelDep*: float
            propagateChannelCalls*: int64
            channelChangesTotal*: int64
            propagateNeighborCalls*: int64
            cdDomainEvals*: int64
            cdWorklistEntryCalls*: int64
            cdCascadeBindingTime*: float
            cdCascadePenaltyTime*: float
            cdCascadeFallbackTime*: float
            cdCascadeCalls*: int64
            cdFastPathCalls*: int64
            cdIncCalls*: int64          # incremental cascade eval calls
            cdIncSkipped*: int64        # total entries×domvals skipped (used cached)
            cdIncEvaluated*: int64      # total entries×domvals actually evaluated
            cdUniformCalls*: int64


# Forward declarations
proc assignValue*[T](state: TabuState[T], position: int, value: T)
proc assignValueLean*[T](state: TabuState[T], position: int, value: T)
proc costDelta*[T](state: TabuState[T], position: int, newValue: T): int
proc movePenalty*[T](state: TabuState[T], constraint: StatefulConstraint[T], position: int, newValue: T): int {.inline.}
proc findLocalConstraintIdx[T](state: TabuState[T], position: int, constraint: StatefulConstraint[T]): int {.inline.}
proc updatePenaltiesForPosition[T](state: TabuState[T], position: int)
proc updateNeighborPenalties*[T](state: TabuState[T], position: int)

################################################################################
# Penalty Routines
################################################################################

# Note: movePenalty must be defined before the included subsystem files,
# since tabuInverseMoves and tabuChannelDep call it.

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
        of DiffnKType:
            result = constraint.diffnKState.moveDelta(position, oldValue, newValue)
        of MatrixElementType:
            result = constraint.matrixElementState.moveDelta(position, oldValue, newValue)
        of NoOverlapFixedBoxType:
            result = constraint.noOverlapFixedBoxState.moveDelta(position, oldValue, newValue)
        of ConnectedType:
            result = constraint.connectedState.moveDelta(position, oldValue, newValue)
        of ConditionalCumulativeType:
            result = constraint.conditionalCumulativeState.moveDelta(position, oldValue, newValue)
        of ConditionalNoOverlapPairType:
            result = constraint.conditionalNoOverlapPairState.moveDelta(position, oldValue, newValue)
        of ConditionalDayCapacityType:
            result = constraint.conditionalDayCapacityState.moveDelta(position, oldValue, newValue)
    when ProfileMoveDelta:
        let elapsed = cpuTime() - startT
        state.profileByType[constraint.stateType].calls += 1
        state.profileByType[constraint.stateType].totalTime += elapsed

################################################################################
# Included subsystems
################################################################################

include tabuInverseMoves
include tabuChannelDep
include tabuElementImplied
include tabuSwapMoves
include tabuFlowMoves

################################################################################
# Dense Array Penalty Lookup
################################################################################

proc penaltyAt*[T](state: TabuState[T], position: int, value: T): int {.inline.} =
    ## Look up penalty for a (position, value) pair using dense arrays.
    if state.isLazy[position]:
        return state.costDelta(position, value)
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

proc batchCostDelta[T](state: TabuState[T], position: int): (int, T, int) =
    ## Batch-compute cost delta for all domain values at a lazy position.
    ## Returns (bestCostDelta, bestValue, movesEvaluated).
    ## Uses batchMovePenalty for constraint types that support it.
    let domain = state.sharedDomain[][position]
    let dLen = domain.len
    let oldValue = state.assignment[position]

    var penalties = newSeq[int](dLen)

    for constraint in state.constraintsAtPosition[position]:
        if constraint.stateType == CumulativeType and
           (constraint.cumulativeState.evalMethod == PositionBased or
            (constraint.cumulativeState.evalMethod == ExpressionBased and
             position in constraint.cumulativeState.expressionsAtPosition)):
            let p = constraint.cumulativeState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == RelationalType:
            let p = constraint.relationalState.batchMovePenalty(
                position, oldValue, domain, state.assignment)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == MatrixElementType:
            let p = constraint.matrixElementState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == TableConstraintType:
            let p = constraint.tableConstraintState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == DiffnType:
            let p = constraint.diffnState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == DiffnKType:
            let p = constraint.diffnKState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == ConditionalDayCapacityType:
            let p = constraint.conditionalDayCapacityState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        else:
            for i in 0..<dLen:
                if domain[i] != oldValue:
                    penalties[i] += state.movePenalty(constraint, position, domain[i])

    # Find minimum (excluding current value)
    var bestDelta = high(int)
    var bestVal = oldValue
    var evaluated = 0
    for i in 0..<dLen:
        if domain[i] == oldValue: continue
        inc evaluated
        if penalties[i] < bestDelta:
            bestDelta = penalties[i]
            bestVal = domain[i]

    return (bestDelta, bestVal, evaluated)

################################################################################
# Penalty Map Routines
################################################################################

proc updatePenaltiesForPosition[T](state: TabuState[T], position: int) =
    ## Full rebuild of penalty map at position, including per-constraint cache.
    ## Uses batch computation for cumulative constraints (prefix-sum approach).
    if state.isLazy[position]: return
    if state.hasDormancy and state.isDormant[position]: return
    let domain = state.sharedDomain[][position]
    let dLen = domain.len
    if dLen == 0: return

    # Zero out penalty map
    for i in 0..<dLen:
        state.penaltyMap[position][i] = 0

    for ci, constraint in state.constraintsAtPosition[position]:
        if constraint.stateType == CumulativeType and
           (constraint.cumulativeState.evalMethod == PositionBased or
            (constraint.cumulativeState.evalMethod == ExpressionBased and
             position in constraint.cumulativeState.expressionsAtPosition)):
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
        elif constraint.stateType == DiffnKType:
            let penalties = constraint.diffnKState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == ConditionalDayCapacityType:
            let penalties = constraint.conditionalDayCapacityState.batchMovePenalty(
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
    if state.isLazy[position]: return
    let constraint = state.constraintsAtPosition[position][localIdx]
    let domain = state.sharedDomain[][position]

    if constraint.stateType == CumulativeType and
       (constraint.cumulativeState.evalMethod == PositionBased or
        (constraint.cumulativeState.evalMethod == ExpressionBased and
         position in constraint.cumulativeState.expressionsAtPosition and
         # Multi-task batch temporarily mutates the resource profile, which isn't
         # safe during single-constraint partial updates — restrict to single-task.
         constraint.cumulativeState.expressionsAtPosition[position].len == 1)):
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
    elif constraint.stateType == DiffnKType:
        let penalties = constraint.diffnKState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == ConditionalDayCapacityType:
        let penalties = constraint.conditionalDayCapacityState.batchMovePenalty(
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
    if state.isLazy[position]: return
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
        when ProfileIteration:
            let tNeighC = epochTime()
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
                    if state.isLazy[pos]:
                        continue
                    # For EqualTo with PositionBased SumExpr + ConstantExpr:
                    # when leftValue changed, ALL positions in leftExpr are affected.
                    # For inequality relations, slack-based skip may reduce this set,
                    # so we still need the check for non-EqualTo.
                    if rc.relation != EqualTo and pos notin affectedPositions:
                        continue

                    let domain = state.sharedDomain[][pos]
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

                when ProfileIteration:
                    state.neighborByType[constraint.stateType] += 1
                    state.neighborTimeByType[constraint.stateType] += epochTime() - tNeighC
                continue  # Done with this constraint via broadcast

        # Standard path
        for pos in searchPos.items:
            if pos == position:
                continue
            if state.isLazy[pos]:
                continue
            if state.hasDormancy and state.isDormant[pos]:
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
        when ProfileIteration:
            state.neighborByType[constraint.stateType] += 1
            state.neighborTimeByType[constraint.stateType] += epochTime() - tNeighC


proc rebuildPenaltyMap*[T](state: TabuState[T]) =
    for position in state.carray.allSearchPositions():
        if not state.isLazy[position]:
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
            let dom = state.sharedDomain[][pos]
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

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], verbose: bool = false, id: int = 0, initialAssignment: seq[T] = @[], forRelinking: bool = false) =
    state.id = id
    state.carray = carray
    # Use shared domain pointer if available (parallel path), otherwise own copy (sequential path)
    if state.carray.sharedDomainPtr != nil:
        state.sharedDomain = state.carray.sharedDomainPtr
    else:
        state.sharedDomain = addr state.carray.reducedDomain
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
        stderr.writeLine("[Init] Neighbor init done")
        stderr.flushFile()
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
            state.assignment[pos] = state.sharedDomain[][pos][0]
        elif pos in inverseGroupPositions:
            # Inverse group positions are initialized below as involutions
            state.assignment[pos] = state.sharedDomain[][pos][0]
        else:
            state.assignment[pos] = sample(state.sharedDomain[][pos])

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
                            let domA = state.sharedDomain[][group.positions[a]]
                            let domB = state.sharedDomain[][group.positions[b]]
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
                        let domA = state.sharedDomain[][group.positions[a]]
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

    if verbose and id == 0:
        stderr.writeLine("[Init] Assignment init done, starting channel fixed-point (" & $carray.channelBindings.len & " bindings)...")
        stderr.flushFile()

    # Compute channel variable initial values from their defining element constraints.
    # Iterate to fixed point: bindings may not be in topological order (e.g., bool2int
    # bindings for i_k are created before int_le_reif bindings for b_k that i_k depends on).
    # A single pass would leave downstream channels stale.
    var channelChanged = true
    var fpIter = 0
    # Check for duplicate channel bindings (multiple bindings targeting same position)
    if verbose and id == 0:
        var bindingsPerPos = initTable[int, seq[int]]()
        for bi, binding in carray.channelBindings:
            bindingsPerPos.mgetOrPut(binding.channelPosition, @[]).add(bi)
        var dups = 0
        for pos, indices in bindingsPerPos.pairs:
            if indices.len > 1:
                inc dups
                if dups <= 3:
                    stderr.writeLine("[Init] WARNING: position " & $pos & " has " & $indices.len & " element channel bindings (indices: " & $indices & ")")
                    for bi in indices:
                        let b = carray.channelBindings[bi]
                        let nConst = block:
                            var c = 0
                            for e in b.arrayElements:
                                if e.isConstant: inc c
                            c
                        stderr.writeLine("[Init]   binding[" & $bi & "]: arrLen=" & $b.arrayElements.len &
                                         " const=" & $nConst & "/" & $b.arrayElements.len &
                                         " idxPositions=" & $b.indexExpression.positions.len)
        if dups > 3:
            stderr.writeLine("[Init] WARNING: ... and " & $(dups - 3) & " more duplicate positions")
        stderr.flushFile()
    while channelChanged:
        channelChanged = false
        fpIter += 1
        for binding in carray.channelBindings:
            let idxVal = binding.indexExpression.evaluate(state.assignment)
            if idxVal >= 0 and idxVal < binding.arrayElements.len:
                let elem = binding.arrayElements[idxVal]
                let newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition]
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    channelChanged = true
        if fpIter > 20:
            if verbose and id == 0:
                stderr.writeLine("[Init] WARNING: channel fixed-point exceeded 20 iterations, breaking")
                # Report which positions are still changing
                var changingPos: seq[int]
                for binding in carray.channelBindings:
                    let idxVal = binding.indexExpression.evaluate(state.assignment)
                    if idxVal >= 0 and idxVal < binding.arrayElements.len:
                        let elem = binding.arrayElements[idxVal]
                        let newVal = if elem.isConstant: elem.constantValue
                                     else: state.assignment[elem.variablePosition]
                        if newVal != state.assignment[binding.channelPosition]:
                            changingPos.add(binding.channelPosition)
                stderr.writeLine("[Init]   Still-changing positions: " & $changingPos[0..min(9, changingPos.len-1)])
                stderr.flushFile()
            break

    if verbose and id == 0:
        stderr.writeLine("[Init] Channel fixed-point done in " & $fpIter & " iterations")
        stderr.flushFile()

    # Compute count-equals channel initial values
    for binding in carray.countEqChannelBindings:
        state.assignment[binding.channelPosition] = evaluateCountEq(binding, state.assignment)

    # Compute inverse channel initial values from forward assignments
    for group in carray.inverseChannelGroups:
        let newInverse = group.recomputeInverse(state.assignment)
        for j, ipos in group.inversePositions:
            state.assignment[ipos] = newInverse[j]

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

        # Build reverse index: position → binding indices that use this position as input
        var posToBindings = initTable[int, seq[int]]()
        for bi, fb in state.flatMinMaxBindings:
            for j in 0..<fb.linearPositions.len:
                let pos = fb.linearPositions[j]
                if pos notin posToBindings:
                    posToBindings[pos] = @[]
                posToBindings[pos].add(bi)

        # Combined element + min/max fixed-point for multi-layer channel dependencies.
        # Element channels may read from min/max channel outputs (e.g., layer 3 element
        # channels selecting from layer 2 set comprehension results). We iterate:
        #   1. Min/max worklist until empty
        #   2. Re-evaluate element channels; if any changed, enqueue affected min/max bindings
        #   3. Repeat until stable
        var worklist: seq[int]  # indices into flatMinMaxBindings
        for i in 0..<state.flatMinMaxBindings.len:
            worklist.add(i)
        var inWorklist = newSeq[bool](state.flatMinMaxBindings.len)
        for i in 0..<inWorklist.len: inWorklist[i] = true

        var fpEvals = 0
        var combinedIter = 0
        while true:
            inc combinedIter
            if combinedIter > 50:
                if verbose and id == 0:
                    stderr.writeLine("[Init] WARNING: combined elem+minmax fixed-point exceeded 50 iterations, breaking")
                    stderr.flushFile()
                break
            # Min/max fixed-point pass
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

            # Re-evaluate element channels that may read from updated min/max channels
            var elemChanged = false
            for binding in carray.channelBindings:
                let idxVal = binding.indexExpression.evaluate(state.assignment)
                if idxVal >= 0 and idxVal < binding.arrayElements.len:
                    let elem = binding.arrayElements[idxVal]
                    let newVal = if elem.isConstant: elem.constantValue
                                 else: state.assignment[elem.variablePosition]
                    if newVal != state.assignment[binding.channelPosition]:
                        state.assignment[binding.channelPosition] = newVal
                        elemChanged = true
                        # Enqueue min/max bindings affected by this element channel change
                        if binding.channelPosition in posToBindings:
                            for downstream in posToBindings[binding.channelPosition]:
                                if not inWorklist[downstream]:
                                    inWorklist[downstream] = true
                                    worklist.add(downstream)
            if not elemChanged:
                break

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
    state.isLazy = newSeq[bool](carray.len)
    for pos in carray.allSearchPositions():
        state.searchPositions.add(pos)
        let dsize = state.sharedDomain[][pos].len
        if dsize > LazyThreshold:
            state.isLazy[pos] = true
        else:
            state.totalDomainSize += dsize

    if verbose and id == 0:
        var bin2, bin3to10, bin11to50, binLarge = 0
        for pos in state.searchPositions:
            let d = state.sharedDomain[][pos].len
            if d <= 2: bin2 += 1
            elif d <= 10: bin3to10 += 1
            elif d <= 50: bin11to50 += 1
            else: binLarge += 1
        echo "[Init] Search positions by domain: d<=2: " & $bin2 & " d<=10: " & $bin3to10 &
             " d<=50: " & $bin11to50 & " d>50: " & $binLarge

    # Initialize dormancy support
    state.isDormant = newSeq[bool](carray.len)
    state.hasDormancy = carray.dormancyBindings.len > 0
    if state.hasDormancy:
        for bi, binding in carray.dormancyBindings:
            state.dormancyBindings.add((dormantPos: binding.dormantPos,
                                        selectorPos: binding.selectorPos,
                                        activeValue: binding.activeValue))
        state.dormancyAtSelector = carray.dormancyAtSelector
        # Set initial dormancy based on current assignment
        var dormantCount = 0
        for bi, binding in state.dormancyBindings:
            if state.assignment[binding.selectorPos] != binding.activeValue:
                state.isDormant[binding.dormantPos] = true
                dormantCount += 1
        if verbose and id == 0:
            echo "[Init] Dormant positions: " & $dormantCount & "/" &
                 $(dormantCount + state.searchPositions.len) & " search positions dormant"

    # Precompute search-only positions per constraint (excluding channels)
    state.constraintSearchPos = initTable[pointer, PackedSet[int]]()
    for c in state.constraints:
        var searchPos: PackedSet[int]
        for pos in c.positions.items:
            if pos notin carray.channelPositions and pos notin carray.fixedPositions:
                searchPos.incl(pos)
        state.constraintSearchPos[cast[pointer](c)] = searchPos

    if verbose and id == 0:
        stderr.writeLine("[Init] Starting channel-dep identification...")
        flushFile(stderr)

    # Identify channel-dep constraints:
    # 1. Pure-channel constraints (all positions are channels)
    # 2. Mixed constraints (some search, some channel) — needed for constraints
    #    where channel positions carry cost information (e.g., cumulative, element)
    state.hasChannelDeps = false
    state.channelDepConstraints = @[]
    state.channelDepSearchPositions = @[]
    for c in state.constraints:
        let cptr = cast[pointer](c)
        let searchPos = state.constraintSearchPos.getOrDefault(cptr)
        if searchPos.len == 0:
            state.channelDepConstraints.add(c)
        else:
            for p in c.positions.items:
                if p in carray.channelPositions:
                    state.channelDepConstraints.add(c)
                    break
    state.channelDepConstraintActive = newSeq[bool](state.channelDepConstraints.len)
    for i in 0..<state.channelDepConstraintActive.len:
        state.channelDepConstraintActive[i] = true
    if state.channelDepConstraints.len > 0:
        state.hasChannelDeps = true
        # Find search positions that have channel bindings (can affect channel-dep constraints)
        for pos in state.searchPositions:
            if pos in carray.channelsAtPosition or pos in carray.minMaxChannelsAtPosition or
               pos in carray.countEqChannelsAtPosition or pos in carray.inverseChannelsAtPosition:
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
                        let chanPos = carray.channelBindings[bi].channelPosition
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
                # Count-equals channel bindings
                if p in carray.countEqChannelsAtPosition:
                    for bi in carray.countEqChannelsAtPosition[p]:
                        let binding = carray.countEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Inverse channel bindings
                if p in carray.inverseChannelsAtPosition:
                    for gi in carray.inverseChannelsAtPosition[p]:
                        let group = carray.inverseChannelGroups[gi]
                        for ipos in group.inversePositions:
                            reachable.incl(ipos)
                            if ipos notin visited:
                                visited.incl(ipos)
                                worklist.add(ipos)
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
                let bindingPtr = addr carray.channelBindings[bi]  # addr avoids value copy under ARC
                # Verify this binding uses the same index expression (same lo) as the first
                let bNode = bindingPtr.indexExpression.node
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
                if bindingPtr.arrayElements.len != arrayLen:
                    isOneHot = false
                    break
                var oneCount = 0
                var zeroCount = 0
                var firstOneIdx = -1
                var firstZeroIdx = -1
                var valid = true
                for j, elem in bindingPtr.arrayElements:
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
                    changesByIdx[firstOneIdx].add((bindingPtr.channelPosition, 1))
                elif zeroCount == 1 and oneCount == arrayLen - 1:
                    # Inverted one-hot: when source == (key+lo), channel = 0
                    changesByIdx[firstZeroIdx].add((bindingPtr.channelPosition, 0))
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
    let domIdxStart = epochTime()
    state.domainIndex = newSeq[Table[T, int]](carray.len)
    for pos in carray.allPositions():
        if state.isLazy[pos]:
            continue  # Lazy positions don't need domainIndex (use linear scan or direct computation)
        state.domainIndex[pos] = initTable[T, int]()
        for i, v in state.sharedDomain[][pos]:
            state.domainIndex[pos][v] = i
    if verbose and id == 0:
        echo "[Init] Built domainIndex in " & $(epochTime() - domIdxStart) & "s"

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

        # Initialize position-indexed simulation arrays for computeChannelDepDelta
        state.cdIsChanged = newSeq[bool](carray.len)
        state.cdSavedVal = newSeq[T](carray.len)
        state.cdDirtyPositions = @[]

        # Precompute flat coefficient lists for each channel-dep constraint
        let nCd = state.channelDepConstraints.len
        state.cdConstraintCoeffs = newSeq[seq[tuple[pos: int, coeff: T]]](nCd)
        state.cdConstraintCoeffsR = newSeq[seq[tuple[pos: int, coeff: T]]](nCd)
        state.cdConstraintCanFast = newSeq[bool](nCd)
        state.cdSavedConstraintCosts = newSeq[int](nCd)
        for ci in 0..<nCd:
            let c = state.channelDepConstraints[ci]
            if c.stateType != RelationalType:
                state.cdConstraintCanFast[ci] = false
                continue
            let rc = c.relationalState
            var canFast = true

            # Extract left side coefficients
            case rc.leftExpr.kind
            of SumExpr:
                if rc.leftExpr.sumExpr.evalMethod == PositionBased:
                    for pos, coeff in rc.leftExpr.sumExpr.coefficient.pairs:
                        state.cdConstraintCoeffs[ci].add((pos: pos, coeff: coeff))
                else: canFast = false
            of ConstantExpr: discard  # No coefficients needed
            else: canFast = false

            if canFast:
                # Extract right side coefficients
                case rc.rightExpr.kind
                of SumExpr:
                    if rc.rightExpr.sumExpr.evalMethod == PositionBased:
                        for pos, coeff in rc.rightExpr.sumExpr.coefficient.pairs:
                            state.cdConstraintCoeffsR[ci].add((pos: pos, coeff: coeff))
                    else: canFast = false
                of ConstantExpr: discard
                else: canFast = false

            state.cdConstraintCanFast[ci] = canFast

        if verbose and id == 0:
            var fastCount, fallbackCount = 0
            var maxCoeffs, totalCoeffs = 0
            for ci in 0..<nCd:
                if state.cdConstraintCanFast[ci]: fastCount += 1
                else: fallbackCount += 1
                let n = state.cdConstraintCoeffs[ci].len + state.cdConstraintCoeffsR[ci].len
                totalCoeffs += n
                if n > maxCoeffs: maxCoeffs = n
            echo "[Init] Channel-dep fast path: " & $fastCount & "/" & $nCd &
                 " constraints (fallback=" & $fallbackCount &
                 ", avg_coeffs=" & $(totalCoeffs div max(1, fastCount)) &
                 " max_coeffs=" & $maxCoeffs & ")"

    # Build level-2 reverse index for targeted channel-dep recomputation
    if not forRelinking and state.hasChannelDeps and state.oneHotChanges.len > 0:
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

    if verbose and id == 0:
        stderr.writeLine("[Init] Starting cascade topology build...")
        flushFile(stderr)

    # Build cascade topologies for channel-dep search positions.
    # For ALL element-only positions (no minMax/inverse), store the channel topology.
    # For positions with constant arrays, also precompute values (static cascade).
    # Dynamic positions evaluate at runtime using the stored topology (batch evaluation).
    # This eliminates per-domain-value worklist overhead for ALL covered positions.
    if not forRelinking and state.hasChannelDeps:
        state.cdCascadePos = initTable[int, int]()
        state.cdCascadeChans = @[]
        state.cdCascadeBindings = @[]
        state.cdCascadeIsMinMax = @[]
        state.cdCascadeExternalDeps = @[]
        state.cdCascadeElemExtDeps = @[]
        state.cdCascadeMinMaxIdx = @[]
        state.cdCascadeCachedValues = @[]
        state.cdCascadeMinMaxInputs = @[]
        state.cdCascadeValues = @[]
        state.cdCascadeIsStatic = @[]
        state.cdCascadeConstraintL = @[]
        state.cdCascadeConstraintR = @[]
        state.cdCascadeConstraintIds = @[]
        let cascadeStart = epochTime()
        var staticCount = 0
        var dynamicCount = 0
        var cascadeFail = 0

        for pos in state.channelDepSearchPositions:
            if state.isLazy[pos]: continue
            # Skip positions with inverse groups (forced changes not captured by cascade)
            if state.inverseEnabled and state.posToInverseGroup[pos] >= 0: continue

            # Walk topology from this position using BFS (FIFO queue) for correct
            # topological ordering. BFS ensures parents are visited before children,
            # which handles diamond patterns (multiple paths to same channel) correctly.
            var topoOrder: seq[int] = @[]
            var topoBindingIdx: seq[int] = @[]
            var topoIsMinMax: seq[bool] = @[]
            var topoSet: PackedSet[int]
            var bfsQueue: seq[int] = @[pos]
            var bfsHead = 0
            var visited: PackedSet[int]
            visited.incl(pos)
            var canBuild = true       # can build topology at all
            var canStatic = true      # can precompute values (constant arrays + local index deps)

            while bfsHead < bfsQueue.len and canBuild:
                let p = bfsQueue[bfsHead]
                inc bfsHead
                if p in carray.channelsAtPosition:
                    for bi in carray.channelsAtPosition[p]:
                        let bindingPtr = addr carray.channelBindings[bi]
                        let chanPos = bindingPtr.channelPosition
                        if chanPos in topoSet:
                            # Diamond pattern — channel already in cascade, skip
                            continue
                        # Check static eligibility
                        if canStatic:
                            for ipos in bindingPtr.indexExpression.positions.items:
                                if ipos != pos and ipos notin topoSet:
                                    canStatic = false
                                    break
                            for elem in bindingPtr.arrayElements:
                                if not elem.isConstant:
                                    canStatic = false
                                    break
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)
                        topoIsMinMax.add(false)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # Min/max channel bindings: include in cascade as dynamic entries
                if p in carray.minMaxChannelsAtPosition:
                    for bi in carray.minMaxChannelsAtPosition[p]:
                        let fb = state.flatMinMaxBindings[bi]
                        let chanPos = fb.channelPosition
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false  # min/max depends on non-local positions
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)  # index into flatMinMaxBindings
                        topoIsMinMax.add(true)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # countEq/inverse channels can't be batched — reject topology entirely
                if p in carray.countEqChannelsAtPosition:
                    canBuild = false
                if p in carray.inverseChannelsAtPosition:
                    canBuild = false

            if not canBuild or topoOrder.len == 0:
                cascadeFail += 1
                continue

            # Build channel values
            let domain = state.sharedDomain[][pos]
            let nChans = topoOrder.len
            let nDom = domain.len
            var chanValues: seq[seq[T]]

            if canStatic:
                # Precompute values for all domain entries (constant arrays only)
                chanValues = newSeq[seq[T]](nChans)
                for ci in 0..<nChans:
                    chanValues[ci] = newSeq[T](nDom)

                let savedPos = state.assignment[pos]
                var savedChans = newSeq[T](nChans)
                for ci in 0..<nChans:
                    savedChans[ci] = state.assignment[topoOrder[ci]]

                for di in 0..<nDom:
                    state.assignment[pos] = domain[di]
                    for ci in 0..<nChans:
                        let bindingPtr = addr carray.channelBindings[topoBindingIdx[ci]]
                        let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                        if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                            chanValues[ci][di] = bindingPtr.arrayElements[idxVal].constantValue
                        else:
                            chanValues[ci][di] = savedChans[ci]
                        state.assignment[topoOrder[ci]] = chanValues[ci][di]

                state.assignment[pos] = savedPos
                for ci in 0..<nChans:
                    state.assignment[topoOrder[ci]] = savedChans[ci]
                staticCount += 1
            else:
                # Dynamic — values computed at runtime via batch evaluation
                chanValues = @[]  # empty signals dynamic
                dynamicCount += 1

            # Map channel position -> index in topoOrder (for constraint coefficient mapping)
            var chanToIdx = initTable[int, int]()
            for ci, cp in topoOrder:
                chanToIdx[cp] = ci

            # Build per-constraint coefficient mapping into cascade channels
            var constraintLocalIds: seq[int] = @[]
            var constraintCoeffL: seq[seq[tuple[cascadeIdx: int, coeff: T]]] = @[]
            var constraintCoeffR: seq[seq[tuple[cascadeIdx: int, coeff: T]]] = @[]

            var seenCi: PackedSet[int]
            for chanPos in topoOrder:
                if chanPos in state.chanPosToDepConstraintIdx:
                    for ci in state.chanPosToDepConstraintIdx[chanPos]:
                        if ci notin seenCi:
                            seenCi.incl(ci)
                            if not state.channelDepConstraintActive[ci]: continue
                            constraintLocalIds.add(ci)
                            var coeffsL: seq[tuple[cascadeIdx: int, coeff: T]] = @[]
                            var coeffsR: seq[tuple[cascadeIdx: int, coeff: T]] = @[]
                            if state.cdConstraintCanFast[ci]:
                                for (cpos, coeff) in state.cdConstraintCoeffs[ci]:
                                    if cpos in chanToIdx:
                                        coeffsL.add((cascadeIdx: chanToIdx[cpos], coeff: coeff))
                                for (cpos, coeff) in state.cdConstraintCoeffsR[ci]:
                                    if cpos in chanToIdx:
                                        coeffsR.add((cascadeIdx: chanToIdx[cpos], coeff: coeff))
                            constraintCoeffL.add(coeffsL)
                            constraintCoeffR.add(coeffsR)

            # Compute external dependencies: positions read by cascade entries that
            # are outside the cascade. Separate element vs min/max deps to allow
            # fast-path when only min/max deps changed (skip element re-evaluation).
            var externalDeps: PackedSet[int]
            var elemExtDeps: PackedSet[int]
            var minMaxIndices: seq[int]
            for ci in 0..<topoOrder.len:
                if topoIsMinMax[ci]:
                    minMaxIndices.add(ci)
                    let fb = state.flatMinMaxBindings[topoBindingIdx[ci]]
                    for j in 0..<fb.linearPositions.len:
                        let lp = fb.linearPositions[j]
                        if lp != pos and lp notin topoSet:
                            externalDeps.incl(lp)
                    for expr in fb.complexExprs:
                        for ep in expr.positions.items:
                            if ep != pos and ep notin topoSet:
                                externalDeps.incl(ep)
                else:
                    let bindingPtr = addr carray.channelBindings[topoBindingIdx[ci]]
                    for ipos in bindingPtr.indexExpression.positions.items:
                        if ipos != pos and ipos notin topoSet:
                            externalDeps.incl(ipos)
                            elemExtDeps.incl(ipos)
                    for elem in bindingPtr.arrayElements:
                        if not elem.isConstant:
                            if elem.variablePosition != pos and elem.variablePosition notin topoSet:
                                externalDeps.incl(elem.variablePosition)
                                elemExtDeps.incl(elem.variablePosition)

            let cascadeIdx = state.cdCascadeChans.len
            state.cdCascadePos[pos] = cascadeIdx
            state.cdCascadeChans.add(topoOrder)
            state.cdCascadeBindings.add(topoBindingIdx)
            state.cdCascadeIsMinMax.add(topoIsMinMax)
            state.cdCascadeExternalDeps.add(externalDeps)
            state.cdCascadeElemExtDeps.add(elemExtDeps)
            state.cdCascadeMinMaxIdx.add(minMaxIndices)
            # Precompute min/max input mapping: which linearPositions are cascade positions
            var mmInputs: seq[seq[tuple[linearIdx: int, topoIdx: int]]]
            for mmIdx in minMaxIndices:
                let fb = state.flatMinMaxBindings[topoBindingIdx[mmIdx]]
                var inputs: seq[tuple[linearIdx: int, topoIdx: int]]
                for j in 0..<fb.linearPositions.len:
                    let lp = fb.linearPositions[j]
                    if lp in chanToIdx:
                        inputs.add((linearIdx: j, topoIdx: chanToIdx[lp]))
                mmInputs.add(inputs)
            state.cdCascadeMinMaxInputs.add(mmInputs)
            # Precompute per-entry inputs and forward deps for incremental cascade eval
            # entryInputs[ci] = set of positions entry ci reads from (excluding pos itself)
            var posToReaders = initTable[int, seq[int]]()  # cascade pos -> entry indices that read it
            var extPosToEntries = initTable[int, seq[int]]()  # external pos -> entry indices
            for ci in 0..<topoOrder.len:
                var inputs: PackedSet[int]
                if topoIsMinMax[ci]:
                    let fb = state.flatMinMaxBindings[topoBindingIdx[ci]]
                    for lp in fb.linearPositions:
                        if lp != pos: inputs.incl(lp)
                    for expr in fb.complexExprs:
                        for ep in expr.positions.items:
                            if ep != pos: inputs.incl(ep)
                else:
                    let bindingPtr = addr carray.channelBindings[topoBindingIdx[ci]]
                    for ipos in bindingPtr.indexExpression.positions.items:
                        if ipos != pos: inputs.incl(ipos)
                    for elem in bindingPtr.arrayElements:
                        if not elem.isConstant and elem.variablePosition != pos:
                            inputs.incl(elem.variablePosition)
                # Register in posToReaders (cascade-internal deps) and extPosToEntries
                for p in inputs.items:
                    if p in topoSet:
                        posToReaders.mgetOrPut(p, @[]).add(ci)
                    else:
                        extPosToEntries.mgetOrPut(p, @[]).add(ci)
            # Build forward deps: from entry ci to entries that read chans[ci]
            var forwardDeps = newSeq[seq[int]](topoOrder.len)
            for ci in 0..<topoOrder.len:
                if topoOrder[ci] in posToReaders:
                    forwardDeps[ci] = posToReaders[topoOrder[ci]]
            state.cdCascadeForwardDeps.add(forwardDeps)
            state.cdCascadeExtPosToEntries.add(extPosToEntries)
            # Allocate cache for this cascade
            state.cdCascadeCachedValues.add(newSeq[seq[T]](topoOrder.len))
            for ci in 0..<topoOrder.len:
                state.cdCascadeCachedValues[^1][ci] = newSeq[T](domain.len)
            state.cdCascadeValues.add(chanValues)
            state.cdCascadeIsStatic.add(canStatic)
            state.cdCascadeConstraintIds.add(constraintLocalIds)
            state.cdCascadeConstraintL.add(constraintCoeffL)
            state.cdCascadeConstraintR.add(constraintCoeffR)

        # Allocate reusable batch evaluation buffers (sized to max cascade)
        if state.cdCascadeChans.len > 0:
            var maxChans = 0
            var maxDom = 0
            for ci in 0..<state.cdCascadeChans.len:
                maxChans = max(maxChans, state.cdCascadeChans[ci].len)
            for pos in state.channelDepSearchPositions:
                maxDom = max(maxDom, state.sharedDomain[][pos].len)
            state.cdBatchValues = newSeq[seq[T]](maxChans)
            for ci in 0..<maxChans:
                state.cdBatchValues[ci] = newSeq[T](maxDom)
            state.cdBatchSaved = newSeq[T](maxChans)
            # Reusable dirty tracking buffers for incremental cascade eval
            state.cdCascadeDirtyBase = newSeq[bool](maxChans)
            state.cdCascadeDirtyDV = newSeq[bool](maxChans)
            state.cdCascadeInWorkList = newSeq[bool](maxChans)
            state.cdCascadeWorkList = newSeq[int](maxChans)  # worst case: all entries in work list

        if verbose and id == 0:
            var totalChans, totalMem = 0
            var elemExtCount, mmExtCount, noExtCount = 0
            for ci in 0..<state.cdCascadeChans.len:
                totalChans += state.cdCascadeChans[ci].len
                for v in state.cdCascadeValues[ci]:
                    totalMem += v.len * sizeof(T)
                if state.cdCascadeElemExtDeps[ci].len > 0: inc elemExtCount
                elif state.cdCascadeExternalDeps[ci].len > 0: inc mmExtCount
                else: inc noExtCount
            echo "[Init] Cascade tables: " & $staticCount & " static + " & $dynamicCount &
                 " dynamic / " & $(staticCount + dynamicCount + cascadeFail) &
                 " positions (fail=" & $cascadeFail &
                 " avg_chans=" & $(totalChans div max(1, staticCount + dynamicCount)) &
                 " mem=" & $(totalMem div 1024) & "KB" &
                 " extDeps: elemExt=" & $elemExtCount & " mmOnlyExt=" & $mmExtCount &
                 " noExt=" & $noExtCount &
                 " built in " & $(epochTime() - cascadeStart) & "s)"
            # Distribution of cascade sizes and constraint counts
            var sizeHist: Table[int, int]
            var constraintHist: Table[int, int]
            var maxConstraints = 0
            var maxChansPos = -1
            var maxChansCnt = 0
            for ci in 0..<state.cdCascadeChans.len:
                let nch = state.cdCascadeChans[ci].len
                sizeHist.mgetOrPut(nch, 0) += 1
                let nco = state.cdCascadeConstraintIds[ci].len
                constraintHist.mgetOrPut(nco, 0) += 1
                if nch > maxChansCnt:
                    maxChansCnt = nch
                    # find the pos
                    for p, idx in state.cdCascadePos.pairs:
                        if idx == ci: maxChansPos = p; break
                if nco > maxConstraints: maxConstraints = nco
            echo "[Init] Cascade size distribution:"
            var sizes: seq[int]
            for s in sizeHist.keys: sizes.add(s)
            algorithm.sort(sizes)
            for s in sizes:
                echo "[Init]   " & $s & " chans: " & $sizeHist[s] & " cascades"
            echo "[Init] Max cascade: " & $maxChansCnt & " chans at pos " & $maxChansPos &
                 " max_constraints=" & $maxConstraints

    # Skip penalty maps, channel-dep penalties, and element implied structures for relinking
    if forRelinking:
        # Minimal structures needed for costDelta/assignValueLean
        state.initSwapStructures()
        state.initFlowStructure()
        state.initInverseStructures()
        return

    if verbose and id == 0:
        stderr.writeLine("[Init] Cascade topology done, initializing penalty arrays...")
        flushFile(stderr)

    # Initialize dense penalty arrays — only for search positions (not channels)
    state.penaltyMap = newSeq[seq[int]](carray.len)
    state.constraintPenalties = newSeq[seq[seq[int]]](carray.len)
    state.tabu = newSeq[seq[int]](carray.len)
    state.channelDepPenalties = newSeq[seq[int]](carray.len)
    for pos in carray.allPositions():
        if pos in carray.channelPositions:
            continue
        let dsize = state.sharedDomain[][pos].len
        if state.isLazy[pos]:
            continue  # Skip all dense arrays for lazy positions (including tabu)
        state.tabu[pos] = newSeq[int](dsize)
        state.penaltyMap[pos] = newSeq[int](dsize)
        state.constraintPenalties[pos] = newSeq[seq[int]](state.constraintsAtPosition[pos].len)
        for ci in 0..<state.constraintsAtPosition[pos].len:
            state.constraintPenalties[pos][ci] = newSeq[int](dsize)
        if state.hasChannelDeps:
            state.channelDepPenalties[pos] = newSeq[int](dsize)

    # Compute initial channel-dep penalties (before penalty map build)
    state.cdInUse = false
    if state.hasChannelDeps:
        # Enable per-constraint delta tracking during initialization
        state.cdTrackPerConstraint = true
        state.cdPerConstraintMaxDelta = newSeq[int](state.channelDepConstraints.len)

        let cdStart = epochTime()
        var cdBinaryCount = 0
        var cdLargeCount = 0
        var cdTotalEvals = 0
        for pos in state.channelDepSearchPositions:
            if state.isLazy[pos]: continue
            let dlen = state.sharedDomain[][pos].len
            cdTotalEvals += dlen
            if dlen <= 2: cdBinaryCount += 1
            else: cdLargeCount += 1
            state.computeChannelDepPenaltiesAt(pos)

        state.cdTrackPerConstraint = false
        if verbose and id == 0:
            echo "[Init] Channel-dep penalties computed in " & $(epochTime() - cdStart) & "s" &
                 " (binary=" & $cdBinaryCount & " large=" & $cdLargeCount & " totalEvals=" & $cdTotalEvals & ")"

        # Check if all channel-dep penalties are zero (tautological constraints).
        block tautologyCheck:
            for pos in state.channelDepSearchPositions:
                if state.isLazy[pos]: continue
                for i in 0..<state.sharedDomain[][pos].len:
                    if state.channelDepPenalties[pos][i] != 0:
                        break tautologyCheck
            # All zero — disable channel-dep overhead entirely
            if verbose and id == 0:
                echo "[Init] All channel-dep penalties are zero — disabling (tautological constraints)"
            state.hasChannelDeps = false

        # Per-constraint tautological filtering: disable constraints that never
        # contributed non-zero delta across ALL (position, domainValue) evaluations.
        # Unlike checking penalty()==0 (which only reflects the current state),
        # this verifies that NO possible move could violate the constraint.
        if state.hasChannelDeps:
            var tautCount = 0
            for ci in 0..<state.channelDepConstraints.len:
                if state.cdPerConstraintMaxDelta[ci] == 0:
                    state.channelDepConstraintActive[ci] = false
                    tautCount += 1
            if tautCount > 0:
                if verbose and id == 0:
                    echo "[Init] Disabled " & $tautCount & "/" & $state.channelDepConstraints.len &
                         " tautological channel-dep constraints (zero delta across all moves)"
                    var tautByType, activeByType: array[StatefulConstraintType, int]
                    for ci in 0..<state.channelDepConstraints.len:
                        let ct = state.channelDepConstraints[ci].stateType
                        if state.channelDepConstraintActive[ci]:
                            activeByType[ct] += 1
                        else:
                            tautByType[ct] += 1
                    for ct in StatefulConstraintType:
                        if tautByType[ct] > 0 or activeByType[ct] > 0:
                            echo "[Init]   " & $ct & ": active=" & $activeByType[ct] & " taut=" & $tautByType[ct]
                if tautCount == state.channelDepConstraints.len:
                    state.hasChannelDeps = false

    # Initialize element implied structures before penalty map so discounts are included
    state.initElementImpliedStructures()
    state.recomputeElementImpliedDiscounts()

    if verbose and id == 0:
        var typeCounts: array[StatefulConstraintType, int]
        var typeMaxPos: array[StatefulConstraintType, int]
        for c in state.constraints:
            typeCounts[c.stateType] += 1
            if c.positions.len > typeMaxPos[c.stateType]:
                typeMaxPos[c.stateType] = c.positions.len
        var typePenalty: array[StatefulConstraintType, int]
        for c in state.constraints:
            if c.penalty() > 0:
                typePenalty[c.stateType] += c.penalty()
        echo "[Init] Constraint type counts (violated cost):"
        for ct in StatefulConstraintType:
            if typeCounts[ct] > 0:
                echo "  " & $ct & ": " & $typeCounts[ct] & " (max_pos=" & $typeMaxPos[ct] & " violated_cost=" & $typePenalty[ct] & ")"
        let searchCount = state.searchPositions.len
        var lazyCount = 0
        for pos in state.searchPositions:
            if state.isLazy[pos]: lazyCount += 1
        if lazyCount > 0:
            echo "[Init] Lazy penalty positions: " & $lazyCount & "/" & $searchCount &
                 " (domain > " & $LazyThreshold & ", using on-demand costDelta)"
        echo "[Init] Building penalty map: " & $(searchCount - lazyCount) & " mapped positions (skipping " & $(carray.len - searchCount) & " channels, " & $lazyCount & " lazy)"

    var penaltyStart = epochTime()
    var penaltyCount = 0
    for pos in carray.allSearchPositions():
        if state.isLazy[pos]: continue
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

    # Initialize GCC group positions for GCC-preserving swaps
    state.gccGroupPositions = @[]
    for constraint in state.constraints:
        if constraint.stateType == GlobalCardinalityType:
            let gcc = constraint.globalCardinalityState
            if gcc.evalMethod == PositionBased:
                var groupPositions: seq[int]
                for pos in gcc.positions.items:
                    if pos notin carray.channelPositions:
                        groupPositions.add(pos)
                if groupPositions.len >= 2:
                    state.gccGroupPositions.add(groupPositions)
    if state.gccGroupPositions.len > 0 and verbose and id == 0:
        echo "[Init] GCC swap groups: " & $state.gccGroupPositions.len & " groups, avg size " &
            $(state.gccGroupPositions.mapIt(it.len).foldl(a + b, 0) div state.gccGroupPositions.len)


proc newTabuState*[T](carray: ConstrainedArray[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id)

proc newTabuState*[T](carray: ConstrainedArray[T], assignment: seq[T], verbose: bool = false, id: int = 0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id, initialAssignment = assignment)

proc newRelinkState*[T](carray: ConstrainedArray[T], assignment: seq[T], id: int = 0): TabuState[T] =
    ## Create a lean TabuState for path relinking: skips penalty maps and
    ## channel-dep penalties (only costDelta/assignValueLean are needed).
    new(result)
    result.init(carray, verbose = false, id = id, initialAssignment = assignment, forRelinking = true)

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
                let bindingPtr = addr state.carray.channelBindings[bi]
                let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                var newVal: T
                if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                    let elem = bindingPtr.arrayElements[idxVal]
                    newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition]
                else:
                    continue  # out of bounds, leave as-is

                if newVal != state.assignment[bindingPtr.channelPosition]:
                    result = true
                    changedChannels.add(bindingPtr.channelPosition)
                    state.assignment[bindingPtr.channelPosition] = newVal
                    for c in state.constraintsAtPosition[bindingPtr.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(bindingPtr.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                        if oldPenalty > 0 and newPenalty == 0:
                            for pos in c.positions.items:
                                state.violationCount[pos] -= 1
                        elif oldPenalty == 0 and newPenalty > 0:
                            for pos in c.positions.items:
                                state.violationCount[pos] += 1
                    when ProfileIteration:
                        state.propagateNeighborCalls += 1
                    state.updateNeighborPenalties(bindingPtr.channelPosition)
                    if bindingPtr.channelPosition notin visited:
                        visited.incl(bindingPtr.channelPosition)
                        worklist.add(bindingPtr.channelPosition)
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
                    when ProfileIteration:
                        state.propagateNeighborCalls += 1
                    state.updateNeighborPenalties(fb.channelPosition)
                    if fb.channelPosition notin visited:
                        visited.incl(fb.channelPosition)
                        worklist.add(fb.channelPosition)
        # Count-equals channel bindings
        if pos in state.carray.countEqChannelsAtPosition:
            for bi in state.carray.countEqChannelsAtPosition[pos]:
                let binding = state.carray.countEqChannelBindings[bi]
                let newVal = evaluateCountEq(binding, state.assignment)
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
                    when ProfileIteration:
                        state.propagateNeighborCalls += 1
                    state.updateNeighborPenalties(binding.channelPosition)
                    if binding.channelPosition notin visited:
                        visited.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Inverse channel bindings: recompute inverse from forward assignments
        if pos in state.carray.inverseChannelsAtPosition:
            for gi in state.carray.inverseChannelsAtPosition[pos]:
                let group = state.carray.inverseChannelGroups[gi]
                let newInverse = group.recomputeInverse(state.assignment)
                for j, ipos in group.inversePositions:
                    if newInverse[j] != state.assignment[ipos]:
                        result = true
                        changedChannels.add(ipos)
                        state.assignment[ipos] = newInverse[j]
                        for c in state.constraintsAtPosition[ipos]:
                            let oldPenalty = c.penalty()
                            c.updatePosition(ipos, newInverse[j])
                            let newPenalty = c.penalty()
                            state.cost += newPenalty - oldPenalty
                            if oldPenalty > 0 and newPenalty == 0:
                                for pos in c.positions.items:
                                    state.violationCount[pos] -= 1
                            elif oldPenalty == 0 and newPenalty > 0:
                                for pos in c.positions.items:
                                    state.violationCount[pos] += 1
                        when ProfileIteration:
                            state.propagateNeighborCalls += 1
                        state.updateNeighborPenalties(ipos)
                        if ipos notin visited:
                            visited.incl(ipos)
                            worklist.add(ipos)

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
                let bindingPtr = addr state.carray.channelBindings[bi]
                let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                var newVal: T
                if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                    let elem = bindingPtr.arrayElements[idxVal]
                    newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition]
                else:
                    continue
                if newVal != state.assignment[bindingPtr.channelPosition]:
                    state.assignment[bindingPtr.channelPosition] = newVal
                    for c in state.constraintsAtPosition[bindingPtr.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(bindingPtr.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if bindingPtr.channelPosition notin visited:
                        visited.incl(bindingPtr.channelPosition)
                        worklist.add(bindingPtr.channelPosition)
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
        # Count-equals channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.countEqChannelsAtPosition:
            for bi in state.carray.countEqChannelsAtPosition[pos]:
                let binding = state.carray.countEqChannelBindings[bi]
                let newVal = evaluateCountEq(binding, state.assignment)
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
        # Inverse channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.inverseChannelsAtPosition:
            for gi in state.carray.inverseChannelsAtPosition[pos]:
                let group = state.carray.inverseChannelGroups[gi]
                let newInverse = group.recomputeInverse(state.assignment)
                for j, ipos in group.inversePositions:
                    if newInverse[j] != state.assignment[ipos]:
                        state.assignment[ipos] = newInverse[j]
                        for c in state.constraintsAtPosition[ipos]:
                            let oldPenalty = c.penalty()
                            c.updatePosition(ipos, newInverse[j])
                            let newPenalty = c.penalty()
                            state.cost += newPenalty - oldPenalty
                        if ipos notin visited:
                            visited.incl(ipos)
                            worklist.add(ipos)

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

    # Save channel-dep constraint costs before propagation (for uniform delta recomputation)
    if state.hasChannelDeps:
        for ci in 0..<state.channelDepConstraints.len:
            state.cdSavedConstraintCosts[ci] = state.channelDepConstraints[ci].penalty()

    # Propagate channel variables affected by this position change
    when ProfileIteration:
        let tProp0 = epochTime()
    let channelsChanged = state.propagateChannels(position, state.changedChannelsBuf)

    # Also propagate channels for forced positions (using pre-allocated buffer)
    if hasInverseMove:
        for (fPos, fOld, fNew) in localForced:
            let forcedChanged = state.propagateChannels(fPos, state.forcedChannelsBuf2)
            if forcedChanged:
                for ch in state.forcedChannelsBuf2:
                    state.changedChannelsBuf.add(ch)

    when ProfileIteration:
        let tProp1 = epochTime()
        state.timePropagateChannels += tProp1 - tProp0
        state.propagateChannelCalls += 1
        state.channelChangesTotal += state.changedChannelsBuf.len

    let anyChannelsChanged = state.changedChannelsBuf.len > 0

    # Recompute channel-dep penalties only for affected search positions
    if state.hasChannelDeps and anyChannelsChanged:
        state.recomputeAffectedChannelDepPenalties(state.changedChannelsBuf, position)
        # Refresh moved position's channel-dep cache before updatePenaltiesForPosition reads it
        if state.channelDepPenalties[position].len > 0:
            when ProfileIteration: state.cdMovedCalls += state.sharedDomain[][position].len
            state.computeChannelDepPenaltiesAt(position)
        if hasInverseMove:
            for (fPos, fOld, fNew) in localForced:
                if state.channelDepPenalties[fPos].len > 0:
                    state.computeChannelDepPenaltiesAt(fPos)

    when ProfileIteration:
        let tCD1 = epochTime()
        state.timeChannelDep += tCD1 - tProp1
        let t1 = epochTime()
        state.timeAssignConstraints += t1 - t0

    # Recompute element implied discounts before penalty rebuild if this is an index position.
    # The discount depends on current array values (updated above via constraint.updatePosition).
    if state.elementImpliedEnabled and position in state.elementImpliedMoves:
        state.recomputeElementImpliedDiscounts()

    # Update dormancy state when a selector position changes
    var wokenPositions: seq[int]
    if state.hasDormancy and position in state.dormancyAtSelector:
        for bi in state.dormancyAtSelector[position]:
            let binding = state.dormancyBindings[bi]
            let wasActive = (oldValueAssign == binding.activeValue)
            let nowActive = (value == binding.activeValue)
            if wasActive and not nowActive:
                # Position becomes dormant (don't-care)
                state.isDormant[binding.dormantPos] = true
            elif nowActive and not wasActive:
                # Position wakes up — penalty map will be rebuilt below
                state.isDormant[binding.dormantPos] = false
                wokenPositions.add(binding.dormantPos)

    state.updatePenaltiesForPosition(position)

    # Rebuild penalty maps for positions that just woke up
    for pos in wokenPositions:
        state.updatePenaltiesForPosition(pos)

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
            let lazy1 = state.isLazy[position]
            let oldIdx = if lazy1: -1 else: state.domainIndex[position].getOrDefault(oldValue, -1)
            if not lazy1 and oldIdx < 0:
                continue

            if state.violationCount[position] == 0 and
               state.channelDepPenalties[position].len == 0:
                continue

            if state.hasDormancy and state.isDormant[position]:
                continue

            inc positionsChecked

            let domain = state.sharedDomain[][position]
            let dLen = domain.len

            # Evaluate domain values — batch for eligible lazy positions, sampling otherwise
            let hasInverse1 = state.inverseEnabled and state.posToInverseGroup[position] >= 0
            let useBatch1 = lazy1 and dLen <= BatchLazyMax and
                (not state.hasChannelDeps or state.channelDepPenalties[position].len == 0) and
                not hasInverse1

            if useBatch1:
                let (bestDelta, bestVal, nEval) = state.batchCostDelta(position)
                movesEvaluated += nEval
                let newCost = state.cost + bestDelta
                if newCost < bestMoveCost:
                    result = @[(position, bestVal)]
                    bestMoveCost = newCost
            else:
                for s in 0..<min(dLen, MAX_CANDIDATES_PER_POS):
                    let i = rand(dLen - 1)
                    if lazy1:
                        if domain[i] == oldValue: continue
                    elif i == oldIdx:
                        continue
                    inc movesEvaluated
                    var newCost: int
                    if lazy1:
                        newCost = state.cost + state.costDelta(position, domain[i])
                    else:
                        newCost = state.cost + state.penaltyMap[position][i]
                        if hasInverse1:
                            newCost += state.inverseDelta[position][i]
                    if lazy1 or state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
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
            let lazy2 = state.isLazy[position]
            let oldIdx = if lazy2: -1 else: state.domainIndex[position].getOrDefault(oldValue, -1)
            if not lazy2 and oldIdx < 0:
                continue

            if state.violationCount[position] == 0 and
               state.channelDepPenalties[position].len == 0:
                continue

            if state.hasDormancy and state.isDormant[position]:
                continue

            let domain = state.sharedDomain[][position]
            let dLen = domain.len
            let hasInverse2 = state.inverseEnabled and state.posToInverseGroup[position] >= 0
            let useBatch2 = lazy2 and dLen <= BatchLazyMax and
                (not state.hasChannelDeps or state.channelDepPenalties[position].len == 0) and
                not hasInverse2

            if useBatch2:
                let (bestDelta, bestVal, nEval) = state.batchCostDelta(position)
                movesEvaluated += nEval
                let newCost = state.cost + bestDelta
                if newCost < bestMoveCost:
                    result = @[(position, bestVal)]
                    bestMoveCost = newCost
                elif newCost == bestMoveCost:
                    result.add((position, bestVal))
            elif dLen <= MAX_CANDIDATES_PER_POS:
                for i in 0..<dLen:
                    if lazy2:
                        if domain[i] == oldValue: continue
                    elif i == oldIdx:
                        continue
                    inc movesEvaluated
                    var newCost: int
                    if lazy2:
                        newCost = state.cost + state.costDelta(position, domain[i])
                    else:
                        newCost = state.cost + state.penaltyMap[position][i]
                        if hasInverse2:
                            newCost += state.inverseDelta[position][i]
                    if lazy2 or state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                        if newCost < bestMoveCost:
                            result = @[(position, domain[i])]
                            bestMoveCost = newCost
                        elif newCost == bestMoveCost:
                            result.add((position, domain[i]))
            else:
                for s in 0..<MAX_CANDIDATES_PER_POS:
                    let i = rand(dLen - 1)
                    if lazy2:
                        if domain[i] == oldValue: continue
                    elif i == oldIdx:
                        continue
                    inc movesEvaluated
                    var newCost: int
                    if lazy2:
                        newCost = state.cost + state.costDelta(position, domain[i])
                    else:
                        newCost = state.cost + state.penaltyMap[position][i]
                        if hasInverse2:
                            newCost += state.inverseDelta[position][i]
                    if lazy2 or state.tabu[position][i] <= state.iteration or newCost < state.bestCost:
                        if newCost < bestMoveCost:
                            result = @[(position, domain[i])]
                            bestMoveCost = newCost
                        elif newCost == bestMoveCost:
                            result.add((position, domain[i]))

    state.movesExplored = movesEvaluated


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
        if state.isLazy[pos]:
            singleCost = state.cost + state.costDelta(pos, val)
        else:
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
        if not state.isLazy[p1]:
            let oldIdx1 = state.domainIndex[p1].getOrDefault(oldVal1, -1)
            if oldIdx1 >= 0:
                state.tabu[p1][oldIdx1] = tabuTenure
        if not state.isLazy[p2]:
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
        if oldIdx >= 0 and not state.isLazy[position]:
            state.tabu[position][oldIdx] = tabuTenure
        # Set tabu on forced positions' old values
        for (fPos, fOldVal) in forcedOldValues:
            let fOldIdx = state.domainIndex[fPos].getOrDefault(fOldVal, -1)
            if fOldIdx >= 0 and not state.isLazy[fPos]:
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
        echo &"[Profile S{state.id}] propagateChannels={state.timePropagateChannels:.3f}s ({state.timePropagateChannels/max(elapsed,0.001)*100:.1f}%) " &
             &"channelDep={state.timeChannelDep:.3f}s ({state.timeChannelDep/max(elapsed,0.001)*100:.1f}%) " &
             &"chanChanges={state.channelChangesTotal} ({state.channelChangesTotal.float/iters:.1f}/iter) " &
             &"propNeighborCalls={state.propagateNeighborCalls} ({state.propagateNeighborCalls.float/iters:.1f}/iter)"
        let cdEvalPerCall = if state.cdMovedCalls > 0: state.cdDomainEvals.float / state.cdMovedCalls.float else: 0.0
        echo &"[Profile S{state.id}] cdDomainEvals={state.cdDomainEvals} cdWorklistEntryCalls={state.cdWorklistEntryCalls} ({cdEvalPerCall:.1f} dirty/domainEval)"
        echo &"[Profile S{state.id}] cdWorklist={state.cdWorklistTime:.3f}s cdPenalty={state.cdPenaltyTime:.3f}s"
        echo &"[Profile S{state.id}] cdCascade: binding={state.cdCascadeBindingTime:.3f}s penalty={state.cdCascadePenaltyTime:.3f}s fallback={state.cdCascadeFallbackTime:.3f}s calls={state.cdCascadeCalls}"
        echo &"[Profile S{state.id}] cdPaths: inc={state.cdIncCalls} fastPath={state.cdFastPathCalls} uniform={state.cdUniformCalls}"
        if state.cdIncCalls > 0:
            echo &"[Profile S{state.id}] cdInc: skipped={state.cdIncSkipped} evaluated={state.cdIncEvaluated} ({state.cdIncSkipped.float/(state.cdIncSkipped.float+state.cdIncEvaluated.float)*100:.1f}% cached)"
        echo "[Profile S" & $state.id & "] Neighbor by type:"
        for ct in StatefulConstraintType:
            if state.neighborByType[ct] > 0:
                echo &"  {ct}: count={state.neighborByType[ct]} ({state.neighborByType[ct].float/iters:.1f}/iter) time={state.neighborTimeByType[ct]:.3f}s ({state.neighborTimeByType[ct]/max(elapsed,0.001)*100:.1f}%)"
    state.logProfileStats()


proc tabuImprove*[T](state: TabuState[T], threshold: int, shouldStop: ptr Atomic[bool] = nil, deadline: float = 0.0): TabuState[T] =
    var lastImprovement = 0

    # Reset timing and profiling counters for this run
    state.startTime = epochTime()
    state.lastLogTime = state.startTime
    state.lastLogIteration = 0
    when ProfileIteration:
        state.timeBestMoves = 0
        state.timeAssignConstraints = 0
        state.timeUpdatePenalties = 0
        state.timeNeighborPenalties = 0
        state.neighborUpdates = 0
        state.neighborBatchCalls = 0
        state.positionsScanned = 0
        state.affectedPosTotal = 0
        state.cdTotalCalls = 0
        state.cdWorklistTime = 0
        state.cdPenaltyTime = 0
        state.cdTargetedPos = 0
        state.cdFullPos = 0
        state.cdNonOneHotPos = 0
        state.cdMovedCalls = 0
        state.affectedPosSkipped = 0
        state.timePropagateChannels = 0
        state.timeChannelDep = 0
        state.propagateChannelCalls = 0
        state.channelChangesTotal = 0
        state.propagateNeighborCalls = 0
        state.cdDomainEvals = 0
        state.cdWorklistEntryCalls = 0
        state.cdCascadeBindingTime = 0
        state.cdCascadePenaltyTime = 0
        state.cdCascadeFallbackTime = 0
        state.cdCascadeCalls = 0
        state.cdFastPathCalls = 0
        state.cdIncCalls = 0
        state.cdIncSkipped = 0
        state.cdIncEvaluated = 0
        state.cdUniformCalls = 0
        for ct in StatefulConstraintType:
            state.neighborByType[ct] = 0
            state.neighborTimeByType[ct] = 0

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

        # Try GCC-preserving swap moves periodically during stagnation
        if state.gccGroupPositions.len > 0 and
           state.iteration - lastImprovement >= 10 and
           (state.iteration - lastImprovement) mod 10 == 0:
            if state.tryGCCSwapMoves():
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via GCC swap")
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
