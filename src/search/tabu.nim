import std/[algorithm, math, packedsets, random, sequtils, sets, strutils, tables, atomics, strformat, os]
from std/times import epochTime, cpuTime

import ../constraints/[algebraic, stateful, allDifferent, relationalConstraint, elementState, types, cumulative, geost, matrixElement, constraintNode, tableConstraint, nvalue, diffn, noOverlapFixedBox, circuit, unionCycle, involution, conditionalCumulative, conditionalNoOverlap, conditionalDayCapacity, disjunctiveClause, adjacencyEqual, valueSupport, multiResourceNoOverlap, circuitTimeProp, multiMachineNoOverlap, conditionalLinear, reservoir, setIntersectCard, conjunctSumAtMost, pseudoBoolLinLe, groupValueDisjoint, guardedCount]
import ../constrainedArray
import ../expressions/expressions

randomize()

# Logging configuration
const LogInterval* = 50000  # Log every N iterations
# Profiling switches — disabled by default. Enable at compile time with
#   -d:profileMoveDelta   → per-constraint-type moveDelta call counts and time
#   -d:profileIteration   → full per-phase iteration timing + neighborByType
# `profileIteration` implies `profileMoveDelta` since the per-type breakdown
# in updateNeighborPenalties is more useful with both available.
const ProfileMoveDelta* = defined(profileMoveDelta) or defined(profileIteration)
const ProfileIteration* = defined(profileIteration)
const LazyThreshold* = 1000  # Positions with domain > this use on-demand costDelta instead of penalty maps
const BatchLazyMax* = 10000  # Lazy positions with domain <= this use batch evaluation in bestMoves

################################################################################
# Type definitions
################################################################################

type
    InitStrategy* = enum
        isRandom     ## Uniform random from domain (default)
        isDomainMin  ## Minimum domain value — helps sum <= K feasibility
        isDomainMax  ## Maximum domain value — helps sum >= K feasibility

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

    CascadeEntryKind* = enum
        ceElement    ## Regular element channel binding
        ceMinMax     ## FlatMinMax channel binding
        ceCountEq    ## CountEq channel binding
        ceWeightedCountEq  ## WeightedCountEq channel binding
        ceArgmax     ## Argmax channel binding
        ceCrossingCountMax  ## Crossing count max channel binding
        ceConditionalCountEq  ## ConditionalCountEq channel binding
        ceExpression  ## Expression channel binding (int_times/int_div/int_mod/int_plus)

    TabuState*[T] = ref object of RootObj
        id*: int  # Identifies this state in parallel runs
        # Search budget handles, set by tabuImprove on entry. Long-running
        # auxiliary scans (swap/permutation/compound-repair helpers) check
        # these periodically so a single helper call cannot overrun the
        # deadline by its full scan length.
        searchDeadline*: float
        stopSignal*: ptr Atomic[bool]
        carray*: ConstrainedArray[T]
        sharedDomain*: ptr seq[seq[T]]  # Points to shared reducedDomain (never copied per state)
        constraintsAtPosition*: seq[seq[StatefulConstraint[T]]]
        constraintIdxAt*: seq[Table[pointer, int]]  # [position][constraint_ptr] -> localIdx
        constraints*: seq[StatefulConstraint[T]]
        neighbors*: seq[seq[int]]

        # Dense array penalty tracking (indexed by domain-local index)
        domainIndex*: seq[Table[T, int]]  # [position][value] -> index in reducedDomain
        # Contiguous-domain fast path: when reducedDomain[pos] is exactly
        # lo, lo+1, ..., value→index is arithmetic and the hash table above is
        # neither built nor consulted. Always false for lazy positions.
        domIdxContiguous*: seq[bool]
        domIdxLo*: seq[T]
        penaltyMap*: seq[seq[int]]  # [position][domainIdx] -> total penalty
        constraintPenalties*: seq[seq[seq[int]]]  # [pos][local_constraint_idx][domainIdx]
        tabu*: seq[seq[int]]  # [position][domainIdx] -> tabu expiration iteration

        assignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int
        # Near-feasible tracking during an optimizer bound probe: the best state
        # in which the objective-bound constraint was the ONLY violated one. Such
        # a state is a feasible solution of the original problem (objective =
        # target + violation), worth keeping when the probe misses its target.
        boundConstraint*: StatefulConstraint[T]
        nearBestCost*: int
        nearBestAssignment*: seq[T]
        nearStallSecs*: float      # see ConstrainedArray.nearStallSecs
        nearStallRef*: float       # time of the run start / last near-feasible gain

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

        # True if the carray has any channel bindings at all. When false,
        # channel propagation is a no-op and can be skipped entirely
        # (avoids worklist allocation + 9 table lookups per assignment).
        anyChannels*: bool
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
        maxPermSwapEvals*: int  # adaptive budget for permutation swap evaluations
        permSwapSlowTime*: float  # wall time spent in simulated (channel-propagating) swap evaluation
        permSwapCalls*, permSwapThrottled*, permSwapApplied*: int
        # Lean trial (tabuImprove): while > 0, updateNeighborPenalties checks the
        # clock and sets trialAborted once past it, turning the rest of a
        # pathologically expensive best-move iteration into no-ops.
        trialAbortAt*: float
        regLineCalls*, regLineApplied*: int
        trialAborted*: bool
        trialNeighborCalls*: int

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

        # Reverse element implied moves: when a channel/array element changes,
        # try to re-point the index variable to satisfy the element constraint.
        reverseElementImpliedEnabled*: bool
        reverseElementImpliedMap*: seq[seq[tuple[constraintIdx: int, idxPos: int]]]
            # [position] -> [(constraint index, index position)] for reverse implied moves
            # Indexed by position (sparse, most entries empty)

        # Inverse group compound move structures
        inverseEnabled*: bool
        inverseGroups*: seq[InverseGroup[int]]
        posToInverseGroup*: seq[int]              # [position] -> group index (-1 if not in any group)
        posToGroupLocalIdx*: seq[int]             # [position] -> local index within group (-1 if not in any group)
        inverseDelta*: seq[seq[int]]              # [pos][domainIdx] -> compound delta from forced changes
        inverseForcedChanges*: seq[(int, int, int)]  # buffer: (pos, oldVal, newVal)
        inverseSavedBuf*: seq[(int, T)]           # reusable buffer for computeChannelDepDelta
        forcedChannelsBuf2*: seq[int]             # reusable buffer for forced position channel propagation

        # Circuit-time-prop writeback: after updatePosition, write computed times to assignment
        circuitTimePropConstraints*: seq[CircuitTimePropConstraint[T]]
        ctpAtLink*: Table[int, seq[int]]           # link (successor) position -> indices into circuitTimePropConstraints
        ctpChangedBuf*: seq[int]                   # reusable buffer for writeback-changed time positions

        # Cached list of tableIn constraint indices for fast stagnation-time table moves
        tableInConstraintIndices*: seq[int]

        deltaMismatches*: int   # CRUSHER_CHECK_DELTA diagnostics
        tourFailStreak*: int    # consecutive fruitless tryTourMoves scans (backoff)
        tourNextTry*: int       # iteration of the next tryTourMoves attempt
        tourPairs*: seq[(int, int, int)]   # (circuit idx, node a, node b): nodes tied by a binary
                                           # relation over one accumulator chain (e.g. same vehicle)
        tourPairsBuilt*: bool
        pairNextTry*: int
        pairFailStreak*: int

        # Regular constraints over search positions, for line-rewrite moves (tabuRegularMoves)
        regularConstraintIndices*: seq[int]

        # Incremental count channels: for wide countEq / weightedCountEq bindings
        # (>= IncCountMinInputs inputs), position -> multiplicity / summed weight.
        # When a single source position changes old -> new, the count changes by
        # w * ([new == target] - [old == target]) instead of an O(inputs) rescan
        # (global-cardinality counts over thousands of variables).
        ceqPosMult*: seq[Table[int, int]]       # [countEq binding] (empty = not wide)
        wceqPosWeight*: seq[Table[int, T]]      # [weightedCountEq binding] (empty = not wide)
        # Source change for the propagation in progress (-1 = unknown)
        propSrcPos*: int
        propSrcOld*: T

        # Cached circuit constraint states (direct-variable only) for circuit-repair moves
        circuitConstraints*: seq[CircuitConstraint[T]]
        # Successor positions of circuits that drive circuit-time chains -> index
        # into circuitConstraints (built lazily). On a VALID tour every single
        # successor move breaks the circuit, so these are left to tour moves.
        ctpCircuitOfPos*: Table[int, int]
        ctpCircuitBuilt*: bool
        # Lean first-improvement run: penalty maps are not read, so stagnation
        # helpers commit moves with assignValueLean (no map maintenance).
        leanSearch*: bool
        # Circuit constraints over channel (derived) positions: their successors are
        # selected by index variables, so a cross-cycle merge is realized by flipping
        # those selectors rather than assigning the channel directly.
        channelCircuitConstraints*: seq[CircuitConstraint[T]]
        cPosToBinding*: Table[int, int]            # channel position -> element channelBinding index
        circuitMergesApplied*: int                 # count of applied cross-cycle merge moves
        circuitMoveCalls*: int                     # times a circuit merge was invoked (for self-disable)

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
        cdCascadeEntryKind: seq[seq[CascadeEntryKind]]  # [cascadeIdx][entryIdx] -> binding type
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
        # Sparse dynamic-cascade evaluation (see computeChannelDepPenaltiesAt)
        cdCascadeNSrcReaders: seq[int]            # [cascadeIdx] -> entries 0..<n read the source position directly
        cdCascadeHasBackEdge: seq[bool]           # [cascadeIdx] -> some entry reads a later entry (sparse unsafe)
        cdCascadeEntryCons: seq[seq[seq[int]]]    # [cascadeIdx][entry] -> constraint-local indices reading it
        cdCascadeSingleIdx: seq[seq[int]]         # [cascadeIdx][cli] -> entry of a single-pos constraint's position, or -1
        cdCascadeConsExt: seq[PackedSet[int]]     # [cascadeIdx] -> positions its constraints read outside the cascade
        # Lean-mode cascade cache validity: cdExtReadersOf[p] lists the cascade
        # source positions whose entries read p from outside the cascade. A move
        # at p (or at a channel p) bumps cdCacheDirty of those sources; a scan
        # whose cdCacheStamp is newer re-scores from the cached per-value channel
        # values instead of re-evaluating the cascade (see applyFirstImprovingMove).
        cdExtReadersOf: Table[int, seq[int]]
        cdCacheStamp: seq[int]
        cdCacheDirty: seq[int]
        cdMoveSeq: int
        # Per-batch affine index shortcut for source-reader element entries
        cdSrcLinOk: seq[bool]
        cdSrcLinBase: seq[T]
        cdSrcLinCoeff: seq[T]
        cdReadersOf: Table[int, seq[int]]         # position -> cascade source positions that READ it (ext deps / constraint inputs)
        # Mixed constraints: a fast-path linear constraint that reads the cascade
        # source position DIRECTLY and channels the source feeds. Scoring it as
        # direct delta + cascade delta is inexact across the max(0, .) hinge (an
        # objective bound near its target gets every mixed move wrong), so the
        # cascade scores it jointly (source coefficient applied with the channel
        # diffs) and movePenalty returns 0 for the (constraint, source) pair.
        cdCascadeSrcPos: seq[int]                          # [cascadeIdx] -> source position
        cdCascadeSrcCoeff: seq[seq[tuple[l, r: T]]]         # [cascadeIdx][cli] -> source coefficients
        cdCascadeMixedClis: seq[seq[int]]                   # [cascadeIdx] -> clis with a nonzero source coefficient
        cdMixedAt: seq[seq[tuple[ci: int, l, r: T]]]         # [pos] -> mixed channel-dep constraints at pos
        cdBatchChanged: seq[seq[int]]             # [domainIdx] -> entries changed for that value (scratch)
        cdCliStamp: seq[int]                      # scratch dedupe stamps per constraint-local index
        cdCliStampGen: int
        # DisjunctiveClause fast cascade path: precomputed term coefficient mappings
        # [cascadeIdx][constraintLocalIdx] -> per-disjunct, per-term list of (coeffIdx, cascadeIdx) pairs
        cdCascadeDCTermCoeffs: seq[seq[seq[seq[seq[tuple[coeffIdx: int, cascIdx: int]]]]]]
        # Reusable buffers for dynamic batch evaluation (avoid per-call allocation)
        cdBatchValues: seq[seq[T]]                # [chanIdx][domainIdx] -> channel value (resized as needed)
        cdBatchSaved: seq[T]                      # saved channel values during batch evaluation
        # Uniform delta: saved constraint costs before propagation
        cdSavedConstraintCosts: seq[int]          # [constraintIdx] -> saved cost before propagateChannels
        # Single-position relational channel-dep constraints (e.g. bounds on a nonlinear
        # expression of one channel): penalty is a pure function of that value, memoized
        # (see singlePosPenalty) instead of re-evaluating the expression tree per candidate.
        cdSinglePos: seq[int]                     # [constraintIdx] -> the position, or -1
        cdSingleCache: seq[Table[T, int]]         # [constraintIdx] -> value -> penalty

        # Partition swap move structures
        partitionGroups*: seq[PartitionGroup[int]]
        partitionEnabled*: bool

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
            cdConsRescoreCalls*: int64  # cascades re-scored from cache (constraint input changed)
            cdLeanRescore*: int64       # lean scan: penalties re-scored from a valid cache
            cdLeanFull*: int64          # lean scan: full cascade evaluation
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

proc domIdx*[T](state: TabuState[T], position: int, value: T): int {.inline.} =
    ## Index of `value` in the reduced domain at `position`, or -1 if absent.
    ## Arithmetic fast path for contiguous domains, hash lookup otherwise.
    ## Lazy positions have neither flag nor table set and always return -1,
    ## matching the previous getOrDefault(-1) behavior.
    when T is SomeInteger:
        if state.domIdxContiguous[position]:
            let off = int(value - state.domIdxLo[position])
            if off >= 0 and off < state.sharedDomain[][position].len:
                return off
            return -1
    state.domainIndex[position].getOrDefault(value, -1)

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
    if state.cdMixedAt.len > position and state.cdMixedAt[position].len > 0:
        # Scored jointly by this position's cascade (see cdMixedAt).
        for m in state.cdMixedAt[position]:
            if cast[pointer](state.channelDepConstraints[m.ci]) == cast[pointer](constraint):
                return 0
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
        of UnionCycleType:
            result = constraint.unionCycleState.moveDelta(position, oldValue, newValue)
        of InvolutionType:
            result = constraint.involutionState.moveDelta(position, oldValue, newValue)
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
        of NValueType:
            result = constraint.nvalueState.moveDelta(position, oldValue, newValue)
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
        of DisjunctiveClauseType:
            result = constraint.disjunctiveClauseState.moveDelta(position, oldValue, newValue)
        of AdjacencyEqualType:
            result = constraint.adjacencyEqualState.moveDelta(position, oldValue, newValue)
        of ConditionalLinearType:
            result = constraint.conditionalLinearState.moveDelta(position, oldValue, newValue)
        of ValueSupportType:
            result = constraint.valueSupportState.moveDelta(position, oldValue, newValue)
        of MultiResourceNoOverlapType:
            result = constraint.multiResourceNoOverlapState.moveDelta(position, oldValue, newValue)
        of CircuitTimePropType:
            result = constraint.circuitTimePropState.moveDelta(position, oldValue, newValue)
        of MultiMachineNoOverlapType:
            result = constraint.multiMachineNoOverlapState.moveDelta(position, oldValue, newValue)
        of ReservoirType:
            result = constraint.reservoirState.moveDelta(position, oldValue, newValue)
        of SetIntersectCardType:
            result = constraint.setIntersectCardState.moveDelta(position, oldValue, newValue)
        of ConjunctSumAtMostType:
            result = constraint.conjunctSumAtMostState.moveDelta(position, oldValue, newValue)
        of PseudoBoolLinLeType:
            result = constraint.pseudoBoolLinLeState.moveDelta(position, oldValue, newValue)
        of GroupValueDisjointType:
            result = constraint.groupValueDisjointState.moveDelta(position, oldValue, newValue)
        of GuardedCountType:
            result = constraint.guardedCountState.moveDelta(position, oldValue, newValue)
    when ProfileMoveDelta:
        let elapsed = cpuTime() - startT
        state.profileByType[constraint.stateType].calls += 1
        state.profileByType[constraint.stateType].totalTime += elapsed

################################################################################
# Included subsystems
################################################################################

let gNoCtpLinkSkip = existsEnv("CRUSHER_NO_CTP_LINK_SKIP")
let gNoSegmentRelocate = not existsEnv("CRUSHER_SEGMENT_RELOCATE")   # opt-in: relocating fixed chains scrambled vrplc vehicle anchors

proc onValidCtpCircuit[T](state: TabuState[T], pos: int): bool {.inline.} =
    ## True when pos is a successor variable of a currently valid circuit whose
    ## tour drives a circuit-time chain (single moves there only break the tour).
    if gNoCtpLinkSkip or state.circuitTimePropConstraints.len == 0 or
       state.circuitConstraints.len == 0:
        return false
    if not state.ctpCircuitBuilt:
        state.ctpCircuitBuilt = true
        for ci, cc in state.circuitConstraints:
            for p in cc.positionArray:
                if p >= 0 and p in state.ctpAtLink:
                    state.ctpCircuitOfPos[p] = ci
    let ci = state.ctpCircuitOfPos.getOrDefault(pos, -1)
    ci >= 0 and state.circuitConstraints[ci].cost == 0

template commitValue[T](state: TabuState[T], position: int, value: T) =
    ## Commit a move from a stagnation helper: lean when the search is lean.
    if state.leanSearch: state.assignValueLean(position, value)
    else: state.assignValue(position, value)

include tabuInverseMoves
# Debug A/B knobs for the cascade cache paths (see applyFirstImprovingMove /
# computeChannelDepPenaltiesAt): disable the lean-scan re-score from cache,
# and the affine index shortcut for source-reader element entries.
let gNoCdStamp = existsEnv("CRUSHER_NO_CD_STAMP")
let gTraceMoves = existsEnv("CRUSHER_TRACE_MOVES")   # debug: print S0's best-move assignments (first 400 iterations)
let gNoSrcLin = existsEnv("CRUSHER_NO_SRC_LIN")
let gNoPosSample = existsEnv("CRUSHER_NO_POS_SAMPLE")       # A/B: flat (position,value) tie sampling
let gNoEmptyCascade = existsEnv("CRUSHER_NO_EMPTY_CASCADE") # A/B: worklist fallback for unread cascades
let gOldWideGuard = existsEnv("CRUSHER_OLD_WIDE_GUARD")     # A/B: count constant element tables as cascade inputs
let gNoCacheRescore = existsEnv("CRUSHER_NO_CACHE_RESCORE") # A/B: never re-score a cascade from cached channel values
let gMixedAll = existsEnv("CRUSHER_MIXED_ALL")               # A/B: joint-score every mixed constraint, not only the objective bound

include tabuChannelDep
include tabuElementImplied
include tabuSwapMoves
include tabuFlowMoves
include tabuLinearRepair
include tabuCircuitMoves
include tabuRegularMoves

################################################################################
# Dense Array Penalty Lookup
################################################################################

proc penaltyAt*[T](state: TabuState[T], position: int, value: T): int {.inline.} =
    ## Look up penalty for a (position, value) pair using dense arrays.
    if state.isLazy[position]:
        return state.costDelta(position, value)
    let idx = state.domIdx(position, value)
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
    let domain {.cursor.} = state.sharedDomain[][position]
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
        elif constraint.stateType == DisjunctiveClauseType:
            let p = constraint.disjunctiveClauseState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == AdjacencyEqualType:
            let p = constraint.adjacencyEqualState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == ConditionalLinearType:
            let p = constraint.conditionalLinearState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == ValueSupportType:
            let p = constraint.valueSupportState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == MultiMachineNoOverlapType:
            let p = constraint.multiMachineNoOverlapState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == ReservoirType:
            let p = constraint.reservoirState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == ConjunctSumAtMostType:
            let p = constraint.conjunctSumAtMostState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == PseudoBoolLinLeType:
            let p = constraint.pseudoBoolLinLeState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == AtMostType:
            let p = constraint.atMostState.batchMovePenalty(
                position, oldValue, domain)
            for i in 0..<dLen: penalties[i] += p[i]
        elif constraint.stateType == GroupValueDisjointType:
            let p = constraint.groupValueDisjointState.batchMovePenalty(
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
    let domain {.cursor.} = state.sharedDomain[][position]
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
        elif constraint.stateType == DisjunctiveClauseType:
            let penalties = constraint.disjunctiveClauseState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == AdjacencyEqualType:
            let penalties = constraint.adjacencyEqualState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == ConditionalLinearType:
            let penalties = constraint.conditionalLinearState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == ValueSupportType:
            let penalties = constraint.valueSupportState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == MultiMachineNoOverlapType:
            let penalties = constraint.multiMachineNoOverlapState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == ReservoirType:
            let penalties = constraint.reservoirState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == ConjunctSumAtMostType:
            let penalties = constraint.conjunctSumAtMostState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == PseudoBoolLinLeType:
            let penalties = constraint.pseudoBoolLinLeState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == AtMostType:
            let penalties = constraint.atMostState.batchMovePenalty(
                position, state.assignment[position], domain)
            for i in 0..<dLen:
                state.constraintPenalties[position][ci][i] = penalties[i]
                state.penaltyMap[position][i] += penalties[i]
        elif constraint.stateType == GroupValueDisjointType:
            let penalties = constraint.groupValueDisjointState.batchMovePenalty(
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
    let domain {.cursor.} = state.sharedDomain[][position]

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
    elif constraint.stateType == DisjunctiveClauseType:
        let penalties = constraint.disjunctiveClauseState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == AdjacencyEqualType:
        let penalties = constraint.adjacencyEqualState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == ValueSupportType:
        let penalties = constraint.valueSupportState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == MultiMachineNoOverlapType:
        let penalties = constraint.multiMachineNoOverlapState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == ConjunctSumAtMostType:
        let penalties = constraint.conjunctSumAtMostState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == PseudoBoolLinLeType:
        let penalties = constraint.pseudoBoolLinLeState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == AtMostType:
        let penalties = constraint.atMostState.batchMovePenalty(
            position, state.assignment[position], domain)
        for i in 0..<domain.len:
            let newP = penalties[i]
            let oldP = state.constraintPenalties[position][localIdx][i]
            state.penaltyMap[position][i] += newP - oldP
            state.constraintPenalties[position][localIdx][i] = newP
    elif constraint.stateType == GroupValueDisjointType:
        let penalties = constraint.groupValueDisjointState.batchMovePenalty(
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
        let idx = state.domIdx(position, value)
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

    if state.trialAbortAt > 0.0:
        if state.trialAborted: return
        inc state.trialNeighborCalls
        # Checked on every call: one call can itself run for a long time on a
        # cascade-heavy model, so a sampled check would overrun by that factor.
        if epochTime() > state.trialAbortAt:
            state.trialAborted = true
            return

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

                    let domain {.cursor.} = state.sharedDomain[][pos]
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

        # PseudoBoolLinLe binary broadcast fast path
        if constraint.stateType == PseudoBoolLinLeType and affectedPositions.len > 0:
            let pb = constraint.pseudoBoolLinLeState
            let currentCost = pb.cost
            let currentSum = pb.currentSum
            let rhs = pb.rhs

            for pos in searchPos.items:
                if pos == position: continue
                if state.isLazy[pos]: continue
                if pos notin affectedPositions: continue

                let domain {.cursor.} = state.sharedDomain[][pos]
                if domain.len != 2 or domain[0] != T(0) or domain[1] != T(1):
                    # Non-binary: fall back to standard update
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
                let coeff = pb.coeffAtPosition.getOrDefault(pos, T(0))

                # For binary domain: flip penalty = max(0, currentSum + flipDelta - rhs) - currentCost
                let flipDelta = if x == 0: coeff else: -coeff
                let newFlip = max(0, currentSum + flipDelta - rhs) - currentCost

                # Binary domain sorted [0,1]: keepIdx = x, flipIdx = 1-x
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

        # Standard path. An empty affected set means no neighbor's cached
        # delta changed (every getAffectedPositions returns the full position
        # set when it cannot narrow), so skip the O(|searchPos|) scan outright:
        # with k value-indexed constraints spanning all n positions (GCC counts
        # decomposed into k AtMost), the scan alone was k*n set probes per move.
        if affectedPositions.len == 0:
            continue
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
            let dom {.cursor.} = state.sharedDomain[][pos]
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

proc initValidCircuits[T](state: TabuState[T], verbose: bool = false) =
    ## Start every circuit (over direct search variables) on a random VALID
    ## Hamiltonian tour: chain the paths formed by fixed arcs and the free
    ## nodes in random order, each link drawn from the tail's domain, with
    ## randomized retries. Single-variable moves cannot merge subtours, so a
    ## random permutation start leaves the search fighting the circuit (and
    ## any chain constraint walking it) instead of the side constraints;
    ## tour moves then keep the circuit valid.
    var nInit = 0
    if verbose: echo "[Init] circuit init: " & $state.circuitConstraints.len & " circuits"
    for cc in state.circuitConstraints:
        let n = cc.n
        if n < 3: continue
        let off = cc.valueOffset
        var fixedSucc = newSeq[int](n)
        var hasFixedPred = newSeq[bool](n)
        var ok = true
        for i in 0..<n:
            let pos = cc.positionArray[i]
            let dom {.cursor.} = state.sharedDomain[][pos]
            fixedSucc[i] = -1
            if dom.len == 1 or pos in state.carray.fixedPositions:
                let v = (if dom.len == 1: int(dom[0]) else: int(state.assignment[pos])) - off
                if v < 0 or v >= n or hasFixedPred[v]:
                    if verbose: echo "[Init] circuit init: inconsistent fixed arc at node " & $i
                    ok = false
                    break
                fixedSucc[i] = v
                hasFixedPred[v] = true
        if not ok: continue
        # Segments: maximal fixed-arc paths, from heads (no fixed predecessor)
        var segHead, segTail: seq[int]
        var covered = 0
        for h in 0..<n:
            if hasFixedPred[h]: continue
            var cur = h
            inc covered
            var guard = 0
            while fixedSucc[cur] >= 0 and guard <= n:
                cur = fixedSucc[cur]
                inc covered
                inc guard
            segHead.add(h)
            segTail.add(cur)
        if covered != n or segHead.len < 2:   # fixed cycle or fully fixed
            if verbose: echo "[Init] circuit init skipped: covered=" & $covered & "/" & $n & " segs=" & $segHead.len
            continue
        let m = segHead.len
        var domSet = newSeq[PackedSet[int]](m)          # allowed heads (node idx) per tail
        for k in 0..<m:
            for v in state.sharedDomain[][cc.positionArray[segTail[k]]]:
                domSet[k].incl(int(v) - off)
        var headSeg: Table[int, int]
        for k in 0..<m: headSeg[segHead[k]] = k
        var order = newSeq[int](m)
        var success = false
        # Phase 1: random insertion. Close a small cycle from a random segment,
        # then insert the remaining segments (random order) at random valid
        # arcs a -> b (head_k in dom(tail_a), head_b in dom(tail_k)).
        block insertion:
            var nextSeg = newSeq[int](m)
            var inCycle = newSeq[bool](m)
            var cycleList: seq[int]
            var pending: seq[int]
            var arcs: seq[int]
            for attempt in 0..<16:
                for k in 0..<m:
                    inCycle[k] = false
                    nextSeg[k] = -1
                cycleList.setLen(0)
                var s0 = rand(m - 1)
                var closed = false
                # Fixed multi-node segments (e.g. giant-tour depot connectors
                # end_v -> start_v+1) first, in head-index order: anchors that
                # accumulate along the tour (vehicle ids, loads) then start
                # consistent and only the free nodes are placed at random.
                if attempt < 8:
                    var multi: seq[int]
                    for k in 0..<m:
                        if segHead[k] != segTail[k]: multi.add(k)
                    if multi.len >= 2:
                        multi.sort(proc (a, b: int): int = cmp(segHead[a], segHead[b]))
                        var okBase = true
                        for t in 0..<multi.len:
                            let a = multi[t]
                            let b = multi[(t + 1) mod multi.len]
                            if segHead[b] notin domSet[a]:
                                okBase = false
                                break
                        if okBase:
                            for t in 0..<multi.len:
                                let a = multi[t]
                                inCycle[a] = true
                                cycleList.add(a)
                                nextSeg[a] = multi[(t + 1) mod multi.len]
                            s0 = multi[0]
                            closed = true
                if not closed:
                    inCycle[s0] = true
                    cycleList.add(s0)
                    closed = segHead[s0] in domSet[s0] and m == 1
                var cur = s0
                var guard = 0
                while not closed and guard < m:
                    inc guard
                    if segHead[s0] in domSet[cur] and cycleList.len >= 2:
                        nextSeg[cur] = s0
                        closed = true
                        break
                    # extend with a random unused segment whose tail can close or continue
                    var best = -1
                    var nSeen = 0
                    for h in domSet[cur].items:
                        if h notin headSeg: continue
                        let k = headSeg[h]
                        if inCycle[k]: continue
                        let canClose = segHead[s0] in domSet[k]
                        inc nSeen
                        if canClose:
                            if best < 0 or segHead[s0] notin domSet[best] or rand(nSeen - 1) == 0:
                                best = k
                        elif best < 0 or (segHead[s0] notin domSet[best] and rand(nSeen - 1) == 0):
                            best = k
                    if best < 0: break
                    nextSeg[cur] = best
                    inCycle[best] = true
                    cycleList.add(best)
                    cur = best
                if not closed: continue
                pending.setLen(0)
                for k in 0..<m:
                    if not inCycle[k]: pending.add(k)
                shuffle(pending)
                var allIn = true
                for k in pending:
                    arcs.setLen(0)
                    for a in cycleList:
                        let b = nextSeg[a]
                        if segHead[k] in domSet[a] and segHead[b] in domSet[k]:
                            arcs.add(a)
                    if arcs.len == 0:
                        allIn = false
                        break
                    let a = arcs[rand(arcs.len - 1)]
                    nextSeg[k] = nextSeg[a]
                    nextSeg[a] = k
                    inCycle[k] = true
                    cycleList.add(k)
                if not allIn: continue
                var c = s0
                for step in 0..<m:
                    order[step] = c
                    c = nextSeg[c]
                success = true
                if verbose: echo "[Init] circuit init (insertion) succeeded at attempt " & $attempt
                break insertion
        for attempt in 0..<64:
            if success: break
            var used = newSeq[bool](m)
            var first = rand(m - 1)
            order[0] = first
            used[first] = true
            var cur = first
            var fail = false
            var cand: seq[int]
            # Warnsdorff: prefer the segment with the fewest onward options
            # only after 32 random attempts failed (random tours spread better)
            let warnsdorff = m <= 300 and attempt >= 32
            for step in 1..<m:
                cand.setLen(0)
                for h in domSet[cur].items:
                    if h in headSeg:
                        let k = headSeg[h]
                        if not used[k]: cand.add(k)
                if cand.len == 0:
                    fail = true
                    break
                var nk = cand[rand(cand.len - 1)]
                if warnsdorff and cand.len > 1:
                    var bestDeg = high(int)
                    var nBest = 0
                    for k in cand:
                        var deg = 0
                        for h in domSet[k].items:
                            if h in headSeg:
                                let kk = headSeg[h]
                                if not used[kk] and kk != k: inc deg
                        # the last step must be able to close back to `first`
                        if step == m - 1 and segHead[first] notin domSet[k]: deg = high(int) - 1
                        if deg < bestDeg:
                            bestDeg = deg
                            nk = k
                            nBest = 1
                        elif deg == bestDeg:
                            inc nBest
                            if rand(nBest - 1) == 0: nk = k
                order[step] = nk
                used[nk] = true
                cur = nk
            if fail: continue
            if segHead[first] notin domSet[cur]: continue
            success = true
            if verbose: echo "[Init] circuit init succeeded at attempt " & $attempt
            break
        if not success:
            if verbose: echo "[Init] circuit init failed after retries (" & $m & " segments)"
            continue
        for step in 0..<m:
            let k = order[step]
            let nxt = order[(step + 1) mod m]
            state.assignment[cc.positionArray[segTail[k]]] = T(segHead[nxt] + off)
        if verbose:
            # sanity: walk the tour
            var seen = newSeq[bool](n)
            var cur = 0
            var cnt = 0
            while not seen[cur]:
                seen[cur] = true
                inc cnt
                cur = int(state.assignment[cc.positionArray[cur]]) - off
                if cur < 0 or cur >= n: break
            echo "[Init] circuit init tour length " & $cnt & "/" & $n & " segments=" & $m
        inc nInit
    if verbose and nInit > 0:
        echo "[Init] Valid circuit tours: " & $nInit & "/" & $state.circuitConstraints.len

proc balancePermutations[T](state: TabuState[T], verbose: bool = false) =
    ## For each alldifferent constraint that is a permutation (domain union size ==
    ## position count), initialize free positions with a valid random permutation of
    ## the remaining values. When groups overlap, the first group wins (positions
    ## already assigned by a prior group are treated as fixed).
    var fixed = initPackedSet[int]()  # positions already assigned by earlier groups
    var groupCount = 0
    # Use a local RNG seeded from state id to avoid perturbing the global random state
    var rng = initRand(42 + state.id * 17)

    for constraint in state.constraints:
        if constraint.stateType != AllDifferentType:
            continue
        let ad = constraint.allDifferentState
        if ad.evalMethod != PositionBased:
            continue

        # Collect non-channel positions and build domain union
        var groupPositions: seq[int]
        var domainUnion = initPackedSet[int]()
        for pos in constraint.positions.items:
            if pos notin state.carray.channelPositions:
                groupPositions.add(pos)
                for v in state.sharedDomain[][pos]:
                    domainUnion.incl(v)

        # Only handle permutation groups (domain union size == position count)
        if groupPositions.len < 2 or domainUnion.len != groupPositions.len:
            continue

        inc groupCount

        # Determine which values are already taken by fixed or previously-assigned positions
        var usedValues = initPackedSet[int]()
        var freePositions: seq[int]
        for pos in groupPositions:
            if pos in fixed or state.sharedDomain[][pos].len == 1:
                usedValues.incl(int(state.assignment[pos]))
            else:
                freePositions.add(pos)

        if freePositions.len == 0:
            continue

        # Remaining values to assign
        var remainingValues: seq[T]
        for v in domainUnion.items:
            if v notin usedValues:
                remainingValues.add(T(v))

        # Greedy random assignment: shuffle positions, assign each the first
        # compatible remaining value (also shuffled for randomness)
        rng.shuffle(freePositions)
        rng.shuffle(remainingValues)

        var assigned = newSeq[bool](remainingValues.len)
        for pos in freePositions:
            var bestIdx = -1
            for i in 0..<remainingValues.len:
                if not assigned[i]:
                    # Check domain compatibility
                    let dom {.cursor.} = state.sharedDomain[][pos]
                    var inDomain = false
                    for dv in dom:
                        if dv == remainingValues[i]:
                            inDomain = true
                            break
                    if inDomain:
                        bestIdx = i
                        break
            if bestIdx >= 0:
                state.assignment[pos] = remainingValues[bestIdx]
                assigned[bestIdx] = true

        # Mark all group positions as fixed for subsequent groups
        for pos in groupPositions:
            fixed.incl(pos)

    if verbose and groupCount > 0:
        stderr.writeLine("[Init] Balanced " & $groupCount & " permutation groups")
        stderr.flushFile()

let gCheckDelta = existsEnv("CRUSHER_CHECK_DELTA")
# A/B switches for the cascade/count evaluation paths (debugging aids)
let gNoExprCascade = existsEnv("CRUSHER_NO_EXPR_CASCADE")
let gNoSparseCascade = existsEnv("CRUSHER_NO_SPARSE_CASCADE")
let gNoIncCount = existsEnv("CRUSHER_NO_INC_COUNT")
let gExactCascadeExt = existsEnv("CRUSHER_EXACT_CASCADE_EXT")
let gNoExactCascadeExt = existsEnv("CRUSHER_NO_EXACT_CASCADE_EXT")
let gDebugViolations = existsEnv("CRUSHER_DEBUG_VIOLATIONS")
let gCtpLazy = existsEnv("CRUSHER_CTP_LAZY")

proc logInitRss*(label: string) =
    ## Verbose-only: resident set size after an init phase (Linux /proc/self/statm).
    try:
        let f = readFile("/proc/self/statm").splitWhitespace()
        if f.len >= 2:
            echo "[Mem] after " & label & ": rss=" & $(parseInt(f[1]) * 4096 div (1024*1024)) & "MiB"
    except CatchableError: discard

proc initStrategyForPopulation*(id, populationSize: int): InitStrategy =
    ## Assigns init strategies to population members.
    ## id 0: domain min, id 1: domain max (if population >= 3), rest: random.
    if populationSize >= 3:
        if id == 0: return isDomainMin
        if id == 1: return isDomainMax
    isRandom

proc init*[T](state: TabuState[T], carray: ConstrainedArray[T], verbose: bool = false, id: int = 0, initialAssignment: seq[T] = @[], initStrategy: InitStrategy = isRandom, forRelinking: bool = false, deadline: float = 0.0) =
    state.id = id
    state.carray = carray
    # Use shared domain pointer if available (parallel path), otherwise own copy (sequential path)
    if state.carray.sharedDomainPtr != nil:
        state.sharedDomain = state.carray.sharedDomainPtr
    else:
        state.sharedDomain = addr state.carray.reducedDomain
    state.anyChannels = carray.channelsAtPosition.len > 0 or
        carray.minMaxChannelsAtPosition.len > 0 or
        carray.countEqChannelsAtPosition.len > 0 or
        carray.weightedCountEqChannelsAtPosition.len > 0 or
        carray.conditionalCountEqChannelsAtPosition.len > 0 or
        carray.argmaxChannelsAtPosition.len > 0 or
        carray.expressionChannelsAtPosition.len > 0 or
        carray.crossingCountMaxChannelsAtPosition.len > 0 or
        carray.inverseChannelsAtPosition.len > 0
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
        if constraint.isObjectiveBound:
            state.boundConstraint = constraint
    state.nearBestCost = high(int)
    state.nearStallSecs = carray.nearStallSecs

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

    # Incremental count-channel tables (see ceqPosMult)
    state.propSrcPos = -1
    state.ceqPosMult = newSeq[Table[int, int]](carray.countEqChannelBindings.len)
    for bi, b in carray.countEqChannelBindings:
        if not gNoIncCount and b.inputPositions.len >= IncCountMinInputs:
            for p in b.inputPositions:
                state.ceqPosMult[bi].mgetOrPut(p, 0) += 1
    state.wceqPosWeight = newSeq[Table[int, T]](carray.weightedCountEqChannelBindings.len)
    for bi, b in carray.weightedCountEqChannelBindings:
        if not gNoIncCount and b.inputPositions.len >= IncCountMinInputs:
            for k, p in b.inputPositions:
                state.wceqPosWeight[bi].mgetOrPut(p, T(0)) += b.weights[k]

    for ci, constraint in state.constraints:
        for pos in constraint.positions.items:
            state.constraintsAtPosition[pos].add(constraint)
        # Collect CircuitTimeProp constraints for writeback
        if constraint.stateType == CircuitTimePropType:
            state.circuitTimePropConstraints.add(constraint.circuitTimePropState)
            for lp in constraint.circuitTimePropState.positionArray:
                if lp >= 0:
                    state.ctpAtLink.mgetOrPut(lp, @[]).add(state.circuitTimePropConstraints.len - 1)
            # Release (waiting) positions also drive the time writeback
            for rp in constraint.circuitTimePropState.releasePositions:
                if rp >= 0:
                    state.ctpAtLink.mgetOrPut(rp, @[]).add(state.circuitTimePropConstraints.len - 1)
        # Cache circuit constraints for stagnation-time cross-cycle merge moves.
        # Skip circuits over channel positions: their successor values are derived
        # from source variables and cannot be assigned directly (same reasoning as
        # the table-move guard below), so the swap move does not apply to them.
        if constraint.stateType == CircuitType and not existsEnv("CRUSHER_NO_CIRCUIT_MOVES"):
            var hasChannelPos = false
            for pos in constraint.circuitState.positions.items:
                if pos in carray.channelPositions:
                    hasChannelPos = true
                    break
            if not hasChannelPos:
                state.circuitConstraints.add(constraint.circuitState)
            else:
                # Circuit over derived positions: repaired via index-selector flips
                # (see tabuCircuitMoves / tryChannelCircuitMoves).
                state.channelCircuitConstraints.add(constraint.circuitState)
        # Regular constraints over distinct non-channel positions: line-rewrite moves
        if constraint.stateType == RegularType:
            let reg = constraint.regularState
            var ok = reg.n > 0 and reg.positionToIndex.len == reg.n
            if ok:
                for pos in reg.sortedPositions:
                    if pos in carray.channelPositions:
                        ok = false
                        break
            if ok:
                state.regularConstraintIndices.add(ci)
        # Cache tableIn constraint indices for fast stagnation-time table moves.
        # Skip constraints whose positions include any channel position: channel
        # values are derived from source vars, so directly assigning a tuple to
        # them is semantically wrong, and their tabu rows are never allocated
        # (tabu.nim:2734-2740 skips channel positions), which would crash at the
        # tabu-tenure write below.
        if constraint.stateType == TableConstraintType and
           constraint.tableConstraintState.mode == TableIn and
           constraint.tableConstraintState.tuples.len > 1:
            var hasChannelPos = false
            for pos in constraint.tableConstraintState.sortedPositions:
                if pos in carray.channelPositions:
                    hasChannelPos = true
                    break
            if not hasChannelPos:
                state.tableInConstraintIndices.add(ci)

    # Map each channel position to its element channel binding, so circuit-merge
    # moves can realize a successor change by flipping the selecting index variable.
    if state.channelCircuitConstraints.len > 0:
        state.cPosToBinding = initTable[int, int]()
        for bi in 0..<carray.channelBindings.len:
            state.cPosToBinding[carray.channelBindings[bi].channelPosition] = bi

    # Build O(1) constraint index lookup
    state.constraintIdxAt = newSeq[Table[pointer, int]](carray.len)
    for pos in carray.allPositions():
        state.constraintIdxAt[pos] = initTable[pointer, int]()
        for i, c in state.constraintsAtPosition[pos]:
            state.constraintIdxAt[pos][cast[pointer](c)] = i

    if verbose and id == 0:
        echo "[Init] Built constraintsAtPosition in " & $(epochTime() - initStart) & "s"
        logInitRss("Built constraintsAtPosition")
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

    # Collect positions belonging to inverse groups so we skip them in normal random init.
    # Build a position→group-indices map so seed clamping can mark whole groups for
    # involution regeneration (clamping a single position would leave the involution
    # invariant broken).
    var inverseGroupPositions: PackedSet[int]
    var positionToInverseGroups = initTable[int, seq[int]]()
    for gi, group in carray.inverseGroups:
        for pos in group.positions:
            inverseGroupPositions.incl(pos)
            positionToInverseGroups.mgetOrPut(pos, @[]).add(gi)
    var clampedInverseGroups: PackedSet[int]

    for pos in carray.allPositions():
        if initialAssignment.len > 0:
            # Seed values can fall outside the current sharedDomain when the seed
            # comes from a previous optimization iteration: tightenReducedDomain
            # may have shrunk the domain after the seed was recorded. Channel
            # positions are recomputed below by the channel fixed-point, so we
            # only need to validate non-channel positions. For inverse-group
            # positions we record the affected group so the involution generator
            # below can rebuild a valid permutation rather than leaving a single
            # randomly-clamped value that breaks the involution invariant.
            if pos in carray.channelPositions:
                state.assignment[pos] = initialAssignment[pos]
            else:
                let dom {.cursor.} = state.sharedDomain[][pos]
                if dom.len > 0 and initialAssignment[pos] notin dom:
                    if pos in inverseGroupPositions:
                        for gi in positionToInverseGroups[pos]:
                            clampedInverseGroups.incl(gi)
                        # Placeholder; overwritten by involution generator below
                        state.assignment[pos] = dom[0]
                    else:
                        case initStrategy
                        of isRandom:    state.assignment[pos] = sample(dom)
                        of isDomainMin: state.assignment[pos] = dom[0]
                        of isDomainMax: state.assignment[pos] = dom[^1]
                else:
                    state.assignment[pos] = initialAssignment[pos]
        elif pos in carray.channelPositions:
            # Channel variables get a placeholder; computed below
            state.assignment[pos] = state.sharedDomain[][pos][0]
        elif pos in inverseGroupPositions:
            # Inverse group positions are initialized below as involutions
            state.assignment[pos] = state.sharedDomain[][pos][0]
        else:
            let dom {.cursor.} = state.sharedDomain[][pos]
            case initStrategy
            of isRandom: state.assignment[pos] = sample(dom)
            of isDomainMin: state.assignment[pos] = dom[0]
            of isDomainMax: state.assignment[pos] = dom[^1]

    # Generate random involutions for inverse group positions.
    # When seeded, only regenerate groups whose seed values were clamped
    # (un-clamped groups already have a valid involution from the previous
    # iteration's solution).
    let regenAllGroups = initialAssignment.len == 0
    if (regenAllGroups or clampedInverseGroups.len > 0) and carray.inverseGroups.len > 0:
        for gi, group in carray.inverseGroups:
            if not regenAllGroups and gi notin clampedInverseGroups:
                continue
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

    # Initialize permutation groups with valid random permutations
    if initialAssignment.len == 0:
        state.balancePermutations(verbose and id == 0)

    # Circuits start on a random valid Hamiltonian tour
    if initialAssignment.len == 0 and not existsEnv("CRUSHER_NO_CIRCUIT_INIT"):
        state.initValidCircuits(verbose and id == 0)

    # Table-aware initialization: for each table constraint, try to satisfy it
    # by picking a valid tuple closest to the current assignment. This dramatically
    # reduces initial cost for table-heavy problems. Process constraints in random
    # order to avoid bias; skip channel positions (they're computed later).
    if initialAssignment.len == 0 and initStrategy == isRandom:
        var tableIndices: seq[int]
        for i, c in state.constraints:
            if c.stateType == TableConstraintType and
               c.tableConstraintState.mode == TableIn:
                tableIndices.add(i)
        shuffle(tableIndices)
        for ci in tableIndices:
            let tc = state.constraints[ci].tableConstraintState
            if tc.tuples.len == 0: continue
            # Find the tuple with minimum Hamming distance to current assignment
            var bestIdx = -1
            var bestDist = tc.sortedPositions.len + 1
            for idx in 0..<tc.tuples.len:
                let tup = tc.tuples[idx]
                var domainOk = true
                var dist = 0
                for col, pos in tc.sortedPositions:
                    let dom {.cursor.} = state.sharedDomain[][pos]
                    if tup[col] notin dom:
                        domainOk = false
                        break
                    if state.assignment[pos] != tup[col]:
                        dist += 1
                if domainOk and dist < bestDist:
                    bestDist = dist
                    bestIdx = idx
            if bestIdx >= 0:
                let tup = tc.tuples[bestIdx]
                for col, pos in tc.sortedPositions:
                    if pos in carray.channelPositions: continue
                    if pos in inverseGroupPositions: continue
                    state.assignment[pos] = tup[col]

    if verbose and id == 0:
        stderr.writeLine("[Init] Assignment init done, starting channel fixed-point (" & $carray.channelBindings.len & " bindings)...")
        stderr.flushFile()

    # Compute argmax channel initial values early — argmax depends only on search
    # variables (signal expressions), which are already assigned. Element channels
    # may read from argmax outputs, so argmax must be set before the element fixed-point.
    for binding in carray.argmaxChannelBindings:
        state.assignment[binding.channelPosition] = evaluateArgmax(binding, state.assignment)

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
                        let b {.cursor.} = carray.channelBindings[bi]
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
            let idxVal = binding.evalIndex(state.assignment)
            if idxVal >= 0 and idxVal < binding.arrayElements.len:
                let elem = binding.arrayElements[idxVal]
                let newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition] + elem.offset
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    channelChanged = true
        for binding in carray.expressionChannelBindings:
            let newVal = binding.evalExpr(state.assignment)
            if newVal != state.assignment[binding.channelPosition]:
                state.assignment[binding.channelPosition] = newVal
                channelChanged = true
        if fpIter > 100:
            var changingPos: seq[int]
            for binding in carray.channelBindings:
                let idxVal = binding.evalIndex(state.assignment)
                if idxVal >= 0 and idxVal < binding.arrayElements.len:
                    let elem = binding.arrayElements[idxVal]
                    let newVal = if elem.isConstant: elem.constantValue
                                 else: state.assignment[elem.variablePosition] + elem.offset
                    if newVal != state.assignment[binding.channelPosition]:
                        changingPos.add(binding.channelPosition)
            if verbose and id == 0:
                stderr.writeLine("[Init] WARNING: channel fixed-point exceeded 100 iterations, breaking (" &
                                 $changingPos.len & " positions still changing)")
                stderr.writeLine("[Init]   Still-changing positions: " & $changingPos[0..min(9, changingPos.len-1)])
                stderr.flushFile()
            break

    if verbose and id == 0:
        stderr.writeLine("[Init] Channel fixed-point done in " & $fpIter & " iterations")
        stderr.flushFile()

    # Compute crossing count max channel initial values
    for binding in carray.crossingCountMaxChannelBindings:
        state.assignment[binding.channelPosition] = evaluateCrossingCountMax(binding, state.assignment)

    # Compute count-equals channel initial values
    for binding in carray.countEqChannelBindings:
        state.assignment[binding.channelPosition] = evaluateCountEq(binding, state.assignment)

    # Compute weighted count-equals channel initial values
    for binding in carray.weightedCountEqChannelBindings:
        state.assignment[binding.channelPosition] = evaluateWeightedCountEq(binding, state.assignment)

    # Compute conditional count-equals channel initial values
    for binding in carray.conditionalCountEqChannelBindings:
        state.assignment[binding.channelPosition] = evaluateConditionalCountEq(binding, state.assignment)

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
            if combinedIter > 200:
                if verbose and id == 0:
                    stderr.writeLine("[Init] WARNING: combined elem+minmax fixed-point exceeded 200 iterations, breaking")
                    stderr.flushFile()
                break
            # Min/max fixed-point pass
            while worklist.len > 0:
                let bi = worklist.pop()
                inWorklist[bi] = false
                inc fpEvals
                let fb {.cursor.} = state.flatMinMaxBindings[bi]
                let newVal = evaluateFlatMinMax(fb, state.assignment)
                if newVal != state.assignment[fb.channelPosition]:
                    state.assignment[fb.channelPosition] = newVal
                    # Enqueue downstream bindings that use this channel as input
                    if fb.channelPosition in posToBindings:
                        for downstream in posToBindings[fb.channelPosition]:
                            if not inWorklist[downstream]:
                                inWorklist[downstream] = true
                                worklist.add(downstream)

            # Re-evaluate element and argmax channels that may read from updated min/max channels
            var elemChanged = false
            for binding in carray.channelBindings:
                let idxVal = binding.evalIndex(state.assignment)
                if idxVal >= 0 and idxVal < binding.arrayElements.len:
                    let elem = binding.arrayElements[idxVal]
                    let newVal = if elem.isConstant: elem.constantValue
                                 else: state.assignment[elem.variablePosition] + elem.offset
                    if newVal != state.assignment[binding.channelPosition]:
                        state.assignment[binding.channelPosition] = newVal
                        elemChanged = true
                        # Enqueue min/max bindings affected by this element channel change
                        if binding.channelPosition in posToBindings:
                            for downstream in posToBindings[binding.channelPosition]:
                                if not inWorklist[downstream]:
                                    inWorklist[downstream] = true
                                    worklist.add(downstream)
            for binding in carray.argmaxChannelBindings:
                let newVal = evaluateArgmax(binding, state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    elemChanged = true
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

    # Repair search positions involved in graduated EqualTo constraints (e.g., flow
    # conservation) by solving the linear system via Gaussian elimination. Without
    # this, randomly-initialized flow variables cause large initial violations that
    # single-variable tabu moves struggle to resolve.
    if initialAssignment.len == 0:
        state.repairLinearEqualities(verbose, id)

        # Re-propagate all channel types that depend on the repaired positions.
        # This mirrors the full channel initialization sequence (argmax, element/
        # expression fixed-point, crossing, count, inverse, min/max).
        for binding in carray.argmaxChannelBindings:
            state.assignment[binding.channelPosition] = evaluateArgmax(binding, state.assignment)

        var repairChannelChanged = true
        var repairFpIter = 0
        while repairChannelChanged:
            repairChannelChanged = false
            repairFpIter += 1
            if repairFpIter > 50: break
            for binding in carray.channelBindings:
                let idxVal = binding.evalIndex(state.assignment)
                if idxVal >= 0 and idxVal < binding.arrayElements.len:
                    let elem = binding.arrayElements[idxVal]
                    let newVal = if elem.isConstant: elem.constantValue
                                 else: state.assignment[elem.variablePosition] + elem.offset
                    if newVal != state.assignment[binding.channelPosition]:
                        state.assignment[binding.channelPosition] = newVal
                        repairChannelChanged = true
            for binding in carray.expressionChannelBindings:
                let newVal = binding.evalExpr(state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    repairChannelChanged = true

        for binding in carray.crossingCountMaxChannelBindings:
            state.assignment[binding.channelPosition] = evaluateCrossingCountMax(binding, state.assignment)
        for binding in carray.countEqChannelBindings:
            state.assignment[binding.channelPosition] = evaluateCountEq(binding, state.assignment)
        for binding in carray.weightedCountEqChannelBindings:
            state.assignment[binding.channelPosition] = evaluateWeightedCountEq(binding, state.assignment)
        for binding in carray.conditionalCountEqChannelBindings:
            state.assignment[binding.channelPosition] = evaluateConditionalCountEq(binding, state.assignment)

        for group in carray.inverseChannelGroups:
            let newInverse = group.recomputeInverse(state.assignment)
            for j, ipos in group.inversePositions:
                state.assignment[ipos] = newInverse[j]

        # Re-evaluate min/max channels with updated values
        if state.flatMinMaxBindings.len > 0:
            for i, fb in state.flatMinMaxBindings:
                let newVal = evaluateFlatMinMax(fb, state.assignment)
                state.assignment[fb.channelPosition] = newVal

    # Initialize CircuitTimeProp constraints first and write their computed
    # times back into the assignment, so channels reading time positions
    # (e.g. an objective max over arrival times) and the remaining constraints
    # initialize against consistent values.
    if state.circuitTimePropConstraints.len > 0:
        for constraint in state.constraints:
            if constraint.stateType == CircuitTimePropType:
                constraint.initialize(state.assignment)
        for ctc in state.circuitTimePropConstraints:
            for i in 0..<ctc.n:
                if ctc.arrivalPositions[i] >= 0:
                    state.assignment[ctc.arrivalPositions[i]] = ctc.arrivalTime[i]
                if ctc.departurePositions[i] >= 0:
                    state.assignment[ctc.departurePositions[i]] = ctc.departureTime[i]
        # Re-evaluate channels that may read the written-back time positions
        var ctpChanged = true
        var ctpIter = 0
        while ctpChanged and ctpIter < 50:
            ctpChanged = false
            inc ctpIter
            for binding in carray.channelBindings:
                let idxVal = binding.evalIndex(state.assignment)
                if idxVal >= 0 and idxVal < binding.arrayElements.len:
                    let elem = binding.arrayElements[idxVal]
                    let newVal = if elem.isConstant: elem.constantValue
                                 else: state.assignment[elem.variablePosition] + elem.offset
                    if newVal != state.assignment[binding.channelPosition]:
                        state.assignment[binding.channelPosition] = newVal
                        ctpChanged = true
            for binding in carray.expressionChannelBindings:
                let newVal = binding.evalExpr(state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    ctpChanged = true
            if state.flatMinMaxBindings.len > 0:
                for fb in state.flatMinMaxBindings:
                    let newVal = evaluateFlatMinMax(fb, state.assignment)
                    if newVal != state.assignment[fb.channelPosition]:
                        state.assignment[fb.channelPosition] = newVal
                        ctpChanged = true

    # Install dense value-count windows on AllDifferent constraints before
    # initialization: exact value bounds derived from the domains let counts
    # use O(1) array indexing instead of hash lookups in the moveDelta /
    # updatePosition hot paths. Values outside the window (e.g. on channel
    # positions with shrunk domains) still work via the table fallback.
    when T is SomeInteger:
        for constraint in state.constraints:
            if constraint.stateType != AllDifferentType: continue
            let ad = constraint.allDifferentState
            var lo = int64.high
            var hi = int64.low
            if ad.evalMethod == PositionBased:
                for pos in constraint.positions.items:
                    for v in state.sharedDomain[][pos]:
                        if int64(v) < lo: lo = int64(v)
                        if int64(v) > hi: hi = int64(v)
            elif ad.allLinear:
                var ok = true
                for i in 0..<ad.expressions.len:
                    var elo = int64(ad.exprConstants[i])
                    var ehi = elo
                    for pos, coeff in ad.exprCoeffs[i].pairs:
                        let domain {.cursor.} = state.sharedDomain[][pos]
                        if domain.len == 0:
                            ok = false
                            break
                        var dmin = domain[0]
                        var dmax = domain[0]
                        for v in domain:
                            if v < dmin: dmin = v
                            if v > dmax: dmax = v
                        if coeff >= 0:
                            elo += int64(coeff) * int64(dmin)
                            ehi += int64(coeff) * int64(dmax)
                        else:
                            elo += int64(coeff) * int64(dmax)
                            ehi += int64(coeff) * int64(dmin)
                    if not ok: break
                    if elo < lo: lo = elo
                    if ehi > hi: hi = ehi
                if not ok: continue
            else:
                continue
            if lo <= hi:
                ad.setValueWindow(lo, hi)

    for constraint in state.constraints:
        if constraint.stateType == CircuitTimePropType:
            continue  # already initialized above (or no instances exist)
        constraint.initialize(state.assignment)

    # Compute maxNetDelta for RelationalType constraints to enable slack-based
    # getAffectedPositions optimization. For inequality constraints (<=, >=),
    # if the slack doesn't change enough, penalty map entries are unchanged.
    block:
        var nComputed = 0
        for constraint in state.constraints:
            if constraint.stateType != RelationalType: continue
            let rc = constraint.relationalState
            if rc.relation notin {LessThanEq, GreaterThanEq, LessThan, GreaterThan}: continue
            # Compute max |leftDelta - rightDelta| for any single position flip
            var maxDelta: T = 0
            var posDeltas: seq[T]   # per-position max deltas (bound-scale calibration)
            for pos in rc.positions.items:
                let domain {.cursor.} = state.sharedDomain[][pos]
                if domain.len < 2: continue
                let dMin = domain[0]
                let dMax = domain[^1]
                let dRange = dMax - dMin
                if dRange <= 0: continue
                # Get coefficient in left and right expressions
                var leftCoeff: T = 0
                var rightCoeff: T = 0
                if pos in rc.leftExpr.positions:
                    case rc.leftExpr.kind
                    of SumExpr:
                        if rc.leftExpr.sumExpr.evalMethod == PositionBased:
                            leftCoeff = rc.leftExpr.sumExpr.coefficient.getOrDefault(pos, T(0))
                        else: leftCoeff = T(1)  # conservative
                    of ConstantExpr: discard
                    else: leftCoeff = T(1)  # conservative for non-sum
                if pos in rc.rightExpr.positions:
                    case rc.rightExpr.kind
                    of SumExpr:
                        if rc.rightExpr.sumExpr.evalMethod == PositionBased:
                            rightCoeff = rc.rightExpr.sumExpr.coefficient.getOrDefault(pos, T(0))
                        else: rightCoeff = T(1)
                    of ConstantExpr: discard
                    else: rightCoeff = T(1)
                let netCoeff = abs(leftCoeff - rightCoeff)
                let posMaxDelta = netCoeff * dRange
                if posMaxDelta > maxDelta:
                    maxDelta = posMaxDelta
                if constraint.isObjectiveBound and posMaxDelta > 0:
                    posDeltas.add(posMaxDelta)
            if maxDelta > 0 and maxDelta < high(T) div 2:
                rc.maxNetDelta = int(maxDelta)
                inc nComputed
            # Objective-bound probe constraint: its raw penalty is in objective
            # units, so a search that counts hard violations as 1 each trades
            # capacity/incompatibility violations for objective gains and never
            # returns to feasibility. Scale it so one unit is a fraction of the
            # typical single-move objective change (median per-position max delta).
            if constraint.isObjectiveBound and posDeltas.len > 0:
                # CRUSHER_BOUND_SCALE_PCT: percent of the median (0 disables, "max" = maxNetDelta).
                let pctStr = getEnv("CRUSHER_BOUND_SCALE_PCT", "100")
                posDeltas.sort()
                let median = int(posDeltas[posDeltas.len div 2])
                var scale = 1
                if pctStr == "max":
                    scale = int(maxDelta)
                else:
                    let pct = try: parseInt(pctStr) except ValueError: 100
                    if pct > 0: scale = max(1, median * pct div 100)
                # A bound that reads a search variable directly AND channels fed
                # by that same variable (kitchen: widths plus the discontinuity
                # indicators they drive) is scored jointly inside the cascade
                # (cdMixedAt / cdCascadeSrcCoeff), and a scaled bound's cost
                # change is never applied as a uniform shift (see
                # applyUniformDelta), so the hinged scale stays exact for mixed
                # bounds too (CRUSHER_CHECK_DELTA: 0 mismatches on kitchen).
                if scale > 1:
                    rc.costScale = scale
                    rc.cost = rc.computeCost(rc.leftValue, rc.rightValue)
                if verbose and id == 0:
                    var nDirect = 0
                    var nChannel = 0
                    for p in constraint.positions.items:
                        if p in carray.channelPositions: inc nChannel
                        elif p notin carray.fixedPositions: inc nDirect
                    echo &"[Init] Objective-bound penalty scale: {rc.costScale} (median single-move delta {median}, max {maxDelta}, setting {pctStr}, direct={nDirect} channel={nChannel})"
        if nComputed > 0 and verbose and id == 0:
            echo "[Init] Computed maxNetDelta for " & $nComputed & " inequality constraints"

    if verbose and id == 0:
        echo "[Init] Initialized constraints in " & $(epochTime() - initStart) & "s"
        logInitRss("Initialized constraints")
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
        if dsize > LazyThreshold or (gCtpLazy and pos in state.ctpAtLink):
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
        stderr.writeLine("[Init] Search positions by domain: d<=2: " & $bin2 & " d<=10: " & $bin3to10 &
             " d<=50: " & $bin11to50 & " d>50: " & $binLarge)

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
               pos in carray.countEqChannelsAtPosition or pos in carray.weightedCountEqChannelsAtPosition or pos in carray.conditionalCountEqChannelsAtPosition or
               pos in carray.inverseChannelsAtPosition or pos in carray.argmaxChannelsAtPosition or
               pos in carray.expressionChannelsAtPosition or pos in carray.crossingCountMaxChannelsAtPosition or
               pos in state.ctpAtLink:
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
                # Circuit-time chains: a link reaches every written-back time position
                if p in state.ctpAtLink:
                    for k in state.ctpAtLink[p]:
                        let ctc = state.circuitTimePropConstraints[k]
                        for tp in ctc.arrivalPositions & ctc.departurePositions:
                            if tp >= 0:
                                reachable.incl(tp)
                                if tp notin visited:
                                    visited.incl(tp)
                                    worklist.add(tp)
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
                        let binding {.cursor.} = carray.minMaxChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Count-equals channel bindings
                if p in carray.countEqChannelsAtPosition:
                    for bi in carray.countEqChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.countEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Weighted count-equals channel bindings
                if p in carray.weightedCountEqChannelsAtPosition:
                    for bi in carray.weightedCountEqChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.weightedCountEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Conditional count-equals channel bindings
                if p in carray.conditionalCountEqChannelsAtPosition:
                    for bi in carray.conditionalCountEqChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.conditionalCountEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Inverse channel bindings
                if p in carray.inverseChannelsAtPosition:
                    for gi in carray.inverseChannelsAtPosition[p]:
                        let group {.cursor.} = carray.inverseChannelGroups[gi]
                        for ipos in group.inversePositions:
                            reachable.incl(ipos)
                            if ipos notin visited:
                                visited.incl(ipos)
                                worklist.add(ipos)
                # Argmax channel bindings
                if p in carray.argmaxChannelsAtPosition:
                    for bi in carray.argmaxChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.argmaxChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Expression channel bindings
                if p in carray.expressionChannelsAtPosition:
                    for bi in carray.expressionChannelsAtPosition[p]:
                        let chanPos = carray.expressionChannelBindings[bi].channelPosition
                        reachable.incl(chanPos)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            worklist.add(chanPos)
                # Crossing count max channel bindings
                if p in carray.crossingCountMaxChannelsAtPosition:
                    for bi in carray.crossingCountMaxChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.crossingCountMaxChannelBindings[bi]
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

    # Build domain index: value -> local array index. Contiguous domains
    # (the common case) use arithmetic indexing via domIdx and skip the
    # hash table entirely.
    let domIdxStart = epochTime()
    state.domainIndex = newSeq[Table[T, int]](carray.len)
    state.domIdxContiguous = newSeq[bool](carray.len)
    state.domIdxLo = newSeq[T](carray.len)
    for pos in carray.allPositions():
        if state.isLazy[pos]:
            continue  # Lazy positions don't need domainIndex (use linear scan or direct computation)
        var contiguous = false
        when T is SomeInteger:
            let dom {.cursor.} = state.sharedDomain[][pos]
            if dom.len > 0:
                contiguous = true
                for i in 1..<dom.len:
                    if dom[i] != dom[0] + T(i):
                        contiguous = false
                        break
                if contiguous:
                    state.domIdxContiguous[pos] = true
                    state.domIdxLo[pos] = dom[0]
        if not contiguous:
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
        state.cdSinglePos = newSeqWith(nCd, -1)
        state.cdSingleCache = newSeq[Table[T, int]](nCd)
        for ci in 0..<nCd:
            let c = state.channelDepConstraints[ci]
            if c.stateType == PseudoBoolLinLeType:
                # PseudoBoolLinLe: sum(c_i * x_i) <= rhs maps to left=sum, right=constant
                let pb = c.pseudoBoolLinLeState
                for pos, coeff in pb.coeffAtPosition.pairs:
                    state.cdConstraintCoeffs[ci].add((pos: pos, coeff: coeff))
                # Right side is constant (rhs) — no coefficients needed
                state.cdConstraintCanFast[ci] = true
                continue
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
            if not canFast and c.positions.len == 1 and
               rc.leftExpr.kind in {StatefulAlgebraicExpr, ConstantExpr} and
               rc.rightExpr.kind in {StatefulAlgebraicExpr, ConstantExpr}:
                for p in c.positions.items: state.cdSinglePos[ci] = p

        if verbose and id == 0 and existsEnv("CRUSHER_DEBUG_CDFAST"):
            var hist: CountTable[string]
            for ci in 0..<nCd:
                if state.cdConstraintCanFast[ci]: continue
                let c = state.channelDepConstraints[ci]
                var key = $c.stateType
                if c.stateType == RelationalType:
                    let rc = c.relationalState
                    key &= " " & $rc.leftExpr.kind & (if rc.leftExpr.kind == SumExpr: "/" & $rc.leftExpr.sumExpr.evalMethod else: "") &
                           " " & $rc.relation & " " & $rc.rightExpr.kind &
                           (if rc.rightExpr.kind == SumExpr: "/" & $rc.rightExpr.sumExpr.evalMethod else: "") &
                           " npos=" & $c.positions.len
                hist.inc(key)
            hist.sort()
            for k, v in hist.pairs: echo "[Init]   cd-fallback ", v, "x ", k

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
            let changes {.cursor.} = state.oneHotChanges[pos]
            let lo = state.oneHotLo[pos]
            for arrayIdx in 0..<changes.len:
                let val = T(arrayIdx + lo)
                let domIdx = state.domIdx(pos, val)
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
            logInitRss("Channel-dep reverse")

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
        state.cdCascadeEntryKind = @[]
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
        state.cdCascadeSrcPos = @[]
        state.cdCascadeSrcCoeff = @[]
        state.cdCascadeMixedClis = @[]
        state.cdMixedAt = @[]
        state.cdCascadeNSrcReaders = @[]
        state.cdCascadeHasBackEdge = @[]
        state.cdCascadeEntryCons = @[]
        state.cdCascadeSingleIdx = @[]
        state.cdCascadeConsExt = @[]
        let cascadeStart = epochTime()
        var staticCount = 0
        var dynamicCount = 0
        var cascadeFail = 0
        var cascadeDepthFail = 0
        var noConstraintSkip = 0  # cascades skipped: zero channel-dep constraints read them

        # Very many channel-dep search positions (e.g. tens of thousands of set-var
        # bools): per-position cascade tables cost seconds and gigabytes to build,
        # while a binary position's fallback evaluates a single alternative value.
        # Keep cascades for the non-binary positions only.
        const ManyCascadePositions = 4000
        let skipBinaryCascades = state.channelDepSearchPositions.len > ManyCascadePositions
        var binaryCascadesSkipped = 0
        var cascadeProgress = 0
        var cascadeEntriesTotal = 0
        for pos in state.channelDepSearchPositions:
            inc cascadeProgress
            if verbose and id == 0 and (cascadeProgress and 1023) == 0:
                echo "[Init]   cascade build: " & $cascadeProgress & "/" & $state.channelDepSearchPositions.len &
                     " positions, " & $cascadeEntriesTotal & " entries, " & $(epochTime() - cascadeStart) & "s"
                logInitRss("cascade progress")
            if state.isLazy[pos]: continue
            if skipBinaryCascades and state.sharedDomain[][pos].len <= 2:
                inc binaryCascadesSkipped
                continue
            # Skip positions with inverse groups (forced changes not captured by cascade)
            if state.inverseEnabled and state.posToInverseGroup[pos] >= 0: continue

            # Walk topology from this position using BFS (FIFO queue) for correct
            # topological ordering. BFS ensures parents are visited before children,
            # which handles diamond patterns (multiple paths to same channel) correctly.
            var topoOrder: seq[int] = @[]
            var topoBindingIdx: seq[int] = @[]
            var topoEntryKind: seq[CascadeEntryKind] = @[]
            var topoSet: PackedSet[int]
            var bfsQueue: seq[int] = @[pos]
            var bfsHead = 0
            var visited: PackedSet[int]
            visited.incl(pos)
            var canBuild = true       # can build topology at all
            var canStatic = true      # can precompute values (constant arrays + local index deps)
            const MaxCascadeChans = 5000  # limit cascade depth to avoid initialization blowup
            var nSrcReaders = -1
            while bfsHead < bfsQueue.len and canBuild:
                if bfsHead == 1 and nSrcReaders < 0:
                    nSrcReaders = topoOrder.len  # entries registered at the source position
                let p = bfsQueue[bfsHead]
                inc bfsHead
                if topoOrder.len >= MaxCascadeChans:
                    canBuild = false
                    break
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
                        topoEntryKind.add(ceElement)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            # Don't propagate downstream from offset channels — they
                            # create long visit-time backward chains. The channel values
                            # still propagate correctly at runtime via the worklist, but
                            # the cascade penalty computation stops here to stay fast.
                            if not bindingPtr.hasOffset:
                                bfsQueue.add(chanPos)
                # Min/max channel bindings: include in cascade as dynamic entries.
                # Implicit channels (detected without defines_var) are cascade-exempt:
                # they're still computed after each move, but their downstream constraints
                # are not included in the penalty-map cascade to control build overhead.
                if p in carray.minMaxChannelsAtPosition:
                    for bi in carray.minMaxChannelsAtPosition[p]:
                        let fb {.cursor.} = state.flatMinMaxBindings[bi]
                        let chanPos = fb.channelPosition
                        if chanPos in carray.implicitMinMaxPositions:
                            continue  # Cascade-exempt: skip downstream propagation
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false  # min/max depends on non-local positions
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)  # index into flatMinMaxBindings
                        topoEntryKind.add(ceMinMax)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # CountEq channel bindings: include in cascade as dynamic entries
                if p in carray.countEqChannelsAtPosition:
                    for bi in carray.countEqChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.countEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false  # countEq depends on non-local positions
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)  # index into countEqChannelBindings
                        topoEntryKind.add(ceCountEq)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # WeightedCountEq channel bindings: include in cascade as dynamic entries
                if p in carray.weightedCountEqChannelsAtPosition:
                    for bi in carray.weightedCountEqChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.weightedCountEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        if chanPos in topoSet:
                            continue
                        canStatic = false
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)
                        topoEntryKind.add(ceWeightedCountEq)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # Argmax channel bindings: include in cascade as dynamic entries
                if p in carray.argmaxChannelsAtPosition:
                    for bi in carray.argmaxChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.argmaxChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false  # argmax depends on non-local positions
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)  # index into argmaxChannelBindings
                        topoEntryKind.add(ceArgmax)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # CrossingCountMax channel bindings: include in cascade as dynamic entries
                if p in carray.crossingCountMaxChannelsAtPosition:
                    for bi in carray.crossingCountMaxChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.crossingCountMaxChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false  # depends on non-local positions
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)
                        topoEntryKind.add(ceCrossingCountMax)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # ConditionalCountEq channels: include in cascade as dynamic entries
                if p in carray.conditionalCountEqChannelsAtPosition:
                    for bi in carray.conditionalCountEqChannelsAtPosition[p]:
                        let binding {.cursor.} = carray.conditionalCountEqChannelBindings[bi]
                        let chanPos = binding.channelPosition
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false  # conditionalCountEq depends on non-local positions
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)  # index into conditionalCountEqChannelBindings
                        topoEntryKind.add(ceConditionalCountEq)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                # Expression channels (e.g. squares of load channels feeding a sum
                # objective): without them, constraints over these channels — often
                # the objective bound — are invisible to cascade move scoring.
                if not gNoExprCascade and p in carray.expressionChannelsAtPosition:
                    for bi in carray.expressionChannelsAtPosition[p]:
                        let chanPos = carray.expressionChannelBindings[bi].channelPosition
                        if chanPos in topoSet:
                            continue  # Diamond — skip
                        canStatic = false
                        topoSet.incl(chanPos)
                        topoOrder.add(chanPos)
                        topoBindingIdx.add(bi)  # index into expressionChannelBindings
                        topoEntryKind.add(ceExpression)
                        if chanPos notin visited:
                            visited.incl(chanPos)
                            bfsQueue.add(chanPos)
                if p in carray.inverseChannelsAtPosition or p in state.ctpAtLink:
                    canBuild = false   # multi-output groups: per-value fallback handles them

            # Wide-input guard: entries such as global-cardinality count channels
            # read every assignment variable; the per-cascade dependency tables are
            # O(entries x inputs) (warehouse: 100 counts x 3219 tokens = 322k refs,
            # ~2.5MB per cascade, thousands of cascades). Past the cap, fall back
            # to per-value channel-dep evaluation for this position.
            const MaxCascadeInputRefs = 50_000
            const MaxTableHeavyCascadeChans = 2000
            if canBuild:
                var inputRefs = 0        # variable inputs (dependency-table cost)
                var tableRefs = 0        # the old count: whole element tables
                for ci in 0..<topoOrder.len:
                    case topoEntryKind[ci]
                    of ceCountEq: inputRefs += carray.countEqChannelBindings[topoBindingIdx[ci]].inputPositions.len
                    of ceWeightedCountEq: inputRefs += carray.weightedCountEqChannelBindings[topoBindingIdx[ci]].inputPositions.len
                    of ceConditionalCountEq:
                        let b {.cursor.} = carray.conditionalCountEqChannelBindings[topoBindingIdx[ci]]
                        inputRefs += b.primaryPositions.len + b.filterPositions.len + b.primaryOnlyPositions.len
                    of ceElement:
                        # Only variable inputs cost dependency-table space: a
                        # constant lookup table (reified linear comparison over a
                        # wide value range) is read, never depended on.
                        let b = addr carray.channelBindings[topoBindingIdx[ci]]
                        tableRefs += b.arrayElements.len
                        inputRefs += b.indexExpression.positions.len
                        for elem in b.arrayElements:
                            if not elem.isConstant: inc inputRefs
                    else: inputRefs += 4
                if gOldWideGuard: inputRefs = max(inputRefs, tableRefs)
                if inputRefs > MaxCascadeInputRefs:
                    canBuild = false
                # A cascade admitted only because its constant tables are no
                # longer counted must still be of moderate size: counting
                # variable inputs lets kitchen's 16 width positions (tables of
                # ~1100 constants, cascades of <= 549 channels) get cascades,
                # but it also admitted three 2300-channel cascades on sdn-chain
                # that the table count had rejected, and evaluating those for
                # every domain value on nearly every lean scan halved sdn's
                # feasible-solution rate (3/6 vs 6/6 runs in 15 s). The
                # per-value worklist fallback is the cheaper path for them.
                if tableRefs > MaxCascadeInputRefs and topoOrder.len > MaxTableHeavyCascadeChans:
                    canBuild = false
            if not canBuild or topoOrder.len == 0:
                cascadeFail += 1
                if verbose and id == 0 and cascadeFail <= 8:
                    echo "[Init]   cascade skipped at pos " & $pos & ": chans=" & $topoOrder.len &
                         " canBuild=" & $canBuild & " domain=" & $state.sharedDomain[][pos].len
                # Mark deep-cascade-failed positions as lazy to avoid per-iteration
                # full recomputation in applyUniformDelta. These positions will use
                # on-demand costDelta evaluation in bestMoves instead.
                # Only mark lazy if domain is large enough to justify skipping penalty maps.
                if topoOrder.len >= MaxCascadeChans and state.sharedDomain[][pos].len > LazyThreshold:
                    state.isLazy[pos] = true
                    inc cascadeDepthFail
                continue

            # Early-skip: if no active channel-dep constraint reads any of the
            # channels in this cascade, the cascade contributes nothing to the
            # penalty map — skip both the value precomputation and the per-cascade
            # bookkeeping. This is purely a perf optimization: the channels still
            # propagate via the global worklist; we just stop using this cascade
            # for penalty deltas.
            block earlySkipCheck:
                for chanPos in topoOrder:
                    if chanPos notin state.chanPosToDepConstraintIdx: continue
                    for ci in state.chanPosToDepConstraintIdx[chanPos]:
                        if state.channelDepConstraintActive[ci]:
                            break earlySkipCheck
                # No active constraint reads any channel in this cascade: register
                # an EMPTY cascade (all-zero penalties, no external deps). Leaving
                # the position without one sends it to the per-value worklist
                # fallback, which simulates the full channel graph for every
                # domain value on every recompute (kitchen: two 307-value
                # paddings cost 9 s of a 19 s run).
                inc noConstraintSkip
                if gNoEmptyCascade: continue
                topoOrder.setLen(0)
                topoBindingIdx.setLen(0)
                topoEntryKind.setLen(0)
                topoSet = initPackedSet[int]()
                canStatic = true

            # Build channel values
            let domain {.cursor.} = state.sharedDomain[][pos]
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
                        let idxVal = bindingPtr[].evalIndex(state.assignment)
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
            var constraintSrcCoeff: seq[tuple[l, r: T]] = @[]
            var mixedClis: seq[int] = @[]

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
                            var srcL, srcR: T
                            if state.cdConstraintCanFast[ci]:
                                for (cpos, coeff) in state.cdConstraintCoeffs[ci]:
                                    if cpos in chanToIdx:
                                        coeffsL.add((cascadeIdx: chanToIdx[cpos], coeff: coeff))
                                    elif cpos == pos:
                                        srcL += coeff
                                for (cpos, coeff) in state.cdConstraintCoeffsR[ci]:
                                    if cpos in chanToIdx:
                                        coeffsR.add((cascadeIdx: chanToIdx[cpos], coeff: coeff))
                                    elif cpos == pos:
                                        srcR += coeff
                            constraintCoeffL.add(coeffsL)
                            constraintCoeffR.add(coeffsR)
                            # Joint (direct + cascade) scoring only for the
                            # optimizer's objective bound: there the hinged
                            # scale makes split scoring inexact (kitchen). For
                            # ordinary model constraints the split scoring is
                            # kept — scoring them jointly changed the lean
                            # search's dynamics enough that sdn-chain found its
                            # feasible solution in 3/12 runs instead of 11/12.
                            let joint = (srcL != 0 or srcR != 0) and
                                (gMixedAll or state.channelDepConstraints[ci].isObjectiveBound)
                            if joint:
                                constraintSrcCoeff.add((l: srcL, r: srcR))
                                mixedClis.add(constraintLocalIds.len - 1)
                                if state.cdMixedAt.len == 0:
                                    state.cdMixedAt = newSeq[seq[tuple[ci: int, l, r: T]]](carray.len)
                                state.cdMixedAt[pos].add((ci: ci, l: srcL, r: srcR))
                            else:
                                constraintSrcCoeff.add((l: T(0), r: T(0)))

            # Build DisjunctiveClause term coefficient mapping for DC fast cascade path
            var dcTermCoeffs: seq[seq[seq[seq[tuple[coeffIdx: int, cascIdx: int]]]]] = @[]
            for cli, ci in constraintLocalIds:
                let c = state.channelDepConstraints[ci]
                if c.stateType == DisjunctiveClauseType:
                    let dc = c.disjunctiveClauseState
                    var perDisjunct: seq[seq[seq[tuple[coeffIdx: int, cascIdx: int]]]] = @[]
                    for d in 0..<dc.disjuncts.len:
                        var perTerm: seq[seq[tuple[coeffIdx: int, cascIdx: int]]] = @[]
                        for t in 0..<dc.disjuncts[d].len:
                            var termMapping: seq[tuple[coeffIdx: int, cascIdx: int]] = @[]
                            for k in 0..<dc.disjuncts[d][t].positions.len:
                                let tpos = dc.disjuncts[d][t].positions[k]
                                if tpos in chanToIdx:
                                    termMapping.add((coeffIdx: k, cascIdx: chanToIdx[tpos]))
                            perTerm.add(termMapping)
                        perDisjunct.add(perTerm)
                    dcTermCoeffs.add(perDisjunct)
                else:
                    dcTermCoeffs.add(@[])  # Empty for non-DC constraints

            # Compute external dependencies: positions read by cascade entries that
            # are outside the cascade. Separate element vs min/max deps to allow
            # fast-path when only min/max deps changed (skip element re-evaluation).
            var externalDeps: PackedSet[int]
            var elemExtDeps: PackedSet[int]
            var minMaxIndices: seq[int]
            for ci in 0..<topoOrder.len:
                case topoEntryKind[ci]
                of ceMinMax:
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
                of ceCountEq:
                    let binding = carray.countEqChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.inputPositions:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)  # treat like element deps for dirty tracking
                of ceConditionalCountEq:
                    let binding = carray.conditionalCountEqChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.primaryPositions:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)
                    for srcPos in binding.filterPositions:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)
                    for srcPos in binding.primaryOnlyPositions:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)
                of ceWeightedCountEq:
                    let binding = carray.weightedCountEqChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.inputPositions:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)
                of ceArgmax:
                    let binding = carray.argmaxChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.inputPositions.items:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)
                of ceCrossingCountMax:
                    let binding = carray.crossingCountMaxChannelBindings[topoBindingIdx[ci]]
                    for cable in binding.cables:
                        for srcPos in [cable.startPos, cable.endPos]:
                            if srcPos != pos and srcPos notin topoSet:
                                externalDeps.incl(srcPos)
                                elemExtDeps.incl(srcPos)
                    for srcPos in binding.permPositions:
                        if srcPos != pos and srcPos notin topoSet:
                            externalDeps.incl(srcPos)
                            elemExtDeps.incl(srcPos)
                of ceElement:
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
                of ceExpression:
                    let binding {.cursor.} = carray.expressionChannelBindings[topoBindingIdx[ci]]
                    for ep in binding.expression.positions.items:
                        if ep != pos and ep notin topoSet:
                            externalDeps.incl(ep)
                            elemExtDeps.incl(ep)

            let cascadeIdx = state.cdCascadeChans.len
            cascadeEntriesTotal += topoOrder.len
            state.cdCascadePos[pos] = cascadeIdx
            state.cdCascadeChans.add(topoOrder)
            state.cdCascadeBindings.add(topoBindingIdx)
            state.cdCascadeEntryKind.add(topoEntryKind)
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
                case topoEntryKind[ci]
                of ceMinMax:
                    let fb = state.flatMinMaxBindings[topoBindingIdx[ci]]
                    for lp in fb.linearPositions:
                        if lp != pos: inputs.incl(lp)
                    for expr in fb.complexExprs:
                        for ep in expr.positions.items:
                            if ep != pos: inputs.incl(ep)
                of ceCountEq:
                    let binding = carray.countEqChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.inputPositions:
                        if srcPos != pos: inputs.incl(srcPos)
                of ceConditionalCountEq:
                    let binding = carray.conditionalCountEqChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.primaryPositions:
                        if srcPos != pos: inputs.incl(srcPos)
                    for srcPos in binding.filterPositions:
                        if srcPos != pos: inputs.incl(srcPos)
                    for srcPos in binding.primaryOnlyPositions:
                        if srcPos != pos: inputs.incl(srcPos)
                of ceWeightedCountEq:
                    let binding = carray.weightedCountEqChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.inputPositions:
                        if srcPos != pos: inputs.incl(srcPos)
                of ceArgmax:
                    let binding = carray.argmaxChannelBindings[topoBindingIdx[ci]]
                    for srcPos in binding.inputPositions.items:
                        if srcPos != pos: inputs.incl(srcPos)
                of ceCrossingCountMax:
                    let binding = carray.crossingCountMaxChannelBindings[topoBindingIdx[ci]]
                    for cable in binding.cables:
                        for srcPos in [cable.startPos, cable.endPos]:
                            if srcPos != pos: inputs.incl(srcPos)
                    for srcPos in binding.permPositions:
                        if srcPos != pos: inputs.incl(srcPos)
                of ceElement:
                    let bindingPtr = addr carray.channelBindings[topoBindingIdx[ci]]
                    for ipos in bindingPtr.indexExpression.positions.items:
                        if ipos != pos: inputs.incl(ipos)
                    for elem in bindingPtr.arrayElements:
                        if not elem.isConstant and elem.variablePosition != pos:
                            inputs.incl(elem.variablePosition)
                of ceExpression:
                    let binding {.cursor.} = carray.expressionChannelBindings[topoBindingIdx[ci]]
                    for ep in binding.expression.positions.items:
                        if ep != pos: inputs.incl(ep)
                # Register in posToReaders (cascade-internal deps) and extPosToEntries
                for p in inputs.items:
                    if p in topoSet:
                        posToReaders.mgetOrPut(p, @[]).add(ci)
                    else:
                        extPosToEntries.mgetOrPut(p, @[]).add(ci)
            # Build forward deps: from entry ci to entries that read chans[ci]
            var forwardDeps = newSeq[seq[int]](topoOrder.len)
            var hasBackEdge = false
            for ci in 0..<topoOrder.len:
                if topoOrder[ci] in posToReaders:
                    forwardDeps[ci] = posToReaders[topoOrder[ci]]
                    for r in forwardDeps[ci]:
                        if r <= ci: hasBackEdge = true
            if nSrcReaders < 0: nSrcReaders = topoOrder.len
            state.cdCascadeNSrcReaders.add(nSrcReaders)
            state.cdCascadeHasBackEdge.add(hasBackEdge or gNoSparseCascade)
            block:
                var entryCons = newSeq[seq[int]](topoOrder.len)
                for cli, dci in constraintLocalIds:
                    for p in state.channelDepConstraints[dci].positions.items:
                        if p in chanToIdx:
                            entryCons[chanToIdx[p]].add(cli)
                state.cdCascadeEntryCons.add(entryCons)
                var singleIdx = newSeq[int](constraintLocalIds.len)
                for cli, dci in constraintLocalIds:
                    let sp = state.cdSinglePos[dci]
                    singleIdx[cli] = if sp >= 0 and sp in chanToIdx: chanToIdx[sp] else: -1
                state.cdCascadeSingleIdx.add(singleIdx)
                # Constraint inputs outside the cascade (other than the source):
                # when one changes, per-value deltas change non-uniformly, so the
                # uniform-delta shortcut in applyUniformDelta is not exact.
                # Only tracked with circuit-time chains, whose writebacks change
                # such inputs on every successor move; elsewhere the extra full
                # recomputes cost ~3x throughput (sparse_mds) for little gain.
                var consExt: PackedSet[int]
                if (state.circuitTimePropConstraints.len > 0 and not gNoExactCascadeExt) or
                   gExactCascadeExt:
                    for dci in constraintLocalIds:
                        for p in state.channelDepConstraints[dci].positions.items:
                            if p != pos and p notin topoSet: consExt.incl(p)
                    # Reverse index: a change at any read-but-not-reached position must
                    # refresh this source's penalties (reachability alone misses it).
                    for p in consExt.items:
                        state.cdReadersOf.mgetOrPut(p, @[]).add(pos)
                    for p in externalDeps.items:
                        if p notin consExt:
                            state.cdReadersOf.mgetOrPut(p, @[]).add(pos)
                state.cdCascadeConsExt.add(consExt)
                for p in externalDeps.items:
                    state.cdExtReadersOf.mgetOrPut(p, @[]).add(pos)
            state.cdCascadeForwardDeps.add(forwardDeps)
            state.cdCascadeExtPosToEntries.add(extPosToEntries)
            # Allocate cache for this cascade
            state.cdCascadeCachedValues.add(newSeq[seq[T]](topoOrder.len))
            for ci in 0..<topoOrder.len:
                state.cdCascadeCachedValues[^1][ci] = newSeq[T](domain.len)
            state.cdCascadeValues.add(chanValues)
            state.cdCascadeIsStatic.add(canStatic)
            state.cdCascadeConstraintIds.add(constraintLocalIds)
            state.cdCascadeSrcPos.add(pos)
            state.cdCascadeSrcCoeff.add(constraintSrcCoeff)
            state.cdCascadeMixedClis.add(mixedClis)
            state.cdCascadeDCTermCoeffs.add(dcTermCoeffs)
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
                 " dynamic / " & $(staticCount + dynamicCount + cascadeFail + noConstraintSkip) &
                 " positions (fail=" & $cascadeFail & " depthFail=" & $cascadeDepthFail &
                 " noCons=" & $noConstraintSkip &
                 (if binaryCascadesSkipped > 0: " binarySkipped=" & $binaryCascadesSkipped else: "") &
                 " avg_chans=" & $(totalChans div max(1, staticCount + dynamicCount)) &
                 " mem=" & $(totalMem div 1024) & "KB" &
                 " extDeps: elemExt=" & $elemExtCount & " mmOnlyExt=" & $mmExtCount &
                 " noExt=" & $noExtCount &
                 " built in " & $(epochTime() - cascadeStart) & "s)"
            logInitRss("Cascade tables")
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
            stderr.writeLine("[Init] Cascade size distribution:")
            var sizes: seq[int]
            for s in sizeHist.keys: sizes.add(s)
            algorithm.sort(sizes)
            for s in sizes:
                stderr.writeLine("[Init]   " & $s & " chans: " & $sizeHist[s] & " cascades")
            stderr.writeLine("[Init] Max cascade: " & $maxChansCnt & " chans at pos " & $maxChansPos &
                 " max_constraints=" & $maxConstraints)

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
    state.cdCacheStamp = newSeq[int](carray.len)
    for i in 0..<carray.len: state.cdCacheStamp[i] = -1
    state.cdCacheDirty = newSeq[int](carray.len)
    state.cdMoveSeq = 0
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
            logInitRss("Channel-dep penalties computed")

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
        # Exception 1: constraints that reference aggregate channel positions
        # (countEq, conditionalCountEq, argmax) are never marked tautological.
        # Exception 2: when NO cascade was built for any position, skip tautological
        # filtering entirely. Without cascades, the per-move delta evaluation depends
        # on the initial random assignment which may sit on a plateau where no single
        # move helps. After a few moves the assignment may change enough that
        # previously-zero-delta constraints become relevant. Deep channel chains
        # (e.g., temporal boolean OR chains) are especially prone to this.
        if state.hasChannelDeps and state.cdCascadePos.len == 0:
            if verbose and id == 0:
                echo "[Init] Skipping tautological filtering (no cascades — deep channel chains)"
        elif state.hasChannelDeps and state.circuitTimePropConstraints.len > 0:
            # CircuitTimeProp writes its time/accumulator positions back after a
            # move, outside the channel graph the cascades see: constraints
            # downstream of those positions show zero delta at init yet become
            # violated once the tour changes. Disabling them hides real violations.
            if verbose and id == 0:
                echo "[Init] Skipping tautological filtering (circuit-time writeback channels)"
        elif state.hasChannelDeps:
            # Build set of aggregate channel positions for tautology exclusion
            var aggregateChannelPositions: PackedSet[int]
            for binding in carray.countEqChannelBindings:
                aggregateChannelPositions.incl(binding.channelPosition)
            for binding in carray.weightedCountEqChannelBindings:
                aggregateChannelPositions.incl(binding.channelPosition)
            for binding in carray.conditionalCountEqChannelBindings:
                aggregateChannelPositions.incl(binding.channelPosition)
            for binding in carray.argmaxChannelBindings:
                aggregateChannelPositions.incl(binding.channelPosition)

            # Count how many cascades reach each constraint. A constraint reachable
            # from multiple search positions can be violated by a SEQUENCE of moves
            # even when no SINGLE move from the initial state changes its penalty.
            # Marking such a constraint tautological hides genuine violations once
            # the search drifts away from the initial assignment. Only constraints
            # reachable from a single cascade are safe to disable based on init-time
            # single-step delta evaluation.
            var cascadeCount = newSeq[int](state.channelDepConstraints.len)
            for cascadeIdx in 0..<state.cdCascadeConstraintIds.len:
                for ci in state.cdCascadeConstraintIds[cascadeIdx]:
                    cascadeCount[ci] += 1

            var tautCount = 0
            var tautSkippedMultiCascade = 0
            for ci in 0..<state.channelDepConstraints.len:
                if state.cdPerConstraintMaxDelta[ci] == 0:
                    # Check if constraint references any aggregate channel position
                    var touchesAggregate = false
                    for p in state.channelDepConstraints[ci].positions.items:
                        if p in aggregateChannelPositions:
                            touchesAggregate = true
                            break
                    if touchesAggregate:
                        continue  # Don't disable — aggregate channels can become non-tautological
                    if cascadeCount[ci] >= 2:
                        tautSkippedMultiCascade += 1
                        continue  # Multiple search positions reach this — multi-step changes can violate it
                    state.channelDepConstraintActive[ci] = false
                    tautCount += 1
            if tautCount > 0 or tautSkippedMultiCascade > 0:
                if verbose and id == 0:
                    echo "[Init] Disabled " & $tautCount & "/" & $state.channelDepConstraints.len &
                         " tautological channel-dep constraints (zero delta across all moves" &
                         (if tautSkippedMultiCascade > 0: "; kept " & $tautSkippedMultiCascade & " multi-cascade" else: "") & ")"
                    var tautByType, activeByType: array[StatefulConstraintType, int]
                    for ci in 0..<state.channelDepConstraints.len:
                        let ct = state.channelDepConstraints[ci].stateType
                        if state.channelDepConstraintActive[ci]:
                            activeByType[ct] += 1
                        else:
                            tautByType[ct] += 1
                    for ct in StatefulConstraintType:
                        if tautByType[ct] > 0 or activeByType[ct] > 0:
                            stderr.writeLine("[Init]   " & $ct & ": active=" & $activeByType[ct] & " taut=" & $tautByType[ct])
                if tautCount == state.channelDepConstraints.len:
                    state.hasChannelDeps = false

    # Initialize element implied structures before penalty map so discounts are included
    state.initElementImpliedStructures()
    state.initReverseElementImpliedStructures()
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
        logInitRss("Built penalty map")
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
        # Detect alldifferent-as-permutation: domain union size == num search positions
        if constraint.stateType == AllDifferentType:
            var groupPositions: seq[int]
            var domainUnion = initPackedSet[int]()
            for pos in constraint.positions.items:
                if pos notin carray.channelPositions:
                    groupPositions.add(pos)
                    for v in state.sharedDomain[][pos]:
                        domainUnion.incl(v)
            if groupPositions.len >= 2 and domainUnion.len == groupPositions.len:
                state.gccGroupPositions.add(groupPositions)
    # Build sharedConstraints for all position pairs within GCC/permutation groups
    # so that swapDelta can compute accurate joint deltas. The table holds one
    # entry per pair: a single 5000-position group is 12.5M entries (gigabytes
    # per worker), so cap it; swapDelta falls back to independent deltas for
    # pairs it does not find, and the GCC swap path uses exactSwapDelta anyway.
    const MaxGccSharedPairs = 300_000
    var gccPairTotal = 0
    for group in state.gccGroupPositions:
        gccPairTotal += group.len * (group.len - 1) div 2
    if state.gccGroupPositions.len > 0 and gccPairTotal > MaxGccSharedPairs:
        if verbose and id == 0:
            echo "[Init] GCC swap groups: " & $state.gccGroupPositions.len & " groups, " &
                $gccPairTotal & " pairs exceed shared-constraint table cap; pair table skipped"
    if state.gccGroupPositions.len > 0 and gccPairTotal <= MaxGccSharedPairs:
        var groupPosSet = initPackedSet[int]()
        for group in state.gccGroupPositions:
            for pos in group:
                groupPosSet.incl(pos)
        for constraint in state.constraints:
            var posInGroups: seq[int]
            for pos in constraint.positions.items:
                if pos in groupPosSet:
                    posInGroups.add(pos)
            if posInGroups.len >= 2:
                for i in 0..<posInGroups.len:
                    for j in (i+1)..<posInGroups.len:
                        let p1 = posInGroups[i]
                        let p2 = posInGroups[j]
                        let key = if p1 < p2: (p1, p2) else: (p2, p1)
                        if key notin state.sharedConstraints:
                            state.sharedConstraints[key] = @[constraint]
                        else:
                            # Avoid duplicates
                            var found = false
                            for existing in state.sharedConstraints[key]:
                                if cast[pointer](existing) == cast[pointer](constraint):
                                    found = true; break
                            if not found:
                                state.sharedConstraints[key].add(constraint)
        # Adaptive swap evaluation budget: scale with group count
        let avgGroupSize = state.gccGroupPositions.mapIt(it.len).foldl(a + b, 0) div max(1, state.gccGroupPositions.len)
        state.maxPermSwapEvals = min(2000, max(500, state.gccGroupPositions.len * avgGroupSize div 3))

        if verbose and id == 0:
            echo "[Init] GCC swap groups: " & $state.gccGroupPositions.len & " groups, avg size " &
                $avgGroupSize &
                ", shared constraint pairs: " & $state.sharedConstraints.len &
                ", swap budget: " & $state.maxPermSwapEvals

    # Initialize partition swap structures
    state.partitionGroups = carray.partitionGroups
    state.partitionEnabled = state.partitionGroups.len > 0
    if state.partitionEnabled and verbose and id == 0:
        echo "[Init] Partition groups: " & $state.partitionGroups.len &
             " groups, members: " & state.partitionGroups.mapIt($it.searchPositions.len).join("/")

    # Channel-only inequality repair: greedy 1/2/3-flip pre-pass on graduated `≥`/`≤`
    # bounds whose SumExpr has no search-position term (e.g. bin-packing capacity
    # bounds emitted by the implicit-lin-eq detector with all indicator-product
    # channel inputs). The default init strategy gives every preference its
    # domain-min value, which on tightly-packed instances starts the search 50+
    # cost units in the hole; this pass uses costDelta + assignValue to greedy
    # down to a near-feasible state before tabu starts.
    #
    # Gated on `enableChannelInequalityRepair`, set only by the implicit-lin-eq
    # translator pass when it actually emits range bounds. Without the gate the
    # pass triggers on any model with a channel-only `≥`/`≤` constraint
    # (counters, indicator-sum bounds), where the greedy descent destabilises
    # search and regresses ~20 mznchallenge tests.
    # Skipped for path-relinking states which have their own seed assignment.
    if not forRelinking and initialAssignment.len == 0 and
            carray.enableChannelInequalityRepair:
        state.repairChannelInequalities(verbose, id, deadline)
        # Capture the post-repair state as the new best so tabu's main loop
        # doesn't start tracking improvements from the pre-repair value.
        if state.cost <= state.bestCost:
            state.bestCost = state.cost
            state.bestAssignment = state.assignment


proc newTabuState*[T](carray: ConstrainedArray[T], verbose: bool = false, id: int = 0, initStrategy: InitStrategy = isRandom, deadline: float = 0.0): TabuState[T] =
    new(result)
    result.init(carray, verbose, id, initStrategy = initStrategy, deadline = deadline)

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
    ## Uses an inWorklist set (not visited set) to avoid duplicate entries while
    ## allowing positions to be re-enqueued when their value changes through
    ## different dependency paths (e.g., multi-layer set comprehension cascades).
    changedChannels.setLen(0)
    if not state.anyChannels:
        return false
    var worklist = @[position]
    var inWorklist: PackedSet[int]
    inWorklist.incl(position)

    while worklist.len > 0:
        let pos = worklist.pop()
        # Source of this propagation (set by assignValue*): wide count channels
        # update incrementally. Consumed on first use so it can't apply twice.
        let srcInc = pos == state.propSrcPos
        let srcOld = state.propSrcOld
        if srcInc: state.propSrcPos = -1
        inWorklist.excl(pos)
        # Element channel bindings
        if pos in state.carray.channelsAtPosition:
            for bi in state.carray.channelsAtPosition[pos]:
                let bindingPtr = addr state.carray.channelBindings[bi]
                let idxVal = bindingPtr[].evalIndex(state.assignment)
                var newVal: T
                if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                    let elem = bindingPtr.arrayElements[idxVal]
                    newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition] + elem.offset
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
                    # Skip per-change penalty updates for offset channels (visit-time
                    # backward chains) to avoid O(n²) cascade re-evaluations. These
                    # are handled by recomputeAffectedChannelDepPenalties in assignValue.
                    if not bindingPtr.hasOffset:
                        state.updateNeighborPenalties(bindingPtr.channelPosition)
                    if bindingPtr.channelPosition notin inWorklist:
                        inWorklist.incl(bindingPtr.channelPosition)
                        worklist.add(bindingPtr.channelPosition)
        # Min/max channel bindings
        if pos in state.carray.minMaxChannelsAtPosition:
            for bi in state.carray.minMaxChannelsAtPosition[pos]:
                let fb {.cursor.} = state.flatMinMaxBindings[bi]
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
                    if fb.channelPosition notin inWorklist:
                        inWorklist.incl(fb.channelPosition)
                        worklist.add(fb.channelPosition)
        # Count-equals channel bindings
        if pos in state.carray.countEqChannelsAtPosition:
            for bi in state.carray.countEqChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.countEqChannelBindings[bi]
                let newVal = if srcInc: state.countEqAfterSrc(bi, pos, srcOld)
                             else: evaluateCountEq(binding, state.assignment)
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
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Weighted count-equals channel bindings
        if pos in state.carray.weightedCountEqChannelsAtPosition:
            for bi in state.carray.weightedCountEqChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bi]
                let newVal = if srcInc: state.wCountEqAfterSrc(bi, pos, srcOld)
                             else: evaluateWeightedCountEq(binding, state.assignment)
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
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Conditional count-equals channel bindings
        if pos in state.carray.conditionalCountEqChannelsAtPosition:
            for bi in state.carray.conditionalCountEqChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bi]
                let newVal = evaluateConditionalCountEq(binding, state.assignment)
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
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Argmax channel bindings
        if pos in state.carray.argmaxChannelsAtPosition:
            for bi in state.carray.argmaxChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.argmaxChannelBindings[bi]
                let newVal = evaluateArgmax(binding, state.assignment)
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
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Crossing count max channel bindings
        if pos in state.carray.crossingCountMaxChannelsAtPosition:
            for bi in state.carray.crossingCountMaxChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.crossingCountMaxChannelBindings[bi]
                let newVal = evaluateCrossingCountMax(binding, state.assignment)
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
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Inverse channel bindings: recompute inverse from forward assignments
        if pos in state.carray.inverseChannelsAtPosition:
            for gi in state.carray.inverseChannelsAtPosition[pos]:
                let group {.cursor.} = state.carray.inverseChannelGroups[gi]
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
                        if ipos notin inWorklist:
                            inWorklist.incl(ipos)
                            worklist.add(ipos)
        # Expression channel bindings
        if pos in state.carray.expressionChannelsAtPosition:
            for bi in state.carray.expressionChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.expressionChannelBindings[bi]
                let newVal = binding.evalExpr(state.assignment)
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
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)

proc cdMarkDirtyAt[T](state: TabuState[T], p: int) {.inline.} =
    ## A value at p changed: cascades reading p from outside are stale.
    if state.cdExtReadersOf.len == 0 or state.cdCacheDirty.len == 0: return
    state.cdExtReadersOf.withValue(p, readers):
        for q in readers[]: state.cdCacheDirty[q] = state.cdMoveSeq

proc propagateChannelsLean[T](state: TabuState[T], position: int) =
    ## Lightweight channel propagation: updates constraint state and cost
    ## but skips penalty map updates entirely. For use during path relinking.
    if not state.anyChannels:
        return
    var worklist = @[position]
    var inWorklist: PackedSet[int]
    inWorklist.incl(position)

    while worklist.len > 0:
        let pos = worklist.pop()
        if pos != position: state.cdMarkDirtyAt(pos)
        # Source of this propagation (set by assignValue*): wide count channels
        # update incrementally. Consumed on first use so it can't apply twice.
        let srcInc = pos == state.propSrcPos
        let srcOld = state.propSrcOld
        if srcInc: state.propSrcPos = -1
        inWorklist.excl(pos)
        # Element channel bindings
        if pos in state.carray.channelsAtPosition:
            for bi in state.carray.channelsAtPosition[pos]:
                let bindingPtr = addr state.carray.channelBindings[bi]
                let idxVal = bindingPtr[].evalIndex(state.assignment)
                var newVal: T
                if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                    let elem = bindingPtr.arrayElements[idxVal]
                    newVal = if elem.isConstant: elem.constantValue
                             else: state.assignment[elem.variablePosition] + elem.offset
                else:
                    continue
                if newVal != state.assignment[bindingPtr.channelPosition]:
                    state.assignment[bindingPtr.channelPosition] = newVal
                    for c in state.constraintsAtPosition[bindingPtr.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(bindingPtr.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if bindingPtr.channelPosition notin inWorklist:
                        inWorklist.incl(bindingPtr.channelPosition)
                        worklist.add(bindingPtr.channelPosition)
        # Min/max channel bindings
        if pos in state.carray.minMaxChannelsAtPosition:
            for bi in state.carray.minMaxChannelsAtPosition[pos]:
                let fb {.cursor.} = state.flatMinMaxBindings[bi]
                let newVal = evaluateFlatMinMax(fb, state.assignment)
                if newVal != state.assignment[fb.channelPosition]:
                    state.assignment[fb.channelPosition] = newVal
                    for c in state.constraintsAtPosition[fb.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(fb.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if fb.channelPosition notin inWorklist:
                        inWorklist.incl(fb.channelPosition)
                        worklist.add(fb.channelPosition)
        # Count-equals channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.countEqChannelsAtPosition:
            for bi in state.carray.countEqChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.countEqChannelBindings[bi]
                let newVal = if srcInc: state.countEqAfterSrc(bi, pos, srcOld)
                             else: evaluateCountEq(binding, state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Weighted count-equals channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.weightedCountEqChannelsAtPosition:
            for bi in state.carray.weightedCountEqChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bi]
                let newVal = if srcInc: state.wCountEqAfterSrc(bi, pos, srcOld)
                             else: evaluateWeightedCountEq(binding, state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Conditional count-equals channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.conditionalCountEqChannelsAtPosition:
            for bi in state.carray.conditionalCountEqChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bi]
                let newVal = evaluateConditionalCountEq(binding, state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Argmax channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.argmaxChannelsAtPosition:
            for bi in state.carray.argmaxChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.argmaxChannelBindings[bi]
                let newVal = evaluateArgmax(binding, state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Crossing count max channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.crossingCountMaxChannelsAtPosition:
            for bi in state.carray.crossingCountMaxChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.crossingCountMaxChannelBindings[bi]
                let newVal = evaluateCrossingCountMax(binding, state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)
        # Inverse channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.inverseChannelsAtPosition:
            for gi in state.carray.inverseChannelsAtPosition[pos]:
                let group {.cursor.} = state.carray.inverseChannelGroups[gi]
                let newInverse = group.recomputeInverse(state.assignment)
                for j, ipos in group.inversePositions:
                    if newInverse[j] != state.assignment[ipos]:
                        state.assignment[ipos] = newInverse[j]
                        for c in state.constraintsAtPosition[ipos]:
                            let oldPenalty = c.penalty()
                            c.updatePosition(ipos, newInverse[j])
                            let newPenalty = c.penalty()
                            state.cost += newPenalty - oldPenalty
                        if ipos notin inWorklist:
                            inWorklist.incl(ipos)
                            worklist.add(ipos)
        # Expression channel bindings (lean: no penalty maps or violationCount)
        if pos in state.carray.expressionChannelsAtPosition:
            for bi in state.carray.expressionChannelsAtPosition[pos]:
                let binding {.cursor.} = state.carray.expressionChannelBindings[bi]
                let newVal = binding.evalExpr(state.assignment)
                if newVal != state.assignment[binding.channelPosition]:
                    state.assignment[binding.channelPosition] = newVal
                    for c in state.constraintsAtPosition[binding.channelPosition]:
                        let oldPenalty = c.penalty()
                        c.updatePosition(binding.channelPosition, newVal)
                        let newPenalty = c.penalty()
                        state.cost += newPenalty - oldPenalty
                    if binding.channelPosition notin inWorklist:
                        inWorklist.incl(binding.channelPosition)
                        worklist.add(binding.channelPosition)

proc writebackCircuitTimes[T](state: TabuState[T], position: int,
                              forced: openArray[(int, int, int)],
                              changedBuf: var seq[int]) =
    ## Copy computed arrival/departure times from CircuitTimeProp constraints
    ## touched by this move (directly or via inverse forced changes) into the
    ## assignment. Collects the positions whose value actually changed into
    ## changedBuf (cleared first) and updates constraints listening on them,
    ## mirroring channel-binding propagation semantics. Callers must then
    ## propagate channels from the changed positions so downstream channels
    ## (e.g. an objective max over arrival times) stay consistent.
    changedBuf.setLen(0)
    for ctc in state.circuitTimePropConstraints:
        var touched = position in ctc.positions
        if not touched:
            for (fPos, fOld, fNew) in forced:
                if fPos in ctc.positions:
                    touched = true
                    break
        if not touched: continue
        for i in 0..<ctc.n:
            if ctc.arrivalPositions[i] >= 0:
                let p = ctc.arrivalPositions[i]
                if state.assignment[p] != ctc.arrivalTime[i]:
                    state.assignment[p] = ctc.arrivalTime[i]
                    changedBuf.add(p)
            if ctc.departurePositions[i] >= 0:
                let p = ctc.departurePositions[i]
                if state.assignment[p] != ctc.departureTime[i]:
                    state.assignment[p] = ctc.departureTime[i]
                    changedBuf.add(p)
    for p in changedBuf:
        for c in state.constraintsAtPosition[p]:
            let oldPenalty = c.penalty()
            c.updatePosition(p, state.assignment[p])
            let newPenalty = c.penalty()
            state.cost += newPenalty - oldPenalty
            if oldPenalty > 0 and newPenalty == 0:
                for pos in c.positions.items:
                    state.violationCount[pos] -= 1
            elif oldPenalty == 0 and newPenalty > 0:
                for pos in c.positions.items:
                    state.violationCount[pos] += 1

proc assignValueLean*[T](state: TabuState[T], position: int, value: T) =
    ## Lightweight assignment: updates constraint state and cost but skips
    ## penalty map updates. Used during path relinking for fast traversal.
    let oldValueLean = state.assignment[position]
    state.assignment[position] = value
    inc state.cdMoveSeq
    state.cdMarkDirtyAt(position)

    for constraint in state.constraintsAtPosition[position]:
        let oldPenalty = constraint.penalty()
        constraint.updatePosition(position, value)
        let newPenalty = constraint.penalty()
        state.cost += newPenalty - oldPenalty
        # Maintain violationCount so swap move filters remain accurate
        if oldPenalty > 0 and newPenalty == 0:
            for pos in constraint.positions.items:
                state.violationCount[pos] -= 1
        elif oldPenalty == 0 and newPenalty > 0:
            for pos in constraint.positions.items:
                state.violationCount[pos] += 1

    # Apply forced changes from inverse group compound move
    let hasInverseMoveLean = state.inverseEnabled and state.posToInverseGroup[position] >= 0
    if hasInverseMoveLean:
        state.computeInverseForcedChanges(position, value, oldValueLean, oldValueProvided = true)
        # Safe to iterate inverseForcedChanges directly: propagateChannelsLean doesn't modify it
        for (fPos, fOld, fNew) in state.inverseForcedChanges:
            state.assignment[fPos] = T(fNew)
            state.cdMarkDirtyAt(fPos)
            for constraint in state.constraintsAtPosition[fPos]:
                let oldPenalty = constraint.penalty()
                constraint.updatePosition(fPos, T(fNew))
                let newPenalty = constraint.penalty()
                state.cost += newPenalty - oldPenalty
                if oldPenalty > 0 and newPenalty == 0:
                    for pos in constraint.positions.items:
                        state.violationCount[pos] -= 1
                elif oldPenalty == 0 and newPenalty > 0:
                    for pos in constraint.positions.items:
                        state.violationCount[pos] += 1
            state.propagateChannelsLean(fPos)

    if not hasInverseMoveLean:
        state.propSrcPos = position
        state.propSrcOld = oldValueLean
    state.propagateChannelsLean(position)
    state.propSrcPos = -1

    # Circuit-time-prop writeback (lean path): copy computed times to assignment
    # positions and propagate downstream channels (e.g. objective max channels).
    if state.circuitTimePropConstraints.len > 0:
        if hasInverseMoveLean:
            state.writebackCircuitTimes(position, state.inverseForcedChanges, state.ctpChangedBuf)
        else:
            state.writebackCircuitTimes(position, [], state.ctpChangedBuf)
        for tp in state.ctpChangedBuf: state.cdMarkDirtyAt(tp)
        for tp in state.ctpChangedBuf:
            state.propagateChannelsLean(tp)

proc assignValue*[T](state: TabuState[T], position: int, value: T) =
    when ProfileIteration:
        let t0 = epochTime()

    let oldValueAssign = state.assignment[position]
    state.assignment[position] = value
    inc state.cdMoveSeq
    state.cdMarkDirtyAt(position)
    if gTraceMoves and state.id == 0 and state.iteration < 400:
        echo "[Trace] S0 it=" & $state.iteration & " pos=" & $position & " " & $oldValueAssign & "->" & $value & " cost=" & $state.cost

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
    if not hasInverseMove:
        state.propSrcPos = position
        state.propSrcOld = oldValueAssign
    discard state.propagateChannels(position, state.changedChannelsBuf)
    state.propSrcPos = -1

    # Also propagate channels for forced positions (using pre-allocated buffer)
    if hasInverseMove:
        for (fPos, fOld, fNew) in localForced:
            let forcedChanged = state.propagateChannels(fPos, state.forcedChannelsBuf2)
            if forcedChanged:
                for ch in state.forcedChannelsBuf2:
                    state.changedChannelsBuf.add(ch)

    # Circuit-time-prop writeback: copy computed times to assignment positions
    # and propagate downstream channels (e.g. objective max over arrival times).
    if state.circuitTimePropConstraints.len > 0:
        state.writebackCircuitTimes(position, localForced, state.ctpChangedBuf)
        for tp in state.ctpChangedBuf:
            # Constraints reading the written-back position directly also hold
            # search positions whose penalty maps must follow (as for channels).
            state.updateNeighborPenalties(tp)
            state.changedChannelsBuf.add(tp)
            let tpChanged = state.propagateChannels(tp, state.forcedChannelsBuf2)
            if tpChanged:
                for ch in state.forcedChannelsBuf2:
                    state.changedChannelsBuf.add(ch)

    when ProfileIteration:
        let tProp1 = epochTime()
        state.timePropagateChannels += tProp1 - tProp0
        state.propagateChannelCalls += 1
        state.channelChangesTotal += state.changedChannelsBuf.len

    let anyChannelsChanged = state.changedChannelsBuf.len > 0
    for ch in state.changedChannelsBuf: state.cdMarkDirtyAt(ch)
    if hasInverseMove:
        for (fPos, fOld, fNew) in localForced: state.cdMarkDirtyAt(fPos)

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

    # Apply reverse element implied moves: when channels changed, try to re-point
    # index variables (e.g., parent) to restore element constraint satisfaction.
    if state.reverseElementImpliedEnabled and anyChannelsChanged:
        {.cast(gcsafe).}:
            state.applyReverseElementImpliedMoves()

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

    # Channel neighbor penalty updates are handled by the cascade-dep system
    # (which simulates channel changes during penalty map evaluation) rather
    # than explicitly updating after each propagation. This avoids O(n²)
    # re-evaluations when many channels change per move.

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
            let oldIdx = if lazy1: -1 else: state.domIdx(position, oldValue)
            if not lazy1 and oldIdx < 0:
                continue

            if state.violationCount[position] == 0 and
               state.channelDepPenalties[position].len == 0:
                continue

            if state.hasDormancy and state.isDormant[position]:
                continue

            inc positionsChecked

            let domain {.cursor.} = state.sharedDomain[][position]
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
                let pmRow {.cursor.} = state.penaltyMap[position]
                let tabuRow {.cursor.} = state.tabu[position]
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
                        newCost = state.cost + pmRow[i]
                        if hasInverse1:
                            newCost += state.inverseDelta[position][i]
                    if lazy1 or tabuRow[i] <= state.iteration or newCost < state.bestCost:
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
            let oldIdx = if lazy2: -1 else: state.domIdx(position, oldValue)
            if not lazy2 and oldIdx < 0:
                continue

            if state.violationCount[position] == 0 and
               state.channelDepPenalties[position].len == 0:
                continue

            if state.hasDormancy and state.isDormant[position]:
                continue

            let domain {.cursor.} = state.sharedDomain[][position]
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
                let pmRow {.cursor.} = state.penaltyMap[position]
                let tabuRow {.cursor.} = state.tabu[position]
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
                        newCost = state.cost + pmRow[i]
                        if hasInverse2:
                            newCost += state.inverseDelta[position][i]
                    if lazy2 or tabuRow[i] <= state.iteration or newCost < state.bestCost:
                        if newCost < bestMoveCost:
                            result = @[(position, domain[i])]
                            bestMoveCost = newCost
                        elif newCost == bestMoveCost:
                            result.add((position, domain[i]))
            else:
                let pmRow {.cursor.} = state.penaltyMap[position]
                let tabuRow {.cursor.} = state.tabu[position]
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
                        newCost = state.cost + pmRow[i]
                        if hasInverse2:
                            newCost += state.inverseDelta[position][i]
                    if lazy2 or tabuRow[i] <= state.iteration or newCost < state.bestCost:
                        if newCost < bestMoveCost:
                            result = @[(position, domain[i])]
                            bestMoveCost = newCost
                        elif newCost == bestMoveCost:
                            result.add((position, domain[i]))

    state.movesExplored = movesEvaluated


proc applyFirstImprovingMove[T](state: TabuState[T]) {.inline.} =
    ## Lean first-improvement move: evaluate via costDelta (no penalty map reads),
    ## apply via assignValueLean (no penalty map rebuild). Much faster for problems
    ## with large channel-dep cascades where penalty map maintenance dominates.
    var bestDelta = high(int)
    var bestPos = -1
    var bestVal: T
    shuffle(state.searchPositions)
    var posChecked = 0

    for position in state.searchPositions:
        if state.onValidCtpCircuit(position): continue
        let oldValue = state.assignment[position]
        # Skip non-violated positions (use constraint state directly, no violationCount)
        var isViolated = false
        for c in state.constraintsAtPosition[position]:
            if c.penalty() > 0:
                isViolated = true; break
        if not isViolated and
           (position >= state.channelDepPenalties.len or state.channelDepPenalties[position].len == 0):
            continue

        inc posChecked
        let domain {.cursor.} = state.sharedDomain[][position]
        # Batch the channel-dep deltas once per position: one cascade pass
        # fills channelDepPenalties[position] for every domain value, instead
        # of simulating the full cascade per candidate value in costDelta.
        let hasChanDep = state.hasChannelDeps and
            position < state.channelDepPenalties.len and
            state.channelDepPenalties[position].len > 0
        if hasChanDep:
            if not gNoCdStamp and not gNoCacheRescore and state.cdCascadeCacheValid(position):
                when ProfileIteration: inc state.cdLeanRescore
                state.rescoreCascadeFromCache(position)
            else:
                when ProfileIteration: inc state.cdLeanFull
                state.computeChannelDepPenaltiesAt(position)
        for di in 0..<domain.len:
            let value = domain[di]
            if value == oldValue: continue

            # Tabu check
            let dIdx = state.domIdx(position, value)
            if dIdx >= 0 and not state.isLazy[position] and
               state.tabu[position][dIdx] > state.iteration and
               bestDelta >= state.bestCost - state.cost:
                continue  # tabu and no aspiration

            var delta = 0
            for constraint in state.constraintsAtPosition[position]:
                delta += state.movePenalty(constraint, position, value)
            if hasChanDep:
                delta += state.channelDepPenalties[position][di]
            if state.inverseEnabled and state.posToInverseGroup[position] >= 0:
                delta += state.computeInverseDeltaAt(position, value)
            if delta < bestDelta:
                bestDelta = delta
                bestPos = position
                bestVal = value
                if delta < 0:
                    break  # first improvement found, stop domain scan

        if bestDelta < 0:
            break  # first improvement found, stop position scan
        if posChecked >= 50:
            break  # cap positions checked

    # Also evaluate permutation swaps
    if state.gccGroupPositions.len > 0 and
       (state.cost <= state.gccGroupPositions.len div 5 or state.iteration mod 3 == 0):
        let (permMoves, permCost) = state.bestPermutationSwapMoves()
        if permMoves.len > 0 and permCost < state.cost + bestDelta:
            # Apply swap
            inc state.permSwapApplied
            let (pp1, pp2, pnv1, pnv2) = sample(permMoves)
            let pov1 = state.assignment[pp1]
            let pov2 = state.assignment[pp2]
            state.assignValueLean(pp1, pnv1)
            state.assignValueLean(pp2, pnv2)
            let tabuTenure = state.iteration + 1 + state.iteration mod 10
            let oi1 = state.domIdx(pp1, pov1)
            if oi1 >= 0 and not state.isLazy[pp1]: state.tabu[pp1][oi1] = tabuTenure
            let oi2 = state.domIdx(pp2, pov2)
            if oi2 >= 0 and not state.isLazy[pp2]: state.tabu[pp2][oi2] = tabuTenure
            state.applyElementImpliedMoves(pp1)
            state.applyElementImpliedMoves(pp2)
            return

    if bestPos >= 0:
        let oldValue = state.assignment[bestPos]
        let costBefore = state.cost
        state.assignValueLean(bestPos, bestVal)
        if gCheckDelta and state.cost - costBefore != bestDelta:
            # Debug (CRUSHER_CHECK_DELTA): predicted move delta disagrees with the
            # actual cost change -> a move-evaluation path is inexact.
            inc state.deltaMismatches
            if state.deltaMismatches <= 20:
                echo "[CheckDelta] S" & $state.id & " it=" & $state.iteration & " pos=" & $bestPos &
                     " " & $oldValue & "->" & $bestVal & " predicted=" & $bestDelta &
                     " actual=" & $(state.cost - costBefore)
            if state.deltaMismatches <= 5:
                # Per-constraint attribution: revert, snapshot, re-apply, diff.
                var before = newSeq[int](state.constraints.len)
                state.assignValueLean(bestPos, oldValue)
                for ci in 0..<state.constraints.len: before[ci] = state.constraints[ci].penalty()
                var directPred = 0
                for constraint in state.constraintsAtPosition[bestPos]:
                    directPred += state.movePenalty(constraint, bestPos, bestVal)
                var chanPred = 0
                if state.hasChannelDeps and bestPos < state.channelDepPenalties.len and
                   state.channelDepPenalties[bestPos].len > 0:
                    state.computeChannelDepPenaltiesAt(bestPos)
                    let dIdx = state.domIdx(bestPos, bestVal)
                    if dIdx >= 0: chanPred = state.channelDepPenalties[bestPos][dIdx]
                let wl = state.computeChannelDepDelta(bestPos, bestVal)
                state.assignValueLean(bestPos, bestVal)
                echo "[CheckDelta]   directPred=" & $directPred & " cascadePred=" & $chanPred & " worklistPred=" & $wl
                for ci in 0..<state.constraints.len:
                    let after = state.constraints[ci].penalty()
                    if after != before[ci]:
                        let c = state.constraints[ci]
                        var isDirect = false
                        for q in c.positions.items:
                            if q == bestPos: isDirect = true
                        var chanInputs = 0
                        for q in c.positions.items:
                            if q in state.carray.channelPositions: inc chanInputs
                        echo "[CheckDelta]   ci=" & $ci & " type=" & $c.stateType & " pen " & $before[ci] & "->" & $after &
                             " direct=" & $isDirect & " positions=" & $c.positions.len & " channelInputs=" & $chanInputs &
                             " inCascade=" & $state.cdCascadeScoresConstraint(bestPos, c)
        let tabuTenure = state.iteration + 1 + state.iteration mod 10
        let oldIdx = state.domIdx(bestPos, oldValue)
        if oldIdx >= 0 and not state.isLazy[bestPos]:
            state.tabu[bestPos][oldIdx] = tabuTenure


proc sampleByPosition[T](moves: seq[(int, T)]): (int, T) =
    ## Tie-break among equal-cost moves by position first, then value. A flat
    ## sample over (position, value) pairs lets a wide-domain variable hog the
    ## plateau moves (kitchen: two 0..306 paddings held ~half of ~1200 zero-delta
    ## ties, so the width/pair sequence that places a fixture was hardly ever
    ## tried). bestMoves appends moves grouped by position.
    if moves.len <= 1: return moves[0]
    var nGroups = 0
    var chosenStart = 0
    var chosenEnd = 1
    var i = 0
    while i < moves.len:
        var j = i + 1
        while j < moves.len and moves[j][0] == moves[i][0]: inc j
        inc nGroups
        if rand(nGroups - 1) == 0:
            chosenStart = i
            chosenEnd = j
        i = j
    moves[chosenStart + rand(chosenEnd - chosenStart - 1)]

proc applyBestMove[T](state: TabuState[T]) {.inline.} =
    when ProfileIteration:
        let tBM = epochTime()
    let moves = state.bestMoves()
    let (swapMoves, swapCost) = state.bestSwapMoves()
    # Evaluate permutation swaps periodically (assignValueLean-based simulation)
    var permMoves: seq[(int, int, T, T)] = @[]
    var permCost = high(int)
    if state.gccGroupPositions.len > 0 and
       (state.cost <= state.gccGroupPositions.len div 5 or state.iteration mod 3 == 0):
        (permMoves, permCost) = state.bestPermutationSwapMoves()
    # Evaluate partition swaps periodically (every 3 iterations) to limit overhead
    # from assignValueLean-based evaluation, but compare properly with other moves.
    var partMoves: seq[(int, int, int, int)]  # typed as int to match T=int
    var partCost = high(int)
    if state.partitionEnabled and state.iteration mod 3 == 0:
        (partMoves, partCost) = state.bestPartitionSwapMoves()

    when ProfileIteration:
        state.timeBestMoves += epochTime() - tBM

    # Determine best single move cost (including inverse delta if applicable)
    var singleCost = high(int)
    if moves.len > 0:
        let (pos, val) = moves[0]
        if state.isLazy[pos]:
            singleCost = state.cost + state.costDelta(pos, val)
        else:
            let idx = state.domIdx(pos, val)
            if idx >= 0:
                singleCost = state.cost + state.penaltyMap[pos][idx]
                if state.inverseEnabled and state.posToInverseGroup[pos] >= 0:
                    singleCost += state.inverseDelta[pos][idx]

    # Find overall best among single, swap, permutation swap, and partition moves
    if permMoves.len > 0 and permCost <= swapCost and permCost <= partCost and permCost < singleCost:
        inc state.permSwapApplied
        # Apply permutation swap move
        let (pp1, pp2, pNewVal1, pNewVal2) = sample(permMoves)
        let pOldVal1 = state.assignment[pp1]
        let pOldVal2 = state.assignment[pp2]
        state.assignValue(pp1, pNewVal1)
        state.assignValue(pp2, pNewVal2)
        let pTabuTenure = state.iteration + 1 + state.iteration mod 10
        if not state.isLazy[pp1]:
            let pOldIdx1 = state.domIdx(pp1, pOldVal1)
            if pOldIdx1 >= 0:
                state.tabu[pp1][pOldIdx1] = pTabuTenure
        if not state.isLazy[pp2]:
            let pOldIdx2 = state.domIdx(pp2, pOldVal2)
            if pOldIdx2 >= 0:
                state.tabu[pp2][pOldIdx2] = pTabuTenure
        state.applyElementImpliedMoves(pp1)
        state.applyElementImpliedMoves(pp2)
    elif partMoves.len > 0 and partCost <= swapCost and partCost < singleCost:
        # Apply partition swap move
        let (deactPos, actPos, newVal, groupIdx) = sample(partMoves)
        let oldActiveVal = state.assignment[deactPos]
        let groupNullVal = state.partitionGroups[groupIdx].nullValue
        state.assignValue(deactPos, groupNullVal)
        state.assignValue(actPos, newVal)
        let tabuTenure = state.iteration + 1 + state.iteration mod 10
        let oldIdx1 = state.domIdx(deactPos, oldActiveVal)
        if oldIdx1 >= 0 and not state.isLazy[deactPos]:
            state.tabu[deactPos][oldIdx1] = tabuTenure
        let oldIdx2 = state.domIdx(actPos, groupNullVal)
        if oldIdx2 >= 0 and not state.isLazy[actPos]:
            state.tabu[actPos][oldIdx2] = tabuTenure
        state.applyElementImpliedMoves(deactPos)
        state.applyElementImpliedMoves(actPos)
    elif swapMoves.len > 0 and swapCost < singleCost:
        # Apply swap move
        let (p1, p2, newVal1, newVal2) = sample(swapMoves)
        let oldVal1 = state.assignment[p1]
        let oldVal2 = state.assignment[p2]
        state.assignValue(p1, newVal1)
        state.assignValue(p2, newVal2)
        let tabuTenure = state.iteration + 1 + state.iteration mod 10
        if not state.isLazy[p1]:
            let oldIdx1 = state.domIdx(p1, oldVal1)
            if oldIdx1 >= 0:
                state.tabu[p1][oldIdx1] = tabuTenure
        if not state.isLazy[p2]:
            let oldIdx2 = state.domIdx(p2, oldVal2)
            if oldIdx2 >= 0:
                state.tabu[p2][oldIdx2] = tabuTenure
        state.applyElementImpliedMoves(p1)
        state.applyElementImpliedMoves(p2)
    elif moves.len > 0:
        let (position, newValue) = if gNoPosSample: sample(moves) else: sampleByPosition(moves)
        let oldValue = state.assignment[position]
        # Compute forced changes BEFORE assignValue to capture old values for tabu
        var forcedOldValues: seq[(int, T)]
        if state.inverseEnabled and state.posToInverseGroup[position] >= 0:
            state.computeInverseForcedChanges(position, newValue)
            for (fPos, fOld, fNew) in state.inverseForcedChanges:
                forcedOldValues.add((fPos, T(fOld)))
        let predicted = if gCheckDelta: state.penaltyAt(position, newValue) else: 0
        let freshPred = if gCheckDelta: state.costDelta(position, newValue) else: 0
        var penBefore: seq[int]
        if gCheckDelta:
            for c in state.constraints: penBefore.add(c.penalty())
        let costBefore = state.cost
        state.assignValue(position, newValue)
        if gCheckDelta and state.cost - costBefore != predicted:
            inc state.deltaMismatches
            if state.deltaMismatches <= 20:
                echo "[CheckDelta] best-move S" & $state.id & " it=" & $state.iteration & " pos=" & $position &
                     " " & $oldValue & "->" & $newValue & " predicted=" & $predicted &
                     " actual=" & $(state.cost - costBefore) & " fresh=" & $freshPred
                if position in state.ctpAtLink and freshPred != state.cost - costBefore:
                    var parts: seq[string]
                    for ci, c in state.constraints:
                        let d = c.penalty() - penBefore[ci]
                        if d != 0:
                            let inCd = c in state.channelDepConstraints
                            parts.add($ci & ":" & $c.stateType & "=" & $d & (if inCd: "(cd)" else: "") &
                                      (if position in c.positions: "(direct)" else: ""))
                    echo "[CheckDelta]   changed: ", parts.join(" ")
        let tabuTenure = state.iteration + 1 + state.iteration mod 10
        let oldIdx = state.domIdx(position, oldValue)
        if oldIdx >= 0 and not state.isLazy[position]:
            state.tabu[position][oldIdx] = tabuTenure
        # Set tabu on forced positions' old values
        for (fPos, fOldVal) in forcedOldValues:
            let fOldIdx = state.domIdx(fPos, fOldVal)
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


proc logViolatedBreakdown[T](state: TabuState[T]) =
    ## Dumps per-type violation breakdown plus top-K violated constraints.
    ## Only meaningful when state.cost > 0; reflects the *current* assignment,
    ## which is typically the best-known when search exhausts at a local optimum.
    if state.cost == 0:
        return
    var typePenalty: array[StatefulConstraintType, int]
    var typeCount: array[StatefulConstraintType, int]
    type Violation = tuple[idx: int, ct: StatefulConstraintType, pen: int, npos: int]
    var top: seq[Violation]
    for i, c in state.constraints:
        let p = int(c.penalty())
        if p > 0:
            typePenalty[c.stateType] += p
            typeCount[c.stateType] += 1
            top.add((idx: i, ct: c.stateType, pen: p, npos: c.positions.len))
    echo &"[Tabu S{state.id}] Violation breakdown by type (cost={state.cost}):"
    for ct in StatefulConstraintType:
        if typeCount[ct] > 0:
            echo &"  {ct}: {typeCount[ct]} violated, total_pen={typePenalty[ct]}"
    # Sort by penalty descending and print top 10
    top.sort(proc(a, b: Violation): int = b.pen - a.pen)
    let k = min(10, top.len)
    echo &"[Tabu S{state.id}] Top {k} violated constraints:"
    for i in 0..<k:
        var detail = ""
        let c = state.constraints[top[i].idx]
        if c.stateType == RelationalType:
            let rc = c.relationalState
            var leftDesc = "?"
            var rightDesc = "?"
            case rc.leftExpr.kind:
                of SumExpr:
                    let sumLen = if rc.leftExpr.sumExpr.evalMethod == PositionBased:
                                     rc.leftExpr.sumExpr.coefficient.len
                                 else: -1
                    let sumVal = rc.leftValue
                    leftDesc = &"Sum({sumLen} terms, val={sumVal}, eval={rc.leftExpr.sumExpr.evalMethod})"
                of ConstantExpr: leftDesc = &"Const({rc.leftExpr.constantValue})"
                else: leftDesc = $rc.leftExpr.kind
            case rc.rightExpr.kind:
                of SumExpr:
                    let sumLen = if rc.rightExpr.sumExpr.evalMethod == PositionBased:
                                     rc.rightExpr.sumExpr.coefficient.len
                                 else: -1
                    rightDesc = &"Sum({sumLen} terms, val={rc.rightValue})"
                of ConstantExpr: rightDesc = &"Const({rc.rightExpr.constantValue})"
                else: rightDesc = $rc.rightExpr.kind
            detail = &" {leftDesc} {rc.relation} {rightDesc} graduated={rc.graduated}"
        # Count search vs channel positions
        var nSearch = 0
        var nChannel = 0
        var nFixed = 0
        for pos in c.positions:
            if pos in state.carray.fixedPositions: nFixed += 1
            elif pos in state.carray.channelPositions: nChannel += 1
            else: nSearch += 1
        echo &"  ci={top[i].idx} type={top[i].ct} pen={top[i].pen} positions={top[i].npos} (search={nSearch} channel={nChannel} fixed={nFixed}){detail}"

proc logExitStats[T](state: TabuState[T], label: string) =
    let elapsed = epochTime() - state.startTime
    let rate = if elapsed > 0: state.iteration.float / elapsed else: 0.0
    echo &"[Tabu S{state.id}] {label}: best={state.bestCost} iters={state.iteration} elapsed={elapsed:.1f}s rate={rate:.0f}/s" &
        (if state.circuitMergesApplied > 0: &" circuitMerges={state.circuitMergesApplied}" else: "")
    if state.regLineCalls > 0:
        echo &"[Tabu S{state.id}] regularLine: calls={state.regLineCalls} applied={state.regLineApplied}"
    if state.permSwapCalls > 0:
        let fastOk = fastSwapEvalOk(state)
        echo &"[Tabu S{state.id}] permSwap: fast={fastOk} anyChannels={state.anyChannels} hasChannelDeps={state.hasChannelDeps} " &
             &"calls={state.permSwapCalls} throttled={state.permSwapThrottled} applied={state.permSwapApplied} " &
             &"slowTime={state.permSwapSlowTime:.2f}s ({state.permSwapSlowTime/max(elapsed,0.001)*100:.0f}%)"
    if state.id == 0 and state.bestCost > 0 and (label == "Exhausted" or gDebugViolations):
        state.logViolatedBreakdown()
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
        echo &"[Profile S{state.id}] cdConsRescore={state.cdConsRescoreCalls} leanRescore={state.cdLeanRescore} leanFull={state.cdLeanFull}"
        echo "[Profile S" & $state.id & "] Neighbor by type:"
        for ct in StatefulConstraintType:
            if state.neighborByType[ct] > 0:
                echo &"  {ct}: count={state.neighborByType[ct]} ({state.neighborByType[ct].float/iters:.1f}/iter) time={state.neighborTimeByType[ct]:.3f}s ({state.neighborTimeByType[ct]/max(elapsed,0.001)*100:.1f}%)"
    state.logProfileStats()


proc tryTableMoves[T](state: TabuState[T], allowPerturb: bool = false): bool =
    ## Stagnation-triggered table move: pick a random table constraint and
    ## try switching to a different valid tuple. Uses cheap simulation via
    ## assignValueLean to find a strictly improving move, then applies it.
    ## When allowPerturb is true, also applies neutral/slightly-worse moves
    ## as a perturbation to escape deep local optima.
    if state.tableInConstraintIndices.len == 0: return false

    # Try a few random table constraints
    const MAX_TABLES = 3
    const MAX_TUPLES_PER_TABLE = 8

    var bestDelta = 0  # only accept strictly improving moves
    var bestCI = -1
    var bestTupleIdx = -1
    # Track best perturbation candidate (smallest non-improving delta)
    var perturbDelta = high(int)
    var perturbCI = -1
    var perturbTupleIdx = -1

    var tableCandidates = state.tableInConstraintIndices
    shuffle(tableCandidates)
    let nTables = min(tableCandidates.len, MAX_TABLES)

    for ti in 0..<nTables:
        let ci = tableCandidates[ti]
        let tc = state.constraints[ci].tableConstraintState
        let nPos = tc.sortedPositions.len

        var tried: PackedSet[int]
        let nTries = min(tc.tuples.len, MAX_TUPLES_PER_TABLE)

        for attempt in 0..<nTries:
            var idx = rand(tc.tuples.len - 1)
            while idx in tried and tried.len < tc.tuples.len:
                idx = rand(tc.tuples.len - 1)
            tried.incl(idx)

            let tup = tc.tuples[idx]

            # Quick check: different from current and domain-compatible?
            var same = true
            var domainOk = true
            for col in 0..<nPos:
                let pos = tc.sortedPositions[col]
                let curVal = state.assignment[pos]
                if tup[col] != curVal:
                    same = false
                    let dom {.cursor.} = state.sharedDomain[][pos]
                    if tup[col] notin dom:
                        domainOk = false
                        break
            if same or not domainOk: continue

            # Simulate: apply via assignValueLean, measure delta, restore
            let origCost = state.cost
            var changes: seq[(int, T)] = @[]
            for col in 0..<nPos:
                let pos = tc.sortedPositions[col]
                if tup[col] != state.assignment[pos]:
                    changes.add((pos, state.assignment[pos]))
                    state.assignValueLean(pos, tup[col])
            let delta = state.cost - origCost
            # Restore
            for i in countdown(changes.len - 1, 0):
                let (pos, oldVal) = changes[i]
                state.assignValueLean(pos, oldVal)

            if delta < bestDelta:
                bestDelta = delta
                bestCI = ci
                bestTupleIdx = idx
            elif allowPerturb and delta >= bestDelta and delta < perturbDelta:
                perturbDelta = delta
                perturbCI = ci
                perturbTupleIdx = idx

    # Prefer improving move; fall back to perturbation if allowed
    let applyCI = if bestCI >= 0: bestCI else: perturbCI
    let applyIdx = if bestCI >= 0: bestTupleIdx else: perturbTupleIdx
    if applyCI < 0: return false

    let tc = state.constraints[applyCI].tableConstraintState
    let tup = tc.tuples[applyIdx]
    let tabuTenure = state.iteration + 1 + state.iteration mod 10
    for col in 0..<tc.sortedPositions.len:
        let pos = tc.sortedPositions[col]
        let oldVal = state.assignment[pos]
        if tup[col] != oldVal:
            let oldIdx = state.domIdx(pos, oldVal)
            if oldIdx >= 0 and not state.isLazy[pos]:
                state.tabu[pos][oldIdx] = tabuTenure
            state.assignValue(pos, tup[col])
    return true


proc tabuImprove*[T](state: TabuState[T], threshold: int, shouldStop: ptr Atomic[bool] = nil, deadline: float = 0.0): TabuState[T] =
    state.searchDeadline = deadline
    state.stopSignal = shouldStop
    var lastImprovement = 0

    # Reset timing and profiling counters for this run
    state.startTime = epochTime()
    state.nearStallRef = state.startTime
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
        state.cdConsRescoreCalls = 0
        state.cdLeanRescore = 0
        state.cdLeanFull = 0
        state.cdIncEvaluated = 0
        state.cdUniformCalls = 0
        for ct in StatefulConstraintType:
            state.neighborByType[ct] = 0
            state.neighborTimeByType[ct] = 0

    # Use lean first-improvement when cascades are large (penalty map rebuild dominates)
    if state.verbose and state.boundConstraint != nil:
        echo &"[Tabu S{state.id}] Tracking objective-bound constraint for near-feasible states (stall cap {state.nearStallSecs:.1f} s)"
    var useLeanSearch = state.hasChannelDeps and
        state.searchPositions.len >= 30 and
        state.channelDepSearchPositions.len > 0 and
        state.channelDepSearchPositions.len.float / state.searchPositions.len.float > 0.5 and
        not existsEnv("CRUSHER_NO_LEAN")   # diagnostic: force the penalty-map path

    # The static gate above only says that channel-dep positions dominate; it
    # does not say which regime is faster. Lean first-improvement re-runs the
    # channel cascade for every domain value of every position it visits,
    # best-move maintains the penalty map incrementally through the affected
    # sets. Measured: work-task-variation needs lean (best-move never finishes
    # a probe), warehouse needs best-move (lean runs at 64 it/s vs 787 it/s and
    # reaches a 40% worse objective). So when the gate fires, trial both for a
    # short slice and keep the one with the higher cost decrease per second.
    # Lean goes first: its iteration cost is bounded (one cascade pass per
    # visited position). A best-move iteration on a cascade-heavy model can run
    # for tens of seconds (work-task-variation: neighbour-penalty updates over
    # every changed channel), so its trial slice is abortable from inside
    # updateNeighborPenalties (trialAbortAt) and an abort counts as a loss.
    var trialPhase = 0   # 0 none, 1 measuring lean, 2 measuring best-move, 3 decided
    var trialStartT = 0.0
    var trialStartIter = 0
    var trialStartCost = 0
    var trialProgress: array[2, float]   # cost units per second: [lean, best-move]
    var trialRate: array[2, float]       # iterations per second
    const TrialSeconds = 0.25
    const TrialIters = 200
    const TrialAbortFactor = 4.0         # best-move slice may take at most this times TrialSeconds
    if useLeanSearch and not existsEnv("CRUSHER_NO_LEAN_TRIAL"):
        trialPhase = 1
        trialStartT = epochTime()
        trialStartIter = state.iteration
        trialStartCost = state.cost

    state.leanSearch = useLeanSearch and not existsEnv("CRUSHER_NO_LEAN_COMMIT")
    if state.verbose:
        echo &"[Tabu S{state.id}] Starting: vars={state.carray.len} constraints={state.constraints.len} threshold={threshold} cost={state.cost}" &
            (if useLeanSearch: " (lean first-improvement)" else: "")

    while state.iteration - lastImprovement < threshold:
        # Near-feasible incumbent: only the optimizer's bound constraint violated.
        # Tracked by the RAW (unscaled) bound violation, i.e. in objective units,
        # so that objective progress too small to register in the scaled cost
        # still counts as search progress (resets the stagnation counter).
        if state.boundConstraint != nil and state.cost > 0 and
           state.cost == state.boundConstraint.penalty():
            var raw = state.cost
            if state.boundConstraint.stateType == RelationalType:
                let rc = state.boundConstraint.relationalState
                raw = case rc.relation
                    of LessThanEq, LessThan: int(rc.leftValue - rc.rightValue)
                    of GreaterThanEq, GreaterThan: int(rc.rightValue - rc.leftValue)
                    else: state.cost
                raw = max(raw, 1)
            if raw < state.nearBestCost:
                state.nearBestCost = raw
                state.nearBestAssignment = state.assignment
                lastImprovement = state.iteration
                state.nearStallRef = epochTime()
        # Check for early termination signal
        if shouldStop != nil and shouldStop[].load():
            if state.verbose:
                state.logExitStats("Stopped")
            state.lastImprovementIter = lastImprovement
            return state

        # Check deadline every 64 iterations. The granularity matters: on
        # channel-heavy models an iteration costs ~0.1-1s (stagnation helpers
        # can run full swap scans inside one iteration), so a coarse mask
        # overruns the deadline by minutes.
        if deadline > 0 and (state.iteration and 0x3F) == 0 and epochTime() > deadline:
            if state.verbose:
                state.logExitStats("Deadline")
            state.lastImprovementIter = lastImprovement
            return state
        # Optimizer probe/ask stall cap: no improvement of any kind (best cost
        # or near-feasible incumbent) for nearStallSecs. Local search cannot
        # prove a bound infeasible, so a hopeless probe (kitchen: 560 of
        # [1..1120], optimum 516) would otherwise run to the global deadline;
        # a probe still descending (community detection, roster: exact optima
        # reached only through such probes) or still finding better
        # near-feasible states (warehouse wlp02) is left running.
        if state.nearStallSecs > 0 and (state.iteration and 0x3F) == 0 and
                epochTime() - state.nearStallRef > state.nearStallSecs:
            if state.verbose:
                state.logExitStats("Stalled")
            state.lastImprovementIter = lastImprovement
            return state

        # The stagnation helpers below can each burn seconds per call (full
        # cascade evaluations over many candidate moves); gate them on the
        # remaining budget or they overrun the deadline by minutes.
        template outOfBudget(): bool =
            (shouldStop != nil and shouldStop[].load()) or
            (deadline > 0 and epochTime() > deadline)

        if trialPhase == 1 or trialPhase == 2:
            let elapsed = epochTime() - trialStartT
            let iters = state.iteration - trialStartIter
            if state.trialAborted or
               (iters > 0 and (elapsed >= TrialSeconds or iters >= TrialIters)):
                let k = trialPhase - 1
                trialProgress[k] = float(trialStartCost - state.cost) / max(elapsed, 1e-6)
                trialRate[k] = float(iters) / max(elapsed, 1e-6)
                if trialPhase == 1:
                    trialPhase = 2
                    useLeanSearch = false
                    state.leanSearch = false
                    # Lean moves left the penalty structures stale.
                    for pos in state.channelDepSearchPositions:
                        if not state.isLazy[pos]:
                            state.computeChannelDepPenaltiesAt(pos)
                    state.rebuildPenaltyMap()
                    trialStartT = epochTime()
                    trialStartIter = state.iteration
                    trialStartCost = state.cost
                    state.trialAborted = false
                    state.trialNeighborCalls = 0
                    state.trialAbortAt = trialStartT + TrialAbortFactor * TrialSeconds
                else:
                    trialPhase = 3
                    let aborted = state.trialAborted
                    state.trialAbortAt = 0.0
                    state.trialAborted = false
                    # Progress decides when either mode made any; otherwise
                    # (both stuck at a local minimum) the faster iterator.
                    let leanWins = aborted or
                        (if max(trialProgress[0], trialProgress[1]) > 0.0:
                            trialProgress[0] >= trialProgress[1]
                         else:
                            trialRate[0] >= trialRate[1])
                    if state.verbose:
                        echo &"[Tabu S{state.id}] Lean trial: lean {trialProgress[0]:.0f} cost/s ({trialRate[0]:.0f} it/s), " &
                             &"best-move {trialProgress[1]:.0f} cost/s ({trialRate[1]:.0f} it/s)" &
                             (if aborted: &" [aborted after {state.trialNeighborCalls} neighbour updates in {elapsed:.1f}s]" else: "") &
                             " -> " & (if leanWins: "lean first-improvement" else: "best-move")
                    if leanWins:
                        useLeanSearch = true
                        state.leanSearch = not existsEnv("CRUSHER_NO_LEAN_COMMIT")
                    else:
                        # Aborted neighbour updates never happened here (no abort), so
                        # the penalty structures are fresh; keep best-move.
                        useLeanSearch = false
                        state.leanSearch = false
        if useLeanSearch:
            state.applyFirstImprovingMove()
        else:
            state.applyBestMove()

        if state.cost < state.bestCost:
            lastImprovement = state.iteration
            state.nearStallRef = epochTime()
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
           (state.iteration - lastImprovement) mod 50 == 0 and
           not outOfBudget():
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
           (state.iteration - lastImprovement) mod 20 == 0 and
           not outOfBudget():
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

        # Regular line rewrites during stagnation: optimal re-solve of one DFA
        # line against the rest of the model (see tabuRegularMoves). Chain while
        # improving; sideways rewrites only in deeper stagnation.
        # (Nonogram note, 2026-11: attempting rewrites every non-improving
        # iteration with sideways after 10 did not change medium_05's ~15%
        # solve rate at 60 s, and hard_01 plateaus at cost ~30 either way.)
        if state.regularConstraintIndices.len > 0 and
           state.iteration - lastImprovement >= 10 and
           (state.iteration - lastImprovement) mod 10 == 0 and
           not outOfBudget():
            let sideways = state.iteration - lastImprovement >= 100
            var lineIters = 0
            while lineIters < 50 and not outOfBudget() and
                    state.tryRegularLineMoves(allowSideways = sideways and lineIters == 0):
                inc lineIters
                inc state.regLineApplied
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via regular line move")
                        state.lastImprovementIter = lastImprovement
                        return state

        # Tour-preserving relocation moves on valid circuits (see tryTourMoves):
        # the main neighborhood for sequencing once the circuit is satisfied.
        # Backoff: after a fruitless full scan, wait 10 * 2^k iterations (k = consecutive
        # failures, reset on success) — scans re-walk every circuit-time chain per candidate.
        if state.circuitConstraints.len > 0 and
           state.iteration - lastImprovement >= 2 and
           state.iteration >= state.tourNextTry and
           not outOfBudget():
            var tourIters = 0
            while tourIters < 20 and not outOfBudget() and state.tryTourMoves(allowPerturb = false):
                inc tourIters
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via tour move")
                        state.lastImprovementIter = lastImprovement
                        return state
            if tourIters == 0:
                state.tourFailStreak = min(state.tourFailStreak + 1, 8)
                state.tourNextTry = state.iteration + 10 * (1 shl state.tourFailStreak)
                if state.iteration - lastImprovement >= 200:
                    discard state.tryTourMoves(allowPerturb = true)
            else:
                state.tourFailStreak = 0
                state.tourNextTry = state.iteration + 2

        # Linked-pair relocation (pickup/delivery on one vehicle) on valid tours
        if state.circuitConstraints.len > 0 and state.circuitTimePropConstraints.len > 0 and
           state.iteration - lastImprovement >= 5 and
           state.iteration >= state.pairNextTry and
           not outOfBudget() and not existsEnv("CRUSHER_NO_PAIR_MOVES"):
            if state.tryPairTourMoves():
                state.pairFailStreak = 0
                state.pairNextTry = state.iteration + 2
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via pair tour move")
                        state.lastImprovementIter = lastImprovement
                        return state
            else:
                state.pairFailStreak = min(state.pairFailStreak + 1, 8)
                state.pairNextTry = state.iteration + 10 * (1 shl state.pairFailStreak)

        # Try circuit cross-cycle merge moves during stagnation: when a circuit
        # constraint has split into disjoint subtours, a 2-opt swap of successors
        # across two cycles merges them — an escape single-variable moves cannot
        # reach. A k-subtour circuit needs k-1 merges, so chain strictly-improving
        # merges until none remain.
        # Self-disable: if the merge has been tried enough times without ever
        # applying, the circuit's domains are too sparse for cross-cycle value
        # swaps to be feasible (e.g. knight's tour). Stop scanning so the helper
        # costs nothing on problems it cannot help.
        if state.circuitConstraints.len > 0 and
           not (state.circuitMoveCalls >= 8 and state.circuitMergesApplied == 0) and
           state.iteration - lastImprovement >= 20 and
           (state.iteration - lastImprovement) mod 20 == 0 and
           not outOfBudget():
            var iterations = 0
            const MAX_CIRCUIT_ITERATIONS = 200
            var progressed = false
            while iterations < MAX_CIRCUIT_ITERATIONS and not outOfBudget() and
                    state.tryCircuitMoves(allowPerturb = false):
                iterations += 1
                progressed = true
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via circuit merge")
                        state.lastImprovementIter = lastImprovement
                        return state
            # Deep stagnation with no improving merge available: take one gentle
            # perturbation to break the plateau so the next round finds new merges.
            if not progressed and state.iteration - lastImprovement >= 300:
                discard state.tryCircuitMoves(allowPerturb = true)

        # Same cross-cycle merge for circuits over channel (derived) variables,
        # realized through index-selector flips (e.g. p1f's union-of-matchings).
        if state.channelCircuitConstraints.len > 0 and
           not (state.circuitMoveCalls >= 12 and state.circuitMergesApplied == 0) and
           state.iteration - lastImprovement >= 20 and
           (state.iteration - lastImprovement) mod 20 == 0 and
           not outOfBudget():
            var citers = 0
            const MAX_CHANNEL_CIRCUIT_ITERATIONS = 200
            var cprogressed = false
            while citers < MAX_CHANNEL_CIRCUIT_ITERATIONS and not outOfBudget() and
                    state.tryChannelCircuitMoves(allowPerturb = false):
                citers += 1
                cprogressed = true
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via channel circuit merge")
                        state.lastImprovementIter = lastImprovement
                        return state
            if not cprogressed and state.iteration - lastImprovement >= 300:
                discard state.tryChannelCircuitMoves(allowPerturb = true)

        # Try table moves during stagnation: switch a table constraint to a
        # different valid tuple, changing multiple variables simultaneously.
        # Short stagnation: only improving moves (safe). Deep stagnation (table-
        # heavy problems): allow perturbation to escape local optima.
        if state.tableInConstraintIndices.len > 0 and
           state.iteration - lastImprovement >= 100 and
           (state.iteration - lastImprovement) mod 100 == 0 and
           not outOfBudget():
            let deepStag = state.tableInConstraintIndices.len >= 10 and
                           state.iteration - lastImprovement >= 500
            if state.tryTableMoves(allowPerturb = deepStag):
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via table move")
                        state.lastImprovementIter = lastImprovement
                        return state

        # Try linear repair moves during stagnation: coordinate multi-variable
        # adjustments on violated EqualTo constraints (e.g., flow conservation)
        if state.iteration - lastImprovement >= 100 and
           (state.iteration - lastImprovement) mod 100 == 0 and
           not outOfBudget():
            if state.tryLinearRepairMoves():
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via linear repair")
                        state.lastImprovementIter = lastImprovement
                        return state

        # Try compound-flip count repair during deeper stagnation: handles cases
        # where single-position flips give delta=0 due to coupled implications.
        # When an improvement is found, iterate (compound moves often chain).
        if state.iteration - lastImprovement >= 200 and
           (state.iteration - lastImprovement) mod 50 == 0 and
           not outOfBudget():
            var iterations = 0
            const MAX_COMPOUND_ITERATIONS = 50
            while iterations < MAX_COMPOUND_ITERATIONS and not outOfBudget() and
                    state.tryCompoundCountRepair():
                iterations += 1
                if state.cost < state.bestCost:
                    lastImprovement = state.iteration
                    state.bestCost = state.cost
                    state.bestAssignment = state.assignment
                    if state.cost == 0:
                        if state.verbose:
                            state.logExitStats("Solution found via compound count repair")
                        state.lastImprovementIter = lastImprovement
                        return state

        state.iteration += 1

        # Periodic logging
        if state.verbose and state.iteration mod LogInterval == 0:
            state.logProgress(lastImprovement)

    if state.verbose:
        state.logExitStats("Exhausted")
        if existsEnv("CRUSHER_DEBUG_CIRCUIT"):
            for cc in state.circuitConstraints:
                var succ: seq[int]
                for p in cc.positionArray: succ.add(int(state.assignment[p]))
                echo "[DebugCircuit] circuit cost=", cc.cost, " succ=", succ
                for i, p in cc.positionArray:
                    var row = ""
                    for v in state.sharedDomain[][p]:
                        if v == state.assignment[p]: continue
                        let before = state.cost
                        let ov = state.assignment[p]
                        state.assignValueLean(p, v)
                        let act = state.cost - before
                        state.assignValueLean(p, ov)
                        row &= " " & $v & ":" & $act & "/" & $state.costDelta(p, v)
                    echo "[DebugCircuit]   node ", i, " moves(actual/pred):", row
            for ctc in state.circuitTimePropConstraints:
                echo "[DebugCircuit] ctp circPen=", ctc.circuitPenalty, " w=", ctc.circuitWeight,
                     " tw=", ctc.timeWindowPenalty, " cost=", ctc.cost, " links=", ctc.links

    state.lastImprovementIter = lastImprovement
    return state


proc tabuImprove*[T](carray: ConstrainedArray[T], threshold: int, verbose: bool = false, deadline: float = 0.0): TabuState[T] =
    var state = newTabuState[T](carray, verbose)
    return state.tabuImprove(threshold, deadline = deadline)
