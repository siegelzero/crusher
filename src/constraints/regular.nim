## Regular Constraint Implementation (DFA-based with column-aware recovery)
##
## Ensures a sequence of variables is accepted by a deterministic finite automaton.
## The DFA is defined by: number of states, input range, transition table,
## initial state, and set of accepting (final) states.
##
## **Penalty**: Uses recovery-based counting. When the DFA enters a fail state (0),
## it counts 1 penalty and recovers to a pre-computed "background state" that
## preserves the DFA's column/row tracking. This gives penalties proportional to
## the number of distinct errors while maintaining correct positional context.
##
## **Hamming mode** (default when the DFA is small enough): the penalty is the
## exact minimum number of variables that must change for the sequence to be
## accepted, computed by forward/backward dynamic programming over the DFA
## (fwd[i][s] = min changes to be in state s after i inputs, bwd[i][s] = min
## changes to accept from state s at input i). This gives local search a smooth
## gradient (e.g. nonogram lines), and moveDelta is O(states * inputs) by
## combining fwd[idx] with bwd[idx+1]. The recovery penalty above is kept for
## DFAs too large for the DP tables.

import std/[packedsets, tables]
import packedSetAssign

################################################################################
# Type definitions
################################################################################

type
    RegularConstraint*[T] = ref object
        n*: int                          # number of variables
        nStates*: int                    # number of DFA states (1-indexed)
        inputMin*: T                     # minimum input value
        inputMax*: T                     # maximum input value
        transition*: seq[seq[int]]       # transition[state][input] -> next state (1-indexed, 0=fail)
        initialState*: int              # 1-indexed initial state
        finalStates*: PackedSet[int]    # set of accepting states (1-indexed)
        sortedPositions*: seq[int]      # sorted variable positions
        positionToIndex*: Table[int, int]  # position -> 0-based index
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        cost*: int

        # Cached DFA state after processing each position (with recovery)
        stateAfter*: seq[int]            # stateAfter[i] = state after processing variable i
        failedAt*: seq[bool]             # failedAt[i] = true if transition failed at position i

        # Background states for column-aware recovery
        backgroundState*: seq[int]       # backgroundState[i] = DFA state at position i with no tile placed

        # Tracking for incremental updates
        lastChangeAffectedPositions*: PackedSet[int]
        lastChangeAffectedCost*: bool

        # Hamming mode (see module doc). Tables are flat: [i * stride + s] with
        # stride = nStates + 1 (state 0 = fail, always HInf).
        useHamming*: bool
        hVals*: seq[int]                 # current input value per index
        hFwd*: seq[int]                  # (n+1) * stride
        hBwd*: seq[int]                  # (n+1) * stride

################################################################################
# Constructor
################################################################################

const
    RegularHammingMaxStateInputs* = 4096
    RegularHammingMaxWork* = 1_000_000
    HInf = high(int) div 4

proc newRegularConstraint*[T](positions: openArray[int],
                               nStates: int,
                               inputMin, inputMax: T,
                               transition: seq[seq[int]],
                               initialState: int,
                               finalStates: openArray[int]): RegularConstraint[T] =
    new(result)
    result.n = positions.len
    result.nStates = nStates
    result.inputMin = inputMin
    result.inputMax = inputMax
    result.transition = transition
    result.initialState = initialState
    result.finalStates = toPackedSet[int](finalStates)
    result.sortedPositions = @positions
    result.positions = toPackedSet[int](positions)
    result.currentAssignment = initTable[int, T]()
    result.cost = 0
    result.stateAfter = newSeq[int](result.n)
    result.failedAt = newSeq[bool](result.n)
    result.lastChangeAffectedPositions = initPackedSet[int]()
    result.lastChangeAffectedCost = false

    result.positionToIndex = initTable[int, int]()
    for i, pos in positions:
        result.positionToIndex[pos] = i

    # Background states are computed properly in initialize() via initializeBackgroundStates()
    # once the actual assignment (with sentinel positions) is available.
    result.backgroundState = newSeq[int](result.n)

    # Hamming mode when the DP tables are cheap: per-update work is
    # n * nStates * nInputs, per-move work nStates * nInputs.
    let nInputs = int(inputMax) - int(inputMin) + 1
    result.useHamming = not defined(regularRecovery) and
                        result.positionToIndex.len == result.n and
                        nStates * nInputs <= RegularHammingMaxStateInputs and
                        result.n * nStates * nInputs <= RegularHammingMaxWork

################################################################################
# DFA simulation
################################################################################

proc getNextState*[T](state: RegularConstraint[T], dfaState: int, inputVal: T): int {.inline.} =
    ## Returns next DFA state given current state and input value.
    ## Returns 0 (fail state) if input is out of range or state is invalid.
    if dfaState <= 0 or dfaState > state.nStates:
        return 0
    # Early range check avoids overflow in the subtraction below
    if int(inputVal) < int(state.inputMin):
        return 0
    let inputIdx = int(inputVal) - int(state.inputMin)
    if inputIdx >= state.transition[dfaState - 1].len:
        return 0
    return state.transition[dfaState - 1][inputIdx]

proc stepWithRecovery[T](state: RegularConstraint[T], curState: int, inputVal: T, posIdx: int): tuple[nextState: int, failed: bool] {.inline.} =
    ## Advance the DFA with column-aware recovery.
    let nextState = state.getNextState(curState, inputVal)
    if nextState == 0:
        # Recovery: use background state at this position (preserves column tracking)
        return (state.backgroundState[posIdx], true)
    return (nextState, false)

################################################################################
# Initialization and updates
################################################################################

proc initializeBackgroundStates*[T](state: RegularConstraint[T], assignment: seq[T]) =
    ## Re-compute background states using actual sentinel positions from the assignment.
    ## This gives more accurate column-aware recovery.
    var targetCounts: Table[int, int]
    let sentinelVal = state.inputMax
    for v in state.inputMin..T(int(state.inputMax) - 1):
        let s = state.getNextState(state.initialState, v)
        if s > 0:
            targetCounts.mgetOrPut(s, 0) += 1

    var neutralValue = state.inputMin
    var maxCount = 0
    for v in state.inputMin..T(int(state.inputMax) - 1):
        let s = state.getNextState(state.initialState, v)
        if s > 0 and targetCounts.getOrDefault(s, 0) > maxCount:
            maxCount = targetCounts[s]
            neutralValue = v

    var bgState = state.initialState
    for i in 0..<state.n:
        let pos = state.sortedPositions[i]
        # If this position is fixed to sentinel, use sentinel; otherwise use neutral
        let inputVal = if assignment[pos] == sentinelVal: sentinelVal else: neutralValue
        bgState = state.getNextState(bgState, inputVal)
        if bgState <= 0: bgState = state.initialState
        state.backgroundState[i] = bgState



################################################################################
# Hamming mode
################################################################################

proc hRecomputeFwd[T](state: RegularConstraint[T], fromIdx: int) =
    ## Recompute fwd rows fromIdx+1..n (row fromIdx must be valid).
    let stride = state.nStates + 1
    let nIn = int(state.inputMax) - int(state.inputMin) + 1
    for i in fromIdx..<state.n:
        let base = i * stride
        let nb = base + stride
        for s in 0..<stride: state.hFwd[nb + s] = HInf
        let xi = state.hVals[i] - int(state.inputMin)
        for s in 1..state.nStates:
            let f = state.hFwd[base + s]
            if f >= HInf: continue
            let row = state.transition[s - 1]
            for k in 0..<min(nIn, row.len):
                let ns = row[k]
                if ns <= 0: continue
                let c = f + (if k == xi: 0 else: 1)
                if c < state.hFwd[nb + ns]: state.hFwd[nb + ns] = c

proc hRecomputeBwd[T](state: RegularConstraint[T], fromIdx: int) =
    ## Recompute bwd rows fromIdx down to 0 (row fromIdx+1 must be valid).
    let stride = state.nStates + 1
    let nIn = int(state.inputMax) - int(state.inputMin) + 1
    for i in countdown(fromIdx, 0):
        let base = i * stride
        let nb = base + stride
        let xi = state.hVals[i] - int(state.inputMin)
        state.hBwd[base] = HInf
        for s in 1..state.nStates:
            var best = HInf
            let row = state.transition[s - 1]
            for k in 0..<min(nIn, row.len):
                let ns = row[k]
                if ns <= 0: continue
                let b = state.hBwd[nb + ns]
                if b >= HInf: continue
                let c = b + (if k == xi: 0 else: 1)
                if c < best: best = c
            state.hBwd[base + s] = best

proc hCost[T](state: RegularConstraint[T]): int {.inline.} =
    let c = state.hBwd[state.initialState]
    # No accepted string of this length at all: constant maximal penalty.
    if c >= HInf: state.n + 1 else: c

proc hInitialize[T](state: RegularConstraint[T]) =
    let stride = state.nStates + 1
    state.hVals = newSeq[int](state.n)
    for i in 0..<state.n:
        state.hVals[i] = int(state.currentAssignment[state.sortedPositions[i]])
    state.hFwd = newSeq[int]((state.n + 1) * stride)
    state.hBwd = newSeq[int]((state.n + 1) * stride)
    for s in 0..<stride: state.hFwd[s] = HInf
    state.hFwd[state.initialState] = 0
    state.hRecomputeFwd(0)
    let last = state.n * stride
    for s in 0..<stride:
        state.hBwd[last + s] = if s > 0 and s in state.finalStates: 0 else: HInf
    if state.n > 0: state.hRecomputeBwd(state.n - 1)
    state.cost = state.hCost()

proc hCostWith[T](state: RegularConstraint[T], idx: int, newValue: T): int =
    ## Penalty if the input at idx were newValue (all else unchanged).
    let stride = state.nStates + 1
    let nIn = int(state.inputMax) - int(state.inputMin) + 1
    let base = idx * stride
    let nb = base + stride
    let xi = int(newValue) - int(state.inputMin)
    var best = HInf
    for s in 1..state.nStates:
        let f = state.hFwd[base + s]
        if f >= HInf: continue
        let row = state.transition[s - 1]
        for k in 0..<min(nIn, row.len):
            let ns = row[k]
            if ns <= 0: continue
            let b = state.hBwd[nb + ns]
            if b >= HInf: continue
            let c = f + b + (if k == xi: 0 else: 1)
            if c < best: best = c
    if best >= HInf: state.n + 1 else: best

proc initialize*[T](state: RegularConstraint[T], assignment: seq[T]) =
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]

    if state.useHamming:
        state.hInitialize()
        state.lastChangeAffectedPositions.assignSet(state.positions)
        state.lastChangeAffectedCost = true
        return

    # Compute background states with actual sentinel positions
    state.initializeBackgroundStates(assignment)

    # Run DFA with recovery
    var currentState = state.initialState
    state.cost = 0
    for i in 0..<state.n:
        let inputVal = state.currentAssignment[state.sortedPositions[i]]
        let (ns, failed) = state.stepWithRecovery(currentState, inputVal, i)
        state.stateAfter[i] = ns
        state.failedAt[i] = failed
        if failed: state.cost += 1
        currentState = ns

    # Check final state
    let finalState = if state.n > 0: state.stateAfter[state.n - 1] else: state.initialState
    if finalState notin state.finalStates:
        state.cost += 1

    # Mark all positions as affected on init
    state.lastChangeAffectedPositions.assignSet(state.positions)
    state.lastChangeAffectedCost = true


proc updatePosition*[T](state: RegularConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        state.lastChangeAffectedPositions = initPackedSet[int]()
        state.lastChangeAffectedCost = false
        return

    state.currentAssignment[position] = newValue
    let idx = state.positionToIndex[position]

    if state.useHamming:
        state.hVals[idx] = int(newValue)
        state.hRecomputeFwd(idx)
        state.hRecomputeBwd(idx)
        let newCost = state.hCost()
        state.lastChangeAffectedCost = newCost != state.cost
        state.cost = newCost
        # Every position's move delta depends on the whole line's DP tables.
        state.lastChangeAffectedPositions.assignSet(state.positions)
        return

    # Re-run DFA with recovery from the changed position forward
    state.lastChangeAffectedPositions = initPackedSet[int]()
    state.lastChangeAffectedPositions.incl(position)

    var currentState: int
    if idx == 0:
        currentState = state.initialState
    else:
        currentState = state.stateAfter[idx - 1]

    let oldFinalState = state.stateAfter[state.n - 1]
    var costDelta = 0

    for i in idx..<state.n:
        let inputVal = state.currentAssignment[state.sortedPositions[i]]
        let (ns, failed) = state.stepWithRecovery(currentState, inputVal, i)

        let oldState = state.stateAfter[i]
        let oldFailed = state.failedAt[i]

        # Track cost delta
        if failed and not oldFailed: costDelta += 1
        elif not failed and oldFailed: costDelta -= 1

        state.stateAfter[i] = ns
        state.failedAt[i] = failed

        if ns != oldState:
            if i + 1 < state.n:
                state.lastChangeAffectedPositions.incl(state.sortedPositions[i + 1])
        else:
            # States have converged - no more changes downstream
            if i > idx:
                break

        currentState = ns

    # Final state penalty delta
    let newFinalState = state.stateAfter[state.n - 1]
    if oldFinalState != newFinalState:
        let oldFinalPenalty = if oldFinalState notin state.finalStates: 1 else: 0
        let newFinalPenalty = if newFinalState notin state.finalStates: 1 else: 0
        costDelta += newFinalPenalty - oldFinalPenalty

    state.cost += costDelta
    state.lastChangeAffectedCost = costDelta != 0


proc getAffectedPositions*[T](state: RegularConstraint[T]): PackedSet[int] =
    return state.lastChangeAffectedPositions


proc deepCopy*[T](state: RegularConstraint[T]): RegularConstraint[T] =
    new(result)
    result.n = state.n
    result.nStates = state.nStates
    result.inputMin = state.inputMin
    result.inputMax = state.inputMax
    result.transition = state.transition
    result.initialState = state.initialState
    result.finalStates = state.finalStates
    result.sortedPositions = state.sortedPositions
    result.positionToIndex = state.positionToIndex
    result.positions = state.positions
    result.currentAssignment = initTable[int, T]()
    for k, v in state.currentAssignment.pairs:
        result.currentAssignment[k] = v
    result.cost = state.cost
    result.stateAfter = @(state.stateAfter)
    result.failedAt = @(state.failedAt)
    result.backgroundState = @(state.backgroundState)
    result.lastChangeAffectedPositions = state.lastChangeAffectedPositions
    result.lastChangeAffectedCost = state.lastChangeAffectedCost
    result.useHamming = state.useHamming
    result.hVals = state.hVals
    result.hFwd = state.hFwd
    result.hBwd = state.hBwd


proc moveDelta*[T](state: RegularConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    let idx = state.positionToIndex[position]

    if state.useHamming:
        return state.hCostWith(idx, newValue) - state.cost

    # Temporarily change
    state.currentAssignment[position] = newValue

    # Get the DFA state entering position idx
    let enterState = if idx == 0: state.initialState else: state.stateAfter[idx - 1]

    # Simulate forward with recovery from idx, computing penalty delta
    var newPenalty = 0
    var oldPenalty = 0
    var curState = enterState
    var reachedEnd = true

    for i in idx..<state.n:
        let inputVal = state.currentAssignment[state.sortedPositions[i]]
        let (ns, failed) = state.stepWithRecovery(curState, inputVal, i)

        if failed: newPenalty += 1
        if state.failedAt[i]: oldPenalty += 1

        curState = ns

        # If new state matches cached state, remaining penalties are unchanged
        if curState == state.stateAfter[i]:
            reachedEnd = false
            break

    # Final state penalty only changes if we reached the end with different state
    if reachedEnd:
        if curState notin state.finalStates: newPenalty += 1
        if state.stateAfter[state.n - 1] notin state.finalStates: oldPenalty += 1

    state.currentAssignment[position] = oldValue
    return newPenalty - oldPenalty
