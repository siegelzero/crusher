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

import std/[packedsets, tables]

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

################################################################################
# Constructor
################################################################################

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

    # Pre-compute background states for column-aware recovery.
    # Find the "neutral" (non-tile) input value by checking which value
    # leads to the most common transition from the initial state.
    var targetCounts: Table[int, int]
    let sentinelVal = inputMax
    for v in inputMin..T(int(inputMax) - 1):
        let s = result.transition[initialState - 1][int(v) - int(inputMin)]
        if s > 0:
            targetCounts.mgetOrPut(s, 0) += 1

    # The neutral value is the one leading to the most common target state
    var neutralValue = inputMin
    var maxCount = 0
    for v in inputMin..T(int(inputMax) - 1):
        let s = result.transition[initialState - 1][int(v) - int(inputMin)]
        if s > 0 and targetCounts.getOrDefault(s, 0) > maxCount:
            maxCount = targetCounts[s]
            neutralValue = v

    # Simulate the DFA with neutral values (and sentinels where fixed)
    result.backgroundState = newSeq[int](result.n)
    var bgState = initialState
    for i in 0..<result.n:
        # Use sentinel value if the position is fixed to sentinel, otherwise neutral
        let inputVal = if int(inputMax) <= int(inputMax): neutralValue else: neutralValue
        # We don't know which positions are sentinels yet (they're determined by the assignment)
        # So we just use the neutral value everywhere for now
        bgState = result.transition[max(bgState - 1, 0)][int(neutralValue) - int(inputMin)]
        if bgState <= 0: bgState = initialState  # safety fallback
        result.backgroundState[i] = bgState

################################################################################
# DFA simulation
################################################################################

proc getNextState[T](state: RegularConstraint[T], dfaState: int, inputVal: T): int {.inline.} =
    ## Returns next DFA state given current state and input value.
    ## Returns 0 (fail state) if input is out of range or state is invalid.
    if dfaState <= 0 or dfaState > state.nStates:
        return 0
    let inputIdx = int(inputVal) - int(state.inputMin)
    if inputIdx < 0 or inputIdx >= state.transition[dfaState - 1].len:
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


proc initialize*[T](state: RegularConstraint[T], assignment: seq[T]) =
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]

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
    state.lastChangeAffectedPositions = state.positions
    state.lastChangeAffectedCost = true


proc updatePosition*[T](state: RegularConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        state.lastChangeAffectedPositions = initPackedSet[int]()
        state.lastChangeAffectedCost = false
        return

    state.currentAssignment[position] = newValue
    let idx = state.positionToIndex[position]

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


proc moveDelta*[T](state: RegularConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    let idx = state.positionToIndex[position]

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
