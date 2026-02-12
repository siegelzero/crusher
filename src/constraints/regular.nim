## Regular Constraint Implementation (DFA-based)
##
## Ensures a sequence of variables is accepted by a deterministic finite automaton.
## The DFA is defined by: number of states, input range, transition table,
## initial state, and set of accepting (final) states.
##
## **Penalty**: count of invalid transitions + (1 if final state not accepting)

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

        # Cached DFA state after processing each position
        stateAfter*: seq[int]            # stateAfter[i] = state after processing variable i

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

    result.positionToIndex = initTable[int, int]()
    for i, pos in positions:
        result.positionToIndex[pos] = i

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

proc runDFA[T](state: RegularConstraint[T], fromIndex: int = 0) =
    ## Run DFA from position fromIndex to end, updating stateAfter cache.
    var currentState: int
    if fromIndex == 0:
        currentState = state.initialState
    else:
        currentState = state.stateAfter[fromIndex - 1]

    for i in fromIndex..<state.n:
        let inputVal = state.currentAssignment[state.sortedPositions[i]]
        currentState = state.getNextState(currentState, inputVal)
        state.stateAfter[i] = currentState

proc computePenalty[T](state: RegularConstraint[T]): int =
    ## Count invalid transitions + final state check
    result = 0
    var currentState = state.initialState

    for i in 0..<state.n:
        let inputVal = state.currentAssignment[state.sortedPositions[i]]
        let nextState = state.getNextState(currentState, inputVal)
        if nextState == 0:
            result += 1
        currentState = nextState

    # Check final state
    let finalState = if state.n > 0: state.stateAfter[state.n - 1] else: state.initialState
    if finalState notin state.finalStates:
        result += 1

################################################################################
# Initialization and updates
################################################################################

proc initialize*[T](state: RegularConstraint[T], assignment: seq[T]) =
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]
    state.runDFA(0)
    state.cost = state.computePenalty()


proc updatePosition*[T](state: RegularConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return
    state.currentAssignment[position] = newValue
    let idx = state.positionToIndex[position]
    # Re-run DFA from the changed position forward
    state.runDFA(idx)
    state.cost = state.computePenalty()


proc moveDelta*[T](state: RegularConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    # Temporarily change, recompute penalty, restore
    state.currentAssignment[position] = newValue

    # Count penalties from scratch with the temporary change
    var tempCost = 0
    var simState = state.initialState
    for i in 0..<state.n:
        let inputVal = state.currentAssignment[state.sortedPositions[i]]
        let ns = state.getNextState(simState, inputVal)
        if ns == 0:
            tempCost += 1
        simState = ns

    # Check final state
    if simState notin state.finalStates:
        tempCost += 1

    state.currentAssignment[position] = oldValue
    return tempCost - state.cost
