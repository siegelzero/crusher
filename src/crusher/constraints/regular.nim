import std/[packedsets, sequtils, tables, sets]

import ../expressions
import common

################################################################################
# Type definitions
################################################################################

type
    RegularConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        # Automaton definition
        numStates*: int
        alphabetSize*: int
        transitionMatrix*: seq[seq[int]]  # [state][input] -> next_state (0 = rejection)
        initialState*: int
        acceptingStates*: HashSet[int]
        # State tracking
        sequence: seq[AlgebraicExpression[T]]
        currentState: int
        stateHistory: seq[int]  # State at each position in sequence
        positions*: PackedSet[int]
        # Incremental update optimization
        lastValidPosition: int  # Last position that was successfully processed
        partialCost: int        # Cost accumulated up to lastValidPosition
        # Evaluation method
        evalMethod: StateEvalMethod

################################################################################
# Constructor functions
################################################################################

func newRegularConstraint*[T](
    sequence: seq[AlgebraicExpression[T]], 
    numStates: int,
    alphabetSize: int, 
    transitionMatrix: seq[seq[int]],
    initialState: int,
    acceptingStates: HashSet[int]
): RegularConstraint[T] =
    ## Create a new regular constraint from a sequence of expressions
    new(result)
    result = RegularConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        numStates: numStates,
        alphabetSize: alphabetSize,
        transitionMatrix: transitionMatrix,
        initialState: initialState,
        acceptingStates: acceptingStates,
        sequence: sequence,
        currentState: initialState,
        stateHistory: @[initialState],
        currentAssignment: initTable[int, T](),
        positions: initPackedSet[int]()
    )
    
    # Collect all positions from expressions
    for expr in sequence:
        for pos in expr.positions.items:
            result.positions.incl(pos)

func newRegularConstraint*[T](
    positions: openArray[int],
    numStates: int,
    alphabetSize: int, 
    transitionMatrix: seq[seq[int]],
    initialState: int,
    acceptingStates: HashSet[int]
): RegularConstraint[T] =
    ## Create a new regular constraint from position indices
    new(result)
    
    # Convert positions to expressions
    var sequence: seq[AlgebraicExpression[T]] = @[]
    for pos in positions:
        sequence.add(newAlgebraicExpression[T](pos))
    
    result = RegularConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        numStates: numStates,
        alphabetSize: alphabetSize,
        transitionMatrix: transitionMatrix,
        initialState: initialState,
        acceptingStates: acceptingStates,
        sequence: sequence,
        currentState: initialState,
        stateHistory: @[initialState],
        currentAssignment: initTable[int, T](),
        positions: toPackedSet[int](positions)
    )

################################################################################
# Basic automaton operations
################################################################################

func isValidInput[T](constraint: RegularConstraint[T], input: T): bool =
    ## Check if input is valid for the automaton alphabet
    when T is int:
        return input >= 1 and input <= constraint.alphabetSize
    else:
        return true  # For now, assume other types are valid

func getTransition*[T](constraint: RegularConstraint[T], state: int, input: T): int =
    ## Get next state given current state and input symbol
    if state < 1 or state > constraint.numStates:
        return 0  # Invalid state leads to rejection
    
    when T is int:
        if input < 1 or input > constraint.alphabetSize:
            return 0  # Invalid input leads to rejection
        return constraint.transitionMatrix[state - 1][input - 1]  # Convert to 0-based indexing
    else:
        return 0  # For now, only support int inputs

func isAccepting*[T](constraint: RegularConstraint[T], state: int): bool =
    ## Check if a state is an accepting state
    return constraint.acceptingStates.contains(state)

func resetAutomaton[T](constraint: RegularConstraint[T]) =
    ## Reset automaton to initial state
    constraint.currentState = constraint.initialState
    constraint.stateHistory = @[constraint.initialState]

################################################################################
# Constraint evaluation
################################################################################

func evaluateSequencePure*[T](constraint: RegularConstraint[T], assignment: Table[int, T]): (int, int) =
    ## Pure evaluation that doesn't modify constraint state
    var currentState = constraint.initialState
    var violations = 0
    
    for expr in constraint.sequence:
        let value = expr.evaluate(assignment)
        let nextState = constraint.getTransition(currentState, value)
        
        if nextState == 0:
            # Invalid transition - count as violation and stay in rejection state
            violations += 1
            currentState = 0
        else:
            currentState = nextState
    
    # Check if final state is accepting
    if not constraint.isAccepting(currentState):
        violations += 1
    
    return (violations, currentState)

proc evaluateSequence[T](constraint: RegularConstraint[T], assignment: Table[int, T]): (int, int) =
    ## Evaluate the sequence and update constraint state history
    var currentState = constraint.initialState
    var violations = 0
    
    # Clear and rebuild state history
    constraint.stateHistory.setLen(0)
    constraint.stateHistory.add(currentState)
    
    for i, expr in constraint.sequence:
        let value = expr.evaluate(assignment)
        let nextState = constraint.getTransition(currentState, value)
        
        if nextState == 0:
            # Invalid transition - count as violation and stay in rejection state
            violations += 1
            currentState = 0
        else:
            currentState = nextState
            
        constraint.stateHistory.add(currentState)
    
    # Check if final state is accepting
    if not constraint.isAccepting(currentState):
        violations += 1
    
    return (violations, currentState)

func evaluateSequenceIncremental[T](constraint: RegularConstraint[T], assignment: Table[int, T], changedPosition: int): (int, int) =
    ## Incrementally evaluate from a changed position, reusing previous computation
    var currentState = constraint.initialState
    var violations = 0
    
    # If we can reuse computation up to the changed position
    if changedPosition > 0 and changedPosition <= constraint.stateHistory.len - 1:
        # Start from the state just before the changed position
        currentState = constraint.stateHistory[changedPosition]
        violations = constraint.partialCost
        
        # Evaluate from changed position onwards
        for i in changedPosition..<constraint.sequence.len:
            let expr = constraint.sequence[i]
            let value = expr.evaluate(assignment)
            let nextState = constraint.getTransition(currentState, value)
            
            if nextState == 0:
                violations += 1
                currentState = 0
            else:
                currentState = nextState
                
            # Update state history from this position
            if i + 1 < constraint.stateHistory.len:
                constraint.stateHistory[i + 1] = currentState
            else:
                constraint.stateHistory.add(currentState)
    else:
        # Fall back to full evaluation
        return constraint.evaluateSequence(assignment)
    
    # Check if final state is accepting
    if not constraint.isAccepting(currentState):
        violations += 1
    
    return (violations, currentState)

################################################################################
# State management for incremental updates
################################################################################

func initialize*[T](constraint: RegularConstraint[T], assignment: seq[T]) =
    ## Initialize the regular constraint with a full assignment
    constraint.cost = 0
    constraint.currentAssignment.clear()
    constraint.currentState = constraint.initialState
    constraint.stateHistory = @[constraint.initialState]
    
    # Build assignment table from positions
    for pos in constraint.positions.items:
        if pos < assignment.len:
            constraint.currentAssignment[pos] = assignment[pos]
    
    # Evaluate the full sequence and update state history (safe during initialization)
    let (violations, finalState) = constraint.evaluateSequence(constraint.currentAssignment)
    constraint.cost = violations
    constraint.currentState = finalState

func updatePosition*[T](constraint: RegularConstraint[T], position: int, newValue: T) =
    ## Update assignment for a specific position and recompute cost efficiently
    constraint.currentAssignment[position] = newValue
    
    # Use pure evaluation to avoid modifying state history during parallel execution
    let (violations, finalState) = constraint.evaluateSequencePure(constraint.currentAssignment)
    constraint.cost = violations
    constraint.currentState = finalState

func getCost*[T](constraint: RegularConstraint[T]): int =
    ## Get current constraint violation cost
    return constraint.cost

func getPositions*[T](constraint: RegularConstraint[T]): PackedSet[int] =
    ## Get all positions this constraint depends on
    return constraint.positions

func getExpressions*[T](constraint: RegularConstraint[T]): seq[AlgebraicExpression[T]] =
    ## Get the sequence expressions
    return constraint.sequence

################################################################################
# Validation and debugging
################################################################################

func validateAutomaton*[T](constraint: RegularConstraint[T]): bool =
    ## Validate that the automaton definition is well-formed
    # Check state bounds
    if constraint.initialState < 1 or constraint.initialState > constraint.numStates:
        return false
    
    # Check accepting states
    for state in constraint.acceptingStates.items:
        if state < 1 or state > constraint.numStates:
            return false
    
    # Check transition matrix dimensions
    if constraint.transitionMatrix.len != constraint.numStates:
        return false
    
    for row in constraint.transitionMatrix:
        if row.len != constraint.alphabetSize:
            return false
        
        # Check that all transitions lead to valid states or rejection (0)
        for nextState in row:
            if nextState < 0 or nextState > constraint.numStates:
                return false
    
    return true

func debugInfo*[T](constraint: RegularConstraint[T]): string =
    ## Get debug information about the constraint state
    result = "RegularConstraint:\n"
    result &= "  States: " & $constraint.numStates & "\n"
    result &= "  Alphabet: " & $constraint.alphabetSize & "\n"
    result &= "  Current State: " & $constraint.currentState & "\n"
    result &= "  Cost: " & $constraint.cost & "\n"
    result &= "  Sequence Length: " & $constraint.sequence.len & "\n"
    result &= "  Positions: " & $constraint.positions.len

################################################################################
# Deep copy for parallel processing
################################################################################

func deepCopy*[T](constraint: RegularConstraint[T]): RegularConstraint[T] =
    ## Create a deep copy of the regular constraint
    result = RegularConstraint[T](
        currentAssignment: constraint.currentAssignment,  # Table is value type, will copy
        cost: constraint.cost,
        # Deep copy automaton definition
        numStates: constraint.numStates,
        alphabetSize: constraint.alphabetSize,
        transitionMatrix: constraint.transitionMatrix,  # seq is deep copied
        initialState: constraint.initialState,
        acceptingStates: constraint.acceptingStates,  # HashSet will be copied
        # Deep copy state tracking
        sequence: constraint.sequence,  # seq of expressions will be copied
        currentState: constraint.currentState,
        stateHistory: constraint.stateHistory,  # seq will be copied
        positions: constraint.positions,  # PackedSet is value type
        # Copy optimization fields
        lastValidPosition: constraint.lastValidPosition,
        partialCost: constraint.partialCost,
        evalMethod: constraint.evalMethod
    )

