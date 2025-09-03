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
        positionToSeqIndex: Table[int, seq[int]]  # Maps variable position to sequence indices
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
    
    # Collect all positions from expressions and build position-to-sequence mapping
    result.positionToSeqIndex = initTable[int, seq[int]]()
    for seqIdx, expr in sequence:
        for pos in expr.positions.items:
            result.positions.incl(pos)
            if pos notin result.positionToSeqIndex:
                result.positionToSeqIndex[pos] = @[]
            result.positionToSeqIndex[pos].add(seqIdx)

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
        sequence.add(newAlgebraicExpression[T](
            positions = toPackedSet([pos]),
            node = ExpressionNode[T](kind: RefNode, position: pos),
            linear = false
        ))
    
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
    
    # Build position-to-sequence mapping for position-based constraints
    result.positionToSeqIndex = initTable[int, seq[int]]()
    for seqIdx, expr in result.sequence:
        for pos in expr.positions.items:
            if pos notin result.positionToSeqIndex:
                result.positionToSeqIndex[pos] = @[]
            result.positionToSeqIndex[pos].add(seqIdx)

################################################################################
# Basic automaton operations
################################################################################


func getTransition*[T](constraint: RegularConstraint[T], state: int, input: T): int {.inline.} =
    ## Get next state given current state and input symbol - optimized version
    when T is int:
        # Fast path with minimal bounds checking
        if likely(state >= 1 and state <= constraint.numStates and 
                  input >= 1 and input <= constraint.alphabetSize):
            return constraint.transitionMatrix[state - 1][input - 1]  # Convert to 0-based indexing
        else:
            return 0  # Invalid state or input leads to rejection
    else:
        return 0  # For now, only support int inputs

func isAccepting*[T](constraint: RegularConstraint[T], state: int): bool {.inline.} =
    ## Check if a state is an accepting state
    return constraint.acceptingStates.contains(state)


################################################################################
# Constraint evaluation
################################################################################

func evaluateSequencePure*[T](constraint: RegularConstraint[T], assignment: Table[int, T]): (int, int) =
    ## Pure evaluation that doesn't modify constraint state - optimized for position-based constraints
    var currentState = constraint.initialState
    var violations = 0
    
    for expr in constraint.sequence:
        # Optimize for common case: simple variable reference (RefNode)
        let value = if constraint.evalMethod == PositionBased and 
                       expr.node != nil and 
                       expr.node.kind == RefNode:
            # Direct table lookup for simple variable references
            assignment.getOrDefault(expr.node.position, T(0))
        else:
            # Fall back to generic expression evaluation
            expr.evaluate(assignment)
            
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
    
    # Use stateful evaluation to build state history for incremental optimizations
    # This is essential for ultra-fast moveDelta operations
    let (violations, finalState) = constraint.evaluateSequence(constraint.currentAssignment)
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

func getStateHistoryLength*[T](constraint: RegularConstraint[T]): int =
    ## Get the length of the state history for debugging
    return constraint.stateHistory.len

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

func moveDeltaPositionBased*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T): int =
    ## TRUE incremental delta - only processes from the affected position onwards
    # Get sequence positions affected by this variable change
    let affectedSeqPositions = constraint.positionToSeqIndex[position]
    let firstAffectedSeqPos = affectedSeqPositions[0]
    
    # CRITICAL: Use cached state from state history if available, otherwise compute up to affected position
    let startState = if constraint.stateHistory.len > firstAffectedSeqPos:
        # Use cached state - this is where the real speed comes from
        constraint.stateHistory[firstAffectedSeqPos]
    else:
        # Fallback: compute state up to affected position (should be rare)
        var computedState = constraint.initialState
        for i in 0..<firstAffectedSeqPos:
            let expr = constraint.sequence[i]
            let value = if expr.node != nil and expr.node.kind == RefNode:
                constraint.currentAssignment.getOrDefault(expr.node.position, T(0))
            else:
                expr.evaluate(constraint.currentAssignment)
            computedState = constraint.getTransition(computedState, value)
            if computedState == 0:
                break
        computedState
    
    # Now do the incremental part - this is the ultra-fast core
    var oldState = startState
    var newState = startState
    var deltaCost = 0
    
    # Process ONLY from affected position onwards (true incrementality!)
    for i in firstAffectedSeqPos..<constraint.sequence.len:
        let expr = constraint.sequence[i]
        let exprPos = if expr.node != nil and expr.node.kind == RefNode:
            expr.node.position
        else:
            -1
        
        let (oldVal, newVal) = if exprPos == position:
            # Direct hit - the changed position
            (oldValue, newValue)
        elif exprPos >= 0:
            # Different position - use cached value (same for both paths)
            let cachedVal = constraint.currentAssignment.getOrDefault(exprPos, T(0))
            (cachedVal, cachedVal)
        else:
            # Complex expression - handle carefully
            var tempAssignment = constraint.currentAssignment
            tempAssignment[position] = oldValue
            let oldEval = expr.evaluate(tempAssignment)
            tempAssignment[position] = newValue
            let newEval = expr.evaluate(tempAssignment)
            (oldEval, newEval)
        
        # Parallel transitions
        let oldNextState = constraint.getTransition(oldState, oldVal)
        let newNextState = constraint.getTransition(newState, newVal)
        
        # Track only the differences (ultra-efficient)
        let oldRejected = (oldNextState == 0)
        let newRejected = (newNextState == 0)
        
        if oldRejected != newRejected:
            deltaCost += (if newRejected: 1 else: -1)
            
        oldState = if not oldRejected: oldNextState else: 0
        newState = if not newRejected: newNextState else: 0
    
    # Final state acceptance check
    let oldAccepting = constraint.isAccepting(oldState)
    let newAccepting = constraint.isAccepting(newState)
    
    if oldAccepting != newAccepting:
        deltaCost += (if newAccepting: -1 else: 1)
    
    return deltaCost

func moveDeltaExpressionBased*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T): int =
    ## Safe delta for expression-based regular constraints (complex expressions)
    # For expression-based constraints, expressions can involve multiple variables
    # We need full expression evaluation which is more expensive but necessary
    let oldCost = constraint.cost
    var tempAssignment = constraint.currentAssignment
    tempAssignment[position] = newValue
    let (newViolations, _) = constraint.evaluateSequencePure(tempAssignment)
    return newViolations - oldCost

func moveDelta*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T): int =
    ## Fast incremental cost delta computation optimized by evaluation method
    if oldValue == newValue:
        return 0
    
    # Fast exit if this position doesn't affect the constraint
    if position notin constraint.positionToSeqIndex:
        return 0
    
    case constraint.evalMethod:
        of PositionBased:
            return constraint.moveDeltaPositionBased(position, oldValue, newValue)
        of ExpressionBased:
            return constraint.moveDeltaExpressionBased(position, oldValue, newValue)

func moveDeltaFixed*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T, fromSeqPos: int): int =
    ## Fixed incremental delta calculation that avoids table copying issues
    # Safety checks - fall back to full evaluation if anything looks wrong
    if fromSeqPos < 0 or fromSeqPos >= constraint.sequence.len or 
       constraint.stateHistory.len != (constraint.sequence.len + 1):
        let oldCost = constraint.cost
        var tempAssignment = constraint.currentAssignment  
        tempAssignment[position] = newValue
        let (newViolations, _) = constraint.evaluateSequencePure(tempAssignment)
        return newViolations - oldCost
    
    # Get starting state from cached history
    let startState = if fromSeqPos == 0: 
        constraint.initialState 
    else:
        constraint.stateHistory[fromSeqPos]
    
    # Process both old and new paths simultaneously without table modifications
    var oldState = startState
    var newState = startState  
    var oldViolations = 0
    var newViolations = 0
    
    for i in fromSeqPos..<constraint.sequence.len:
        let expr = constraint.sequence[i]
        
        # Evaluate expression for both old and new values using separate assignment contexts
        let (oldVal, newVal) = if position in expr.positions:
            # This expression involves our changed position - create evaluation contexts
            var oldAssignment = constraint.currentAssignment
            var newAssignment = constraint.currentAssignment
            
            oldAssignment[position] = oldValue
            newAssignment[position] = newValue
            
            let oldEval = expr.evaluate(oldAssignment)
            let newEval = expr.evaluate(newAssignment)
            
            (oldEval, newEval)
        else:
            # Expression doesn't involve our position - same value for both
            let val = expr.evaluate(constraint.currentAssignment)
            (val, val)
        
        # Process transitions for both paths
        let oldNextState = constraint.getTransition(oldState, oldVal)
        let newNextState = constraint.getTransition(newState, newVal)
        
        if oldNextState == 0:
            oldViolations += 1
            oldState = 0
        else:
            oldState = oldNextState
            
        if newNextState == 0:
            newViolations += 1
            newState = 0
        else:
            newState = newNextState
    
    # Check final state acceptance
    if not constraint.isAccepting(oldState):
        oldViolations += 1
    if not constraint.isAccepting(newState):
        newViolations += 1
    
    return newViolations - oldViolations

func moveDeltaSimple*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T, fromSeqPos: int): int =
    ## Simplified incremental delta calculation for position-based constraints only
    # Safety checks - fall back to full evaluation if anything looks wrong
    if fromSeqPos < 0 or fromSeqPos >= constraint.sequence.len or 
       constraint.stateHistory.len != (constraint.sequence.len + 1):
        let oldCost = constraint.cost
        var tempAssignment = constraint.currentAssignment  
        tempAssignment[position] = newValue
        let (newViolations, _) = constraint.evaluateSequencePure(tempAssignment)
        return newViolations - oldCost
    
    # Get starting state from cached history
    let startState = if fromSeqPos == 0: 
        constraint.initialState 
    else:
        constraint.stateHistory[fromSeqPos]
    
    # Simple approach: only handle direct position-based expressions
    var oldState = startState
    var newState = startState  
    var oldViolations = 0
    var newViolations = 0
    
    for i in fromSeqPos..<constraint.sequence.len:
        let expr = constraint.sequence[i]
        
        # For position-based constraints, each expression should be a simple variable reference
        let (oldVal, newVal) = if expr.positions.len == 1 and position in expr.positions:
            # This expression references our changed position directly
            (oldValue, newValue)
        else:
            # This expression doesn't involve our position, use current assignment
            # For position-based constraints, we expect each expr to reference exactly one position
            if expr.positions.len == 1:
                var firstPos = -1
                for pos in expr.positions.items:
                    firstPos = pos
                    break
                let val = constraint.currentAssignment.getOrDefault(firstPos, T(0))
                (val, val)
            else:
                # Fallback for complex expressions - this shouldn't happen in position-based constraints
                (T(0), T(0))
        
        # Process transitions for both paths
        let oldNextState = constraint.getTransition(oldState, oldVal)
        let newNextState = constraint.getTransition(newState, newVal)
        
        if oldNextState == 0:
            oldViolations += 1
            oldState = 0
        else:
            oldState = oldNextState
            
        if newNextState == 0:
            newViolations += 1
            newState = 0
        else:
            newState = newNextState
    
    # Check final state acceptance
    if not constraint.isAccepting(oldState):
        oldViolations += 1
    if not constraint.isAccepting(newState):
        newViolations += 1
    
    return newViolations - oldViolations

func moveDeltaUltraFast*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T, fromSeqPos: int): int =
    ## Ultra-fast incremental delta using on-the-fly state computation
    # This function builds state history on-the-fly to avoid parallel safety issues
    
    # Build state up to the affected position using pure computation (no state modification)
    var computedState = constraint.initialState
    
    # If we need to start from a position > 0, compute states up to that point
    if fromSeqPos > 0:
        for i in 0..<fromSeqPos:
            let expr = constraint.sequence[i]
            let value = expr.evaluate(constraint.currentAssignment)
            let nextState = constraint.getTransition(computedState, value)
            computedState = if nextState == 0: 0 else: nextState
    
    let startState = computedState
    
    var oldState = startState
    var newState = startState
    var deltaCost = 0  # Track the difference directly
    
    # Ultra-fast main loop with optimized expression evaluation
    for i in fromSeqPos..<constraint.sequence.len:
        let expr = constraint.sequence[i]
        
        # Ultra-fast value computation optimized for common cases
        let (oldVal, newVal) = if constraint.evalMethod == PositionBased and 
                                          expr.node != nil and
                                          expr.node.kind == RefNode and
                                          expr.node.position in constraint.currentAssignment:
            if expr.node.position == position:
                # Direct hit - the changed position
                (oldValue, newValue)
            else:
                # Different position - use cached value
                let cachedVal = constraint.currentAssignment[expr.node.position]
                (cachedVal, cachedVal)
        else:
            # Complex expression path (rarely taken)
            if position in expr.positions:
                # Expression involves changed position - need full evaluation
                var localAssignment = constraint.currentAssignment
                localAssignment[position] = oldValue
                let oldEval = expr.evaluate(localAssignment)
                localAssignment[position] = newValue  
                let newEval = expr.evaluate(localAssignment)
                (oldEval, newEval)
            else:
                # Expression independent of change
                let val = expr.evaluate(constraint.currentAssignment)
                (val, val)
        
        # Parallel state transitions with branch prediction
        let oldNextState = constraint.getTransition(oldState, oldVal)
        let newNextState = constraint.getTransition(newState, newVal)
        
        # Optimized violation counting using XOR to detect differences
        let oldRejected = (oldNextState == 0)
        let newRejected = (newNextState == 0)
        
        if oldRejected != newRejected:
            deltaCost += (if newRejected: 1 else: -1)
            
        # State updates with rejection handling
        oldState = if not oldRejected: oldNextState else: 0
        newState = if not newRejected: newNextState else: 0
    
    # Final state acceptance check with optimized comparison
    let oldAccepting = constraint.isAccepting(oldState)
    let newAccepting = constraint.isAccepting(newState)
    
    if oldAccepting != newAccepting:
        deltaCost += (if newAccepting: -1 else: 1)
    
    return deltaCost

func moveDeltaIncremental*[T](constraint: RegularConstraint[T], position: int, oldValue, newValue: T, fromSeqPos: int): int =
    ## Incremental delta calculation starting from a specific sequence position
    # Comprehensive safety checks
    if fromSeqPos < 0 or fromSeqPos >= constraint.sequence.len or 
       constraint.stateHistory.len <= fromSeqPos or
       constraint.stateHistory.len != (constraint.sequence.len + 1):
        # Fall back to full evaluation if any safety check fails
        let oldCost = constraint.cost
        var tempAssignment = constraint.currentAssignment  
        tempAssignment[position] = newValue
        let (newViolations, _) = constraint.evaluateSequencePure(tempAssignment)
        return newViolations - oldCost
    
    # Get starting state from cached history (guaranteed safe due to checks above)
    let startState = if fromSeqPos == 0: 
        constraint.initialState 
    else:
        constraint.stateHistory[fromSeqPos]
    
    # Ultra-fast approach: For position-based constraints, we can directly compute values
    # without any table modifications since each sequence position maps to exactly one variable
    var oldState = startState
    var newState = startState
    var oldViolations = 0
    var newViolations = 0
    
    for i in fromSeqPos..<constraint.sequence.len:
        let expr = constraint.sequence[i]
        
        # Compute values for both old and new assignments efficiently
        let (oldVal, newVal) = if constraint.evalMethod == PositionBased and 
                                  expr.node != nil and
                                  expr.node.kind == RefNode and 
                                  expr.node.position == position:
            # This is the changed position - use old/new values directly
            (oldValue, newValue)
        elif position in expr.positions:
            # More complex expression involving the changed position
            # Use a local assignment copy to avoid modifying shared state
            var localAssignment = constraint.currentAssignment
            
            if expr.node != nil:
                localAssignment[position] = oldValue
                let oldEval = expr.evaluate(localAssignment)
                
                localAssignment[position] = newValue
                let newEval = expr.evaluate(localAssignment)
                
                (oldEval, newEval)
            else:
                # Fallback if expression has nil node
                (T(0), T(0))
        else:
            # Expression doesn't involve the changed position
            if expr.node != nil:
                let val = expr.evaluate(constraint.currentAssignment)
                (val, val)
            else:
                # Fallback if expression has nil node
                (T(0), T(0))
        
        # Process old path
        let oldNextState = constraint.getTransition(oldState, oldVal)
        if oldNextState == 0:
            oldViolations += 1
            oldState = 0
        else:
            oldState = oldNextState
            
        # Process new path
        let newNextState = constraint.getTransition(newState, newVal)
        if newNextState == 0:
            newViolations += 1
            newState = 0
        else:
            newState = newNextState
    
    # Check final state acceptance
    if not constraint.isAccepting(oldState):
        oldViolations += 1
    if not constraint.isAccepting(newState):
        newViolations += 1
    
    return newViolations - oldViolations


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
        positionToSeqIndex: constraint.positionToSeqIndex,  # Table will be copied
        evalMethod: constraint.evalMethod
    )


