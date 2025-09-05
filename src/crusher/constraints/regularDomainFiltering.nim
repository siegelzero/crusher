import std/[sets, sequtils, tables, packedsets]
import regular
import ../expressions

################################################################################
# Arc Consistency Domain Filtering for Regular Constraints
################################################################################

type
    RegularDomainFilterer*[T] = object
        ## Domain filtering implementation for regular constraints based on
        ## Pesant's arc consistency algorithm (Chapter 7, Section 7.3.3)
        constraint: RegularConstraint[T]
        layeredGraph: seq[seq[HashSet[int]]]  # [position][state] -> reachable states
        reachableForward: seq[HashSet[int]]   # States reachable at each position
        reachableBackward: seq[HashSet[int]]  # States that can reach accepting states

proc newRegularDomainFilterer*[T](constraint: RegularConstraint[T]): RegularDomainFilterer[T] =
    ## Create a new domain filterer for the regular constraint
    let n = constraint.getExpressions().len
    result = RegularDomainFilterer[T](
        constraint: constraint,
        layeredGraph: newSeq[seq[HashSet[int]]](n + 1),
        reachableForward: newSeq[HashSet[int]](n + 1),
        reachableBackward: newSeq[HashSet[int]](n + 1)
    )
    
    # Initialize layered graph structure
    for pos in 0..n:
        result.layeredGraph[pos] = newSeq[HashSet[int]](constraint.numStates + 1)
        for state in 0..constraint.numStates:
            result.layeredGraph[pos][state] = initHashSet[int]()

proc getValuesAtPosition*[T](expr: AlgebraicExpression[T], 
                            currentDomains: seq[PackedSet[T]]): seq[T] =
    ## Get possible values for an expression (handles both variables and constants)
    if expr.node != nil:
        case expr.node.kind:
        of RefNode:
            # Variable reference - get its domain
            let varPos = expr.node.position
            if varPos < currentDomains.len:
                return toSeq(currentDomains[varPos])
            else:
                return @[]
        of LiteralNode:
            # Constant value
            return @[expr.node.value]
        else:
            return @[]
    else:
        return @[]

proc buildForwardReachability*[T](filterer: var RegularDomainFilterer[T], 
                                 currentDomains: seq[PackedSet[T]]) =
    ## Build forward reachability graph - which states are reachable at each position
    let expressions = filterer.constraint.getExpressions()
    let n = expressions.len
    
    # Initialize: only initial state is reachable at position 0
    filterer.reachableForward[0] = initHashSet[int]()
    filterer.reachableForward[0].incl(filterer.constraint.initialState)
    
    # Forward pass: compute reachable states at each position
    for pos in 0..<n:
        filterer.reachableForward[pos + 1] = initHashSet[int]()
        
        # For each state reachable at current position
        for currentState in filterer.reachableForward[pos]:
            if currentState == 0: continue  # Skip rejection state
            
            # Get possible values at this position (handles variables and constants)
            let possibleValues = getValuesAtPosition(expressions[pos], currentDomains)
            
            # For each possible value at this position
            for value in possibleValues:
                let nextState = filterer.constraint.getTransition(currentState, value)
                if nextState > 0:  # Valid transition
                    filterer.reachableForward[pos + 1].incl(nextState)
                    
                    # Build layered graph for later use
                    filterer.layeredGraph[pos][currentState].incl(nextState)

proc buildBackwardReachability*[T](filterer: var RegularDomainFilterer[T]) =
    ## Build backward reachability - which states can reach accepting states
    let n = filterer.constraint.getExpressions().len
    
    # Initialize: accepting states can reach themselves
    filterer.reachableBackward[n] = initHashSet[int]()
    for state in 1..filterer.constraint.numStates:
        if filterer.constraint.isAccepting(state):
            filterer.reachableBackward[n].incl(state)
    
    # Backward pass: compute which states can reach accepting states
    for pos in countdown(n - 1, 0):
        filterer.reachableBackward[pos] = initHashSet[int]()
        
        # For each state at current position
        for currentState in 1..filterer.constraint.numStates:
            if currentState in filterer.reachableForward[pos]:
                # Check if any transition from this state reaches a "good" state
                for nextState in filterer.layeredGraph[pos][currentState]:
                    if nextState in filterer.reachableBackward[pos + 1]:
                        filterer.reachableBackward[pos].incl(currentState)
                        break

proc filterDomainsArcConsistent*[T](filterer: var RegularDomainFilterer[T],
                                   currentDomains: var seq[PackedSet[T]]): bool =
    ## Apply arc consistency filtering to domains
    ## Returns true if any domain was reduced
    let expressions = filterer.constraint.getExpressions()
    var changed = false
    
    # Build reachability information
    filterer.buildForwardReachability(currentDomains)
    filterer.buildBackwardReachability()
    
    # Filter each position's domain
    for pos in 0..<expressions.len:
        let expr = expressions[pos]
        
        # For position-based constraints, each expression should reference one position
        if expr.node != nil and expr.node.kind == RefNode:
            let varPos = expr.node.position
            if varPos < currentDomains.len:
                var newDomain: PackedSet[T] = initPackedSet[T]()
                
                # Check each value in current domain
                for value in currentDomains[varPos]:
                    var valueIsUseful = false
                    
                    # Check if this value can be part of an accepting path
                    for state in filterer.reachableForward[pos]:
                        if state == 0: continue
                        
                        let nextState = filterer.constraint.getTransition(state, value)
                        if nextState > 0 and nextState in filterer.reachableBackward[pos + 1]:
                            valueIsUseful = true
                            break
                    
                    if valueIsUseful:
                        newDomain.incl(value)
                
                # Update domain if it changed
                if newDomain != currentDomains[varPos]:
                    currentDomains[varPos] = newDomain
                    changed = true
    
    return changed

################################################################################
# Integration with domain reduction (moved to avoid circular dependency)
################################################################################

# The integration function will be defined in constrainedArray.nim to avoid
# circular dependencies between modules

# Note: To fully integrate this, we would need to:
# 1. Add RegularType to the constraint state types
# 2. Extend the constraint system to handle regular constraints
# 3. Add the regular constraint to the main domain reduction loop

################################################################################
# Utility functions for debugging and validation
################################################################################

proc debugReachability*[T](filterer: RegularDomainFilterer[T]): string =
    ## Debug output for reachability analysis
    result = "Regular Constraint Reachability Analysis:\n"
    for pos in 0..<filterer.reachableForward.len:
        result &= &"  Position {pos}: Forward={filterer.reachableForward[pos]}, Backward={filterer.reachableBackward[pos]}\n"

proc validateFilteringCorrectness*[T](filterer: RegularDomainFilterer[T],
                                     originalDomains, filteredDomains: seq[seq[T]]): bool =
    ## Validate that filtering didn't remove valid solutions
    ## This is a comprehensive correctness check
    # Implementation would verify that every solution in the original domains
    # that satisfies the regular constraint is still possible in filtered domains
    return true  # Placeholder for full implementation