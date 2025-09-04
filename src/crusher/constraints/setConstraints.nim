import std/[packedsets, tables, sequtils]
import ../expressions

################################################################################
# Type definitions for Set Constraints
################################################################################

type
    SetConstraintType* = enum
        SetMembershipType,      # set_in: element ∈ set
        SetCardinalityType,     # set_card: |set| = cardinality  
        SetEqualityType,        # set_eq: setA = setB
        SetSubsetType          # set_subset: setA ⊆ setB

    SetMembershipConstraint*[T] = ref object
        elementPosition*: int        # Variable position for element
        setPositions*: PackedSet[int] # Variable positions for the set (boolean variables)
        universe*: seq[int]         # Ordered elements that could be in the set (matches setPositions order)
        universeSet*: PackedSet[int] # O(1) universe membership testing
        currentAssignment*: Table[int, T] # Current variable assignments
        elementValue*: T            # Cached current element value
        isMember*: bool             # Cached membership status
        cost*: int                  # Violation cost (0 = satisfied, 1 = violated)
        setPositionsSeq*: seq[int]  # Cached conversion of setPositions to seq for performance
        
    SetCardinalityConstraint*[T] = ref object
        setPositions*: PackedSet[int] # Variable positions for the set (boolean variables)
        cardinalityPosition*: int   # Variable position for cardinality
        currentAssignment*: Table[int, T] # Current variable assignments
        cardinalityValue*: T        # Cached current cardinality variable value
        actualCardinality*: int     # Cached actual set cardinality
        cost*: int                  # Violation cost (abs difference)
        
    SetEqualityConstraint*[T] = ref object
        setAPositions*: PackedSet[int] # Variable positions for first set
        setBPositions*: PackedSet[int] # Variable positions for second set
        currentAssignment*: Table[int, T] # Current variable assignments
        differenceCount*: int       # Number of elements in symmetric difference
        cost*: int                  # Violation cost (0 = equal, >0 = different)
        
    SetSubsetConstraint*[T] = ref object
        subsetPositions*: PackedSet[int]   # Variable positions for subset
        supersetPositions*: PackedSet[int] # Variable positions for superset
        currentAssignment*: Table[int, T]  # Current variable assignments
        violationCount*: int        # Number of elements in subset but not superset
        cost*: int                  # Violation cost

    SetMembershipReifConstraint*[T] = ref object
        elementPosition*: int        # Variable position for element
        setPositions*: PackedSet[int] # Variable positions for the set (boolean variables)
        universe*: seq[int]         # Ordered elements that could be in the set (matches setPositions order)
        universeSet*: PackedSet[int] # O(1) universe membership testing
        boolPosition*: int          # Variable position for boolean result
        currentAssignment*: Table[int, T] # Current variable assignments
        elementValue*: T            # Cached current element value
        boolValue*: T               # Cached current boolean value
        isMember*: bool             # Cached membership status  
        cost*: int                  # Violation cost (0 = satisfied, 1 = violated)
        setPositionsSeq*: seq[int]  # Cached conversion of setPositions to seq for performance

################################################################################  
# SetMembershipConstraint (set_in) implementation
################################################################################

func newSetMembershipConstraint*[T](elementPosition: int, setPositions: PackedSet[int], universe: seq[int]): SetMembershipConstraint[T] =
    result = SetMembershipConstraint[T](
        elementPosition: elementPosition,
        setPositions: setPositions,
        universe: universe,
        universeSet: universe.toPackedSet(),  # O(1) universe membership testing
        currentAssignment: initTable[int, T](),
        elementValue: default(T),
        isMember: false,
        cost: 1,  # Initially violated until initialized
        setPositionsSeq: toSeq(setPositions)  # Cache the conversion
    )

proc checkMembership[T](state: SetMembershipConstraint[T], elementValue: int): bool {.inline.} =
    ## Helper to check if an element value is in the current set
    if state.setPositions.len == 0:
        # Constant set case - O(1) lookup
        return elementValue in state.universeSet
    else:
        # Variable set case - single pass through universe
        for i, universeElement in state.universe:
            if universeElement == elementValue:
                return int(state.currentAssignment[state.setPositionsSeq[i]]) == 1
        return false  # Element not in universe

proc initialize*[T](state: SetMembershipConstraint[T], assignment: seq[T]) =
    # Store all relevant assignments
    state.currentAssignment.clear()
    state.currentAssignment[state.elementPosition] = assignment[state.elementPosition]
    for pos in state.setPositions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Get current element value
    state.elementValue = assignment[state.elementPosition]
    let elementValue = int(state.elementValue)
    
    # Check if element is in the current set
    state.isMember = state.checkMembership(elementValue)
    
    state.cost = if state.isMember: 0 else: 1

proc updatePosition*[T](state: SetMembershipConstraint[T], position: int, newValue: T) {.inline.} =
    # Update our local assignment tracking
    state.currentAssignment[position] = newValue
    
    if position == state.elementPosition:
        # Element changed - recalculate membership
        state.elementValue = newValue
        let elementValue = int(newValue)
        state.isMember = state.checkMembership(elementValue)
                    
    elif position in state.setPositions:
        # Set membership changed - only update if this affects current element
        let currentElementValue = int(state.elementValue)
        if currentElementValue in state.universe:
            for i, universeElement in state.universe:
                if universeElement == currentElementValue:
                    if state.setPositionsSeq[i] == position:
                        # This position change affects our element
                        state.isMember = int(newValue) == 1
                        break
    
    state.cost = if state.isMember: 0 else: 1

proc moveDelta*[T](state: SetMembershipConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    if position == state.elementPosition:
        # Element variable changed - use cached membership for old value
        let oldElementValue = int(oldValue)
        let newElementValue = int(newValue)
        
        if oldElementValue == newElementValue:
            return 0  # No change
        
        # OLD: Use cached membership status (optimization!)
        let oldMember = state.isMember
        
        # NEW: Only calculate new membership  
        let newMember = state.checkMembership(newElementValue)
        
        # Return cost delta
        let oldCost = if oldMember: 0 else: 1
        let newCost = if newMember: 0 else: 1
        return newCost - oldCost
        
    elif position in state.setPositions:
        # Set membership position changed
        let oldInSet = int(oldValue) == 1
        let newInSet = int(newValue) == 1
        
        if oldInSet == newInSet:
            return 0  # No change in membership
        
        # Check if this position affects current element
        let currentElementValue = int(state.elementValue)
        if currentElementValue in state.universe:
            for i, universeElement in state.universe:
                if universeElement == currentElementValue:
                    if state.setPositionsSeq[i] == position:
                        # This change affects our element's membership
                        let oldCost = if oldInSet: 0 else: 1
                        let newCost = if newInSet: 0 else: 1
                        return newCost - oldCost
                    break
    
    return 0  # No change

################################################################################
# SetCardinalityConstraint (set_card) implementation  
################################################################################

func newSetCardinalityConstraint*[T](setPositions: PackedSet[int], cardinalityPosition: int): SetCardinalityConstraint[T] =
    result = SetCardinalityConstraint[T](
        setPositions: setPositions,
        cardinalityPosition: cardinalityPosition,
        currentAssignment: initTable[int, T](),
        cardinalityValue: default(T),
        actualCardinality: 0,
        cost: 0
    )

proc initialize*[T](state: SetCardinalityConstraint[T], assignment: seq[T]) =
    # Store all relevant assignments
    state.currentAssignment.clear()
    state.currentAssignment[state.cardinalityPosition] = assignment[state.cardinalityPosition]
    for pos in state.setPositions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Get current cardinality variable value
    state.cardinalityValue = assignment[state.cardinalityPosition]
    
    # Calculate actual set cardinality by counting 1s in set positions
    state.actualCardinality = 0
    for pos in state.setPositions:
        if int(assignment[pos]) == 1:
            state.actualCardinality += 1
    
    state.cost = abs(int(state.cardinalityValue) - state.actualCardinality)

proc updatePosition*[T](state: SetCardinalityConstraint[T], position: int, newValue: T) {.inline.} =
    # Update our local assignment tracking
    state.currentAssignment[position] = newValue
    
    if position == state.cardinalityPosition:
        # Cardinality variable changed
        state.cardinalityValue = newValue
        state.cost = abs(int(newValue) - state.actualCardinality)
        
    elif position in state.setPositions:
        # Set membership changed - recalculate actual cardinality
        let oldValue = state.currentAssignment.getOrDefault(position, default(T))
        let oldInSet = int(oldValue) == 1  
        let newInSet = int(newValue) == 1
        
        if oldInSet != newInSet:
            if newInSet:
                state.actualCardinality += 1
            else:
                state.actualCardinality -= 1
                
            state.cost = abs(int(state.cardinalityValue) - state.actualCardinality)

proc moveDelta*[T](state: SetCardinalityConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    if position == state.cardinalityPosition:
        # Cardinality variable changed
        let oldCost = abs(int(oldValue) - state.actualCardinality)
        let newCost = abs(int(newValue) - state.actualCardinality)
        return newCost - oldCost
        
    elif position in state.setPositions:
        # Set membership changed
        let oldInSet = int(oldValue) == 1
        let newInSet = int(newValue) == 1
        
        if oldInSet == newInSet:
            return 0  # No change in membership
        
        # Calculate new actual cardinality
        let newActualCardinality = if newInSet: 
            state.actualCardinality + 1 
        else: 
            state.actualCardinality - 1
            
        let oldCost = abs(int(state.cardinalityValue) - state.actualCardinality)
        let newCost = abs(int(state.cardinalityValue) - newActualCardinality)
        return newCost - oldCost
    
    return 0

################################################################################
# SetEqualityConstraint (set_eq) implementation
################################################################################

func newSetEqualityConstraint*[T](setAPositions: PackedSet[int], setBPositions: PackedSet[int]): SetEqualityConstraint[T] =
    result = SetEqualityConstraint[T](
        setAPositions: setAPositions,
        setBPositions: setBPositions,
        currentAssignment: initTable[int, T](),
        differenceCount: 0,
        cost: 0
    )

proc initialize*[T](state: SetEqualityConstraint[T], assignment: seq[T]) =
    # Store all relevant assignments
    state.currentAssignment.clear()
    for pos in state.setAPositions:
        state.currentAssignment[pos] = assignment[pos]
    for pos in state.setBPositions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Calculate symmetric difference count
    # Must have same size to use paired comparison (assumes same universe)
    if state.setAPositions.len != state.setBPositions.len:
        # Sets have different universes - count all differences
        let cardinalityA = toSeq(state.setAPositions).countIt(int(assignment[it]) == 1)
        let cardinalityB = toSeq(state.setBPositions).countIt(int(assignment[it]) == 1)
        state.differenceCount = abs(cardinalityA - cardinalityB) + 
                               max(cardinalityA, cardinalityB)
    else:
        # Assume same universe, compare position by position
        state.differenceCount = 0
        let setASeq = toSeq(state.setAPositions)
        let setBSeq = toSeq(state.setBPositions)
        for i in 0..<setASeq.len:
            let aInSet = int(assignment[setASeq[i]]) == 1
            let bInSet = int(assignment[setBSeq[i]]) == 1
            if aInSet != bInSet:
                state.differenceCount += 1
    
    state.cost = state.differenceCount

proc updatePosition*[T](state: SetEqualityConstraint[T], position: int, newValue: T) {.inline.} =
    # Update our local assignment tracking
    state.currentAssignment[position] = newValue
    
    if position in state.setAPositions or position in state.setBPositions:
        # Recalculate difference count
        if state.setAPositions.len != state.setBPositions.len:
            # Different universes
            let cardinalityA = toSeq(state.setAPositions).countIt(int(state.currentAssignment[it]) == 1)
            let cardinalityB = toSeq(state.setBPositions).countIt(int(state.currentAssignment[it]) == 1)
            state.differenceCount = abs(cardinalityA - cardinalityB) + 
                                   max(cardinalityA, cardinalityB)
        else:
            # Same universe - paired comparison
            state.differenceCount = 0
            let setASeq = toSeq(state.setAPositions)
            let setBSeq = toSeq(state.setBPositions)
            for i in 0..<setASeq.len:
                let aInSet = int(state.currentAssignment[setASeq[i]]) == 1
                let bInSet = int(state.currentAssignment[setBSeq[i]]) == 1
                if aInSet != bInSet:
                    state.differenceCount += 1
                    
        state.cost = state.differenceCount

proc moveDelta*[T](state: SetEqualityConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    if position notin state.setAPositions and position notin state.setBPositions:
        return 0  # Position doesn't affect either set
    
    let oldInSet = int(oldValue) == 1
    let newInSet = int(newValue) == 1
    
    if oldInSet == newInSet:
        return 0  # No change in membership
    
    # Calculate impact on difference count
    if state.setAPositions.len != state.setBPositions.len:
        # Different universes - any change affects the cost
        return if newInSet: 1 else: -1
    else:
        # Same universe - find corresponding position
        let setASeq = toSeq(state.setAPositions)
        let setBSeq = toSeq(state.setBPositions)
        
        for i in 0..<setASeq.len:
            if setASeq[i] == position:
                # Position is in setA, check setB
                let bInSet = int(state.currentAssignment[setBSeq[i]]) == 1
                if oldInSet == bInSet and newInSet != bInSet:
                    return 1  # Was equal, now different
                elif oldInSet != bInSet and newInSet == bInSet:
                    return -1  # Was different, now equal
                break
            elif setBSeq[i] == position:
                # Position is in setB, check setA  
                let aInSet = int(state.currentAssignment[setASeq[i]]) == 1
                if oldInSet == aInSet and newInSet != aInSet:
                    return 1  # Was equal, now different
                elif oldInSet != aInSet and newInSet == aInSet:
                    return -1  # Was different, now equal
                break
    
    return 0

################################################################################
# SetSubsetConstraint (set_subset) implementation
################################################################################

func newSetSubsetConstraint*[T](subsetPositions: PackedSet[int], supersetPositions: PackedSet[int]): SetSubsetConstraint[T] =
    result = SetSubsetConstraint[T](
        subsetPositions: subsetPositions,
        supersetPositions: supersetPositions,
        currentAssignment: initTable[int, T](),
        violationCount: 0,
        cost: 0
    )

proc initialize*[T](state: SetSubsetConstraint[T], assignment: seq[T]) =
    # Store all relevant assignments
    state.currentAssignment.clear()
    for pos in state.subsetPositions:
        state.currentAssignment[pos] = assignment[pos]
    for pos in state.supersetPositions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Count elements in subset but not in superset
    state.violationCount = 0
    if state.subsetPositions.len != state.supersetPositions.len:
        # Different universes - simplified approach
        let subsetCardinality = toSeq(state.subsetPositions).countIt(int(assignment[it]) == 1)
        let supersetCardinality = toSeq(state.supersetPositions).countIt(int(assignment[it]) == 1)
        state.violationCount = max(0, subsetCardinality - supersetCardinality)
    else:
        # Same universe - paired comparison
        let subsetSeq = toSeq(state.subsetPositions)
        let supersetSeq = toSeq(state.supersetPositions)
        for i in 0..<subsetSeq.len:
            let inSubset = int(assignment[subsetSeq[i]]) == 1
            let inSuperset = int(assignment[supersetSeq[i]]) == 1
            if inSubset and not inSuperset:
                state.violationCount += 1
    
    state.cost = state.violationCount

proc updatePosition*[T](state: SetSubsetConstraint[T], position: int, newValue: T) {.inline.} =
    # Update our local assignment tracking
    state.currentAssignment[position] = newValue
    
    if position in state.subsetPositions or position in state.supersetPositions:
        # Recalculate violation count
        state.violationCount = 0
        if state.subsetPositions.len != state.supersetPositions.len:
            # Different universes
            let subsetCardinality = toSeq(state.subsetPositions).countIt(int(state.currentAssignment[it]) == 1)
            let supersetCardinality = toSeq(state.supersetPositions).countIt(int(state.currentAssignment[it]) == 1)
            state.violationCount = max(0, subsetCardinality - supersetCardinality)
        else:
            # Same universe - paired comparison
            let subsetSeq = toSeq(state.subsetPositions)
            let supersetSeq = toSeq(state.supersetPositions)
            for i in 0..<subsetSeq.len:
                let inSubset = int(state.currentAssignment[subsetSeq[i]]) == 1
                let inSuperset = int(state.currentAssignment[supersetSeq[i]]) == 1
                if inSubset and not inSuperset:
                    state.violationCount += 1
                    
        state.cost = state.violationCount

proc moveDelta*[T](state: SetSubsetConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    if position notin state.subsetPositions and position notin state.supersetPositions:
        return 0  # Position doesn't affect either set
    
    let oldInSet = int(oldValue) == 1
    let newInSet = int(newValue) == 1
    
    if oldInSet == newInSet:
        return 0  # No change in membership
    
    # Calculate impact on violation count
    if state.subsetPositions.len != state.supersetPositions.len:
        # Different universes - simplified approach
        if position in state.subsetPositions:
            return if newInSet: 1 else: -1  # Adding/removing from subset
        else:  # position in superset
            return if newInSet: -1 else: 1  # Adding to superset reduces violations
    else:
        # Same universe - find corresponding position
        let subsetSeq = toSeq(state.subsetPositions)
        let supersetSeq = toSeq(state.supersetPositions)
        
        for i in 0..<subsetSeq.len:
            if subsetSeq[i] == position:
                # Position is in subset, check superset
                let inSuperset = int(state.currentAssignment[supersetSeq[i]]) == 1
                if oldInSet and not inSuperset and not newInSet:
                    return -1  # Removed violation (was in subset but not superset)
                elif not oldInSet and not inSuperset and newInSet:
                    return 1  # Added violation (now in subset but not superset)
                break
            elif supersetSeq[i] == position:
                # Position is in superset, check subset
                let inSubset = int(state.currentAssignment[subsetSeq[i]]) == 1
                if inSubset and not oldInSet and newInSet:
                    return -1  # Removed violation (subset element now in superset)
                elif inSubset and oldInSet and not newInSet:
                    return 1  # Added violation (subset element no longer in superset)
                break
    
    return 0

################################################################################
# SetMembershipReifConstraint (set_in_reif) implementation
################################################################################

func newSetMembershipReifConstraint*[T](elementPosition: int, setPositions: PackedSet[int], universe: seq[int], boolPosition: int): SetMembershipReifConstraint[T] =
    result = SetMembershipReifConstraint[T](
        elementPosition: elementPosition,
        setPositions: setPositions,
        universe: universe,
        universeSet: universe.toPackedSet(),  # O(1) universe membership testing
        boolPosition: boolPosition,
        currentAssignment: initTable[int, T](),
        elementValue: default(T),
        boolValue: default(T),
        isMember: false,
        cost: 1,  # Initially violated until initialized
        setPositionsSeq: toSeq(setPositions)  # Cache the conversion
    )

proc checkElementMembership[T](state: SetMembershipReifConstraint[T], elementValue: int): bool {.inline.} =
    ## Helper to check if an element value is in the current set
    if state.setPositions.len == 0:
        # Constant set case - O(1) lookup
        return elementValue in state.universeSet
    else:
        # Variable set case - single pass through universe
        for i, universeElement in state.universe:
            if universeElement == elementValue:
                return int(state.currentAssignment[state.setPositionsSeq[i]]) == 1
        return false  # Element not in universe

proc initialize*[T](state: SetMembershipReifConstraint[T], assignment: seq[T]) =
    # Store all relevant assignments
    state.currentAssignment.clear()
    state.currentAssignment[state.elementPosition] = assignment[state.elementPosition]
    state.currentAssignment[state.boolPosition] = assignment[state.boolPosition]
    for pos in state.setPositions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Get current values
    state.elementValue = assignment[state.elementPosition]
    state.boolValue = assignment[state.boolPosition]
    let elementValue = int(state.elementValue)
    
    # Check if element is in the current set
    state.isMember = state.checkElementMembership(elementValue)
    
    # Calculate cost: boolean should match membership
    let boolSaysTrue = int(state.boolValue) == 1
    state.cost = if boolSaysTrue == state.isMember: 0 else: 1

proc updatePosition*[T](state: SetMembershipReifConstraint[T], position: int, newValue: T) {.inline.} =
    # Update our local assignment tracking
    state.currentAssignment[position] = newValue
    
    if position == state.elementPosition:
        # Element changed - recalculate membership
        state.elementValue = newValue
        let elementValue = int(newValue)
        state.isMember = state.checkElementMembership(elementValue)
                    
    elif position == state.boolPosition:
        # Boolean result changed
        state.boolValue = newValue
        
    elif position in state.setPositions:
        # Set membership changed - only update if this affects current element
        let currentElementValue = int(state.elementValue)
        if currentElementValue in state.universe:
            for i, universeElement in state.universe:
                if universeElement == currentElementValue:
                    if state.setPositionsSeq[i] == position:
                        # This position change affects our element
                        state.isMember = int(newValue) == 1
                        break
    
    # Recalculate cost: boolean should match membership
    let boolSaysTrue = int(state.boolValue) == 1
    state.cost = if boolSaysTrue == state.isMember: 0 else: 1

proc moveDelta*[T](state: SetMembershipReifConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    if position == state.elementPosition:
        # Element variable changed - use cached membership for old value
        let oldElementValue = int(oldValue)
        let newElementValue = int(newValue)
        
        if oldElementValue == newElementValue:
            return 0  # No change
        
        # OLD: Use cached membership status (this is the key optimization!)
        let oldMember = state.isMember
        
        # NEW: Only calculate new membership
        let newMember = state.checkElementMembership(newElementValue)
        
        # Calculate cost delta
        let boolSaysTrue = int(state.boolValue) == 1
        let oldCost = if boolSaysTrue == oldMember: 0 else: 1
        let newCost = if boolSaysTrue == newMember: 0 else: 1
        return newCost - oldCost
        
    elif position == state.boolPosition:
        # Boolean result variable changed
        let oldBoolSaysTrue = int(oldValue) == 1
        let newBoolSaysTrue = int(newValue) == 1
        
        if oldBoolSaysTrue == newBoolSaysTrue:
            return 0  # No change in boolean value
        
        # Cost delta based on whether new/old boolean matches membership (use cached membership)
        let oldCost = if oldBoolSaysTrue == state.isMember: 0 else: 1
        let newCost = if newBoolSaysTrue == state.isMember: 0 else: 1
        return newCost - oldCost
        
    elif position in state.setPositions:
        # Set membership position changed
        let oldInSet = int(oldValue) == 1
        let newInSet = int(newValue) == 1
        
        if oldInSet == newInSet:
            return 0  # No change in membership
        
        # Check if this position affects current element
        let currentElementValue = int(state.elementValue)
        if currentElementValue in state.universe:
            for i, universeElement in state.universe:
                if universeElement == currentElementValue:
                    if state.setPositionsSeq[i] == position:
                        # This change affects our element's membership
                        let boolSaysTrue = int(state.boolValue) == 1
                        let oldCost = if boolSaysTrue == oldInSet: 0 else: 1
                        let newCost = if boolSaysTrue == newInSet: 0 else: 1
                        return newCost - oldCost
                    break
    
    return 0  # No change

################################################################################
# String representations
################################################################################

func `$`*[T](constraint: SetMembershipConstraint[T]): string =
    "SetMembership(elem@pos:" & $constraint.elementPosition & " ∈ set, cost:" & $constraint.cost & ")"

func `$`*[T](constraint: SetCardinalityConstraint[T]): string =
    "SetCardinality(|set| = var@pos:" & $constraint.cardinalityPosition & ", cost:" & $constraint.cost & ")"

func `$`*[T](constraint: SetEqualityConstraint[T]): string =
    "SetEquality(setA = setB, cost:" & $constraint.cost & ")"

func `$`*[T](constraint: SetSubsetConstraint[T]): string =
    "SetSubset(subset ⊆ superset, cost:" & $constraint.cost & ")"

func `$`*[T](constraint: SetMembershipReifConstraint[T]): string =
    "SetMembershipReif(elem@pos:" & $constraint.elementPosition & " ∈ set ↔ bool@pos:" & $constraint.boolPosition & ", cost:" & $constraint.cost & ")"