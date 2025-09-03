import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    ElementConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        indexPosition*: int
        valuePosition*: int
        constantArray*: seq[T]
        positions*: PackedSet[int]

################################################################################
# ElementConstraint creation
################################################################################

func newElementConstraint*[T](indexPos: int, constantArray: seq[T], valuePos: int): ElementConstraint[T] =
    # Allocates and initializes new ElementConstraint[T]
    new(result)
    result = ElementConstraint[T](
        cost: 0,
        indexPosition: indexPos,
        valuePosition: valuePos,
        constantArray: constantArray,
        positions: toPackedSet[int]([indexPos, valuePos]),
        currentAssignment: initTable[int, T]()
    )

################################################################################
# ElementConstraint initialization and updates
################################################################################

proc initialize*[T](state: ElementConstraint[T], assignment: seq[T]) =
    # Initialize the constraint state from the current assignment
    state.cost = 0
    state.currentAssignment.clear()
    
    # Store current assignments for index and value positions
    state.currentAssignment[state.indexPosition] = assignment[state.indexPosition]
    state.currentAssignment[state.valuePosition] = assignment[state.valuePosition]
    
    # Calculate cost: cost = 1 if value != array[index], else 0
    let indexValue = assignment[state.indexPosition]
    let valueValue = assignment[state.valuePosition]
    
    # Check bounds and calculate cost
    if indexValue >= 0 and indexValue < state.constantArray.len:
        if valueValue != state.constantArray[indexValue]:
            state.cost = 1
        else:
            state.cost = 0
    else:
        # Index out of bounds - constraint is violated
        state.cost = 1

proc updatePosition*[T](state: ElementConstraint[T], position: int, newValue: T) =
    # Update state when a variable assignment changes
    if position != state.indexPosition and position != state.valuePosition:
        return  # Position not relevant to this constraint
    
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return  # No change
    
    # Update assignment
    state.currentAssignment[position] = newValue
    
    # Recalculate cost
    let indexValue = state.currentAssignment[state.indexPosition]
    let valueValue = state.currentAssignment[state.valuePosition]
    
    if indexValue >= 0 and indexValue < state.constantArray.len:
        if valueValue != state.constantArray[indexValue]:
            state.cost = 1
        else:
            state.cost = 0
    else:
        # Index out of bounds - constraint is violated
        state.cost = 1

proc moveDelta*[T](state: ElementConstraint[T], position: int, oldValue, newValue: T): int =
    # Calculate the change in cost if we make this move
    if position != state.indexPosition and position != state.valuePosition:
        return 0  # Position not relevant to this constraint
    
    if oldValue == newValue:
        return 0  # No change
    
    # Calculate current cost
    let currentIndexValue = state.currentAssignment[state.indexPosition]
    let currentValueValue = state.currentAssignment[state.valuePosition]
    var currentCost = 0
    
    if currentIndexValue >= 0 and currentIndexValue < state.constantArray.len:
        if currentValueValue != state.constantArray[currentIndexValue]:
            currentCost = 1
    else:
        currentCost = 1
    
    # Calculate new cost after the move
    var newIndexValue = currentIndexValue
    var newValueValue = currentValueValue
    
    if position == state.indexPosition:
        newIndexValue = newValue
    else:
        newValueValue = newValue
    
    var newCost = 0
    if newIndexValue >= 0 and newIndexValue < state.constantArray.len:
        if newValueValue != state.constantArray[newIndexValue]:
            newCost = 1
    else:
        newCost = 1
    
    return newCost - currentCost

################################################################################
# Deep Copy for ElementConstraint (for parallel processing)
################################################################################

proc deepCopy*[T](constraint: ElementConstraint[T]): ElementConstraint[T] =
    # Creates a deep copy of an ElementConstraint for thread-safe parallel processing
    result = ElementConstraint[T](
        cost: constraint.cost,
        indexPosition: constraint.indexPosition,
        valuePosition: constraint.valuePosition,
        constantArray: @[],  # Will copy below
        positions: initPackedSet[int](),
        currentAssignment: initTable[int, T]()
    )
    
    # Copy constant array
    for item in constraint.constantArray:
        result.constantArray.add(item)
    
    # Copy positions
    for item in constraint.positions:
        result.positions.incl(item)
    
    # Copy current assignment
    for k, v in constraint.currentAssignment.pairs:
        result.currentAssignment[k] = v

################################################################################
# Type alias for backward compatibility
################################################################################

type ElementState*[T] = ElementConstraint[T]