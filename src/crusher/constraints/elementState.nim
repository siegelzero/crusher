import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    ArrayElement*[T] = object
        case isConstant*: bool
            of true:
                constantValue*: T
            of false:
                variablePosition*: int

    ElementConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        cost*: int
        indexPosition*: int
        valuePosition*: int
        case isConstantArray*: bool
            of true:
                constantArray*: seq[T]
            of false:
                arrayElements*: seq[ArrayElement[T]]
                arrayPositions*: PackedSet[int]
        positions*: PackedSet[int]

################################################################################
# ElementConstraint creation
################################################################################

func newElementConstraint*[T](indexPos: int, constantArray: seq[T], valuePos: int): ElementConstraint[T] =
    # Allocates and initializes new ElementConstraint[T] for constant array
    new(result)
    result = ElementConstraint[T](
        cost: 0,
        indexPosition: indexPos,
        valuePosition: valuePos,
        isConstantArray: true,
        constantArray: constantArray,
        positions: toPackedSet[int]([indexPos, valuePos]),
        currentAssignment: initTable[int, T]()
    )

func newElementConstraint*[T](indexPos: int, arrayElements: seq[ArrayElement[T]], valuePos: int): ElementConstraint[T] =
    # Allocates and initializes new ElementConstraint[T] for variable array
    new(result)
    
    # Collect all variable positions involved
    var allPositions: seq[int] = @[indexPos, valuePos]
    var arrayPositions = initPackedSet[int]()
    
    for element in arrayElements:
        if not element.isConstant:
            allPositions.add(element.variablePosition)
            arrayPositions.incl(element.variablePosition)
    
    result = ElementConstraint[T](
        cost: 0,
        indexPosition: indexPos,
        valuePosition: valuePos,
        isConstantArray: false,
        arrayElements: arrayElements,
        arrayPositions: arrayPositions,
        positions: toPackedSet[int](allPositions),
        currentAssignment: initTable[int, T]()
    )

################################################################################
# ElementConstraint utility functions
################################################################################

func getArrayValue*[T](state: ElementConstraint[T], index: int): T =
    # Get the value at the given index in the array (constant or variable)
    case state.isConstantArray:
        of true:
            if index >= 0 and index < state.constantArray.len:
                return state.constantArray[index]
            else:
                # Index out of bounds - this will cause constraint violation
                # Return a default value, cost calculation will handle the violation
                return T.default
        of false:
            if index >= 0 and index < state.arrayElements.len:
                let element = state.arrayElements[index]
                if element.isConstant:
                    return element.constantValue
                else:
                    return state.currentAssignment[element.variablePosition]
            else:
                # Index out of bounds
                return T.default

func getArraySize*[T](state: ElementConstraint[T]): int =
    # Get the size of the array
    case state.isConstantArray:
        of true:
            return state.constantArray.len
        of false:
            return state.arrayElements.len

################################################################################
# ElementConstraint initialization and updates
################################################################################

proc initialize*[T](state: ElementConstraint[T], assignment: seq[T]) =
    # Initialize the constraint state from the current assignment
    state.cost = 0
    state.currentAssignment.clear()
    
    # Store current assignments for all relevant positions
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Calculate cost: cost = 1 if value != array[index], else 0
    let indexValue = assignment[state.indexPosition]
    let valueValue = assignment[state.valuePosition]
    
    # Check bounds and calculate cost
    let arraySize = state.getArraySize()
    if indexValue >= 0 and indexValue < arraySize:
        let arrayValue = state.getArrayValue(indexValue)
        if valueValue != arrayValue:
            state.cost = 1
        else:
            state.cost = 0
    else:
        # Index out of bounds - constraint is violated
        state.cost = 1

proc updatePosition*[T](state: ElementConstraint[T], position: int, newValue: T) =
    # Update state when a variable assignment changes
    if position notin state.positions:
        return  # Position not relevant to this constraint
    
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return  # No change
    
    # Update assignment
    state.currentAssignment[position] = newValue
    
    # Recalculate cost
    let indexValue = state.currentAssignment[state.indexPosition]
    let valueValue = state.currentAssignment[state.valuePosition]
    
    let arraySize = state.getArraySize()
    if indexValue >= 0 and indexValue < arraySize:
        let arrayValue = state.getArrayValue(indexValue)
        if valueValue != arrayValue:
            state.cost = 1
        else:
            state.cost = 0
    else:
        # Index out of bounds - constraint is violated
        state.cost = 1

proc moveDelta*[T](state: ElementConstraint[T], position: int, oldValue, newValue: T): int =
    # Calculate the change in cost if we make this move
    if position notin state.positions:
        return 0  # Position not relevant to this constraint
    
    if oldValue == newValue:
        return 0  # No change
    
    # Use the current cost directly from state
    let currentCost = state.cost
    let currentIndexValue = state.currentAssignment[state.indexPosition]
    let currentValueValue = state.currentAssignment[state.valuePosition]
    let arraySize = state.getArraySize()
    
    # Calculate new cost after the move by simulating the assignment change
    var tempAssignment = state.currentAssignment
    tempAssignment[position] = newValue
    
    var newIndexValue = currentIndexValue
    var newValueValue = currentValueValue
    
    if position == state.indexPosition:
        newIndexValue = newValue
    elif position == state.valuePosition:
        newValueValue = newValue
    
    var newCost = 0
    if newIndexValue >= 0 and newIndexValue < arraySize:
        # For variable arrays, we need to check if any array variables changed
        var newArrayValue: T
        case state.isConstantArray:
            of true:
                newArrayValue = state.constantArray[newIndexValue]
            of false:
                let element = state.arrayElements[newIndexValue]
                if element.isConstant:
                    newArrayValue = element.constantValue
                else:
                    newArrayValue = tempAssignment[element.variablePosition]
        
        if newValueValue != newArrayValue:
            newCost = 1
    else:
        newCost = 1
    
    return newCost - currentCost

################################################################################
# Deep Copy for ElementConstraint (for parallel processing)
################################################################################

proc deepCopy*[T](constraint: ElementConstraint[T]): ElementConstraint[T] =
    # Creates a deep copy of an ElementConstraint for thread-safe parallel processing
    case constraint.isConstantArray:
        of true:
            result = ElementConstraint[T](
                cost: constraint.cost,
                indexPosition: constraint.indexPosition,
                valuePosition: constraint.valuePosition,
                isConstantArray: true,
                constantArray: @[],  # Will copy below
                positions: initPackedSet[int](),
                currentAssignment: initTable[int, T]()
            )
            # Copy constant array
            for item in constraint.constantArray:
                result.constantArray.add(item)
        of false:
            result = ElementConstraint[T](
                cost: constraint.cost,
                indexPosition: constraint.indexPosition,
                valuePosition: constraint.valuePosition,
                isConstantArray: false,
                arrayElements: @[],  # Will copy below
                arrayPositions: initPackedSet[int](),
                positions: initPackedSet[int](),
                currentAssignment: initTable[int, T]()
            )
            # Copy array elements
            for element in constraint.arrayElements:
                result.arrayElements.add(element)
            # Copy array positions
            for item in constraint.arrayPositions:
                result.arrayPositions.incl(item)
    
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