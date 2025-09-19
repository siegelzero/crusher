## Element Constraint Implementation
## =================================
##
## This module implements the Element constraint, which enforces the indexing relationship
## `array[indexExpr] = valueExpr`, where the array can contain constants, variables, or mixed elements.
##
## **Constraint Definition**:
## `array[index] = value`
##
## **Key Features**:
## - Support for constant arrays, variable arrays, and mixed arrays
## - Automatic bounds checking for array indices
## - Binary violation cost (0 if satisfied, 1 if violated)
## - Efficient caching of array element values
## - Handles out-of-bounds indices gracefully
##
## **Array Types**:
## - **Constant Array**: Fixed lookup table with predetermined values
## - **Variable Array**: Array elements are variables that can change
## - **Mixed Array**: Combination of constants and variables
##
## **Applications**:
## - Lookup tables: Implementing function mappings y = f(x)
## - Configuration selection: Choose settings based on mode
## - Data structure modeling: Array/list access patterns
## - Routing problems: Path selection from alternatives
## - Resource mapping: Dynamic resource assignment based on conditions
## - State machines: State transition tables
##
## **Violation Cost**: Binary constraint (0 = satisfied, 1 = violated)
## - Checks exact equality after bounds validation
##
## **Performance**: O(1) evaluation with cached array access, efficient bound checking

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

    ElementState*[T] = ref object
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
# ElementState creation
################################################################################

func newElementState*[T](indexPos: int, constantArray: seq[T], valuePos: int): ElementState[T] =
    # Allocates and initializes new ElementState[T] for constant array
    new(result)
    result = ElementState[T](
        cost: 0,
        indexPosition: indexPos,
        valuePosition: valuePos,
        isConstantArray: true,
        constantArray: constantArray,
        positions: toPackedSet[int]([indexPos, valuePos]),
        currentAssignment: initTable[int, T]()
    )

func newElementState*[T](indexPos: int, arrayElements: seq[ArrayElement[T]], valuePos: int): ElementState[T] =
    # Allocates and initializes new ElementState[T] for variable array
    new(result)

    # Collect all variable positions involved
    var allPositions: seq[int] = @[indexPos, valuePos]
    var arrayPositions = initPackedSet[int]()

    for element in arrayElements:
        if not element.isConstant:
            allPositions.add(element.variablePosition)
            arrayPositions.incl(element.variablePosition)

    result = ElementState[T](
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
# ElementState utility functions
################################################################################

func getArrayValue*[T](state: ElementState[T], index: int): T =
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

func getArraySize*[T](state: ElementState[T]): int =
    # Get the size of the array
    case state.isConstantArray:
        of true:
            return state.constantArray.len
        of false:
            return state.arrayElements.len

################################################################################
# ElementState initialization and updates
################################################################################

proc initialize*[T](state: ElementState[T], assignment: seq[T]) =
    # Initialize the constraint state from the current assignment
    state.cost = 0
    state.currentAssignment.clear()

    # Store current assignments for all relevant positions
    for pos in state.positions.items:
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

proc updatePosition*[T](state: ElementState[T], position: int, newValue: T) =
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

proc moveDelta*[T](state: ElementState[T], position: int, oldValue, newValue: T): int =
    # Efficient incremental calculation of cost change
    if position notin state.positions or oldValue == newValue:
        return 0

    let arraySize = state.getArraySize()

    # Handle each position type with minimal calculation
    if position == state.indexPosition:
        # Index variable changed: array[newValue] vs array[oldValue]
        let valueValue = state.currentAssignment[state.valuePosition]

        # Old constraint satisfaction
        var oldSatisfied = false
        if oldValue >= 0 and oldValue < arraySize:
            let oldArrayValue = state.getArrayValue(oldValue)
            oldSatisfied = (valueValue == oldArrayValue)

        # New constraint satisfaction
        var newSatisfied = false
        if newValue >= 0 and newValue < arraySize:
            let newArrayValue = state.getArrayValue(newValue)
            newSatisfied = (valueValue == newArrayValue)

        # Return delta: 0 if satisfied, 1 if violated
        return (if newSatisfied: 0 else: 1) - (if oldSatisfied: 0 else: 1)

    elif position == state.valuePosition:
        # Value variable changed: simple comparison with current array value
        let indexValue = state.currentAssignment[state.indexPosition]

        if indexValue >= 0 and indexValue < arraySize:
            let arrayValue = state.getArrayValue(indexValue)
            let oldSatisfied = (oldValue == arrayValue)
            let newSatisfied = (newValue == arrayValue)
            return (if newSatisfied: 0 else: 1) - (if oldSatisfied: 0 else: 1)
        else:
            # Index out of bounds - constraint always violated regardless of value
            return 0

    else:
        # Array variable changed - only affects constraint if it's the indexed element
        let indexValue = state.currentAssignment[state.indexPosition]
        let valueValue = state.currentAssignment[state.valuePosition]

        # Find which array element this position corresponds to
        if not state.isConstantArray and indexValue >= 0 and indexValue < arraySize:
            let element = state.arrayElements[indexValue]
            if not element.isConstant and element.variablePosition == position:
                # This array position is currently indexed
                let oldSatisfied = (valueValue == oldValue)
                let newSatisfied = (valueValue == newValue)
                return (if newSatisfied: 0 else: 1) - (if oldSatisfied: 0 else: 1)

        # Array change doesn't affect currently indexed element
        return 0

