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

import ../expressions/expressions
import common

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
        positions*: PackedSet[int]
        lastAffectedPositions*: PackedSet[int]
        case evalMethod*: StateEvalMethod
            of PositionBased:
                indexPosition*: int
                valuePosition*: int
                case isConstantArray*: bool
                    of true:
                        constantArray*: seq[T]
                    of false:
                        arrayElements*: seq[ArrayElement[T]]
                        arrayPositions*: PackedSet[int]
            of ExpressionBased:
                indexExpression*: AlgebraicExpression[T]
                valueExpression*: AlgebraicExpression[T]
                isConstantArrayEB*: bool
                constantArrayEB*: seq[T]  # Used when isConstantArrayEB = true
                arrayExpressionsEB*: seq[AlgebraicExpression[T]]  # Used when isConstantArrayEB = false
                indexExprPositions*: Table[int, seq[int]]  # positions affecting index expr
                valueExprPositions*: Table[int, seq[int]]  # positions affecting value expr
                arrayExprPositions*: Table[int, seq[int]]  # positions affecting array elements (empty for constant)

################################################################################
# ElementState creation
################################################################################

func newElementState*[T](indexPos: int, constantArray: seq[T], valuePos: int): ElementState[T] =
    # Allocates and initializes new ElementState[T] for constant array (position-based)
    new(result)
    result = ElementState[T](
        cost: 0,
        evalMethod: PositionBased,
        indexPosition: indexPos,
        valuePosition: valuePos,
        isConstantArray: true,
        constantArray: constantArray,
        positions: toPackedSet[int]([indexPos, valuePos]),
        currentAssignment: initTable[int, T]()
    )

func newElementState*[T](indexPos: int, arrayElements: seq[ArrayElement[T]], valuePos: int): ElementState[T] =
    # Allocates and initializes new ElementState[T] for variable array (position-based)
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
        evalMethod: PositionBased,
        indexPosition: indexPos,
        valuePosition: valuePos,
        isConstantArray: false,
        arrayElements: arrayElements,
        arrayPositions: arrayPositions,
        positions: toPackedSet[int](allPositions),
        currentAssignment: initTable[int, T]()
    )

func newElementStateExprBased*[T](indexExpr: AlgebraicExpression[T],
                                   arrayExprs: seq[AlgebraicExpression[T]],
                                   valueExpr: AlgebraicExpression[T]): ElementState[T] =
    # Allocates and initializes new ElementState[T] for expression-based evaluation with variable array
    # This supports computed index expressions like (Y * W + X)
    new(result)

    # Collect all positions from all expressions
    var allPositions = initPackedSet[int]()
    allPositions.incl(indexExpr.positions)
    allPositions.incl(valueExpr.positions)
    for expr in arrayExprs:
        allPositions.incl(expr.positions)

    # Build position maps for each expression type
    let indexExprPositions = buildExpressionPositionMap(@[indexExpr])
    let valueExprPositions = buildExpressionPositionMap(@[valueExpr])
    let arrayExprPositions = buildExpressionPositionMap(arrayExprs)

    result = ElementState[T](
        cost: 0,
        evalMethod: ExpressionBased,
        indexExpression: indexExpr,
        valueExpression: valueExpr,
        isConstantArrayEB: false,
        constantArrayEB: @[],
        arrayExpressionsEB: arrayExprs,
        indexExprPositions: indexExprPositions,
        valueExprPositions: valueExprPositions,
        arrayExprPositions: arrayExprPositions,
        positions: allPositions,
        currentAssignment: initTable[int, T]()
    )

func newElementStateExprBasedConst*[T](indexExpr: AlgebraicExpression[T],
                                        constantArray: seq[T],
                                        valueExpr: AlgebraicExpression[T]): ElementState[T] =
    # Allocates and initializes new ElementState[T] for expression-based evaluation with constant array
    # This supports computed index expressions like (Y * W + X) into a constant lookup table
    # Useful for shape lookups: Shape[Rr * 3 + Cf]
    new(result)

    # Collect all positions from index and value expressions only (array is constant)
    var allPositions = initPackedSet[int]()
    allPositions.incl(indexExpr.positions)
    allPositions.incl(valueExpr.positions)

    # Build position maps for index and value expressions
    let indexExprPositions = buildExpressionPositionMap(@[indexExpr])
    let valueExprPositions = buildExpressionPositionMap(@[valueExpr])

    result = ElementState[T](
        cost: 0,
        evalMethod: ExpressionBased,
        indexExpression: indexExpr,
        valueExpression: valueExpr,
        isConstantArrayEB: true,
        constantArrayEB: constantArray,
        arrayExpressionsEB: @[],
        indexExprPositions: indexExprPositions,
        valueExprPositions: valueExprPositions,
        arrayExprPositions: initTable[int, seq[int]](),  # Empty - no array positions for constant
        positions: allPositions,
        currentAssignment: initTable[int, T]()
    )

################################################################################
# ElementState utility functions
################################################################################

func getArrayValue*[T](state: ElementState[T], index: int): T =
    # Get the value at the given index in the array (constant or variable)
    case state.evalMethod:
        of PositionBased:
            case state.isConstantArray:
                of true:
                    if index >= 0 and index < state.constantArray.len:
                        return state.constantArray[index]
                    else:
                        return T.default
                of false:
                    if index >= 0 and index < state.arrayElements.len:
                        let element = state.arrayElements[index]
                        if element.isConstant:
                            return element.constantValue
                        else:
                            return state.currentAssignment[element.variablePosition]
                    else:
                        return T.default
        of ExpressionBased:
            if state.isConstantArrayEB:
                # Constant array with expression index
                if index >= 0 and index < state.constantArrayEB.len:
                    return state.constantArrayEB[index]
                else:
                    return T.default
            else:
                # Variable array with expression index
                if index >= 0 and index < state.arrayExpressionsEB.len:
                    return state.arrayExpressionsEB[index].evaluate(state.currentAssignment)
                else:
                    return T.default

func getArraySize*[T](state: ElementState[T]): int =
    # Get the size of the array
    case state.evalMethod:
        of PositionBased:
            case state.isConstantArray:
                of true:
                    return state.constantArray.len
                of false:
                    return state.arrayElements.len
        of ExpressionBased:
            if state.isConstantArrayEB:
                return state.constantArrayEB.len
            else:
                return state.arrayExpressionsEB.len

func getIndexValue*[T](state: ElementState[T]): T =
    # Get the current index value
    case state.evalMethod:
        of PositionBased:
            return state.currentAssignment[state.indexPosition]
        of ExpressionBased:
            return state.indexExpression.evaluate(state.currentAssignment)

func getValueValue*[T](state: ElementState[T]): T =
    # Get the current value expression result
    case state.evalMethod:
        of PositionBased:
            return state.currentAssignment[state.valuePosition]
        of ExpressionBased:
            return state.valueExpression.evaluate(state.currentAssignment)

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
    let indexValue = state.getIndexValue()
    let valueValue = state.getValueValue()

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
        state.lastAffectedPositions = initPackedSet[int]()
        return

    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        state.lastAffectedPositions = initPackedSet[int]()
        return

    # Compute affected positions before updating assignment
    var affected = initPackedSet[int]()

    case state.evalMethod:
    of PositionBased:
        if position == state.indexPosition:
            # Index changed: value position always affected
            affected.incl(state.valuePosition)
            # Old indexed array element (if variable)
            if not state.isConstantArray:
                let arraySize = state.getArraySize()
                if oldValue >= 0 and oldValue < arraySize:
                    let oldElem = state.arrayElements[oldValue]
                    if not oldElem.isConstant:
                        affected.incl(oldElem.variablePosition)
                if newValue >= 0 and newValue < arraySize:
                    let newElem = state.arrayElements[newValue]
                    if not newElem.isConstant:
                        affected.incl(newElem.variablePosition)

        elif position == state.valuePosition:
            # Value changed: index position affected, plus current array element
            affected.incl(state.indexPosition)
            if not state.isConstantArray:
                let indexValue = state.currentAssignment[state.indexPosition]
                let arraySize = state.getArraySize()
                if indexValue >= 0 and indexValue < arraySize:
                    let elem = state.arrayElements[indexValue]
                    if not elem.isConstant:
                        affected.incl(elem.variablePosition)

        else:
            # Array variable changed — only matters if at current index
            if not state.isConstantArray:
                let indexValue = state.currentAssignment[state.indexPosition]
                let arraySize = state.getArraySize()
                if indexValue >= 0 and indexValue < arraySize:
                    let elem = state.arrayElements[indexValue]
                    if not elem.isConstant and elem.variablePosition == position:
                        affected.incl(state.indexPosition)
                        affected.incl(state.valuePosition)
            # else: not at current index, no affected positions

    of ExpressionBased:
        # Conservative: return all positions
        affected = state.positions

    state.lastAffectedPositions = affected

    # Update assignment
    state.currentAssignment[position] = newValue

    # Recalculate cost
    let indexValue = state.getIndexValue()
    let valueValue = state.getValueValue()

    let arraySize = state.getArraySize()
    if indexValue >= 0 and indexValue < arraySize:
        let arrayValue = state.getArrayValue(indexValue)
        if valueValue != arrayValue:
            state.cost = 1
        else:
            state.cost = 0
    else:
        state.cost = 1

func getAffectedPositions*[T](state: ElementState[T]): PackedSet[int] =
    return state.lastAffectedPositions

proc moveDelta*[T](state: ElementState[T], position: int, oldValue, newValue: T): int =
    # Efficient incremental calculation of cost change
    if position notin state.positions or oldValue == newValue:
        return 0

    let arraySize = state.getArraySize()

    case state.evalMethod:
        of PositionBased:
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

        of ExpressionBased:
            # For expression-based, we need to evaluate the constraint with old and new values
            # Save original assignment value
            let originalValue = state.currentAssignment[position]

            # Calculate old cost (with original value)
            let oldIndexValue = state.indexExpression.evaluate(state.currentAssignment)
            let oldValueValue = state.valueExpression.evaluate(state.currentAssignment)
            var oldSatisfied = false
            if oldIndexValue >= 0 and oldIndexValue < arraySize:
                let oldArrayValue = state.getArrayValue(oldIndexValue)
                oldSatisfied = (oldValueValue == oldArrayValue)

            # Temporarily update assignment to calculate new cost
            state.currentAssignment[position] = newValue
            let newIndexValue = state.indexExpression.evaluate(state.currentAssignment)
            let newValueValue = state.valueExpression.evaluate(state.currentAssignment)
            var newSatisfied = false
            if newIndexValue >= 0 and newIndexValue < arraySize:
                let newArrayValue = state.getArrayValue(newIndexValue)
                newSatisfied = (newValueValue == newArrayValue)

            # Restore original assignment
            state.currentAssignment[position] = originalValue

            return (if newSatisfied: 0 else: 1) - (if oldSatisfied: 0 else: 1)

