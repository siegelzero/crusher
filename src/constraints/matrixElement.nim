## MatrixElement Constraint Implementation
## ========================================
##
## Enforces `matrix[row, col] == value` for a 2D matrix stored as a flat array.
## Supports constant row + variable col, variable row + constant col,
## and variable row + variable col.
##
## Key advantage over expression-based element: works with raw 0-based positions,
## avoiding the overhead of expression tree evaluation for index arithmetic.
##
## **Violation Cost**: Binary (0 = satisfied, 1 = violated)

import std/[packedsets, tables]

import ../expressions/expressions
import elementState

################################################################################
# Type definitions
################################################################################

type
    IndexKind* = enum
        ConstantIndex,
        VariableIndex

    MatrixElementState*[T] = ref object
        numRows*, numCols*: int
        matrixElements*: seq[ArrayElement[T]]  # flat row-major
        # Row index
        rowKind*: IndexKind
        rowConstant*: int      # used when rowKind == ConstantIndex
        rowPosition*: int      # used when rowKind == VariableIndex
        # Col index
        colKind*: IndexKind
        colConstant*: int      # used when colKind == ConstantIndex
        colPosition*: int      # used when colKind == VariableIndex
        # Value
        valuePosition*: int
        # State
        positions*: PackedSet[int]
        cost*: int
        currentAssignment*: Table[int, T]
        # Tracking for smart getAffectedPositions
        lastAffectedPositions*: PackedSet[int]

################################################################################
# Utility
################################################################################

func getRow[T](state: MatrixElementState[T]): int {.inline.} =
    case state.rowKind
    of ConstantIndex: state.rowConstant
    of VariableIndex: state.currentAssignment[state.rowPosition]

func getCol[T](state: MatrixElementState[T]): int {.inline.} =
    case state.colKind
    of ConstantIndex: state.colConstant
    of VariableIndex: state.currentAssignment[state.colPosition]

func flatIndex[T](state: MatrixElementState[T], row, col: int): int {.inline.} =
    row * state.numCols + col

func inBounds[T](state: MatrixElementState[T], row, col: int): bool {.inline.} =
    row >= 0 and row < state.numRows and col >= 0 and col < state.numCols

func getMatrixValue[T](state: MatrixElementState[T], flatIdx: int): T {.inline.} =
    let elem = state.matrixElements[flatIdx]
    if elem.isConstant:
        return elem.constantValue
    else:
        return state.currentAssignment[elem.variablePosition]

func matrixVarPosition[T](state: MatrixElementState[T], row, col: int): int {.inline.} =
    ## Returns the variable position of the matrix element at (row, col), or -1 if constant/OOB.
    if not state.inBounds(row, col):
        return -1
    let flatIdx = state.flatIndex(row, col)
    let elem = state.matrixElements[flatIdx]
    if elem.isConstant: -1 else: elem.variablePosition

func computeCost[T](state: MatrixElementState[T]): int =
    let row = state.getRow()
    let col = state.getCol()
    if not state.inBounds(row, col):
        return 1
    let flatIdx = state.flatIndex(row, col)
    let matVal = state.getMatrixValue(flatIdx)
    let valVal = state.currentAssignment[state.valuePosition]
    if matVal != valVal: 1 else: 0

################################################################################
# Constructors
################################################################################

func newMatrixElementState*[T](matrixElements: seq[ArrayElement[T]], numRows, numCols: int,
                                rowConstant: int, colPosition: int, valuePosition: int): MatrixElementState[T] =
    ## Constant row, variable col
    new(result)
    result.numRows = numRows
    result.numCols = numCols
    result.matrixElements = matrixElements
    result.rowKind = ConstantIndex
    result.rowConstant = rowConstant
    result.rowPosition = -1
    result.colKind = VariableIndex
    result.colConstant = -1
    result.colPosition = colPosition
    result.valuePosition = valuePosition
    result.cost = 0
    result.currentAssignment = initTable[int, T]()

    # Build positions: col position, value position, plus matrix variable positions
    # in the constant row only (since row is fixed, only that row's vars matter,
    # plus any var that could be at the currently-indexed position)
    var posSet = initPackedSet[int]()
    posSet.incl(colPosition)
    posSet.incl(valuePosition)
    # Include all variable positions in the specified row
    for c in 0..<numCols:
        let flatIdx = rowConstant * numCols + c
        if flatIdx < matrixElements.len and not matrixElements[flatIdx].isConstant:
            posSet.incl(matrixElements[flatIdx].variablePosition)
    result.positions = posSet

func newMatrixElementStateRowVar*[T](matrixElements: seq[ArrayElement[T]], numRows, numCols: int,
                                      rowPosition: int, colConstant: int, valuePosition: int): MatrixElementState[T] =
    ## Variable row, constant col
    new(result)
    result.numRows = numRows
    result.numCols = numCols
    result.matrixElements = matrixElements
    result.rowKind = VariableIndex
    result.rowConstant = -1
    result.rowPosition = rowPosition
    result.colKind = ConstantIndex
    result.colConstant = colConstant
    result.colPosition = -1
    result.valuePosition = valuePosition
    result.cost = 0
    result.currentAssignment = initTable[int, T]()

    # Build positions: row position, value position, plus matrix variable positions
    # in the constant column only
    var posSet = initPackedSet[int]()
    posSet.incl(rowPosition)
    posSet.incl(valuePosition)
    # Include all variable positions in the specified column
    for r in 0..<numRows:
        let flatIdx = r * numCols + colConstant
        if flatIdx < matrixElements.len and not matrixElements[flatIdx].isConstant:
            posSet.incl(matrixElements[flatIdx].variablePosition)
    result.positions = posSet

func newMatrixElementStateVarVar*[T](matrixElements: seq[ArrayElement[T]], numRows, numCols: int,
                                      rowPosition, colPosition, valuePosition: int): MatrixElementState[T] =
    ## Variable row, variable col
    new(result)
    result.numRows = numRows
    result.numCols = numCols
    result.matrixElements = matrixElements
    result.rowKind = VariableIndex
    result.rowConstant = -1
    result.rowPosition = rowPosition
    result.colKind = VariableIndex
    result.colConstant = -1
    result.colPosition = colPosition
    result.valuePosition = valuePosition
    result.cost = 0
    result.currentAssignment = initTable[int, T]()

    # Build positions: row, col, value positions, plus all matrix variable positions
    var posSet = initPackedSet[int]()
    posSet.incl(rowPosition)
    posSet.incl(colPosition)
    posSet.incl(valuePosition)
    for elem in matrixElements:
        if not elem.isConstant:
            posSet.incl(elem.variablePosition)
    result.positions = posSet

################################################################################
# State management
################################################################################

proc initialize*[T](state: MatrixElementState[T], assignment: seq[T]) =
    state.currentAssignment.clear()
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]
    state.cost = state.computeCost()

proc updatePosition*[T](state: MatrixElementState[T], position: int, newValue: T) =
    if position notin state.positions:
        state.lastAffectedPositions = initPackedSet[int]()
        return

    let oldValue = state.currentAssignment[position]
    let oldRow = state.getRow()
    let oldCol = state.getCol()

    state.currentAssignment[position] = newValue
    state.cost = state.computeCost()

    if oldValue == newValue:
        state.lastAffectedPositions = initPackedSet[int]()
        return

    # Compute minimal set of affected positions.
    # For each OTHER position Q, we include Q if moveDelta(Q, ...) could return
    # different values after this change.
    var affected = initPackedSet[int]()

    if state.rowKind == VariableIndex and position == state.rowPosition:
        # Row changed: indexed position moves, affecting value, col, old/new matrix elements
        let newRow = newValue
        affected.incl(state.valuePosition)
        if state.colKind == VariableIndex:
            affected.incl(state.colPosition)
        let oldPos = state.matrixVarPosition(oldRow, oldCol)
        if oldPos >= 0: affected.incl(oldPos)
        let newPos = state.matrixVarPosition(newRow, oldCol)
        if newPos >= 0: affected.incl(newPos)

    elif state.colKind == VariableIndex and position == state.colPosition:
        # Col changed: indexed position moves, affecting value, row, old/new matrix elements
        let newCol = newValue
        affected.incl(state.valuePosition)
        if state.rowKind == VariableIndex:
            affected.incl(state.rowPosition)
        let oldPos = state.matrixVarPosition(oldRow, oldCol)
        if oldPos >= 0: affected.incl(oldPos)
        let newPos = state.matrixVarPosition(oldRow, newCol)
        if newPos >= 0: affected.incl(newPos)

    elif position == state.valuePosition:
        # Value changed: index positions and currently-indexed matrix element are affected
        if state.rowKind == VariableIndex:
            affected.incl(state.rowPosition)
        if state.colKind == VariableIndex:
            affected.incl(state.colPosition)
        let matPos = state.matrixVarPosition(oldRow, oldCol)
        if matPos >= 0: affected.incl(matPos)

    else:
        # Matrix variable changed: only matters if at the currently-indexed position
        if state.inBounds(oldRow, oldCol):
            let flatIdx = state.flatIndex(oldRow, oldCol)
            let elem = state.matrixElements[flatIdx]
            if not elem.isConstant and elem.variablePosition == position:
                # At current index: affects value and index positions
                affected.incl(state.valuePosition)
                if state.rowKind == VariableIndex:
                    affected.incl(state.rowPosition)
                if state.colKind == VariableIndex:
                    affected.incl(state.colPosition)
        # else: not at current index, no affected positions

    state.lastAffectedPositions = affected

################################################################################
# moveDelta - O(1) incremental evaluation
################################################################################

proc moveDelta*[T](state: MatrixElementState[T], position: int, oldValue, newValue: T): int =
    if position notin state.positions or oldValue == newValue:
        return 0

    let curRow = state.getRow()
    let curCol = state.getCol()
    let curValue = state.currentAssignment[state.valuePosition]

    # Compute old satisfaction
    var oldSatisfied = false
    if state.inBounds(curRow, curCol):
        let oldFlatIdx = state.flatIndex(curRow, curCol)
        oldSatisfied = (state.getMatrixValue(oldFlatIdx) == curValue)

    # Determine what changes based on which position is affected
    var newSatisfied = false

    if state.rowKind == VariableIndex and position == state.rowPosition:
        # Row changes: new flat index = newValue * numCols + curCol
        if state.inBounds(newValue, curCol):
            let newFlatIdx = state.flatIndex(newValue, curCol)
            newSatisfied = (state.getMatrixValue(newFlatIdx) == curValue)

    elif state.colKind == VariableIndex and position == state.colPosition:
        # Col changes: new flat index = curRow * numCols + newValue
        if state.inBounds(curRow, newValue):
            let newFlatIdx = state.flatIndex(curRow, newValue)
            newSatisfied = (state.getMatrixValue(newFlatIdx) == curValue)

    elif position == state.valuePosition:
        # Value changes: same flat index, compare with matrix value
        if state.inBounds(curRow, curCol):
            let flatIdx = state.flatIndex(curRow, curCol)
            newSatisfied = (state.getMatrixValue(flatIdx) == newValue)

    else:
        # Matrix variable changes: only matters if it's at the currently-indexed flat position
        if state.inBounds(curRow, curCol):
            let flatIdx = state.flatIndex(curRow, curCol)
            let elem = state.matrixElements[flatIdx]
            if not elem.isConstant and elem.variablePosition == position:
                # This is the currently-indexed matrix element
                newSatisfied = (newValue == curValue)
            else:
                # Not the currently-indexed position, no effect
                return 0
        else:
            return 0

    return (if newSatisfied: 0 else: 1) - (if oldSatisfied: 0 else: 1)

################################################################################
# Batch penalty computation
################################################################################

proc batchMovePenalty*[T](state: MatrixElementState[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
    ## Compute moveDelta for ALL domain values at a position in a tight loop.
    ## Avoids per-value dispatch overhead by precomputing shared state.
    result = newSeq[int](domain.len)

    if position notin state.positions:
        return  # all zeros

    let curRow = state.getRow()
    let curCol = state.getCol()
    let curValue = state.currentAssignment[state.valuePosition]

    # Compute current cost (baseline)
    var oldCost = 1  # default: violated (OOB)
    if state.inBounds(curRow, curCol):
        let oldFlatIdx = state.flatIndex(curRow, curCol)
        if state.getMatrixValue(oldFlatIdx) == curValue:
            oldCost = 0

    if state.rowKind == ConstantIndex and state.colKind == VariableIndex:
        # Const-row variant
        let constRow = state.rowConstant

        if position == state.colPosition:
            # Col changes: for each candidate c, check matrix[constRow, c] == curValue
            for i in 0..<domain.len:
                let c = domain[i]
                var newCost = 1
                if c >= 0 and c < state.numCols:
                    let flatIdx = state.flatIndex(constRow, c)
                    if state.getMatrixValue(flatIdx) == curValue:
                        newCost = 0
                result[i] = newCost - oldCost

        elif position == state.valuePosition:
            # Value changes: matrix lookup doesn't change, compare each candidate to matrixVal
            if state.inBounds(curRow, curCol):
                let flatIdx = state.flatIndex(curRow, curCol)
                let matVal = state.getMatrixValue(flatIdx)
                for i in 0..<domain.len:
                    let newCost = if domain[i] == matVal: 0 else: 1
                    result[i] = newCost - oldCost
            else:
                # OOB: all candidates yield cost 1, same as oldCost (also 1)
                discard  # all zeros

        else:
            # Matrix cell: only matters if this is Z[constRow, curCol]
            if state.inBounds(curRow, curCol):
                let flatIdx = state.flatIndex(curRow, curCol)
                let elem = state.matrixElements[flatIdx]
                if not elem.isConstant and elem.variablePosition == position:
                    # This is the active matrix cell: for each candidate, check == curValue
                    for i in 0..<domain.len:
                        let newCost = if domain[i] == curValue: 0 else: 1
                        result[i] = newCost - oldCost
                # else: not the active cell, all zeros

    elif state.rowKind == VariableIndex and state.colKind == ConstantIndex:
        # Const-col variant
        let constCol = state.colConstant

        if position == state.rowPosition:
            # Row changes: for each candidate r, check matrix[r, constCol] == curValue
            for i in 0..<domain.len:
                let r = domain[i]
                var newCost = 1
                if r >= 0 and r < state.numRows:
                    let flatIdx = state.flatIndex(r, constCol)
                    if state.getMatrixValue(flatIdx) == curValue:
                        newCost = 0
                result[i] = newCost - oldCost

        elif position == state.valuePosition:
            # Value changes: matrix lookup doesn't change
            if state.inBounds(curRow, curCol):
                let flatIdx = state.flatIndex(curRow, curCol)
                let matVal = state.getMatrixValue(flatIdx)
                for i in 0..<domain.len:
                    let newCost = if domain[i] == matVal: 0 else: 1
                    result[i] = newCost - oldCost
            else:
                discard  # all zeros

        else:
            # Matrix cell: only matters if this is Z[curRow, constCol]
            if state.inBounds(curRow, curCol):
                let flatIdx = state.flatIndex(curRow, curCol)
                let elem = state.matrixElements[flatIdx]
                if not elem.isConstant and elem.variablePosition == position:
                    for i in 0..<domain.len:
                        let newCost = if domain[i] == curValue: 0 else: 1
                        result[i] = newCost - oldCost

    else:
        # Var-var variant: fallback to individual moveDelta calls
        for i in 0..<domain.len:
            result[i] = state.moveDelta(position, currentValue, domain[i])

################################################################################
# Affected positions (for neighbor penalty updates)
################################################################################

func getAffectedPositions*[T](state: MatrixElementState[T]): PackedSet[int] =
    return state.lastAffectedPositions

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](state: MatrixElementState[T]): MatrixElementState[T] =
    case state.rowKind
    of ConstantIndex:
        result = newMatrixElementState[T](
            state.matrixElements, state.numRows, state.numCols,
            state.rowConstant, state.colPosition, state.valuePosition
        )
    of VariableIndex:
        case state.colKind
        of ConstantIndex:
            result = newMatrixElementStateRowVar[T](
                state.matrixElements, state.numRows, state.numCols,
                state.rowPosition, state.colConstant, state.valuePosition
            )
        of VariableIndex:
            result = newMatrixElementStateVarVar[T](
                state.matrixElements, state.numRows, state.numCols,
                state.rowPosition, state.colPosition, state.valuePosition
            )
