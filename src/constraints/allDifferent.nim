## AllDifferent Constraint Implementation
## =====================================
##
## This module implements the AllDifferent constraint, which ensures all variables
## in the specified positions take different values (no duplicates).
##
## **Constraint Definition**:
## `∀i,j ∈ positions, i ≠ j : x[i] ≠ x[j]`
##
## **Key Features**:
## - Position-based and expression-based evaluation modes
## - Efficient incremental updates using value frequency counting
## - Linear violation cost based on number of duplicate pairs
## - Hash table-based O(1) value lookup and counting
##
## **Applications**:
## - N-Queens problem: Ensuring no conflicts between queens
## - Resource assignment: Unique resource allocation per task
## - Scheduling: Non-overlapping activities in time slots
## - Permutation problems: Generating unique arrangements
## - Graph coloring: Adjacent nodes get different colors
## - Sudoku puzzles: Row/column/box uniqueness constraints
##
## **Violation Cost**: Sum of conflicts between duplicate values
## - For each value v: `max(0, count(v) - 1)` duplicates contribute to cost
##
## **Performance**: O(1) incremental move evaluation, O(n) initialization where n = number of positions/expressions

import std/[packedsets, tables]

import ../expressions/expressions
import common

################################################################################
# Type definitions
################################################################################

type
    AllDifferentConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        countTable: Table[T, int]
        # Dense value-count window: counts for values in
        # [winLo, winLo + denseCounts.len) are kept in denseCounts with O(1)
        # array indexing; countTable is only the fallback for values outside
        # the window. Installed via setValueWindow (from domain bounds) before
        # initialize; empty denseCounts means all counts go through countTable.
        winLo: int64
        denseCounts: seq[int32]
        cost*: int
        lastOldValue*: T
        lastNewValue*: T
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions: PackedSet[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition: Table[int, seq[int]]
                # Cached expression values and coefficients for O(1) moveDelta
                exprValues*: seq[T]  # cached current expression values
                exprCoeffs*: seq[Table[int, T]]  # [expr_idx][position] -> coefficient
                exprConstants*: seq[T]  # constant term per expression
                allLinear*: bool  # true if all expressions are linear
                # Precomputed per-position affected sets: union of positions of
                # all expressions containing that position. updatePosition just
                # records the moved position; no per-call set building.
                affectedByPos: Table[int, PackedSet[int]]
                lastAffectedKey: int  # position of last updatePosition (-1 = none)

################################################################################
# AllDifferentConstraint creation
################################################################################

func newAllDifferentConstraint*[T](positions: openArray[int] ): AllDifferentConstraint[T] =
    # Allocates and initializes new AllDifferentConstraint[T]
    new(result)
    result = AllDifferentConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        countTable: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )

func newAllDifferentConstraint*[T](expressions: seq[AlgebraicExpression[T]]): AllDifferentConstraint[T] =
    # Allocates and initializes new AllDifferentConstraint[T]
    new(result)
    result = AllDifferentConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        countTable: initTable[T, int](),
        currentAssignment: initTable[int, T](),
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

    # Precompute per-position affected sets for getAffectedPositions
    result.lastAffectedKey = -1
    result.affectedByPos = initTable[int, PackedSet[int]]()
    for pos, exprIndices in result.expressionsAtPosition.pairs:
        var affected = initPackedSet[int]()
        for i in exprIndices:
            affected.incl(expressions[i].positions)
        result.affectedByPos[pos] = affected

    # Extract linear coefficients for O(1) moveDelta
    result.allLinear = true
    result.exprValues = newSeq[T](expressions.len)
    result.exprCoeffs = newSeq[Table[int, T]](expressions.len)
    result.exprConstants = newSeq[T](expressions.len)
    for i, expr in expressions:
        result.exprCoeffs[i] = initTable[int, T]()
        if expr.linear:
            # Extract coefficients by probing
            var assignment = initTable[int, T]()
            for pos in expr.positions.items:
                assignment[pos] = T(0)
            result.exprConstants[i] = expr.evaluate(assignment)
            for pos in expr.positions.items:
                assignment[pos] = T(1)
                result.exprCoeffs[i][pos] = expr.evaluate(assignment) - result.exprConstants[i]
                assignment[pos] = T(0)
        else:
            result.allLinear = false

################################################################################
# AllDifferentConstraint utility functions
################################################################################


const AllDiffMaxWindow = 1 shl 20  # max dense window entries (4MB of int32)

proc setValueWindow*[T](state: AllDifferentConstraint[T], lo, hi: int64) =
    ## Install a dense count window covering [lo, hi]. Call before initialize.
    ## Values observed outside the window still work via the table fallback.
    let size = hi - lo + 1
    if size <= 0 or size > AllDiffMaxWindow:
        return
    state.winLo = lo
    state.denseCounts = newSeq[int32](int(size))

func cnt[T](state: AllDifferentConstraint[T], value: T): int {.inline.} =
    when T is SomeInteger:
        if state.denseCounts.len > 0:
            let idx = int64(value) - state.winLo
            if idx >= 0 and idx < state.denseCounts.len:
                return int(state.denseCounts[idx])
    getCount(state.countTable, value)

proc bumpCount[T](state: AllDifferentConstraint[T], value: T, delta: int) {.inline.} =
    when T is SomeInteger:
        if state.denseCounts.len > 0:
            let idx = int64(value) - state.winLo
            if idx >= 0 and idx < state.denseCounts.len:
                state.denseCounts[idx] += int32(delta)
                return
    if delta > 0:
        incrementCount(state.countTable, value)
    else:
        decrementCount(state.countTable, value)

func contribution[T](state: AllDifferentConstraint[T], value: T): int {.inline.} =
    max(0, state.cnt(value) - 1)


proc adjustCounts[T](state: AllDifferentConstraint[T], oldValue, newValue: T) {.inline.} =
    # Adjust value counts and state cost for the removal of oldValue and addition of newValue
    state.cost -= state.contribution(oldValue)
    state.cost -= state.contribution(newValue)
    state.bumpCount(oldValue, -1)
    state.bumpCount(newValue, 1)
    state.cost += state.contribution(oldValue)
    state.cost += state.contribution(newValue)

################################################################################
# AllDifferentConstraint initialization and updates
################################################################################

proc initialize*[T](state: AllDifferentConstraint[T], assignment: seq[T]) =
    state.countTable.clear()
    for i in 0..<state.denseCounts.len:
        state.denseCounts[i] = 0
    state.cost = 0
    var value: T
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions.items:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                state.bumpCount(value, 1)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for i, exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                state.exprValues[i] = value
                state.bumpCount(value, 1)

    # Calculate cost from both count structures
    for value, count in state.countTable.pairs:
        state.cost += max(0, count - 1)
    for count in state.denseCounts:
        state.cost += max(0, int(count) - 1)


proc updatePosition*[T](state: AllDifferentConstraint[T], position: int, newValue: T) =
    # State Update assigning newValue to position
    let oldValue = state.currentAssignment[position]
    state.lastOldValue = oldValue
    state.lastNewValue = newValue
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue
                state.adjustCounts(oldValue, newValue)

            of ExpressionBased:
                state.lastAffectedKey = position
                var oldExpValue, newExpValue: T
                for i in state.expressionsAtPosition[position]:
                    oldExpValue = state.exprValues[i]
                    state.currentAssignment[position] = newValue
                    if state.allLinear:
                        let coeff = state.exprCoeffs[i][position]
                        newExpValue = oldExpValue + coeff * (newValue - oldValue)
                    else:
                        newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.exprValues[i] = newExpValue
                    state.adjustCounts(oldExpValue, newExpValue)


proc moveDelta*[T](state: AllDifferentConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    var oldExpValue, newExpValue: T
    var oldValueCount, newValueCount: int

    case state.evalMethod:
        of PositionBased:
            oldValueCount = state.cnt(oldValue)
            doAssert oldValueCount >= 1, "oldValue should exist in count table"
            result -= oldValueCount - 1
            oldValueCount -= 1
            result += max(0, oldValueCount - 1)

            newValueCount = state.cnt(newValue)
            result -= max(0, newValueCount - 1)
            newValueCount += 1
            result += newValueCount - 1

        of ExpressionBased:
            for i in state.expressionsAtPosition[position]:
                oldExpValue = state.exprValues[i]

                oldValueCount = state.cnt(oldExpValue)
                result -= oldValueCount - 1
                oldValueCount -= 1
                result += max(0, oldValueCount - 1)

                if state.allLinear:
                    let coeff = state.exprCoeffs[i][position]
                    newExpValue = oldExpValue + coeff * (newValue - oldValue)
                else:
                    state.currentAssignment[position] = newValue
                    newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.currentAssignment[position] = oldValue

                newValueCount = state.cnt(newExpValue)
                result -= max(0, newValueCount - 1)
                newValueCount += 1
                result += newValueCount - 1


func getAffectedPositions*[T](state: AllDifferentConstraint[T]): PackedSet[int] =
    case state.evalMethod:
        of PositionBased:
            return state.positions
        of ExpressionBased:
            if state.lastAffectedKey >= 0:
                return state.affectedByPos.getOrDefault(state.lastAffectedKey)
            return initPackedSet[int]()


func getAffectedDomainValues*[T](state: AllDifferentConstraint[T], position: int): seq[T] =
    ## Returns only the old/new values whose counts changed, unless this position's
    ## current value is one of them (in which case all values are affected since the
    ## baseline removal cost changes).
    let curVal = state.currentAssignment[position]
    if curVal == state.lastOldValue or curVal == state.lastNewValue:
        return @[]  # All values affected
    else:
        return @[state.lastOldValue, state.lastNewValue]
