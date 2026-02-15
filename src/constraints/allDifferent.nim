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
                lastAffectedPositions*: PackedSet[int]  # positions affected by last updatePosition

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


func contribution[T](state: AllDifferentConstraint[T], value: T): int {.inline.} =
    max(0, getCount(state.countTable, value) - 1)


proc adjustCounts[T](state: AllDifferentConstraint[T], oldValue, newValue: T) {.inline.} =
    # Adjust value counts and state cost for the removal of oldValue and addition of newValue
    state.cost -= state.contribution(oldValue)
    state.cost -= state.contribution(newValue)
    decrementCount(state.countTable, oldValue)
    incrementCount(state.countTable, newValue)
    state.cost += state.contribution(oldValue)
    state.cost += state.contribution(newValue)

################################################################################
# AllDifferentConstraint initialization and updates
################################################################################

proc initialize*[T](state: AllDifferentConstraint[T], assignment: seq[T]) =
    var value: T
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions.items:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                incrementCount(state.countTable, value)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for i, exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                state.exprValues[i] = value
                incrementCount(state.countTable, value)

    # Calculate cost from count table for both methods
    for value, count in state.countTable.pairs:
        state.cost += max(0, count - 1)


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
                state.lastAffectedPositions = initPackedSet[int]()
                var oldExpValue, newExpValue: T
                for i in state.expressionsAtPosition[position]:
                    for pos in state.expressions[i].positions.items:
                        state.lastAffectedPositions.incl(pos)
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
            oldValueCount = getCount(state.countTable, oldValue)
            doAssert oldValueCount >= 1, "oldValue should exist in count table"
            result -= oldValueCount - 1
            oldValueCount -= 1
            result += max(0, oldValueCount - 1)

            newValueCount = getCount(state.countTable, newValue)
            result -= max(0, newValueCount - 1)
            newValueCount += 1
            result += newValueCount - 1

        of ExpressionBased:
            for i in state.expressionsAtPosition[position]:
                oldExpValue = state.exprValues[i]

                oldValueCount = getCount(state.countTable, oldExpValue)
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

                newValueCount = getCount(state.countTable, newExpValue)
                result -= max(0, newValueCount - 1)
                newValueCount += 1
                result += newValueCount - 1


func getAffectedPositions*[T](state: AllDifferentConstraint[T]): PackedSet[int] =
    case state.evalMethod:
        of PositionBased:
            return state.positions
        of ExpressionBased:
            return state.lastAffectedPositions


func getAffectedDomainValues*[T](state: AllDifferentConstraint[T], position: int): seq[T] =
    ## Returns only the old/new values whose counts changed, unless this position's
    ## current value is one of them (in which case all values are affected since the
    ## baseline removal cost changes).
    let curVal = state.currentAssignment[position]
    if curVal == state.lastOldValue or curVal == state.lastNewValue:
        return @[]  # All values affected
    else:
        return @[state.lastOldValue, state.lastNewValue]
