## Global Cardinality Constraint Implementation
## ============================================
##
## This module implements the Global Cardinality constraint, which ensures specific
## occurrence counts for multiple values simultaneously. Supports both exact counts
## and bounded counts (lower/upper bounds).
##
## **Constraint Definitions**:
## - **Exact**: `∀v ∈ cover : |{i ∈ positions : x[i] = v}| = targetCounts[v]`
## - **Bounded**: `∀v ∈ cover : lowerBounds[v] ≤ |{i ∈ positions : x[i] = v}| ≤ upperBounds[v]`
##
## **Key Features**:
## - Position-based and expression-based evaluation modes
## - Efficient incremental updates using value frequency tracking
## - Handles both exact count requirements and bounded count ranges
## - Penalty for values outside the cover set
##
## **Applications**:
## - Workforce scheduling: Exact staff requirements per role
## - Resource allocation: Bounded resource usage per category
## - Load balancing: Balanced distribution across servers
## - Quality control: Target occurrence rates
##
## **Performance**: O(1) incremental move evaluation, O(n) initialization where n = number of positions/expressions

import std/[packedsets, tables]

import ../expressions/expressions
import common

################################################################################
# Type definitions
################################################################################

type
    GlobalCardinalityType* = enum
        ExactCounts, BoundedCounts

    GlobalCardinalityConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        countTable: Table[T, int]  # Track actual counts of each value
        cover: seq[T]  # Values to count
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions: PackedSet[int]
            of ExpressionBased:
                expressions: seq[AlgebraicExpression[T]]
                expressionsAtPosition: Table[int, seq[int]]
        case constraintType*: GlobalCardinalityType
            of ExactCounts:
                targetCounts: Table[T, int]  # Target counts for each value
            of BoundedCounts:
                lowerBounds: Table[T, int]   # Lower bounds
                upperBounds: Table[T, int]   # Upper bounds

################################################################################
# GlobalCardinalityConstraint creation
################################################################################

func newExactGlobalCardinality*[T](positions: openArray[int], cover: openArray[T], counts: openArray[int]): GlobalCardinalityConstraint[T] =
    # Allocates and initializes new GlobalCardinalityConstraint[T] with exact counts
    doAssert cover.len == counts.len, "cover and counts arrays must have same length"
    new(result)

    var targetCounts = initTable[T, int]()
    for i in 0..<cover.len:
        targetCounts[cover[i]] = counts[i]

    result = GlobalCardinalityConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        countTable: initTable[T, int](),
        constraintType: ExactCounts,
        targetCounts: targetCounts,
        cover: @cover,
        currentAssignment: initTable[int, T]()
    )

func newBoundedGlobalCardinality*[T](positions: openArray[int], cover: openArray[T], lbound: openArray[int], ubound: openArray[int]): GlobalCardinalityConstraint[T] =
    # Allocates and initializes new GlobalCardinalityConstraint[T] with lower/upper bounds
    doAssert cover.len == lbound.len and cover.len == ubound.len, "cover, lbound, and ubound arrays must have same length"
    new(result)

    var lowerBounds = initTable[T, int]()
    var upperBounds = initTable[T, int]()
    for i in 0..<cover.len:
        lowerBounds[cover[i]] = lbound[i]
        upperBounds[cover[i]] = ubound[i]
        doAssert lbound[i] <= ubound[i], "Lower bound must be <= upper bound"

    result = GlobalCardinalityConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        countTable: initTable[T, int](),
        constraintType: BoundedCounts,
        lowerBounds: lowerBounds,
        upperBounds: upperBounds,
        cover: @cover,
        currentAssignment: initTable[int, T]()
    )

func newExactGlobalCardinality*[T](expressions: seq[AlgebraicExpression[T]], cover: openArray[T], counts: openArray[int]): GlobalCardinalityConstraint[T] =
    # Allocates and initializes new GlobalCardinalityConstraint[T] with exact counts for expressions
    doAssert cover.len == counts.len, "cover and counts arrays must have same length"
    new(result)

    var targetCounts = initTable[T, int]()
    for i in 0..<cover.len:
        targetCounts[cover[i]] = counts[i]

    result = GlobalCardinalityConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        countTable: initTable[T, int](),
        constraintType: ExactCounts,
        targetCounts: targetCounts,
        cover: @cover,
        currentAssignment: initTable[int, T]()
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

func newBoundedGlobalCardinality*[T](expressions: seq[AlgebraicExpression[T]], cover: openArray[T], lbound: openArray[int], ubound: openArray[int]): GlobalCardinalityConstraint[T] =
    # Allocates and initializes new GlobalCardinalityConstraint[T] with lower/upper bounds for expressions
    doAssert cover.len == lbound.len and cover.len == ubound.len, "cover, lbound, and ubound arrays must have same length"
    new(result)

    var lowerBounds = initTable[T, int]()
    var upperBounds = initTable[T, int]()
    for i in 0..<cover.len:
        lowerBounds[cover[i]] = lbound[i]
        upperBounds[cover[i]] = ubound[i]
        doAssert lbound[i] <= ubound[i], "Lower bound must be <= upper bound"

    result = GlobalCardinalityConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        countTable: initTable[T, int](),
        constraintType: BoundedCounts,
        lowerBounds: lowerBounds,
        upperBounds: upperBounds,
        cover: @cover,
        currentAssignment: initTable[int, T]()
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

################################################################################
# GlobalCardinalityConstraint utility functions
################################################################################


func contribution[T](state: GlobalCardinalityConstraint[T], value: T): int {.inline.} =
    # Cost contribution for either exact or bounded count constraint
    case state.constraintType:
        of ExactCounts:
            if value in state.targetCounts:
                let actualCount = getCount(state.countTable, value)
                let targetCount = state.targetCounts[value]
                return abs(actualCount - targetCount)
            else:
                # Value not in cover, contributes its count as penalty
                return getCount(state.countTable, value)
        of BoundedCounts:
            if value in state.lowerBounds:
                let actualCount = getCount(state.countTable, value)
                let lowerBound = state.lowerBounds[value]
                let upperBound = state.upperBounds[value]
                if actualCount < lowerBound:
                    return lowerBound - actualCount
                elif actualCount > upperBound:
                    return actualCount - upperBound
                else:
                    return 0
            else:
                # Value not in cover, contributes its count as penalty
                return getCount(state.countTable, value)


proc adjustCounts[T](state: GlobalCardinalityConstraint[T], oldValue, newValue: T) {.inline.} =
    # Adjust value counts and state cost for the removal of oldValue and addition of newValue
    state.cost -= state.contribution(oldValue)
    state.cost -= state.contribution(newValue)
    decrementCount(state.countTable, oldValue)
    incrementCount(state.countTable, newValue)
    state.cost += state.contribution(oldValue)
    state.cost += state.contribution(newValue)

################################################################################
# GlobalCardinalityConstraint initialization and updates
################################################################################

proc initialize*[T](state: GlobalCardinalityConstraint[T], assignment: seq[T]) =
    var value: T
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                incrementCount(state.countTable, value)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                incrementCount(state.countTable, value)

    # Calculate cost from actual counts vs targets/bounds
    case state.constraintType:
        of ExactCounts:
            for value in state.cover:
                state.cost += state.contribution(value)
            # Also account for values not in cover
            for value in state.countTable.keys:
                if value notin state.targetCounts:
                    state.cost += getCount(state.countTable, value)
        of BoundedCounts:
            for value in state.cover:
                state.cost += state.contribution(value)
            # Also account for values not in cover
            for value in state.countTable.keys:
                if value notin state.lowerBounds:
                    state.cost += getCount(state.countTable, value)

proc updatePosition*[T](state: GlobalCardinalityConstraint[T], position: int, newValue: T) =
    # State Update assigning newValue to position
    let oldValue = state.currentAssignment[position]
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue
                state.adjustCounts(oldValue, newValue)

            of ExpressionBased:
                var oldExpValue, newExpValue: T
                for i in state.expressionsAtPosition[position]:
                    oldExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.currentAssignment[position] = newValue
                    newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.adjustCounts(oldExpValue, newExpValue)

proc moveDelta*[T](state: GlobalCardinalityConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    proc simulateCountChange[T](state: GlobalCardinalityConstraint[T], value: T, countDelta: int): int {.inline.} =
        # Helper function to calculate cost delta when changing a value's count
        let currentCount = getCount(state.countTable, value)
        let oldCost = state.contribution(value)
        let newCount = currentCount + countDelta

        case state.constraintType:
            of ExactCounts:
                if value in state.targetCounts:
                    let target = state.targetCounts[value]
                    return abs(newCount - target) - oldCost
                else:
                    return newCount - oldCost
            of BoundedCounts:
                if value in state.lowerBounds:
                    let lowerBound = state.lowerBounds[value]
                    let upperBound = state.upperBounds[value]
                    let newCost = if newCount < lowerBound: lowerBound - newCount
                                 elif newCount > upperBound: newCount - upperBound
                                 else: 0
                    return newCost - oldCost
                else:
                    return newCount - oldCost

    case state.evalMethod:
        of PositionBased:
            result = simulateCountChange(state, oldValue, -1) + simulateCountChange(state, newValue, 1)

        of ExpressionBased:
            # Optimized version: avoid temporary assignment copy by modifying in place
            let originalValue = state.currentAssignment[position]

            for i in state.expressionsAtPosition[position]:
                let oldExpValue = state.expressions[i].evaluate(state.currentAssignment)

                # Temporarily modify assignment for new evaluation
                state.currentAssignment[position] = newValue
                let newExpValue = state.expressions[i].evaluate(state.currentAssignment)

                result += simulateCountChange(state, oldExpValue, -1) + simulateCountChange(state, newExpValue, 1)

            # Restore original value
            state.currentAssignment[position] = originalValue