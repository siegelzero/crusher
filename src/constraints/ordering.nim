## Ordering Constraint Implementation
## ==================================
##
## This module implements ordering constraints that enforce monotonic relationships
## between variables: increasing, decreasing, strictly increasing, and strictly decreasing.
##
## **Constraint Definitions**:
## - **Increasing**: `∀i ∈ [0, n-2] : x[positions[i]] ≤ x[positions[i+1]]`
## - **Decreasing**: `∀i ∈ [0, n-2] : x[positions[i]] ≥ x[positions[i+1]]`
## - **Strictly Increasing**: `∀i ∈ [0, n-2] : x[positions[i]] < x[positions[i+1]]`
## - **Strictly Decreasing**: `∀i ∈ [0, n-2] : x[positions[i]] > x[positions[i+1]]`
##
## **Key Features**:
## - Position-based and expression-based evaluation modes
## - Efficient adjacent-pair violation checking
## - Support for all four ordering relationship types
## - Incremental move evaluation with minimal recomputation
##
## **Applications**:
## - Scheduling: Temporal ordering constraints (start ≤ finish)
## - Resource management: Capacity/priority ordering
## - Data processing: Sorted sequence requirements
## - Quality control: Monotonic trend enforcement
## - Performance optimization: Ensuring improvement over time
##
## **Violation Cost**: Sum of ordering violations between adjacent pairs
## - Each violated constraint contributes 1 to total cost
##
## **Performance**: O(k) incremental move evaluation where k = number of affected adjacent pairs

import std/[packedsets, sequtils, tables, algorithm]

import ../expressions/[expressions, types]

################################################################################
# Type definitions
################################################################################

type
    OrderingType* = enum
        Increasing,
        StrictlyIncreasing,
        Decreasing,
        StrictlyDecreasing

    OrderingConstraint*[T] = ref object
        orderingType*: OrderingType
        currentAssignment*: Table[int, T]
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions*: PackedSet[int]
                sortedPositions*: seq[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# Ordering violation detection templates
################################################################################

template violatesOrdering[T](val1, val2: T, orderingType: OrderingType): bool =
    case orderingType:
        of Increasing: val1 > val2
        of StrictlyIncreasing: val1 >= val2
        of Decreasing: val1 < val2
        of StrictlyDecreasing: val1 <= val2

################################################################################
# OrderingConstraint creation
################################################################################

func newOrderingConstraint*[T](positions: openArray[int], orderingType: OrderingType): OrderingConstraint[T] =
    new(result)
    # For all ordering types, we always sort positions in ascending order
    # The ordering type determines how we check values, not position order
    let sortedPositions = sorted(@positions)

    result = OrderingConstraint[T](
        orderingType: orderingType,
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        sortedPositions: sortedPositions,
        currentAssignment: initTable[int, T](),
    )

func newOrderingConstraint*[T](expressions: seq[AlgebraicExpression[T]], orderingType: OrderingType): OrderingConstraint[T] =
    new(result)
    result = OrderingConstraint[T](
        orderingType: orderingType,
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        currentAssignment: initTable[int, T](),
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

################################################################################
# Convenience constructors for specific ordering types
################################################################################

func newIncreasingConstraint*[T](positions: openArray[int]): OrderingConstraint[T] =
    newOrderingConstraint[T](positions, Increasing)

func newIncreasingConstraint*[T](expressions: seq[AlgebraicExpression[T]]): OrderingConstraint[T] =
    newOrderingConstraint[T](expressions, Increasing)

func newStrictlyIncreasingConstraint*[T](positions: openArray[int]): OrderingConstraint[T] =
    newOrderingConstraint[T](positions, StrictlyIncreasing)

func newStrictlyIncreasingConstraint*[T](expressions: seq[AlgebraicExpression[T]]): OrderingConstraint[T] =
    newOrderingConstraint[T](expressions, StrictlyIncreasing)

func newDecreasingConstraint*[T](positions: openArray[int]): OrderingConstraint[T] =
    newOrderingConstraint[T](positions, Decreasing)

func newDecreasingConstraint*[T](expressions: seq[AlgebraicExpression[T]]): OrderingConstraint[T] =
    newOrderingConstraint[T](expressions, Decreasing)

func newStrictlyDecreasingConstraint*[T](positions: openArray[int]): OrderingConstraint[T] =
    newOrderingConstraint[T](positions, StrictlyDecreasing)

func newStrictlyDecreasingConstraint*[T](expressions: seq[AlgebraicExpression[T]]): OrderingConstraint[T] =
    newOrderingConstraint[T](expressions, StrictlyDecreasing)

################################################################################
# OrderingConstraint utility functions
################################################################################

func countViolations[T](state: OrderingConstraint[T]): int {.inline.} =
    result = 0
    case state.evalMethod:
        of PositionBased:
            for i in 0..<(state.sortedPositions.len - 1):
                let pos1 = state.sortedPositions[i]
                let pos2 = state.sortedPositions[i + 1]
                let val1 = state.currentAssignment[pos1]
                let val2 = state.currentAssignment[pos2]
                if violatesOrdering(val1, val2, state.orderingType):
                    result += 1
        of ExpressionBased:
            for i in 0..<(state.expressions.len - 1):
                let val1 = state.expressions[i].evaluate(state.currentAssignment)
                let val2 = state.expressions[i + 1].evaluate(state.currentAssignment)
                if violatesOrdering(val1, val2, state.orderingType):
                    result += 1

################################################################################
# OrderingConstraint initialization and updates
################################################################################

proc initialize*[T](state: OrderingConstraint[T], assignment: seq[T]) =
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions.items:
                state.currentAssignment[pos] = assignment[pos]

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

    state.cost = state.countViolations()

proc updatePosition*[T](state: OrderingConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]
    if oldValue != newValue:
        let costDelta = state.moveDelta(position, oldValue, newValue)
        state.currentAssignment[position] = newValue
        state.cost += costDelta

proc moveDelta*[T](state: OrderingConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    result = 0
    case state.evalMethod:
        of PositionBased:
            var posIndex = -1
            for i, pos in state.sortedPositions:
                if pos == position:
                    posIndex = i
                    break

            if posIndex == -1:
                return 0

            # Check constraint with previous position
            if posIndex > 0:
                let prevPos = state.sortedPositions[posIndex - 1]
                let prevVal = state.currentAssignment[prevPos]

                let oldViolation = if violatesOrdering(prevVal, oldValue, state.orderingType): 1 else: 0
                let newViolation = if violatesOrdering(prevVal, newValue, state.orderingType): 1 else: 0
                result += newViolation - oldViolation

            # Check constraint with next position
            if posIndex < state.sortedPositions.len - 1:
                let nextPos = state.sortedPositions[posIndex + 1]
                let nextVal = state.currentAssignment[nextPos]

                let oldViolation = if violatesOrdering(oldValue, nextVal, state.orderingType): 1 else: 0
                let newViolation = if violatesOrdering(newValue, nextVal, state.orderingType): 1 else: 0
                result += newViolation - oldViolation

        of ExpressionBased:
            # Only evaluate expressions that depend on the changed position
            if position notin state.expressionsAtPosition:
                return 0

            let affectedExpressions = state.expressionsAtPosition[position]
            var tempAssignment = state.currentAssignment
            tempAssignment[position] = newValue

            # Track which constraint pairs we've already processed to avoid double-counting
            var processedPairs: seq[(int, int)] = @[]

            result = 0
            for exprIndex in affectedExpressions:
                # Check constraint with previous expression
                if exprIndex > 0:
                    let pairKey = (exprIndex - 1, exprIndex)
                    if pairKey notin processedPairs:
                        processedPairs.add(pairKey)
                        let val1Old = state.expressions[exprIndex - 1].evaluate(state.currentAssignment)
                        let val2Old = state.expressions[exprIndex].evaluate(state.currentAssignment)
                        let val1New = state.expressions[exprIndex - 1].evaluate(tempAssignment)
                        let val2New = state.expressions[exprIndex].evaluate(tempAssignment)

                        let oldViolation = if violatesOrdering(val1Old, val2Old, state.orderingType): 1 else: 0
                        let newViolation = if violatesOrdering(val1New, val2New, state.orderingType): 1 else: 0
                        result += newViolation - oldViolation

                # Check constraint with next expression
                if exprIndex < state.expressions.len - 1:
                    let pairKey = (exprIndex, exprIndex + 1)
                    if pairKey notin processedPairs:
                        processedPairs.add(pairKey)
                        let val1Old = state.expressions[exprIndex].evaluate(state.currentAssignment)
                        let val2Old = state.expressions[exprIndex + 1].evaluate(state.currentAssignment)
                        let val1New = state.expressions[exprIndex].evaluate(tempAssignment)
                        let val2New = state.expressions[exprIndex + 1].evaluate(tempAssignment)

                        let oldViolation = if violatesOrdering(val1Old, val2Old, state.orderingType): 1 else: 0
                        let newViolation = if violatesOrdering(val1New, val2New, state.orderingType): 1 else: 0
                        result += newViolation - oldViolation
