import std/[packedsets, tables]

import ../expressions/expressions

################################################################################
# MultiknapsackConstraint - Global Constraint
#
# The multiknapsack constraint ensures that for each value v in the domain,
# the total weight of items assigned to value v does not exceed capacity[v].
#
# Mathematical form: ∀v ∈ Values : Σ(i where x[i] = v) weights[i] ≤ capacity[v]
#
# Applications:
# - Bin packing with different bin capacities
# - Resource allocation with capacity limits
# - Load balancing across servers/machines
# - Vehicle routing with weight/volume constraints
################################################################################

type
    MultiknapsackConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        weights*: seq[T]  # Weight for each position index
        capacities*: Table[T, T]  # Capacity for each value
        loadTable*: Table[T, T]  # Current load for each value
        cost*: int
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions*: PackedSet[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# MultiknapsackConstraint creation
################################################################################

func newMultiknapsackConstraint*[T](positions: openArray[int], weights: openArray[T], capacities: openArray[(T, T)]): MultiknapsackConstraint[T] =
    # Allocates and initializes new MultiknapsackConstraint[T] for positions
    doAssert positions.len == weights.len, "positions and weights arrays must have same length"
    new(result)

    var capacityTable = initTable[T, T]()
    for (value, capacity) in capacities:
        capacityTable[value] = capacity

    result = MultiknapsackConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        weights: @weights,
        capacities: capacityTable,
        loadTable: initTable[T, T](),
        currentAssignment: initTable[int, T](),
    )

func newMultiknapsackConstraint*[T](expressions: seq[AlgebraicExpression[T]], weights: openArray[T], capacities: openArray[(T, T)]): MultiknapsackConstraint[T] =
    # Allocates and initializes new MultiknapsackConstraint[T] for expressions
    doAssert expressions.len == weights.len, "expressions and weights arrays must have same length"
    new(result)

    var capacityTable = initTable[T, T]()
    for (value, capacity) in capacities:
        capacityTable[value] = capacity

    result = MultiknapsackConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        weights: @weights,
        capacities: capacityTable,
        loadTable: initTable[T, T](),
        currentAssignment: initTable[int, T](),
    )

    result.expressionsAtPosition = buildExpressionPositionMap(expressions)

################################################################################
# MultiknapsackConstraint utility functions
################################################################################

func getLoad*[T](loadTable: Table[T, T], value: T): T {.inline.} =
    ## Gets the current load for a value, returning 0 if not present
    loadTable.getOrDefault(value, T(0))

proc incrementLoad*[T](loadTable: var Table[T, T], value: T, weight: T) {.inline.} =
    ## Increments the load for a value by the given weight
    if value in loadTable:
        loadTable[value] += weight
    else:
        loadTable[value] = weight

proc decrementLoad*[T](loadTable: var Table[T, T], value: T, weight: T) {.inline.} =
    ## Decrements the load for a value by the given weight, removing zero entries
    if value in loadTable:
        loadTable[value] -= weight
        if loadTable[value] <= T(0):
            loadTable.del(value)

func overCapacity[T](state: MultiknapsackConstraint[T], value: T): T {.inline.} =
    ## Returns how much a value exceeds its capacity (0 if within capacity)
    let currentLoad = getLoad(state.loadTable, value)
    let capacity = state.capacities.getOrDefault(value, T(0))
    return max(T(0), currentLoad - capacity)

proc adjustLoads[T](state: MultiknapsackConstraint[T], oldValue, newValue: T, weight: T) {.inline.} =
    ## Adjust loads and state cost for the removal of oldValue and addition of newValue with given weight
    state.cost -= int(state.overCapacity(oldValue))
    state.cost -= int(state.overCapacity(newValue))
    decrementLoad(state.loadTable, oldValue, weight)
    incrementLoad(state.loadTable, newValue, weight)
    state.cost += int(state.overCapacity(oldValue))
    state.cost += int(state.overCapacity(newValue))

################################################################################
# MultiknapsackConstraint initialization and updates
################################################################################

proc initialize*[T](state: MultiknapsackConstraint[T], assignment: seq[T]) =
    # Clear previous state
    state.loadTable.clear()
    state.currentAssignment.clear()
    state.cost = 0

    var value: T
    case state.evalMethod:
        of PositionBased:
            var posIndex = 0
            for pos in state.positions.items:
                value = assignment[pos]
                state.currentAssignment[pos] = value
                incrementLoad(state.loadTable, value, state.weights[posIndex])
                posIndex += 1

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for i, exp in state.expressions:
                value = exp.evaluate(state.currentAssignment)
                incrementLoad(state.loadTable, value, state.weights[i])

    # Calculate cost from load table - sum of all over-capacity amounts
    state.cost = 0
    for value in state.loadTable.keys:
        state.cost += int(state.overCapacity(value))

proc updatePosition*[T](state: MultiknapsackConstraint[T], position: int, newValue: T) =
    # State Update assigning newValue to position
    let oldValue = state.currentAssignment[position]
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue
                # Find the weight for this position
                var posIndex = 0
                for pos in state.positions.items:
                    if pos == position:
                        state.adjustLoads(oldValue, newValue, state.weights[posIndex])
                        break
                    posIndex += 1

            of ExpressionBased:
                var oldExpValue, newExpValue: T
                for i in state.expressionsAtPosition[position]:
                    oldExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.currentAssignment[position] = newValue
                    newExpValue = state.expressions[i].evaluate(state.currentAssignment)
                    state.adjustLoads(oldExpValue, newExpValue, state.weights[i])

proc moveDelta*[T](state: MultiknapsackConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0

    proc simulateLoadChange[T](state: MultiknapsackConstraint[T], value: T, weightDelta: T): int {.inline.} =
        # Helper function to calculate cost delta when changing a value's load
        let currentLoad = getLoad(state.loadTable, value)
        let capacity = state.capacities.getOrDefault(value, T(0))
        let oldOverCapacity = max(T(0), currentLoad - capacity)
        let newLoad = currentLoad + weightDelta
        let newOverCapacity = max(T(0), newLoad - capacity)
        return int(newOverCapacity - oldOverCapacity)

    case state.evalMethod:
        of PositionBased:
            # Find the weight for this position
            var posIndex = 0
            for pos in state.positions.items:
                if pos == position:
                    let weight = state.weights[posIndex]
                    result = simulateLoadChange(state, oldValue, -weight) + simulateLoadChange(state, newValue, weight)
                    break
                posIndex += 1

        of ExpressionBased:
            # Temporarily modify assignment for evaluation
            let originalValue = state.currentAssignment[position]

            for i in state.expressionsAtPosition[position]:
                let oldExpValue = state.expressions[i].evaluate(state.currentAssignment)

                # Temporarily modify assignment for new evaluation
                state.currentAssignment[position] = newValue
                let newExpValue = state.expressions[i].evaluate(state.currentAssignment)

                let weight = state.weights[i]
                result += simulateLoadChange(state, oldExpValue, -weight) + simulateLoadChange(state, newExpValue, weight)

            # Restore original value
            state.currentAssignment[position] = originalValue
