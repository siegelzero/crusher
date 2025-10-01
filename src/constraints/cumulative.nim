## Cumulative Constraint Implementation
## =====================================
##
## This module implements the Cumulative constraint for resource-constrained scheduling.
## The cumulative constraint ensures that at each point in time, the total resource
## consumption of overlapping tasks does not exceed a given capacity limit.
##
## **Constraint Definition**:
## `∀t ∈ Time : Σ(tasks i where origin[i] ≤ t < origin[i] + duration[i]) height[i] ≤ limit`
##
## **Key Features**:
## - Position-based and expression-based evaluation modes
## - Efficient incremental updates using event-based timeline tracking
## - Linear violation cost based on resource overload at each time point
## - Support for both constant and variable durations/heights
##
## **Applications**:
## - Project scheduling: Tasks with resource requirements (workers, machines)
## - Manufacturing: Production scheduling with machine capacity limits
## - Computing: Job scheduling with CPU/memory constraints
## - Logistics: Vehicle routing with capacity constraints over time
## - Energy management: Power consumption scheduling within grid capacity
##
## **Violation Cost**: Sum of resource overloads across all time points
## - For each time t where demand > limit: cost += (demand - limit)
##
## **Performance**: O(k) move evaluation where k = number of affected time points

import std/[packedsets, tables]

import ../expressions/expressions

################################################################################
# Type definitions
################################################################################

type
    CumulativeConstraint*[T] = ref object
        currentAssignment*: Table[int, T]
        resourceProfile*: Table[T, T]  # time -> current resource usage
        cost*: int
        limit*: T
        case evalMethod*: StateEvalMethod
            of PositionBased:
                originPositions*: seq[int]
                durations*: seq[T]
                heights*: seq[T]
            of ExpressionBased:
                originExpressions*: seq[AlgebraicExpression[T]]
                durationsExpr*: seq[T]  # Can be extended to expressions if needed
                heightsExpr*: seq[T]    # Can be extended to expressions if needed
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# CumulativeConstraint creation
################################################################################

func newCumulativeConstraint*[T](originPositions: openArray[int],
                                 durations: openArray[T],
                                 heights: openArray[T],
                                 limit: T): CumulativeConstraint[T] =
    ## Creates a position-based cumulative constraint
    ## - originPositions: Variable positions representing task start times
    ## - durations: Duration of each task (constant)
    ## - heights: Resource consumption of each task (constant)
    ## - limit: Maximum resource capacity
    doAssert originPositions.len == durations.len, "originPositions and durations must have same length"
    doAssert originPositions.len == heights.len, "originPositions and heights must have same length"

    new(result)
    result = CumulativeConstraint[T](
        cost: 0,
        limit: limit,
        evalMethod: PositionBased,
        originPositions: @originPositions,
        durations: @durations,
        heights: @heights,
        resourceProfile: initTable[T, T](),
        currentAssignment: initTable[int, T](),
    )

func newCumulativeConstraint*[T](originExpressions: seq[AlgebraicExpression[T]],
                                 durations: openArray[T],
                                 heights: openArray[T],
                                 limit: T): CumulativeConstraint[T] =
    ## Creates an expression-based cumulative constraint
    doAssert originExpressions.len == durations.len, "originExpressions and durations must have same length"
    doAssert originExpressions.len == heights.len, "originExpressions and heights must have same length"

    new(result)
    result = CumulativeConstraint[T](
        cost: 0,
        limit: limit,
        evalMethod: ExpressionBased,
        originExpressions: originExpressions,
        durationsExpr: @durations,
        heightsExpr: @heights,
        resourceProfile: initTable[T, T](),
        currentAssignment: initTable[int, T](),
        expressionsAtPosition: buildExpressionPositionMap(originExpressions)
    )

################################################################################
# CumulativeConstraint utility functions
################################################################################

func getResourceUsage[T](profile: Table[T, T], time: T): T {.inline.} =
    ## Gets the resource usage at a given time point
    profile.getOrDefault(time, T(0))

proc updateResourceProfile[T](state: CumulativeConstraint[T], taskIdx: int, origin: T, isAdding: bool) =
    ## Updates the resource profile for a task being added or removed
    ## isAdding = true: add task to profile, false: remove task from profile
    let duration = case state.evalMethod:
        of PositionBased: state.durations[taskIdx]
        of ExpressionBased: state.durationsExpr[taskIdx]

    let height = case state.evalMethod:
        of PositionBased: state.heights[taskIdx]
        of ExpressionBased: state.heightsExpr[taskIdx]

    # Update resource profile for the time range [origin, origin + duration)
    for t in origin ..< (origin + duration):
        let currentUsage = state.resourceProfile.getResourceUsage(t)
        let newUsage = if isAdding: currentUsage + height else: currentUsage - height

        if newUsage == T(0):
            state.resourceProfile.del(t)
        else:
            state.resourceProfile[t] = newUsage

proc recalculateCost[T](state: CumulativeConstraint[T]) =
    ## Recalculates the total cost from the resource profile
    state.cost = 0
    for time, usage in state.resourceProfile.pairs:
        if usage > state.limit:
            state.cost += int(usage - state.limit)

################################################################################
# CumulativeConstraint initialization and updates
################################################################################

proc initialize*[T](state: CumulativeConstraint[T], assignment: seq[T]) =
    ## Initializes the cumulative constraint with the given assignment
    state.resourceProfile.clear()
    state.cost = 0

    case state.evalMethod:
        of PositionBased:
            for i, pos in state.originPositions:
                let origin = assignment[pos]
                state.currentAssignment[pos] = origin
                state.updateResourceProfile(i, origin, isAdding = true)

        of ExpressionBased:
            # Store all relevant position values
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            # Evaluate each origin expression and build resource profile
            for i, exp in state.originExpressions:
                let origin = exp.evaluate(state.currentAssignment)
                state.updateResourceProfile(i, origin, isAdding = true)

    state.recalculateCost()

proc updatePosition*[T](state: CumulativeConstraint[T], position: int, newValue: T) =
    ## Updates the constraint state when a position changes
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return

    case state.evalMethod:
        of PositionBased:
            # Find which task this position corresponds to
            for i, pos in state.originPositions:
                if pos == position:
                    # Remove old task instance from profile
                    state.updateResourceProfile(i, oldValue, isAdding = false)
                    # Add new task instance to profile
                    state.currentAssignment[position] = newValue
                    state.updateResourceProfile(i, newValue, isAdding = true)
                    break

        of ExpressionBased:
            # Find all expressions affected by this position
            if position in state.expressionsAtPosition:
                for i in state.expressionsAtPosition[position]:
                    # Remove old contribution
                    let oldOrigin = state.originExpressions[i].evaluate(state.currentAssignment)
                    state.updateResourceProfile(i, oldOrigin, isAdding = false)

                    # Update assignment and add new contribution
                    state.currentAssignment[position] = newValue
                    let newOrigin = state.originExpressions[i].evaluate(state.currentAssignment)
                    state.updateResourceProfile(i, newOrigin, isAdding = true)
            else:
                state.currentAssignment[position] = newValue

    state.recalculateCost()

proc moveDelta*[T](state: CumulativeConstraint[T], position: int, oldValue, newValue: T): int =
    ## Calculates the cost delta for moving a position from oldValue to newValue
    if oldValue == newValue:
        return 0

    # Create a temporary resource profile change map
    var profileDelta = initTable[T, T]()

    case state.evalMethod:
        of PositionBased:
            # Find which task this position corresponds to
            for i, pos in state.originPositions:
                if pos == position:
                    let duration = state.durations[i]
                    let height = state.heights[i]

                    # Track changes from removing old task
                    for t in oldValue ..< (oldValue + duration):
                        let currentDelta = profileDelta.getOrDefault(t, T(0))
                        profileDelta[t] = currentDelta - height

                    # Track changes from adding new task
                    for t in newValue ..< (newValue + duration):
                        let currentDelta = profileDelta.getOrDefault(t, T(0))
                        profileDelta[t] = currentDelta + height
                    break

        of ExpressionBased:
            if position in state.expressionsAtPosition:
                for i in state.expressionsAtPosition[position]:
                    # Evaluate old origin
                    let oldOrigin = state.originExpressions[i].evaluate(state.currentAssignment)
                    let duration = state.durationsExpr[i]
                    let height = state.heightsExpr[i]

                    # Track changes from removing old task
                    for t in oldOrigin ..< (oldOrigin + duration):
                        let currentDelta = profileDelta.getOrDefault(t, T(0))
                        profileDelta[t] = currentDelta - height

                    # Evaluate new origin with temporary assignment
                    state.currentAssignment[position] = newValue
                    let newOrigin = state.originExpressions[i].evaluate(state.currentAssignment)
                    state.currentAssignment[position] = oldValue  # Restore

                    # Track changes from adding new task
                    for t in newOrigin ..< (newOrigin + duration):
                        let currentDelta = profileDelta.getOrDefault(t, T(0))
                        profileDelta[t] = currentDelta + height

    # Calculate cost delta
    var costDelta = 0
    for time, delta in profileDelta.pairs:
        let oldUsage = state.resourceProfile.getResourceUsage(time)
        let newUsage = oldUsage + delta

        let oldOverload = max(0, int(oldUsage - state.limit))
        let newOverload = max(0, int(newUsage - state.limit))

        costDelta += newOverload - oldOverload

    return costDelta
