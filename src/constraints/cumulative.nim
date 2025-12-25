# Cumulative Constraint for resource-constrained scheduling
#
# The cumulative constraint ensures that at each point in time, the total resource
# consumption of overlapping tasks does not exceed a given capacity limit.
#
# **Constraint Definition**:
# `∀t ∈ Time : Σ(tasks i where origin[i] ≤ t < origin[i] + duration[i]) height[i] ≤ limit`
#
# **Performance**: O(k) move evaluation where k = number of affected time points
# Uses array-based resource profile for O(1) access instead of hash tables.

import std/[packedsets, sequtils, tables]
import ../expressions/expressions

################################################################################
# Type definitions
################################################################################

type
    CumulativeConstraint*[T] = ref object
        currentAssignment*: seq[T]       # position -> current value (array for O(1) access)
        resourceProfile*: seq[T]         # time -> current resource usage (array for O(1) access)
        cost*: int
        limit*: T
        maxTime*: int                    # Maximum time value in profile
        lastChangedPosition*: int        # Track last changed position for smart affected positions
        lastOldValue*: T                 # Track old value for smart affected positions
        case evalMethod*: StateEvalMethod
            of PositionBased:
                originPositions*: seq[int]
                durations*: seq[T]
                heights*: seq[T]
                positionToTask*: seq[int]  # position -> task index (-1 if not a task position)
            of ExpressionBased:
                originExpressions*: seq[AlgebraicExpression[T]]
                durationsExpr*: seq[T]
                heightsExpr*: seq[T]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# CumulativeConstraint creation
################################################################################

func newCumulativeConstraint*[T](originPositions: openArray[int],
                                 durations: openArray[T],
                                 heights: openArray[T],
                                 limit: T,
                                 maxTime: int = 500): CumulativeConstraint[T] =
    ## Creates a position-based cumulative constraint
    doAssert originPositions.len == durations.len, "originPositions and durations must have same length"
    doAssert originPositions.len == heights.len, "originPositions and heights must have same length"

    # Find max position to size the positionToTask array
    var maxPos = 0
    for pos in originPositions:
        if pos > maxPos:
            maxPos = pos

    # Build position-to-task lookup array (-1 means not a task position)
    var posToTask = newSeq[int](maxPos + 1)
    for i in 0..maxPos:
        posToTask[i] = -1
    for i, pos in originPositions:
        posToTask[pos] = i

    new(result)
    result = CumulativeConstraint[T](
        cost: 0,
        limit: limit,
        maxTime: maxTime,
        evalMethod: PositionBased,
        originPositions: @originPositions,
        durations: @durations,
        heights: @heights,
        positionToTask: posToTask,
        resourceProfile: newSeq[T](maxTime + 1),
        currentAssignment: newSeq[T](maxPos + 1),
    )

func newCumulativeConstraint*[T](originExpressions: seq[AlgebraicExpression[T]],
                                 durations: openArray[T],
                                 heights: openArray[T],
                                 limit: T,
                                 maxTime: int = 500): CumulativeConstraint[T] =
    ## Creates an expression-based cumulative constraint
    doAssert originExpressions.len == durations.len, "originExpressions and durations must have same length"
    doAssert originExpressions.len == heights.len, "originExpressions and heights must have same length"

    # Find max position from all expressions
    var maxPos = 0
    for exp in originExpressions:
        for pos in exp.positions.items:
            if pos > maxPos:
                maxPos = pos

    new(result)
    result = CumulativeConstraint[T](
        cost: 0,
        limit: limit,
        maxTime: maxTime,
        evalMethod: ExpressionBased,
        originExpressions: originExpressions,
        durationsExpr: @durations,
        heightsExpr: @heights,
        resourceProfile: newSeq[T](maxTime + 1),
        currentAssignment: newSeq[T](maxPos + 1),
        expressionsAtPosition: buildExpressionPositionMap(originExpressions)
    )

################################################################################
# CumulativeConstraint utility functions
################################################################################

proc updateResourceProfile[T](state: CumulativeConstraint[T], taskIdx: int, origin: T, isAdding: bool) =
    ## Updates the resource profile for a task being added or removed
    let duration = case state.evalMethod:
        of PositionBased: state.durations[taskIdx]
        of ExpressionBased: state.durationsExpr[taskIdx]

    let height = case state.evalMethod:
        of PositionBased: state.heights[taskIdx]
        of ExpressionBased: state.heightsExpr[taskIdx]

    # Update resource profile for the time range [origin, origin + duration)
    let startT = int(origin)
    let endT = int(origin + duration)
    for t in startT ..< min(endT, state.maxTime + 1):
        if t >= 0:
            if isAdding:
                state.resourceProfile[t] += height
            else:
                state.resourceProfile[t] -= height

proc recalculateCost[T](state: CumulativeConstraint[T]) =
    # Recalculates the total cost from the resource profile
    state.cost = 0
    for t in 0..state.maxTime:
        let usage = state.resourceProfile[t]
        if usage > state.limit:
            state.cost += usage - state.limit

proc calculateCostDelta[T](oldUsage, newUsage, limit: T): int {.inline.} =
    ## Calculates the change in cost when usage changes at a single time point
    let oldOverload = max(0, int(oldUsage - limit))
    let newOverload = max(0, int(newUsage - limit))
    return newOverload - oldOverload

################################################################################
# CumulativeConstraint initialization and updates
################################################################################

proc initialize*[T](state: CumulativeConstraint[T], assignment: seq[T]) =
    ## Initializes the cumulative constraint with the given assignment
    # Calculate required maxTime from assignment values and durations
    var requiredMaxTime = state.maxTime
    case state.evalMethod:
        of PositionBased:
            for i, pos in state.originPositions:
                let origin = assignment[pos]
                let endTime = int(origin) + int(state.durations[i])
                if endTime > requiredMaxTime:
                    requiredMaxTime = endTime
        of ExpressionBased:
            for i, exp in state.originExpressions:
                var tempAssign = initTable[int, T]()
                for pos in exp.positions.items:
                    tempAssign[pos] = assignment[pos]
                let origin = exp.evaluate(tempAssign)
                let endTime = int(origin) + int(state.durationsExpr[i])
                if endTime > requiredMaxTime:
                    requiredMaxTime = endTime

    # Resize resource profile if needed
    if requiredMaxTime > state.maxTime:
        state.maxTime = requiredMaxTime
        state.resourceProfile = newSeq[T](requiredMaxTime + 1)

    # Reset resource profile
    for t in 0..state.maxTime:
        state.resourceProfile[t] = T(0)
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
                var tempAssign = initTable[int, T]()
                for pos in exp.positions.items:
                    tempAssign[pos] = assignment[pos]
                let origin = exp.evaluate(tempAssign)
                state.updateResourceProfile(i, origin, isAdding = true)

    state.recalculateCost()

proc updatePosition*[T](state: CumulativeConstraint[T], position: int, newValue: T) =
    ## Updates the constraint state when a position changes
    ## Uses incremental cost update for O(duration) complexity
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return

    # Track change for getAffectedPositions
    state.lastChangedPosition = position
    state.lastOldValue = oldValue

    case state.evalMethod:
        of PositionBased:
            # O(1) lookup for which task this position corresponds to
            if position < state.positionToTask.len and state.positionToTask[position] >= 0:
                let i = state.positionToTask[position]
                let duration = state.durations[i]

                # Calculate cost delta for affected time points
                var costDelta = 0
                let height = state.heights[i]

                # Old range
                let oldStart = int(oldValue)
                let oldEnd = int(oldValue + duration)
                # New range
                let newStart = int(newValue)
                let newEnd = int(newValue + duration)

                # Process old range (task being removed)
                for t in oldStart ..< min(oldEnd, state.maxTime + 1):
                    if t >= 0:
                        let inNewRange = t >= newStart and t < newEnd
                        if not inNewRange:
                            let oldUsage = state.resourceProfile[t]
                            let newUsage = oldUsage - height
                            costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)
                            state.resourceProfile[t] = newUsage

                # Process new range (task being added)
                for t in newStart ..< min(newEnd, state.maxTime + 1):
                    if t >= 0:
                        let inOldRange = t >= oldStart and t < oldEnd
                        if not inOldRange:
                            let oldUsage = state.resourceProfile[t]
                            let newUsage = oldUsage + height
                            costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)
                            state.resourceProfile[t] = newUsage

                state.currentAssignment[position] = newValue
                state.cost += costDelta
            else:
                state.currentAssignment[position] = newValue

        of ExpressionBased:
            # Find all expressions affected by this position
            if position in state.expressionsAtPosition:
                var costDelta = 0

                for i in state.expressionsAtPosition[position]:
                    # Evaluate old origin
                    var tempAssign = initTable[int, T]()
                    for pos in state.originExpressions[i].positions.items:
                        tempAssign[pos] = state.currentAssignment[pos]
                    let oldOrigin = state.originExpressions[i].evaluate(tempAssign)
                    let duration = state.durationsExpr[i]
                    let height = state.heightsExpr[i]

                    # Remove old task contribution
                    let oldStart = int(oldOrigin)
                    let oldEnd = int(oldOrigin + duration)
                    for t in oldStart ..< min(oldEnd, state.maxTime + 1):
                        if t >= 0:
                            let oldUsage = state.resourceProfile[t]
                            state.resourceProfile[t] = oldUsage - height
                            costDelta += calculateCostDelta(oldUsage, oldUsage - height, state.limit)

                # Update assignment
                state.currentAssignment[position] = newValue

                for i in state.expressionsAtPosition[position]:
                    # Evaluate new origin
                    var tempAssign = initTable[int, T]()
                    for pos in state.originExpressions[i].positions.items:
                        tempAssign[pos] = state.currentAssignment[pos]
                    let newOrigin = state.originExpressions[i].evaluate(tempAssign)
                    let duration = state.durationsExpr[i]
                    let height = state.heightsExpr[i]

                    # Add new task contribution
                    let newStart = int(newOrigin)
                    let newEnd = int(newOrigin + duration)
                    for t in newStart ..< min(newEnd, state.maxTime + 1):
                        if t >= 0:
                            let oldUsage = state.resourceProfile[t]
                            state.resourceProfile[t] = oldUsage + height
                            costDelta += calculateCostDelta(oldUsage, oldUsage + height, state.limit)

                state.cost += costDelta
            else:
                state.currentAssignment[position] = newValue

proc getAffectedPositions*[T](state: CumulativeConstraint[T]): PackedSet[int] =
    ## Returns positions of tasks that overlap in time with the last changed task.
    result = initPackedSet[int]()

    case state.evalMethod:
        of PositionBased:
            if state.lastChangedPosition >= state.positionToTask.len or
               state.positionToTask[state.lastChangedPosition] < 0:
                return result

            let changedTask = state.positionToTask[state.lastChangedPosition]
            let changedDuration = state.durations[changedTask]
            let oldStart = state.lastOldValue
            let newStart = state.currentAssignment[state.lastChangedPosition]

            # Time range affected by the change
            let affectedStart = min(oldStart, newStart)
            let affectedEnd = max(oldStart + changedDuration, newStart + changedDuration)

            # Find tasks that overlap with this range
            for i, pos in state.originPositions:
                let taskStart = state.currentAssignment[pos]
                let taskEnd = taskStart + state.durations[i]
                if taskStart < affectedEnd and taskEnd > affectedStart:
                    result.incl(pos)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                result.incl(pos)

proc getAffectedDomainValues*[T](state: CumulativeConstraint[T], position: int): seq[T] =
    ## Returns only the domain values that need penalty recalculation after the last change.
    ## For cumulative, only values overlapping with the changed time range are affected.
    result = @[]

    case state.evalMethod:
        of PositionBased:
            if state.lastChangedPosition >= state.positionToTask.len or
               state.positionToTask[state.lastChangedPosition] < 0:
                return result
            if position >= state.positionToTask.len or state.positionToTask[position] < 0:
                return result

            let changedTask = state.positionToTask[state.lastChangedPosition]
            let changedDuration = state.durations[changedTask]
            let oldStart = state.lastOldValue
            let newStart = state.currentAssignment[state.lastChangedPosition]

            let thisTask = state.positionToTask[position]
            let thisDuration = state.durations[thisTask]

            # Time range affected by the change
            let affectedStart = min(oldStart, newStart)
            let affectedEnd = max(oldStart + changedDuration, newStart + changedDuration)

            # Domain values for this position that overlap with affected range
            # A value V overlaps if [V, V+thisDuration) intersects [affectedStart, affectedEnd)
            # This means: V < affectedEnd AND V + thisDuration > affectedStart
            # So: affectedStart - thisDuration < V < affectedEnd
            let minVal = max(0, int(affectedStart) - int(thisDuration) + 1)
            let maxVal = min(state.maxTime, int(affectedEnd) - 1)

            for v in minVal..maxVal:
                result.add(T(v))

        of ExpressionBased:
            # Fall back to empty (will use full domain)
            discard

proc getGoodStartTimes*[T](state: CumulativeConstraint[T], position: int, maxCandidates: int = 30): seq[T] =
    ## Returns candidate start times where this task might fit well.
    ## Uses the resource profile to find times with available capacity.
    ## Much faster than evaluating all domain values.
    result = @[]

    case state.evalMethod:
        of PositionBased:
            if position >= state.positionToTask.len or state.positionToTask[position] < 0:
                return result

            let taskIdx = state.positionToTask[position]
            let duration = state.durations[taskIdx]
            let height = state.heights[taskIdx]
            let currentStart = state.currentAssignment[position]

            # Always include current position and nearby positions
            result.add(currentStart)
            if currentStart > T(0): result.add(currentStart - T(1))
            if currentStart > T(1): result.add(currentStart - T(2))
            if currentStart < T(state.maxTime - int(duration)): result.add(currentStart + T(1))
            if currentStart < T(state.maxTime - int(duration) - 1): result.add(currentStart + T(2))

            # Scan for times where task would fit (usage + height <= limit)
            var t = 0
            while t <= state.maxTime - int(duration) and result.len < maxCandidates:
                # Check if task fits at time t
                var fits = true
                var minSlack = state.limit  # Track minimum slack in this window
                for dt in 0 ..< int(duration):
                    let timePoint = t + dt
                    if timePoint <= state.maxTime:
                        # Don't count current task's contribution
                        var usage = state.resourceProfile[timePoint]
                        if currentStart <= T(timePoint) and T(timePoint) < currentStart + duration:
                            usage -= height
                        if usage + height > state.limit:
                            fits = false
                            break
                        let slack = state.limit - usage - height
                        if slack < minSlack:
                            minSlack = slack

                if fits and T(t) != currentStart:
                    result.add(T(t))

                # Skip ahead - if we found a fit, jump by duration to find non-overlapping slots
                if fits:
                    t += max(1, int(duration) div 2)
                else:
                    t += 1

            # If we didn't find enough, add some evenly spaced samples
            if result.len < maxCandidates div 2:
                let step = max(1, (state.maxTime - int(duration)) div (maxCandidates - result.len))
                var t2 = 0
                while t2 <= state.maxTime - int(duration) and result.len < maxCandidates:
                    let val = T(t2)
                    if val notin result:
                        result.add(val)
                    t2 += step

        of ExpressionBased:
            # Fall back to no filtering for expression-based
            discard

proc moveDelta*[T](state: CumulativeConstraint[T], position: int, oldValue, newValue: T): int =
    ## Calculates the cost delta for moving a position from oldValue to newValue
    ## O(duration) complexity - only examines affected time points
    if oldValue == newValue:
        return 0

    case state.evalMethod:
        of PositionBased:
            if position >= state.positionToTask.len or state.positionToTask[position] < 0:
                return 0

            let i = state.positionToTask[position]
            let duration = state.durations[i]
            let height = state.heights[i]

            var costDelta = 0

            let oldStart = int(oldValue)
            let oldEnd = int(oldValue + duration)
            let newStart = int(newValue)
            let newEnd = int(newValue + duration)

            # Time points where task is being removed (old position)
            for t in oldStart ..< min(oldEnd, state.maxTime + 1):
                if t >= 0:
                    let inNewRange = t >= newStart and t < newEnd
                    if not inNewRange:
                        let oldUsage = state.resourceProfile[t]
                        let newUsage = oldUsage - height
                        costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)

            # Time points where task is being added (new position)
            for t in newStart ..< min(newEnd, state.maxTime + 1):
                if t >= 0:
                    let inOldRange = t >= oldStart and t < oldEnd
                    if not inOldRange:
                        let oldUsage = state.resourceProfile[t]
                        let newUsage = oldUsage + height
                        costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)

            return costDelta

        of ExpressionBased:
            if position notin state.expressionsAtPosition:
                return 0

            var profileDelta = initTable[int, T]()

            for i in state.expressionsAtPosition[position]:
                # Evaluate old origin
                var tempAssign = initTable[int, T]()
                for pos in state.originExpressions[i].positions.items:
                    tempAssign[pos] = state.currentAssignment[pos]
                let oldOrigin = state.originExpressions[i].evaluate(tempAssign)
                let duration = state.durationsExpr[i]
                let height = state.heightsExpr[i]

                # Track changes from removing old task
                for t in int(oldOrigin) ..< int(oldOrigin + duration):
                    if t >= 0 and t <= state.maxTime:
                        profileDelta[t] = profileDelta.getOrDefault(t, T(0)) - height

                # Evaluate new origin with updated position
                tempAssign[position] = newValue
                let newOrigin = state.originExpressions[i].evaluate(tempAssign)

                # Track changes from adding new task
                for t in int(newOrigin) ..< int(newOrigin + duration):
                    if t >= 0 and t <= state.maxTime:
                        profileDelta[t] = profileDelta.getOrDefault(t, T(0)) + height

            # Calculate cost delta
            var costDelta = 0
            for time, delta in profileDelta.pairs:
                if delta != T(0):
                    let oldUsage = state.resourceProfile[time]
                    let newUsage = oldUsage + delta
                    costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)

            return costDelta
