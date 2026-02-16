# Cumulative Constraint for resource-constrained scheduling
#
# The cumulative constraint ensures that at each point in time, the total resource
# consumption of overlapping tasks does not exceed a given capacity limit.
#
# **Constraint Definition**:
# `∀t ∈ Time : Σ(tasks i where origin[i] ≤ t < origin[i] + duration[i]) height[i] ≤ limit`
#
# **Performance**: O(min(|shift|, duration)) move evaluation via symmetric difference.
# Only the time points entering/leaving the task's range are examined.
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
            if position < state.positionToTask.len and state.positionToTask[position] >= 0:
                let i = state.positionToTask[position]
                let duration = state.durations[i]
                let height = state.heights[i]
                var costDelta = 0

                let oldStart = int(oldValue)
                let oldEnd = int(oldValue + duration)
                let newStart = int(newValue)
                let newEnd = int(newValue + duration)
                let tMax = state.maxTime + 1

                # Symmetric difference: only update time points that actually change
                if newStart > oldStart:
                    for t in max(0, oldStart) ..< min(tMax, min(newStart, oldEnd)):
                        let oldUsage = state.resourceProfile[t]
                        let newUsage = oldUsage - height
                        costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)
                        state.resourceProfile[t] = newUsage
                    for t in max(0, max(oldEnd, newStart)) ..< min(tMax, newEnd):
                        let oldUsage = state.resourceProfile[t]
                        let newUsage = oldUsage + height
                        costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)
                        state.resourceProfile[t] = newUsage
                else:
                    for t in max(0, newStart) ..< min(tMax, min(oldStart, newEnd)):
                        let oldUsage = state.resourceProfile[t]
                        let newUsage = oldUsage + height
                        costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)
                        state.resourceProfile[t] = newUsage
                    for t in max(0, max(newEnd, oldStart)) ..< min(tMax, oldEnd):
                        let oldUsage = state.resourceProfile[t]
                        let newUsage = oldUsage - height
                        costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)
                        state.resourceProfile[t] = newUsage

                state.currentAssignment[position] = newValue
                state.cost += costDelta
            else:
                state.currentAssignment[position] = newValue

        of ExpressionBased:
            if position in state.expressionsAtPosition:
                var costDelta = 0
                let tMax = state.maxTime + 1

                # Evaluate all old/new origins upfront (before mutating assignment)
                var changes: seq[tuple[oldStart, oldEnd, newStart, newEnd: int, height: T]]
                for i in state.expressionsAtPosition[position]:
                    var tempAssign = initTable[int, T]()
                    for pos in state.originExpressions[i].positions.items:
                        tempAssign[pos] = state.currentAssignment[pos]
                    let oldOrigin = state.originExpressions[i].evaluate(tempAssign)
                    tempAssign[position] = newValue
                    let newOrigin = state.originExpressions[i].evaluate(tempAssign)
                    if oldOrigin == newOrigin:
                        continue
                    let duration = state.durationsExpr[i]
                    changes.add((
                        oldStart: int(oldOrigin), oldEnd: int(oldOrigin + duration),
                        newStart: int(newOrigin), newEnd: int(newOrigin + duration),
                        height: state.heightsExpr[i]
                    ))

                # Pass 1: remove "leaving" time points (in old range but not new)
                for c in changes:
                    if c.newStart > c.oldStart:
                        for t in max(0, c.oldStart) ..< min(tMax, min(c.newStart, c.oldEnd)):
                            let u = state.resourceProfile[t]
                            state.resourceProfile[t] = u - c.height
                            costDelta += calculateCostDelta(u, u - c.height, state.limit)
                    else:
                        for t in max(0, max(c.newEnd, c.oldStart)) ..< min(tMax, c.oldEnd):
                            let u = state.resourceProfile[t]
                            state.resourceProfile[t] = u - c.height
                            costDelta += calculateCostDelta(u, u - c.height, state.limit)

                state.currentAssignment[position] = newValue

                # Pass 2: add "entering" time points (in new range but not old)
                for c in changes:
                    if c.newStart > c.oldStart:
                        for t in max(0, max(c.oldEnd, c.newStart)) ..< min(tMax, c.newEnd):
                            let u = state.resourceProfile[t]
                            state.resourceProfile[t] = u + c.height
                            costDelta += calculateCostDelta(u, u + c.height, state.limit)
                    else:
                        for t in max(0, c.newStart) ..< min(tMax, min(c.oldStart, c.newEnd)):
                            let u = state.resourceProfile[t]
                            state.resourceProfile[t] = u + c.height
                            costDelta += calculateCostDelta(u, u + c.height, state.limit)

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
    ## Calculates the cost delta for moving a position from oldValue to newValue.
    ## O(min(|shift|, duration)) complexity via symmetric difference of old/new time ranges.
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
            let tMax = state.maxTime + 1

            # Symmetric difference: only visit time points that actually change.
            # For a shift of k, this touches O(min(k, duration)) points instead of O(2*duration).
            if newStart > oldStart:
                # Shift right: left tail leaves, right tail enters
                for t in max(0, oldStart) ..< min(tMax, min(newStart, oldEnd)):
                    costDelta += calculateCostDelta(state.resourceProfile[t],
                        state.resourceProfile[t] - height, state.limit)
                for t in max(0, max(oldEnd, newStart)) ..< min(tMax, newEnd):
                    costDelta += calculateCostDelta(state.resourceProfile[t],
                        state.resourceProfile[t] + height, state.limit)
            else:
                # Shift left: left tail enters, right tail leaves
                for t in max(0, newStart) ..< min(tMax, min(oldStart, newEnd)):
                    costDelta += calculateCostDelta(state.resourceProfile[t],
                        state.resourceProfile[t] + height, state.limit)
                for t in max(0, max(newEnd, oldStart)) ..< min(tMax, oldEnd):
                    costDelta += calculateCostDelta(state.resourceProfile[t],
                        state.resourceProfile[t] - height, state.limit)

            return costDelta

        of ExpressionBased:
            if position notin state.expressionsAtPosition:
                return 0

            var profileDelta = initTable[int, T]()
            let tMax = state.maxTime + 1

            for i in state.expressionsAtPosition[position]:
                var tempAssign = initTable[int, T]()
                for pos in state.originExpressions[i].positions.items:
                    tempAssign[pos] = state.currentAssignment[pos]
                let oldOrigin = state.originExpressions[i].evaluate(tempAssign)
                tempAssign[position] = newValue
                let newOrigin = state.originExpressions[i].evaluate(tempAssign)

                if oldOrigin == newOrigin:
                    continue

                let duration = state.durationsExpr[i]
                let height = state.heightsExpr[i]
                let oldStart = int(oldOrigin)
                let oldEnd = int(oldOrigin + duration)
                let newStart = int(newOrigin)
                let newEnd = int(newOrigin + duration)

                # Symmetric difference: only track time points that actually change
                if newStart > oldStart:
                    for t in max(0, oldStart) ..< min(tMax, min(newStart, oldEnd)):
                        profileDelta[t] = profileDelta.getOrDefault(t, T(0)) - height
                    for t in max(0, max(oldEnd, newStart)) ..< min(tMax, newEnd):
                        profileDelta[t] = profileDelta.getOrDefault(t, T(0)) + height
                else:
                    for t in max(0, newStart) ..< min(tMax, min(oldStart, newEnd)):
                        profileDelta[t] = profileDelta.getOrDefault(t, T(0)) + height
                    for t in max(0, max(newEnd, oldStart)) ..< min(tMax, oldEnd):
                        profileDelta[t] = profileDelta.getOrDefault(t, T(0)) - height

            # Calculate cost delta
            var costDelta = 0
            for time, delta in profileDelta.pairs:
                if delta != T(0):
                    let oldUsage = state.resourceProfile[time]
                    let newUsage = oldUsage + delta
                    costDelta += calculateCostDelta(oldUsage, newUsage, state.limit)

            return costDelta


proc batchMovePenalty*[T](state: CumulativeConstraint[T], position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    ## Compute cost + moveDelta for ALL domain values at a position using prefix sums.
    ## O(maxTime + domainSize) instead of O(domainSize * duration).
    result = newSeq[int](domain.len)

    if state.evalMethod != PositionBased:
        # Fallback to individual computation
        for i, v in domain:
            result[i] = state.cost + state.moveDelta(position, currentValue, v)
        return

    if position >= state.positionToTask.len or state.positionToTask[position] < 0:
        # Not a task origin — penalty doesn't change
        for i in 0..<domain.len:
            result[i] = state.cost
        return

    let taskIdx = state.positionToTask[position]
    let duration = int(state.durations[taskIdx])
    let height = int(state.heights[taskIdx])
    let limit = int(state.limit)
    let tMax = state.maxTime + 1

    # Step 1: Compute "removed profile" overuse and delta array
    # removedProfile[t] = resourceProfile[t] - height if t is in old task range, else resourceProfile[t]
    # delta[t] = max(0, removedProfile[t] + height - limit) - max(0, removedProfile[t] - limit)
    #   = extra overuse at t when our task is placed there
    let oldStart = max(0, int(currentValue))
    let oldEnd = min(tMax, int(currentValue) + duration)

    # Build prefix sum of delta values
    var prefixDelta = newSeq[int64](tMax + 1)
    var baseOveruse: int64 = 0
    for t in 0..<tMax:
        let rp = int(state.resourceProfile[t])
        var removedP: int
        if t >= oldStart and t < oldEnd:
            removedP = rp - height
        else:
            removedP = rp
        let overuseWithout = max(0, removedP - limit)
        let overuseWith = max(0, removedP + height - limit)
        baseOveruse += int64(overuseWithout)
        prefixDelta[t + 1] = prefixDelta[t] + int64(overuseWith - overuseWithout)

    # Step 2: For each candidate, compute total penalty in O(1)
    for i, v in domain:
        let newStart = max(0, int(v))
        let newEnd = min(tMax, int(v) + duration)
        if newStart >= tMax:
            # Task entirely outside profile — penalty is just base overuse
            result[i] = int(baseOveruse)
        else:
            let addedCost = prefixDelta[newEnd] - prefixDelta[newStart]
            result[i] = int(baseOveruse + addedCost)
