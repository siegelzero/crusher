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
        limitPosition*: int              # Position of variable limit (-1 = constant limit)
        prefixDeltaBuf*: seq[int64]      # Pre-allocated buffer for batch prefix sums
        # Variable duration/height support (for channel-dependent scheduling, e.g. MRCPSP)
        durationPositions*: seq[int]     # per-task: position of dur var (-1 if constant)
        heightPositions*: seq[int]       # per-task: position of height var (-1 if constant)
        durPosToTask*: Table[int, int]   # dur position → task index
        heightPosToTask*: Table[int, int] # height position → task index
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

proc getDuration*[T](state: CumulativeConstraint[T], taskIdx: int): T {.inline.} =
    ## Read current duration for a task: from assignment if variable, else fixed constant.
    if state.durationPositions.len > 0 and state.durationPositions[taskIdx] >= 0:
        state.currentAssignment[state.durationPositions[taskIdx]]
    else:
        case state.evalMethod:
        of PositionBased: state.durations[taskIdx]
        of ExpressionBased: state.durationsExpr[taskIdx]

proc getHeight*[T](state: CumulativeConstraint[T], taskIdx: int): T {.inline.} =
    ## Read current height for a task: from assignment if variable, else fixed constant.
    if state.heightPositions.len > 0 and state.heightPositions[taskIdx] >= 0:
        state.currentAssignment[state.heightPositions[taskIdx]]
    else:
        case state.evalMethod:
        of PositionBased: state.heights[taskIdx]
        of ExpressionBased: state.heightsExpr[taskIdx]

proc getTaskOrigin*[T](state: CumulativeConstraint[T], taskIdx: int): T {.inline.} =
    ## Get current origin for a task.
    case state.evalMethod:
    of PositionBased: state.currentAssignment[state.originPositions[taskIdx]]
    of ExpressionBased: state.originExpressions[taskIdx].evaluate(state.currentAssignment)

proc hasVarDurHeight*[T](state: CumulativeConstraint[T]): bool {.inline.} =
    state.durationPositions.len > 0

################################################################################
# CumulativeConstraint creation
################################################################################

func newCumulativeConstraint*[T](originPositions: openArray[int],
                                 durations: openArray[T],
                                 heights: openArray[T],
                                 limit: T,
                                 maxTime: int = 500,
                                 limitPosition: int = -1): CumulativeConstraint[T] =
    ## Creates a position-based cumulative constraint
    doAssert originPositions.len == durations.len, "originPositions and durations must have same length"
    doAssert originPositions.len == heights.len, "originPositions and heights must have same length"

    # Find max position to size the positionToTask array and currentAssignment
    var maxPos = 0
    for pos in originPositions:
        if pos > maxPos:
            maxPos = pos
    if limitPosition > maxPos:
        maxPos = limitPosition

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
        limitPosition: limitPosition,
        evalMethod: PositionBased,
        originPositions: @originPositions,
        durations: @durations,
        heights: @heights,
        positionToTask: posToTask,
        resourceProfile: newSeq[T](maxTime + 1),
        currentAssignment: newSeq[T](maxPos + 1),
        prefixDeltaBuf: newSeq[int64](maxTime + 2),
    )

func newCumulativeConstraint*[T](originExpressions: seq[AlgebraicExpression[T]],
                                 durations: openArray[T],
                                 heights: openArray[T],
                                 limit: T,
                                 maxTime: int = 500,
                                 limitPosition: int = -1): CumulativeConstraint[T] =
    ## Creates an expression-based cumulative constraint
    doAssert originExpressions.len == durations.len, "originExpressions and durations must have same length"
    doAssert originExpressions.len == heights.len, "originExpressions and heights must have same length"

    # Find max position from all expressions
    var maxPos = 0
    for exp in originExpressions:
        for pos in exp.positions.items:
            if pos > maxPos:
                maxPos = pos
    if limitPosition > maxPos:
        maxPos = limitPosition

    new(result)
    result = CumulativeConstraint[T](
        cost: 0,
        limit: limit,
        maxTime: maxTime,
        limitPosition: limitPosition,
        evalMethod: ExpressionBased,
        originExpressions: originExpressions,
        durationsExpr: @durations,
        heightsExpr: @heights,
        resourceProfile: newSeq[T](maxTime + 1),
        currentAssignment: newSeq[T](maxPos + 1),
        prefixDeltaBuf: newSeq[int64](maxTime + 2),
        expressionsAtPosition: buildExpressionPositionMap(originExpressions)
    )

################################################################################
# CumulativeConstraint utility functions
################################################################################

proc updateResourceProfile[T](state: CumulativeConstraint[T], taskIdx: int, origin: T, isAdding: bool) =
    ## Updates the resource profile for a task being added or removed
    let duration = state.getDuration(taskIdx)
    let height = state.getHeight(taskIdx)

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
    # Update limit from variable if applicable
    if state.limitPosition >= 0:
        state.limit = assignment[state.limitPosition]
        state.currentAssignment[state.limitPosition] = assignment[state.limitPosition]

    # Store dur/height position values in currentAssignment
    if state.hasVarDurHeight:
        for i in 0..<state.durationPositions.len:
            let dp = state.durationPositions[i]
            if dp >= 0:
                state.currentAssignment[dp] = assignment[dp]
            let hp = state.heightPositions[i]
            if hp >= 0:
                state.currentAssignment[hp] = assignment[hp]

    # Calculate required maxTime from assignment values and durations
    var requiredMaxTime = state.maxTime
    case state.evalMethod:
        of PositionBased:
            for i, pos in state.originPositions:
                let origin = assignment[pos]
                state.currentAssignment[pos] = origin
                let endTime = int(origin) + int(state.getDuration(i))
                if endTime > requiredMaxTime:
                    requiredMaxTime = endTime
        of ExpressionBased:
            # Store all relevant position values first
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            for i, exp in state.originExpressions:
                let origin = exp.evaluate(state.currentAssignment)
                let endTime = int(origin) + int(state.getDuration(i))
                if endTime > requiredMaxTime:
                    requiredMaxTime = endTime

    # Resize resource profile if needed
    if requiredMaxTime > state.maxTime:
        state.maxTime = requiredMaxTime
        state.resourceProfile = newSeq[T](requiredMaxTime + 1)
        state.prefixDeltaBuf = newSeq[int64](requiredMaxTime + 2)

    # Reset resource profile
    for t in 0..state.maxTime:
        state.resourceProfile[t] = T(0)
    state.cost = 0

    case state.evalMethod:
        of PositionBased:
            for i, pos in state.originPositions:
                let origin = assignment[pos]
                state.updateResourceProfile(i, origin, isAdding = true)

        of ExpressionBased:
            # Evaluate each origin expression and build resource profile
            for i, exp in state.originExpressions:
                let origin = exp.evaluate(state.currentAssignment)
                state.updateResourceProfile(i, origin, isAdding = true)

    state.recalculateCost()

proc updatePosition*[T](state: CumulativeConstraint[T], position: int, newValue: T) =
    ## Updates the constraint state when a position changes
    ## Uses incremental cost update for O(duration) complexity
    if position >= state.currentAssignment.len:
        return
    let oldValue = state.currentAssignment[position]
    if oldValue == newValue:
        return

    # Track change for getAffectedPositions
    state.lastChangedPosition = position
    state.lastOldValue = oldValue

    # Handle variable limit change
    if position == state.limitPosition:
        state.limit = newValue
        state.currentAssignment[position] = newValue
        state.recalculateCost()
        return

    # Handle duration position change: re-profile the affected task
    if state.hasVarDurHeight and position in state.durPosToTask:
        let taskIdx = state.durPosToTask[position]
        let origin = state.getTaskOrigin(taskIdx)
        let height = state.getHeight(taskIdx)
        let oldDur = oldValue
        let newDur = newValue
        var costDelta = 0
        let tMax = state.maxTime + 1
        let startT = max(0, int(origin))
        # Remove time points that are in old range but not new
        if newDur < oldDur:
            for t in max(0, startT + int(newDur)) ..< min(tMax, startT + int(oldDur)):
                let u = state.resourceProfile[t]
                state.resourceProfile[t] = u - height
                costDelta += calculateCostDelta(u, u - height, state.limit)
        elif newDur > oldDur:
            for t in max(0, startT + int(oldDur)) ..< min(tMax, startT + int(newDur)):
                let u = state.resourceProfile[t]
                state.resourceProfile[t] = u + height
                costDelta += calculateCostDelta(u, u + height, state.limit)
        state.currentAssignment[position] = newValue
        state.cost += costDelta
        return

    # Handle height position change: adjust resource usage across task's time range
    if state.hasVarDurHeight and position in state.heightPosToTask:
        let taskIdx = state.heightPosToTask[position]
        let origin = state.getTaskOrigin(taskIdx)
        let duration = state.getDuration(taskIdx)
        let oldHeight = oldValue
        let newHeight = newValue
        let heightDelta = newHeight - oldHeight
        var costDelta = 0
        let tMax = state.maxTime + 1
        let startT = max(0, int(origin))
        let endT = min(tMax, int(origin) + int(duration))
        for t in startT ..< endT:
            let u = state.resourceProfile[t]
            state.resourceProfile[t] = u + heightDelta
            costDelta += calculateCostDelta(u, u + heightDelta, state.limit)
        state.currentAssignment[position] = newValue
        state.cost += costDelta
        return

    case state.evalMethod:
        of PositionBased:
            if position < state.positionToTask.len and state.positionToTask[position] >= 0:
                let i = state.positionToTask[position]
                let duration = state.getDuration(i)
                let height = state.getHeight(i)
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
                    let duration = state.getDuration(i)
                    changes.add((
                        oldStart: int(oldOrigin), oldEnd: int(oldOrigin + duration),
                        newStart: int(newOrigin), newEnd: int(newOrigin + duration),
                        height: state.getHeight(i)
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

    # If the limit changed, all task/dur/height positions are affected
    if state.limitPosition >= 0 and state.lastChangedPosition == state.limitPosition:
        case state.evalMethod:
            of PositionBased:
                for pos in state.originPositions:
                    result.incl(pos)
            of ExpressionBased:
                for pos in state.expressionsAtPosition.keys:
                    result.incl(pos)
        if state.hasVarDurHeight:
            for pos in state.durPosToTask.keys: result.incl(pos)
            for pos in state.heightPosToTask.keys: result.incl(pos)
        result.incl(state.limitPosition)
        return result

    # If a dur/height changed, all overlapping task origins are affected
    if state.hasVarDurHeight and (state.lastChangedPosition in state.durPosToTask or
                                   state.lastChangedPosition in state.heightPosToTask):
        let taskIdx = if state.lastChangedPosition in state.durPosToTask:
                          state.durPosToTask[state.lastChangedPosition]
                      else:
                          state.heightPosToTask[state.lastChangedPosition]
        let origin = state.getTaskOrigin(taskIdx)
        let dur = state.getDuration(taskIdx)
        # Use max of old and new duration to cover full affected range
        let oldDur = state.lastOldValue
        let maxDur = max(dur, oldDur)
        let affectedStart = int(origin)
        let affectedEnd = int(origin) + int(maxDur)
        case state.evalMethod:
            of PositionBased:
                for i, pos in state.originPositions:
                    let taskStart = int(state.currentAssignment[pos])
                    let taskEnd = taskStart + int(state.getDuration(i))
                    if taskStart < affectedEnd and taskEnd > affectedStart:
                        result.incl(pos)
            of ExpressionBased:
                for pos in state.expressionsAtPosition.keys:
                    result.incl(pos)
        if state.limitPosition >= 0:
            result.incl(state.limitPosition)
        return result

    case state.evalMethod:
        of PositionBased:
            if state.lastChangedPosition >= state.positionToTask.len or
               state.positionToTask[state.lastChangedPosition] < 0:
                return result

            let changedTask = state.positionToTask[state.lastChangedPosition]
            let changedDuration = state.getDuration(changedTask)
            let oldStart = state.lastOldValue
            let newStart = state.currentAssignment[state.lastChangedPosition]

            # Time range affected by the change
            let affectedStart = min(oldStart, newStart)
            let affectedEnd = max(oldStart + changedDuration, newStart + changedDuration)

            # Find tasks that overlap with this range
            for i, pos in state.originPositions:
                let taskStart = state.currentAssignment[pos]
                let taskEnd = taskStart + state.getDuration(i)
                if taskStart < affectedEnd and taskEnd > affectedStart:
                    result.incl(pos)

            # A task move affects the limit position's penalties too
            if state.limitPosition >= 0:
                result.incl(state.limitPosition)

        of ExpressionBased:
            for pos in state.expressionsAtPosition.keys:
                result.incl(pos)
            if state.limitPosition >= 0:
                result.incl(state.limitPosition)

proc getAffectedDomainValues*[T](state: CumulativeConstraint[T], position: int): seq[T] =
    ## Returns only the domain values that need penalty recalculation after the last change.
    ## For cumulative, only values overlapping with the changed time range are affected.
    result = @[]

    # If limit changed, all domain values are affected for every position
    if state.limitPosition >= 0 and state.lastChangedPosition == state.limitPosition:
        return result  # empty = all values

    # If querying the limit position, all limit values are affected
    if position == state.limitPosition:
        return result  # empty = all values

    case state.evalMethod:
        of PositionBased:
            if state.lastChangedPosition >= state.positionToTask.len or
               state.positionToTask[state.lastChangedPosition] < 0:
                return result
            if position >= state.positionToTask.len or state.positionToTask[position] < 0:
                return result

            let changedTask = state.positionToTask[state.lastChangedPosition]
            let changedDuration = state.getDuration(changedTask)
            let oldStart = state.lastOldValue
            let newStart = state.currentAssignment[state.lastChangedPosition]

            let thisTask = state.positionToTask[position]
            let thisDuration = state.getDuration(thisTask)

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

    # Limit position is not a task — no start time candidates
    if position == state.limitPosition:
        return result

    case state.evalMethod:
        of PositionBased:
            if position >= state.positionToTask.len or state.positionToTask[position] < 0:
                return result

            let taskIdx = state.positionToTask[position]
            let duration = state.getDuration(taskIdx)
            let height = state.getHeight(taskIdx)
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

    # Handle variable limit change
    if position == state.limitPosition:
        var newCost = 0
        for t in 0..state.maxTime:
            let usage = state.resourceProfile[t]
            if usage > newValue:
                newCost += int(usage - newValue)
        return newCost - state.cost

    # Handle duration position change
    if state.hasVarDurHeight and position in state.durPosToTask:
        let taskIdx = state.durPosToTask[position]
        let origin = state.getTaskOrigin(taskIdx)
        let height = state.getHeight(taskIdx)
        let oldDur = oldValue
        let newDur = newValue
        var costDelta = 0
        let tMax = state.maxTime + 1
        let startT = max(0, int(origin))
        if newDur < oldDur:
            # Shorter duration: time points leaving
            for t in max(0, startT + int(newDur)) ..< min(tMax, startT + int(oldDur)):
                costDelta += calculateCostDelta(state.resourceProfile[t],
                    state.resourceProfile[t] - height, state.limit)
        elif newDur > oldDur:
            # Longer duration: time points entering
            for t in max(0, startT + int(oldDur)) ..< min(tMax, startT + int(newDur)):
                costDelta += calculateCostDelta(state.resourceProfile[t],
                    state.resourceProfile[t] + height, state.limit)
        return costDelta

    # Handle height position change
    if state.hasVarDurHeight and position in state.heightPosToTask:
        let taskIdx = state.heightPosToTask[position]
        let origin = state.getTaskOrigin(taskIdx)
        let duration = state.getDuration(taskIdx)
        let heightDelta = newValue - oldValue
        var costDelta = 0
        let tMax = state.maxTime + 1
        let startT = max(0, int(origin))
        let endT = min(tMax, int(origin) + int(duration))
        for t in startT ..< endT:
            costDelta += calculateCostDelta(state.resourceProfile[t],
                state.resourceProfile[t] + heightDelta, state.limit)
        return costDelta

    case state.evalMethod:
        of PositionBased:
            if position >= state.positionToTask.len or state.positionToTask[position] < 0:
                return 0

            let i = state.positionToTask[position]
            let duration = state.getDuration(i)
            let height = state.getHeight(i)
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

            let tMax = state.maxTime + 1

            # Evaluate old origins before mutation
            type TaskChange = tuple[oldStart, oldEnd, newStart, newEnd: int, height: T]
            var changes: seq[TaskChange]

            for i in state.expressionsAtPosition[position]:
                let oldOrigin = state.originExpressions[i].evaluate(state.currentAssignment)
                state.currentAssignment[position] = newValue
                let newOrigin = state.originExpressions[i].evaluate(state.currentAssignment)
                state.currentAssignment[position] = oldValue

                if oldOrigin == newOrigin:
                    continue

                let duration = state.getDuration(i)
                changes.add((
                    oldStart: int(oldOrigin), oldEnd: int(oldOrigin + duration),
                    newStart: int(newOrigin), newEnd: int(newOrigin + duration),
                    height: state.getHeight(i)
                ))

            if changes.len == 0:
                return 0

            # Apply symmetric differences directly to resource profile, accumulate cost delta
            var costDelta = 0

            # Pass 1: remove leaving time points
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

            # Pass 2: add entering time points
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

            # Undo: restore resource profile
            for c in changes:
                if c.newStart > c.oldStart:
                    for t in max(0, c.oldStart) ..< min(tMax, min(c.newStart, c.oldEnd)):
                        state.resourceProfile[t] += c.height
                    for t in max(0, max(c.oldEnd, c.newStart)) ..< min(tMax, c.newEnd):
                        state.resourceProfile[t] -= c.height
                else:
                    for t in max(0, max(c.newEnd, c.oldStart)) ..< min(tMax, c.oldEnd):
                        state.resourceProfile[t] += c.height
                    for t in max(0, c.newStart) ..< min(tMax, min(c.oldStart, c.newEnd)):
                        state.resourceProfile[t] -= c.height

            return costDelta


proc batchMovePenalty*[T](state: CumulativeConstraint[T], position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    ## Compute moveDelta for ALL domain values at a position using prefix sums.
    ## O(maxTime + domainSize) instead of O(domainSize * duration).
    result = newSeq[int](domain.len)

    # Handle variable limit position: iterate profile for each candidate limit value
    if position == state.limitPosition:
        for i, v in domain:
            var newCost = 0
            for t in 0..state.maxTime:
                let usage = state.resourceProfile[t]
                if usage > v:
                    newCost += int(usage - v)
            result[i] = newCost - state.cost
        return

    # Handle dur/height positions: fall back to per-value moveDelta (small domains)
    if state.hasVarDurHeight and (position in state.durPosToTask or
                                   position in state.heightPosToTask):
        for i, v in domain:
            if v != currentValue:
                result[i] = state.moveDelta(position, currentValue, v)
        return

    if state.evalMethod == ExpressionBased:
        if position notin state.expressionsAtPosition:
            return
        let taskIndices = state.expressionsAtPosition[position]
        if taskIndices.len == 1:
            # Single task affected — use prefix-sum batch approach
            let taskIdx = taskIndices[0]
            let duration = int(state.getDuration(taskIdx))
            let height = int(state.getHeight(taskIdx))
            let limit = int(state.limit)
            let tMax = state.maxTime + 1

            # Evaluate current origin
            let oldOrigin = state.originExpressions[taskIdx].evaluate(state.currentAssignment)
            let oldStart = max(0, int(oldOrigin))
            let oldEnd = min(tMax, int(oldOrigin) + duration)

            # Build prefix sum with current task removed
            state.prefixDeltaBuf[0] = 0
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
                state.prefixDeltaBuf[t + 1] = state.prefixDeltaBuf[t] + int64(overuseWith - overuseWithout)

            let currentCost = int64(state.cost)
            for i, v in domain:
                if v == currentValue:
                    continue
                state.currentAssignment[position] = v
                let newOrigin = state.originExpressions[taskIdx].evaluate(state.currentAssignment)
                let newStart = max(0, int(newOrigin))
                let newEnd = min(tMax, int(newOrigin) + duration)
                if newStart >= tMax:
                    result[i] = int(baseOveruse - currentCost)
                else:
                    let addedCost = state.prefixDeltaBuf[newEnd] - state.prefixDeltaBuf[newStart]
                    result[i] = int(baseOveruse + addedCost - currentCost)
            state.currentAssignment[position] = currentValue
            return
        else:
            # Multiple tasks affected — batch via mutate/restore
            let limit = int(state.limit)
            let tMax = state.maxTime + 1

            # Pre-evaluate current origins and remove all affected tasks from profile
            type TaskInfo = tuple[taskIdx: int, duration, height: int, oldStart, oldEnd: int]
            var tasks: seq[TaskInfo]
            for taskIdx in taskIndices:
                let oldOrigin = state.originExpressions[taskIdx].evaluate(state.currentAssignment)
                let duration = int(state.getDuration(taskIdx))
                let height = int(state.getHeight(taskIdx))
                let oldStart = max(0, int(oldOrigin))
                let oldEnd = min(tMax, int(oldOrigin) + duration)
                tasks.add((taskIdx: taskIdx, duration: duration, height: height,
                           oldStart: oldStart, oldEnd: oldEnd))
                # Remove this task from profile
                for t in oldStart..<oldEnd:
                    state.resourceProfile[t] -= T(height)

            # Compute base cost (profile without affected tasks)
            var baseCost = 0
            for t in 0..<tMax:
                let usage = int(state.resourceProfile[t])
                if usage > limit:
                    baseCost += usage - limit

            # For each candidate: add tasks to base profile, compute cost delta, remove.
            let currentCost = state.cost
            var newRanges = newSeq[(int, int)](tasks.len)

            for i, v in domain:
                if v == currentValue:
                    continue
                state.currentAssignment[position] = v

                # Evaluate all new origins and add to profile
                var minStart = tMax
                var maxEnd = 0
                for ti in 0..<tasks.len:
                    let task = tasks[ti]
                    let newOrigin = state.originExpressions[task.taskIdx].evaluate(state.currentAssignment)
                    let ns = max(0, int(newOrigin))
                    let ne = min(tMax, int(newOrigin) + task.duration)
                    newRanges[ti] = (ns, ne)
                    if ns < minStart: minStart = ns
                    if ne > maxEnd: maxEnd = ne
                    for t in ns..<ne:
                        state.resourceProfile[t] += T(task.height)

                # Compute cost delta at touched time points
                var costDelta = 0
                for t in minStart..<maxEnd:
                    var added = 0
                    for ti in 0..<tasks.len:
                        let (ns, ne) = newRanges[ti]
                        if t >= ns and t < ne:
                            added += tasks[ti].height
                    if added > 0:
                        let withTasks = int(state.resourceProfile[t])
                        let baseVal = withTasks - added
                        costDelta += max(0, withTasks - limit) - max(0, baseVal - limit)

                result[i] = costDelta + baseCost - currentCost

                # Remove tasks from profile
                for ti in 0..<tasks.len:
                    let (ns, ne) = newRanges[ti]
                    for t in ns..<ne:
                        state.resourceProfile[t] -= T(tasks[ti].height)

            # Restore original profile (add tasks back with original origins)
            state.currentAssignment[position] = currentValue
            for task in tasks:
                for t in task.oldStart..<task.oldEnd:
                    state.resourceProfile[t] += T(task.height)
            return

    if position >= state.positionToTask.len or state.positionToTask[position] < 0:
        # Not a task origin — moveDelta is 0 for all values
        return

    let taskIdx = state.positionToTask[position]
    let duration = int(state.getDuration(taskIdx))
    let height = int(state.getHeight(taskIdx))
    let limit = int(state.limit)
    let tMax = state.maxTime + 1

    # Step 1: Compute "removed profile" overuse and delta array
    # removedProfile[t] = resourceProfile[t] - height if t is in old task range, else resourceProfile[t]
    # delta[t] = max(0, removedProfile[t] + height - limit) - max(0, removedProfile[t] - limit)
    #   = extra overuse at t when our task is placed there
    let oldStart = max(0, int(currentValue))
    let oldEnd = min(tMax, int(currentValue) + duration)

    # Build prefix sum of delta values
    state.prefixDeltaBuf[0] = 0
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
        state.prefixDeltaBuf[t + 1] = state.prefixDeltaBuf[t] + int64(overuseWith - overuseWithout)

    # Step 2: For each candidate, compute total penalty in O(1)
    let currentCost = int64(state.cost)
    for i, v in domain:
        let newStart = max(0, int(v))
        let newEnd = min(tMax, int(v) + duration)
        if newStart >= tMax:
            # Task entirely outside profile — penalty is just base overuse
            result[i] = int(baseOveruse - currentCost)
        else:
            let addedCost = state.prefixDeltaBuf[newEnd] - state.prefixDeltaBuf[newStart]
            result[i] = int(baseOveruse + addedCost - currentCost)
