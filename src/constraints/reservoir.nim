## Reservoir constraint: at each event point (task start time), the cumulative
## consumption of all tasks starting at or before that point must be within
## [-maxDiff, maxDiff].
##
## Semantics: for each task i in sorted start-time order:
##   prefixSum[i] = sum(consumption[j] for j where start[j] <= start[i])
##   violation[i] = max(0, abs(prefixSum[i]) - maxDiff)
##   cost = sum(violation[i])
##
## This is a general-purpose constraint for producer/consumer resource
## balance problems (mass balance, energy balance, etc.).

import std/[packedsets, tables, algorithm]

type
    ReservoirConstraint*[T] = ref object
        taskPositions*: seq[int]    # position indices for start-time variables
        consumptions*: seq[int]     # consumption value per task (can be negative)
        maxDiff*: int               # symmetric bound: |cumulative| <= maxDiff
        nTasks*: int
        currentValues*: seq[T]      # cached start times indexed by task
        posToTask*: Table[int, int] # position → task index
        cost*: int
        lastChangedPosition*: int
        lastOldValue*: T

func computeCostFromValues[T](c: ReservoirConstraint[T], values: seq[T]): int =
    ## Compute total penalty from given start time values.
    # Sort tasks by start time (stable sort for determinism with ties)
    var order = newSeq[int](c.nTasks)
    for i in 0..<c.nTasks: order[i] = i
    order.sort(proc(a, b: int): int =
        cmp(int(values[a]), int(values[b])))

    result = 0
    var prefix = 0
    for idx in order:
        prefix += c.consumptions[idx]
        if prefix > c.maxDiff:
            result += prefix - c.maxDiff
        elif prefix < -c.maxDiff:
            result += -c.maxDiff - prefix

func newReservoirConstraint*[T](
    taskPositions: seq[int], consumptions: seq[int], maxDiff: int
): ReservoirConstraint[T] =
    new(result)
    result.taskPositions = taskPositions
    result.consumptions = consumptions
    result.maxDiff = maxDiff
    result.nTasks = taskPositions.len
    result.currentValues = newSeq[T](result.nTasks)
    result.posToTask = initTable[int, int]()
    for i in 0..<result.nTasks:
        result.posToTask[taskPositions[i]] = i
    result.cost = 0
    result.lastChangedPosition = -1
    result.lastOldValue = T(0)

func initialize*[T](c: ReservoirConstraint[T], assignment: seq[T]) =
    for i in 0..<c.nTasks:
        c.currentValues[i] = assignment[c.taskPositions[i]]
    c.cost = c.computeCostFromValues(c.currentValues)

func moveDelta*[T](c: ReservoirConstraint[T],
                    position: int, oldValue, newValue: T): int {.inline.} =
    if oldValue == newValue: return 0
    if position notin c.posToTask: return 0

    let taskIdx = c.posToTask[position]
    # Build modified values and compute new cost
    var tmpValues = c.currentValues
    tmpValues[taskIdx] = newValue
    let newCost = c.computeCostFromValues(tmpValues)
    return newCost - c.cost

func updatePosition*[T](c: ReservoirConstraint[T],
                          position: int, newValue: T) {.inline.} =
    if position notin c.posToTask: return
    let taskIdx = c.posToTask[position]
    c.lastChangedPosition = position
    c.lastOldValue = c.currentValues[taskIdx]
    c.currentValues[taskIdx] = newValue
    c.cost = c.computeCostFromValues(c.currentValues)

func getAffectedPositions*[T](c: ReservoirConstraint[T]): PackedSet[int] =
    # All task positions may need penalty recalculation
    result = initPackedSet[int]()
    for pos in c.taskPositions:
        result.incl(pos)

func getAffectedDomainValues*[T](c: ReservoirConstraint[T], position: int): seq[T] =
    return @[]  # all values potentially affected

proc batchMovePenalty*[T](c: ReservoirConstraint[T],
                          position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    result = newSeq[int](domain.len)
    if position notin c.posToTask: return

    let taskIdx = c.posToTask[position]
    let currentCost = c.cost

    # Sort other tasks by start time (excluding the moving task)
    type OtherTask = tuple[startTime: int, consumption: int]
    var others = newSeq[OtherTask](c.nTasks - 1)
    var oi = 0
    for i in 0..<c.nTasks:
        if i == taskIdx: continue
        others[oi] = (startTime: int(c.currentValues[i]),
                      consumption: c.consumptions[i])
        inc oi
    others.sort(proc(a, b: OtherTask): int = cmp(a.startTime, b.startTime))

    # Compute prefix sums of other tasks' consumption
    var otherPrefix = newSeq[int](others.len + 1)
    for i in 0..<others.len:
        otherPrefix[i + 1] = otherPrefix[i] + others[i].consumption

    let myConsumption = c.consumptions[taskIdx]

    for di in 0..<domain.len:
        let newStart = int(domain[di])
        # Find insertion point: task goes after all others with startTime <= newStart
        var insertIdx = others.len
        for i in 0..<others.len:
            if others[i].startTime > newStart:
                insertIdx = i
                break

        # Compute cost with task inserted at insertIdx
        var newCost = 0
        var prefix = 0
        for i in 0..<others.len:
            if i == insertIdx:
                # Insert our task here
                prefix += myConsumption
                let absP = if prefix >= 0: prefix else: -prefix
                if absP > c.maxDiff:
                    newCost += absP - c.maxDiff
            prefix += others[i].consumption
            let absP = if prefix >= 0: prefix else: -prefix
            if absP > c.maxDiff:
                newCost += absP - c.maxDiff
        if insertIdx == others.len:
            # Our task goes last
            prefix += myConsumption
            let absP = if prefix >= 0: prefix else: -prefix
            if absP > c.maxDiff:
                newCost += absP - c.maxDiff

        result[di] = newCost - currentCost

proc deepCopy*[T](c: ReservoirConstraint[T]): ReservoirConstraint[T] =
    new(result)
    result.taskPositions = c.taskPositions     # immutable, share
    result.consumptions = c.consumptions       # immutable, share
    result.maxDiff = c.maxDiff
    result.nTasks = c.nTasks
    result.currentValues = newSeq[T](c.nTasks) # fresh, will be initialized
    result.posToTask = c.posToTask             # immutable, share
    result.cost = 0
    result.lastChangedPosition = -1
    result.lastOldValue = T(0)
