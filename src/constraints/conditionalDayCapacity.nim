# Conditional Day Capacity Constraint
#
# A weighted sum-per-day constraint where each task contributes its weight to
# a specific day's load, conditioned on boolean/equality predicates.
#
# For each day d: sum(weight[i] * active(i)) <= capacity[d]
#   where active(i) = all conditions for task i are met
#
# Task i is active when:
#   - selection condition: assignment[selectionPos] == selectionVal
#   - admission: assignment[admissionPos] == d (determines which day)
#   - optional extra condition: assignment[extraCondPos] == extraCondVal (e.g., OT==o)
#
# Used for surgeon/OT capacity constraints (H3/H4 in IHTC).
#
# Performance: O(1) moveDelta for any position change.

import std/[packedsets]

type
  DayCapacityTask* = object
    weight*: int              # surgery duration (coefficient)
    admissionPos*: int        # position of admission variable
    selectionPos*: int        # position of selection variable (-1 if always selected)
    selectionVal*: int        # required value for selection (typically 1 = true)
    extraCondPos*: int        # position of extra condition (-1 if none)
    extraCondVal*: int        # required value for extra condition (e.g., OT number)

  ConditionalDayCapacityConstraint*[T] = ref object
    tasks*: seq[DayCapacityTask]
    capacities*: seq[int]     # capacity[d] for each day d (0..maxDay)
    maxDay*: int
    # Runtime state
    load*: seq[int]           # load[d] = total weight on day d
    cost*: int
    activeFlags*: seq[bool]   # per task: currently active?
    currentAssignment*: seq[T]
    # Position tracking
    lastChangedPosition*: int
    lastOldValue*: T
    admissionPosToTasks*: seq[seq[int]]  # admissionPos -> [task indices] (sparse via table)
    selectionPosToTasks*: seq[seq[int]]  # selectionPos -> [task indices]
    extraCondPosToTasks*: seq[seq[int]]  # extraCondPos -> [task indices]
    maxPos*: int


func isActive[T](task: DayCapacityTask, assignment: seq[T]): bool {.inline.} =
  if task.selectionPos >= 0:
    if assignment[task.selectionPos] != T(task.selectionVal):
      return false
  if task.extraCondPos >= 0:
    if assignment[task.extraCondPos] != T(task.extraCondVal):
      return false
  return true


func newConditionalDayCapacityConstraint*[T](
    tasks: seq[DayCapacityTask],
    capacities: seq[int],
    maxDay: int): ConditionalDayCapacityConstraint[T] =

  var maxPos = 0
  for task in tasks:
    if task.admissionPos > maxPos: maxPos = task.admissionPos
    if task.selectionPos > maxPos: maxPos = task.selectionPos
    if task.extraCondPos > maxPos: maxPos = task.extraCondPos

  # Build position -> task index maps (using seq of seq, indexed by position)
  var admMap = newSeq[seq[int]](maxPos + 1)
  var selMap = newSeq[seq[int]](maxPos + 1)
  var extMap = newSeq[seq[int]](maxPos + 1)

  for i, task in tasks:
    admMap[task.admissionPos].add(i)
    if task.selectionPos >= 0:
      selMap[task.selectionPos].add(i)
    if task.extraCondPos >= 0:
      extMap[task.extraCondPos].add(i)

  new(result)
  result.tasks = tasks
  result.capacities = capacities
  result.maxDay = maxDay
  result.maxPos = maxPos
  result.cost = 0
  result.load = newSeq[int](maxDay + 1)
  result.activeFlags = newSeq[bool](tasks.len)
  result.currentAssignment = newSeq[T](maxPos + 1)
  result.lastChangedPosition = -1
  result.admissionPosToTasks = admMap
  result.selectionPosToTasks = selMap
  result.extraCondPosToTasks = extMap


func computeCost(load: seq[int], capacities: seq[int], maxDay: int): int =
  for d in 0..maxDay:
    let excess = load[d] - capacities[d]
    if excess > 0:
      result += excess


proc initialize*[T](c: ConditionalDayCapacityConstraint[T], assignment: seq[T]) =
  # Copy relevant assignment values
  for i in 0..<min(assignment.len, c.currentAssignment.len):
    c.currentAssignment[i] = assignment[i]

  # Reset load
  for d in 0..c.maxDay:
    c.load[d] = 0

  # Add active tasks
  for i, task in c.tasks:
    c.activeFlags[i] = task.isActive(assignment)
    if c.activeFlags[i]:
      let day = int(assignment[task.admissionPos])
      if day >= 0 and day <= c.maxDay:
        c.load[day] += task.weight

  c.cost = computeCost(c.load, c.capacities, c.maxDay)


proc updatePosition*[T](c: ConditionalDayCapacityConstraint[T], position: int, newValue: T) =
  if position > c.maxPos: return

  c.lastChangedPosition = position
  c.lastOldValue = c.currentAssignment[position]
  c.currentAssignment[position] = newValue

  let oldValue = c.lastOldValue

  # Case 1: admission position changed — shift load between days
  if position < c.admissionPosToTasks.len:
    for taskIdx in c.admissionPosToTasks[position]:
      if c.activeFlags[taskIdx]:
        let oldDay = int(oldValue)
        let newDay = int(newValue)
        if oldDay != newDay:
          if oldDay >= 0 and oldDay <= c.maxDay:
            c.load[oldDay] -= c.tasks[taskIdx].weight
          if newDay >= 0 and newDay <= c.maxDay:
            c.load[newDay] += c.tasks[taskIdx].weight

  # Case 2: selection position changed — activate/deactivate tasks
  if position < c.selectionPosToTasks.len:
    for taskIdx in c.selectionPosToTasks[position]:
      let wasActive = c.activeFlags[taskIdx]
      let isNowActive = c.tasks[taskIdx].isActive(c.currentAssignment)
      if wasActive != isNowActive:
        c.activeFlags[taskIdx] = isNowActive
        let day = int(c.currentAssignment[c.tasks[taskIdx].admissionPos])
        if day >= 0 and day <= c.maxDay:
          if isNowActive:
            c.load[day] += c.tasks[taskIdx].weight
          else:
            c.load[day] -= c.tasks[taskIdx].weight

  # Case 3: extra condition position changed — activate/deactivate tasks
  if position < c.extraCondPosToTasks.len:
    for taskIdx in c.extraCondPosToTasks[position]:
      let wasActive = c.activeFlags[taskIdx]
      let isNowActive = c.tasks[taskIdx].isActive(c.currentAssignment)
      if wasActive != isNowActive:
        c.activeFlags[taskIdx] = isNowActive
        let day = int(c.currentAssignment[c.tasks[taskIdx].admissionPos])
        if day >= 0 and day <= c.maxDay:
          if isNowActive:
            c.load[day] += c.tasks[taskIdx].weight
          else:
            c.load[day] -= c.tasks[taskIdx].weight

  c.cost = computeCost(c.load, c.capacities, c.maxDay)


proc moveDelta*[T](c: ConditionalDayCapacityConstraint[T], position: int, oldValue, newValue: T): int =
  if oldValue == newValue: return 0
  if position > c.maxPos: return 0

  let oldCost = c.cost
  var newCost = oldCost

  # Case 1: admission position changed
  if position < c.admissionPosToTasks.len:
    for taskIdx in c.admissionPosToTasks[position]:
      if not c.activeFlags[taskIdx]: continue
      let w = c.tasks[taskIdx].weight
      let oldDay = int(oldValue)
      let newDay = int(newValue)
      if oldDay == newDay: continue

      # Remove from old day
      if oldDay >= 0 and oldDay <= c.maxDay:
        let oldExcess = max(c.load[oldDay] - c.capacities[oldDay], 0)
        let newExcess = max(c.load[oldDay] - w - c.capacities[oldDay], 0)
        newCost += newExcess - oldExcess

      # Add to new day
      if newDay >= 0 and newDay <= c.maxDay:
        let oldExcess = max(c.load[newDay] - c.capacities[newDay], 0)
        let newExcess = max(c.load[newDay] + w - c.capacities[newDay], 0)
        newCost += newExcess - oldExcess

  # Case 2: selection or extra condition changed — tasks may activate/deactivate
  template handleConditionChange(posToTasks: seq[seq[int]]) =
    if position < posToTasks.len:
      for taskIdx in posToTasks[position]:
        let task = c.tasks[taskIdx]
        let wasActive = c.activeFlags[taskIdx]

        # Check new activation with hypothetical change
        var isNowActive = true
        if task.selectionPos >= 0:
          let val = if task.selectionPos == position: newValue else: c.currentAssignment[task.selectionPos]
          if val != T(task.selectionVal):
            isNowActive = false
        if isNowActive and task.extraCondPos >= 0:
          let val = if task.extraCondPos == position: newValue else: c.currentAssignment[task.extraCondPos]
          if val != T(task.extraCondVal):
            isNowActive = false

        if wasActive == isNowActive: continue

        let day = int(c.currentAssignment[task.admissionPos])
        if day < 0 or day > c.maxDay: continue
        let w = task.weight

        if wasActive and not isNowActive:
          # Deactivate: remove weight
          let oldExcess = max(c.load[day] - c.capacities[day], 0)
          let newExcess = max(c.load[day] - w - c.capacities[day], 0)
          newCost += newExcess - oldExcess
        elif not wasActive and isNowActive:
          # Activate: add weight
          let oldExcess = max(c.load[day] - c.capacities[day], 0)
          let newExcess = max(c.load[day] + w - c.capacities[day], 0)
          newCost += newExcess - oldExcess

  handleConditionChange(c.selectionPosToTasks)
  handleConditionChange(c.extraCondPosToTasks)

  return newCost - oldCost


proc batchMovePenalty*[T](c: ConditionalDayCapacityConstraint[T], position: int, oldValue: T, domain: seq[T]): seq[int] =
  ## Compute moveDelta for all values in domain at once.
  result = newSeq[int](domain.len)
  if position > c.maxPos: return

  # Case 1: admission position — tasks move between days
  if position < c.admissionPosToTasks.len and c.admissionPosToTasks[position].len > 0:
    # Collect total weight of active tasks at this position
    var totalWeight = 0
    for taskIdx in c.admissionPosToTasks[position]:
      if c.activeFlags[taskIdx]:
        totalWeight += c.tasks[taskIdx].weight
    if totalWeight > 0:
      let oldDay = int(oldValue)
      # Pre-compute removal from old day
      var removalDelta = 0
      if oldDay >= 0 and oldDay <= c.maxDay:
        let oldExcess = max(c.load[oldDay] - c.capacities[oldDay], 0)
        let newExcess = max(c.load[oldDay] - totalWeight - c.capacities[oldDay], 0)
        removalDelta = newExcess - oldExcess

      for i, v in domain:
        let newDay = int(v)
        if newDay == oldDay:
          result[i] = 0
          continue
        var delta = removalDelta
        # Add to new day
        if newDay >= 0 and newDay <= c.maxDay:
          let oldExcess = max(c.load[newDay] - c.capacities[newDay], 0)
          let newExcess = max(c.load[newDay] + totalWeight - c.capacities[newDay], 0)
          delta += newExcess - oldExcess
        result[i] = delta

  # Case 2: selection or extra condition — tasks activate/deactivate
  template handleBatchCondition(posToTasks: seq[seq[int]]) =
    if position < posToTasks.len:
      for taskIdx in posToTasks[position]:
        let task = c.tasks[taskIdx]
        let wasActive = c.activeFlags[taskIdx]
        let day = int(c.currentAssignment[task.admissionPos])
        if day < 0 or day > c.maxDay: continue
        let w = task.weight

        for i, v in domain:
          if v == oldValue:
            result[i] += 0
            continue
          # Check activation with hypothetical value
          var isNowActive = true
          if task.selectionPos >= 0:
            let sv = if task.selectionPos == position: v else: c.currentAssignment[task.selectionPos]
            if sv != T(task.selectionVal):
              isNowActive = false
          if isNowActive and task.extraCondPos >= 0:
            let ev = if task.extraCondPos == position: v else: c.currentAssignment[task.extraCondPos]
            if ev != T(task.extraCondVal):
              isNowActive = false

          if wasActive == isNowActive: continue
          if wasActive and not isNowActive:
            let oldExcess = max(c.load[day] - c.capacities[day], 0)
            let newExcess = max(c.load[day] - w - c.capacities[day], 0)
            result[i] += newExcess - oldExcess
          elif not wasActive and isNowActive:
            let oldExcess = max(c.load[day] - c.capacities[day], 0)
            let newExcess = max(c.load[day] + w - c.capacities[day], 0)
            result[i] += newExcess - oldExcess

  handleBatchCondition(c.selectionPosToTasks)
  handleBatchCondition(c.extraCondPosToTasks)


proc getAffectedPositions*[T](c: ConditionalDayCapacityConstraint[T]): PackedSet[int] =
  let pos = c.lastChangedPosition
  if pos < 0:
    # Initial: return all positions
    result = initPackedSet[int]()
    for task in c.tasks:
      result.incl(task.admissionPos)
      if task.selectionPos >= 0:
        result.incl(task.selectionPos)
      if task.extraCondPos >= 0:
        result.incl(task.extraCondPos)
    return result

  # Determine which days were affected
  var affectedDays: PackedSet[int]

  if pos < c.admissionPosToTasks.len:
    for taskIdx in c.admissionPosToTasks[pos]:
      if c.activeFlags[taskIdx]:
        let oldDay = int(c.lastOldValue)
        let newDay = int(c.currentAssignment[pos])
        if oldDay >= 0 and oldDay <= c.maxDay: affectedDays.incl(oldDay)
        if newDay >= 0 and newDay <= c.maxDay: affectedDays.incl(newDay)

  if pos < c.selectionPosToTasks.len:
    for taskIdx in c.selectionPosToTasks[pos]:
      let day = int(c.currentAssignment[c.tasks[taskIdx].admissionPos])
      if day >= 0 and day <= c.maxDay: affectedDays.incl(day)

  if pos < c.extraCondPosToTasks.len:
    for taskIdx in c.extraCondPosToTasks[pos]:
      let day = int(c.currentAssignment[c.tasks[taskIdx].admissionPos])
      if day >= 0 and day <= c.maxDay: affectedDays.incl(day)

  if affectedDays.len == 0:
    return initPackedSet[int]()

  # Return positions of all tasks on affected days
  result = initPackedSet[int]()
  for i, task in c.tasks:
    if not c.activeFlags[i]: continue
    let day = int(c.currentAssignment[task.admissionPos])
    if day >= 0 and day <= c.maxDay and day in affectedDays:
      result.incl(task.admissionPos)
      if task.selectionPos >= 0:
        result.incl(task.selectionPos)
      if task.extraCondPos >= 0:
        result.incl(task.extraCondPos)


proc deepCopy*[T](c: ConditionalDayCapacityConstraint[T]): ConditionalDayCapacityConstraint[T] =
  new(result)
  result.tasks = c.tasks
  result.capacities = c.capacities
  result.maxDay = c.maxDay
  result.maxPos = c.maxPos
  result.cost = 0
  result.load = newSeq[int](c.maxDay + 1)
  result.activeFlags = newSeq[bool](c.tasks.len)
  result.currentAssignment = newSeq[T](c.currentAssignment.len)
  result.lastChangedPosition = -1
  result.admissionPosToTasks = c.admissionPosToTasks
  result.selectionPosToTasks = c.selectionPosToTasks
  result.extraCondPosToTasks = c.extraCondPosToTasks
