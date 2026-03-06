# Conditional Cumulative Constraint
#
# A cumulative constraint where each task is conditionally active based on variable values.
# Task i is active only when ALL conditions are met (e.g., room[p] == r AND selection[p] == 1).
# When active, the task contributes height to the resource profile at [start, start+duration).
#
# Used for room capacity constraints where a patient only occupies a room
# when assigned to that room and selected.
#
# Performance: O(duration) for initialize/updatePosition, O(min(|shift|, duration)) for moveDelta.

import std/[packedsets, sequtils, tables]

type
  TaskCondition* = object
    position*: int    # position to check
    value*: int       # required value for condition to be met

  ConditionalTask* = object
    startPosition*: int          # position of start time variable (-1 if fixedStart used)
    fixedStart*: int             # fixed start time (-1 if startPosition used)
    duration*: int               # constant task duration
    height*: int                 # constant task height (resource usage)
    conditions*: seq[TaskCondition]  # ALL must match for task to be active

  FixedTask* = object
    start*: int
    duration*: int
    height*: int

  ConditionalCumulativeConstraint*[T] = ref object
    fixedTasks*: seq[FixedTask]
    tasks*: seq[ConditionalTask]
    limit*: int
    # Runtime state
    resourceProfile*: seq[T]
    cost*: int
    maxTime*: int
    activeFlags*: seq[bool]       # per-task: is currently active?
    currentAssignment*: seq[T]    # full assignment snapshot (indexed by position)
    # Position tracking
    lastChangedPosition*: int
    lastOldValue*: T
    startPosToTasks*: Table[int, seq[int]]     # start pos -> task indices
    condPosToTasks*: Table[int, seq[int]]       # condition pos -> task indices
    allCondPositions*: PackedSet[int]           # all condition positions (for quick lookup)


func getStart[T](task: ConditionalTask, assignment: seq[T]): T {.inline.} =
  if task.fixedStart >= 0: T(task.fixedStart)
  else: assignment[task.startPosition]

func isActive[T](task: ConditionalTask, assignment: seq[T]): bool {.inline.} =
  for cond in task.conditions:
    if assignment[cond.position] != T(cond.value):
      return false
  return true


func newConditionalCumulativeConstraint*[T](
    fixedTasks: seq[FixedTask],
    tasks: seq[ConditionalTask],
    limit: int,
    maxTime: int = 500): ConditionalCumulativeConstraint[T] =

  var startToTasks = initTable[int, seq[int]]()
  var condToTasks = initTable[int, seq[int]]()
  var condPositions: PackedSet[int]
  var maxPos = 0

  for i, task in tasks:
    if task.fixedStart < 0:  # only track variable-start tasks
      startToTasks.mgetOrPut(task.startPosition, @[]).add(i)
      if task.startPosition > maxPos: maxPos = task.startPosition
    for cond in task.conditions:
      condToTasks.mgetOrPut(cond.position, @[]).add(i)
      condPositions.incl(cond.position)
      if cond.position > maxPos: maxPos = cond.position

  new(result)
  result.fixedTasks = fixedTasks
  result.tasks = tasks
  result.limit = limit
  result.maxTime = maxTime
  result.cost = 0
  result.resourceProfile = newSeq[T](maxTime + 1)
  result.activeFlags = newSeq[bool](tasks.len)
  result.currentAssignment = newSeq[T](maxPos + 1)
  result.lastChangedPosition = -1
  result.startPosToTasks = startToTasks
  result.condPosToTasks = condToTasks
  result.allCondPositions = condPositions


func computeCost[T](profile: seq[T], limit: T, maxTime: int): int =
  for t in 0..maxTime:
    let excess = profile[t] - limit
    if excess > 0:
      result += excess


proc addTaskToProfile[T](c: ConditionalCumulativeConstraint[T], taskIdx: int) =
  let task = c.tasks[taskIdx]
  let start = task.getStart(c.currentAssignment)
  let endT = start + T(task.duration)
  let hi = min(int(endT) - 1, c.maxTime)
  for t in max(int(start), 0)..hi:
    c.resourceProfile[t] += T(task.height)

proc removeTaskFromProfile[T](c: ConditionalCumulativeConstraint[T], taskIdx: int) =
  let task = c.tasks[taskIdx]
  let start = task.getStart(c.currentAssignment)
  let endT = start + T(task.duration)
  let hi = min(int(endT) - 1, c.maxTime)
  for t in max(int(start), 0)..hi:
    c.resourceProfile[t] -= T(task.height)


proc initialize*[T](c: ConditionalCumulativeConstraint[T], assignment: seq[T]) =
  # Copy assignment for positions we care about
  for i in 0..<min(assignment.len, c.currentAssignment.len):
    c.currentAssignment[i] = assignment[i]

  # Reset profile
  for t in 0..c.maxTime:
    c.resourceProfile[t] = T(0)

  # Add fixed tasks
  for ft in c.fixedTasks:
    let endT = ft.start + ft.duration
    for t in max(ft.start, 0)..min(endT - 1, c.maxTime):
      c.resourceProfile[t] += T(ft.height)

  # Add active conditional tasks
  for i, task in c.tasks:
    c.activeFlags[i] = task.isActive(assignment)
    if c.activeFlags[i]:
      c.addTaskToProfile(i)

  c.cost = computeCost(c.resourceProfile, T(c.limit), c.maxTime)


proc updatePosition*[T](c: ConditionalCumulativeConstraint[T], position: int, newValue: T) =
  c.lastChangedPosition = position
  c.lastOldValue = c.currentAssignment[position]
  c.currentAssignment[position] = newValue

  # Check if this position is a condition for any tasks
  if position in c.condPosToTasks:
    for taskIdx in c.condPosToTasks[position]:
      let wasActive = c.activeFlags[taskIdx]
      let isNowActive = c.tasks[taskIdx].isActive(c.currentAssignment)
      if wasActive and not isNowActive:
        c.removeTaskFromProfile(taskIdx)
        c.activeFlags[taskIdx] = false
      elif not wasActive and isNowActive:
        c.activeFlags[taskIdx] = true
        c.addTaskToProfile(taskIdx)

  # Check if this position is a start time for any active tasks
  if position in c.startPosToTasks:
    for taskIdx in c.startPosToTasks[position]:
      if c.activeFlags[taskIdx]:
        let task = c.tasks[taskIdx]
        let oldStart = int(c.lastOldValue)
        let newStart = int(newValue)
        if oldStart != newStart:
          # Remove from old position
          let oldEnd = oldStart + task.duration
          for t in max(oldStart, 0)..min(oldEnd - 1, c.maxTime):
            c.resourceProfile[t] -= T(task.height)
          # Add at new position
          let newEnd = newStart + task.duration
          for t in max(newStart, 0)..min(newEnd - 1, c.maxTime):
            c.resourceProfile[t] += T(task.height)

  c.cost = computeCost(c.resourceProfile, T(c.limit), c.maxTime)


proc moveDelta*[T](c: ConditionalCumulativeConstraint[T], position: int, oldValue, newValue: T): int =
  if oldValue == newValue: return 0

  let oldCost = c.cost
  var newCost = oldCost

  # Case 1: position is a condition — tasks may activate/deactivate
  if position in c.condPosToTasks:
    for taskIdx in c.condPosToTasks[position]:
      let task = c.tasks[taskIdx]
      let wasActive = c.activeFlags[taskIdx]

      # Check new activation with the hypothetical change
      var isNowActive = true
      for cond in task.conditions:
        let val = if cond.position == position: newValue else: c.currentAssignment[cond.position]
        if val != T(cond.value):
          isNowActive = false
          break

      if wasActive == isNowActive: continue  # no change

      let start = int(task.getStart(c.currentAssignment))
      let endT = start + task.duration
      let h = task.height

      if wasActive and not isNowActive:
        # Task deactivates: remove its contribution
        for t in max(start, 0)..min(endT - 1, c.maxTime):
          let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
          let newExcess = max(int(c.resourceProfile[t]) - h - c.limit, 0)
          newCost += newExcess - oldExcess
      elif not wasActive and isNowActive:
        # Task activates: add its contribution
        for t in max(start, 0)..min(endT - 1, c.maxTime):
          let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
          let newExcess = max(int(c.resourceProfile[t]) + h - c.limit, 0)
          newCost += newExcess - oldExcess

  # Case 2: position is a start time — shift active tasks
  # (not mutually exclusive with Case 1: a position could be both)
  if position in c.startPosToTasks:
    for taskIdx in c.startPosToTasks[position]:
      if not c.activeFlags[taskIdx]: continue
      let task = c.tasks[taskIdx]
      let oldStart = int(oldValue)
      let newStart = int(newValue)
      if oldStart == newStart: continue

      let oldEnd = oldStart + task.duration
      let newEnd = newStart + task.duration
      let h = T(task.height)

      # Use symmetric difference: only examine time points that change
      # Remove from old-only range, add to new-only range
      if newStart >= oldEnd or oldStart >= newEnd:
        # No overlap between old and new ranges
        for t in max(oldStart, 0)..min(oldEnd - 1, c.maxTime):
          let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
          let newExcess = max(int(c.resourceProfile[t]) - int(h) - c.limit, 0)
          newCost += newExcess - oldExcess
        for t in max(newStart, 0)..min(newEnd - 1, c.maxTime):
          let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
          let newExcess = max(int(c.resourceProfile[t]) + int(h) - c.limit, 0)
          newCost += newExcess - oldExcess
      else:
        # Overlapping ranges: only process the symmetric difference
        let overlapStart = max(oldStart, newStart)
        let overlapEnd = min(oldEnd, newEnd)
        # Points in old range but not new
        if oldStart < overlapStart:
          for t in max(oldStart, 0)..min(overlapStart - 1, c.maxTime):
            let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
            let newExcess = max(int(c.resourceProfile[t]) - int(h) - c.limit, 0)
            newCost += newExcess - oldExcess
        if oldEnd > overlapEnd:
          for t in max(overlapEnd, 0)..min(oldEnd - 1, c.maxTime):
            let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
            let newExcess = max(int(c.resourceProfile[t]) - int(h) - c.limit, 0)
            newCost += newExcess - oldExcess
        # Points in new range but not old
        if newStart < overlapStart:
          for t in max(newStart, 0)..min(overlapStart - 1, c.maxTime):
            let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
            let newExcess = max(int(c.resourceProfile[t]) + int(h) - c.limit, 0)
            newCost += newExcess - oldExcess
        if newEnd > overlapEnd:
          for t in max(overlapEnd, 0)..min(newEnd - 1, c.maxTime):
            let oldExcess = max(int(c.resourceProfile[t]) - c.limit, 0)
            let newExcess = max(int(c.resourceProfile[t]) + int(h) - c.limit, 0)
            newCost += newExcess - oldExcess

  return newCost - oldCost


proc getAffectedPositions*[T](c: ConditionalCumulativeConstraint[T]): PackedSet[int] =
  # When a condition position changes, all start positions of affected tasks need updates
  # When a start position changes, other start positions overlapping the changed range need updates
  let pos = c.lastChangedPosition
  if pos < 0:
    # Return all positions
    result = initPackedSet[int]()
    for i, task in c.tasks:
      if task.fixedStart < 0:
        result.incl(task.startPosition)
      for cond in task.conditions:
        result.incl(cond.position)
    return result

  if pos in c.allCondPositions:
    # Condition change: return start positions of tasks whose activation changed
    result = initPackedSet[int]()
    for taskIdx in c.condPosToTasks.getOrDefault(pos, @[]):
      let task = c.tasks[taskIdx]
      if task.fixedStart < 0:
        result.incl(task.startPosition)
      for cond in task.conditions:
        result.incl(cond.position)
    return result

  if pos in c.startPosToTasks:
    # Start position change: return positions of tasks overlapping changed time range
    result = initPackedSet[int]()
    let oldStart = int(c.lastOldValue)
    let newStart = int(c.currentAssignment[pos])
    var rangeStart = min(oldStart, newStart)
    var rangeEnd = max(oldStart, newStart)
    # Extend by max duration to catch overlapping tasks
    for taskIdx in c.startPosToTasks[pos]:
      rangeEnd = max(rangeEnd, max(oldStart, newStart) + c.tasks[taskIdx].duration)
    for i, task in c.tasks:
      if not c.activeFlags[i]: continue
      let tStart = int(task.getStart(c.currentAssignment))
      let tEnd = tStart + task.duration
      if tStart < rangeEnd and tEnd > rangeStart:
        if task.fixedStart < 0:
          result.incl(task.startPosition)
    return result

  return initPackedSet[int]()


func getAffectedDomainValues*[T](c: ConditionalCumulativeConstraint[T], position: int): seq[T] =
  # For condition positions: all values matter
  if position in c.allCondPositions:
    return @[]
  # For start positions: return values overlapping with changed time range
  return @[]  # safe default: recalculate all


proc deepCopy*[T](c: ConditionalCumulativeConstraint[T]): ConditionalCumulativeConstraint[T] =
  new(result)
  result.fixedTasks = c.fixedTasks
  result.tasks = c.tasks
  result.limit = c.limit
  result.maxTime = c.maxTime
  result.cost = 0
  result.resourceProfile = newSeq[T](c.maxTime + 1)
  result.activeFlags = newSeq[bool](c.tasks.len)
  result.currentAssignment = newSeq[T](c.currentAssignment.len)
  result.lastChangedPosition = -1
  result.startPosToTasks = c.startPosToTasks
  result.condPosToTasks = c.condPosToTasks
  result.allCondPositions = c.allCondPositions
