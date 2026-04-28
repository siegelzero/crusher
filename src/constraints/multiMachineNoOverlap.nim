# Multi-Machine No-Overlap Constraint
#
# Enforces: for each machine m, tasks assigned to m do not overlap in time.
# Semantically equivalent to a set of cumulative(limit=1) constraints with
# bool2int(int_eq_reif(machine[t], m)) heights, but consolidated into a
# single constraint that avoids the explosion of channel bindings.
#
# Penalty (no setup): sum over all machines of integral of max(0, overlap_count(t) - 1).
# Same semantics as cumulative(limit=1).
#
# Optional setup matrix: when `setupMatrix` is non-empty, the constraint instead
# enforces sequence-dependent setup: for any two tasks i, j on the same machine
# with start[i] < start[j], require  start[i] + dur[i] + setup[i][j] <= start[j].
# Penalty for a machine = sum over consecutive (i, j) on the machine of
#   max(0, end[i] + setup[i][j] - start[j])
# where consecutive is by sorted start time (with task index as tie-breaker).
#
# Performance:
#   - No setup: O(k log k) moveDelta, O(maxTime) batch via prefix sums.
#   - With setup: O(k log k) moveDelta (sort + linear scan); batch falls back
#     to per-value evaluation.

import std/[packedsets, algorithm, tables]

type
  MultiMachineNoOverlapConstraint*[T] = ref object
    taskCount*: int
    startPositions*: seq[int]     # position of start time for each task
    machinePositions*: seq[int]   # position of machine assignment for each task (-1 if fixed)
    fixedMachines*: seq[int]      # fixed machine value for tasks with machinePositions=-1
    durations*: seq[int]          # constant duration for each task

    # Optional sequence-dependent setup. setupMatrix[i][j] = setup time after
    # task i finishes before task j can start on the same machine. Empty when
    # the constraint is plain no-overlap.
    setupMatrix*: seq[seq[int]]

    # Cached state
    cost*: int
    currentStarts*: seq[T]        # cached start values per task
    currentMachines*: seq[T]      # cached machine values per task
    machineCosts*: seq[int]       # per-machine penalty contribution

    lastChangedPosition*: int
    lastOldValue*: T

    # Lookups
    startPosToTask*: Table[int, int]    # start position → task index
    machinePosToTask*: Table[int, int]  # machine position → task index
    maxTime*: int                        # max possible end time
    numMachineValues*: int               # number of distinct machine values


################################################################################
# Sweep-line penalty computation
################################################################################

proc sweepPenalty(events: var seq[(int, int)]): int =
  ## Compute excess-over-1 integral from sorted events.
  if events.len <= 2: return 0
  events.sort()
  var count = 0
  var lastTime = events[0][0]
  result = 0
  for i in 0..<events.len:
    let (time, delta) = events[i]
    if count > 1 and time > lastTime:
      result += (count - 1) * (time - lastTime)
    lastTime = time
    count += delta


proc setupPenaltyForMachine[T](c: MultiMachineNoOverlapConstraint[T], machine: int,
                                excludeTask: int = -1,
                                includeTaskIdx: int = -1, includeStart: int = 0,
                                altTaskIdx: int = -1, altStart: int = 0): int =
  ## Setup-aware penalty: gather tasks on the machine, sort by start time,
  ## sum max(0, end_prev + setup[prev][curr] - start_curr) over consecutive pairs.
  ## Tie-break ties by task index for determinism.
  var tasks = newSeqOfCap[tuple[start, idx: int]](c.taskCount)
  for t in 0..<c.taskCount:
    if t == excludeTask: continue
    let m = if c.machinePositions[t] >= 0: int(c.currentMachines[t])
            else: c.fixedMachines[t]
    if m != machine: continue
    let s = if t == altTaskIdx: altStart else: int(c.currentStarts[t])
    tasks.add((start: s, idx: t))
  if includeTaskIdx >= 0:
    tasks.add((start: includeStart, idx: includeTaskIdx))
  if tasks.len < 2: return 0
  tasks.sort(proc (a, b: tuple[start, idx: int]): int =
    if a.start != b.start: return cmp(a.start, b.start)
    return cmp(a.idx, b.idx))
  result = 0
  for k in 1..<tasks.len:
    let prev = tasks[k - 1]
    let curr = tasks[k]
    let endPrev = prev.start + c.durations[prev.idx]
    let setup = c.setupMatrix[prev.idx][curr.idx]
    let required = endPrev + setup
    if required > curr.start:
      result += required - curr.start

proc computeMachinePenalty*[T](c: MultiMachineNoOverlapConstraint[T], machine: int,
                                excludeTask: int = -1,
                                includeTaskIdx: int = -1, includeStart: int = 0,
                                altTaskIdx: int = -1, altStart: int = 0): int =
  ## Compute penalty for a single machine.
  ## excludeTask: task to exclude (being removed from this machine)
  ## includeTaskIdx: extra task to include (being added to this machine)
  ## altTaskIdx: task on this machine whose start is overridden to altStart
  if c.setupMatrix.len > 0:
    return setupPenaltyForMachine(c, machine, excludeTask, includeTaskIdx,
                                   includeStart, altTaskIdx, altStart)

  var events = newSeqOfCap[(int, int)](c.taskCount)

  for t in 0..<c.taskCount:
    if t == excludeTask: continue
    let m = if c.machinePositions[t] >= 0: int(c.currentMachines[t])
            else: c.fixedMachines[t]
    if m != machine: continue
    let s = if t == altTaskIdx: altStart else: int(c.currentStarts[t])
    let e = s + c.durations[t]
    events.add((s, 1))
    events.add((e, -1))

  # Include extra task if specified
  if includeTaskIdx >= 0:
    events.add((includeStart, 1))
    events.add((includeStart + c.durations[includeTaskIdx], -1))

  return sweepPenalty(events)


proc computeTotalCost*[T](c: MultiMachineNoOverlapConstraint[T]) =
  ## Recompute total cost and per-machine costs from scratch.
  c.cost = 0
  for m in 0..<c.numMachineValues:
    c.machineCosts[m] = c.computeMachinePenalty(m)
    c.cost += c.machineCosts[m]


################################################################################
# Constructor
################################################################################

func newMultiMachineNoOverlapConstraint*[T](
    startPositions: seq[int],
    machinePositions: seq[int],
    fixedMachines: seq[int],
    durations: seq[int],
    numMachineValues: int,
    maxTime: int,
    setupMatrix: seq[seq[int]] = @[]): MultiMachineNoOverlapConstraint[T] =
  let n = startPositions.len
  doAssert machinePositions.len == n
  doAssert fixedMachines.len == n
  doAssert durations.len == n
  if setupMatrix.len > 0:
    doAssert setupMatrix.len == n
    for row in setupMatrix:
      doAssert row.len == n

  new(result)
  result.taskCount = n
  result.startPositions = startPositions
  result.machinePositions = machinePositions
  result.fixedMachines = fixedMachines
  result.durations = durations
  result.setupMatrix = setupMatrix
  result.numMachineValues = numMachineValues
  result.maxTime = maxTime
  result.cost = 0
  result.lastChangedPosition = -1

  result.currentStarts = newSeq[T](n)
  result.currentMachines = newSeq[T](n)
  result.machineCosts = newSeq[int](numMachineValues)

  result.startPosToTask = initTable[int, int]()
  result.machinePosToTask = initTable[int, int]()
  for t in 0..<n:
    result.startPosToTask[startPositions[t]] = t
    if machinePositions[t] >= 0:
      result.machinePosToTask[machinePositions[t]] = t


################################################################################
# Constraint interface
################################################################################

proc initialize*[T](c: MultiMachineNoOverlapConstraint[T], assignment: seq[T]) =
  for t in 0..<c.taskCount:
    c.currentStarts[t] = assignment[c.startPositions[t]]
    if c.machinePositions[t] >= 0:
      c.currentMachines[t] = assignment[c.machinePositions[t]]
    else:
      c.currentMachines[t] = T(c.fixedMachines[t])
  c.computeTotalCost()


proc updatePosition*[T](c: MultiMachineNoOverlapConstraint[T], position: int, newValue: T) =
  c.lastChangedPosition = position
  if position in c.startPosToTask:
    let taskIdx = c.startPosToTask[position]
    c.lastOldValue = c.currentStarts[taskIdx]
    c.currentStarts[taskIdx] = newValue
    # Recompute penalty for affected machine
    let m = if c.machinePositions[taskIdx] >= 0: int(c.currentMachines[taskIdx])
            else: c.fixedMachines[taskIdx]
    let oldMC = c.machineCosts[m]
    c.machineCosts[m] = c.computeMachinePenalty(m)
    c.cost += c.machineCosts[m] - oldMC
  elif position in c.machinePosToTask:
    let taskIdx = c.machinePosToTask[position]
    c.lastOldValue = c.currentMachines[taskIdx]
    let oldM = int(c.currentMachines[taskIdx])
    let newM = int(newValue)
    c.currentMachines[taskIdx] = newValue
    # Recompute penalties for old and new machines
    let oldCostOldM = c.machineCosts[oldM]
    c.machineCosts[oldM] = c.computeMachinePenalty(oldM)
    c.cost += c.machineCosts[oldM] - oldCostOldM
    if newM != oldM:
      let oldCostNewM = c.machineCosts[newM]
      c.machineCosts[newM] = c.computeMachinePenalty(newM)
      c.cost += c.machineCosts[newM] - oldCostNewM


func moveDelta*[T](c: MultiMachineNoOverlapConstraint[T], position: int, oldValue, newValue: T): int =
  if oldValue == newValue: return 0

  if position in c.startPosToTask:
    # Start time change — only affects one machine
    let taskIdx = c.startPosToTask[position]
    let m = if c.machinePositions[taskIdx] >= 0: int(c.currentMachines[taskIdx])
            else: c.fixedMachines[taskIdx]
    let oldCost = c.machineCosts[m]
    let newCost = c.computeMachinePenalty(m, altTaskIdx=taskIdx, altStart=int(newValue))
    return newCost - oldCost

  elif position in c.machinePosToTask:
    # Machine change — affects old and new machines
    let taskIdx = c.machinePosToTask[position]
    let oldM = int(c.currentMachines[taskIdx])
    let newM = int(newValue)
    if oldM == newM: return 0

    let taskStart = int(c.currentStarts[taskIdx])
    # Remove from old machine
    let oldCostOldM = c.machineCosts[oldM]
    let newCostOldM = c.computeMachinePenalty(oldM, excludeTask=taskIdx)
    # Add to new machine
    let oldCostNewM = c.machineCosts[newM]
    let newCostNewM = c.computeMachinePenalty(newM, includeTaskIdx=taskIdx, includeStart=taskStart)
    return (newCostOldM - oldCostOldM) + (newCostNewM - oldCostNewM)

  return 0


proc getAffectedPositions*[T](c: MultiMachineNoOverlapConstraint[T]): PackedSet[int] =
  result = initPackedSet[int]()
  if c.lastChangedPosition < 0:
    # Return all positions
    for t in 0..<c.taskCount:
      result.incl(c.startPositions[t])
      if c.machinePositions[t] >= 0:
        result.incl(c.machinePositions[t])
    return

  if c.lastChangedPosition in c.startPosToTask:
    # Start time changed — tasks on the same machine are affected
    let taskIdx = c.startPosToTask[c.lastChangedPosition]
    let m = if c.machinePositions[taskIdx] >= 0: int(c.currentMachines[taskIdx])
            else: c.fixedMachines[taskIdx]
    for t in 0..<c.taskCount:
      let tm = if c.machinePositions[t] >= 0: int(c.currentMachines[t])
               else: c.fixedMachines[t]
      if tm == m:
        result.incl(c.startPositions[t])
        if c.machinePositions[t] >= 0:
          result.incl(c.machinePositions[t])

  elif c.lastChangedPosition in c.machinePosToTask:
    # Machine changed — tasks on old and new machines affected
    let taskIdx = c.machinePosToTask[c.lastChangedPosition]
    let newM = if c.machinePositions[taskIdx] >= 0: int(c.currentMachines[taskIdx])
               else: c.fixedMachines[taskIdx]
    let oldM = int(c.lastOldValue)
    for t in 0..<c.taskCount:
      let tm = if c.machinePositions[t] >= 0: int(c.currentMachines[t])
               else: c.fixedMachines[t]
      if tm == oldM or tm == newM:
        result.incl(c.startPositions[t])
        if c.machinePositions[t] >= 0:
          result.incl(c.machinePositions[t])


proc getAffectedDomainValues*[T](c: MultiMachineNoOverlapConstraint[T]): seq[T] =
  return @[]  # all values (safe default)


################################################################################
# Batch penalty for lazy domains (start time positions)
################################################################################

proc batchMovePenalty*[T](c: MultiMachineNoOverlapConstraint[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
  ## Efficient batch evaluation for start time positions.
  ## Uses prefix-sum approach: O(maxTime + |domain|).
  result = newSeq[int](domain.len)

  if c.setupMatrix.len > 0:
    # Setup-aware penalty — fall back to per-value evaluation since the
    # consecutive-pair structure invalidates the prefix-sum approach.
    for i in 0..<domain.len:
      result[i] = c.moveDelta(position, currentValue, domain[i])
    return

  if position notin c.startPosToTask:
    # Machine position — evaluate individually
    for i in 0..<domain.len:
      result[i] = c.moveDelta(position, currentValue, domain[i])
    return

  let taskIdx = c.startPosToTask[position]
  let m = if c.machinePositions[taskIdx] >= 0: int(c.currentMachines[taskIdx])
          else: c.fixedMachines[taskIdx]
  let dur = c.durations[taskIdx]
  let baseCost = c.machineCosts[m]

  # Build occupation profile for machine m (excluding this task)
  let profileLen = c.maxTime + dur + 2
  var profile = newSeq[int](profileLen)

  for t in 0..<c.taskCount:
    if t == taskIdx: continue
    let tm = if c.machinePositions[t] >= 0: int(c.currentMachines[t])
             else: c.fixedMachines[t]
    if tm != m: continue
    let s = max(0, int(c.currentStarts[t]))
    let e = min(s + c.durations[t], profileLen)
    # Use delta encoding: +1 at start, -1 at end
    profile[s] += 1
    if e < profileLen:
      profile[e] -= 1

  # Prefix sum to get actual profile
  for i in 1..<profileLen:
    profile[i] += profile[i-1]

  # For limit=1: penalty_with(s) = base_without + occupied_count(s, s+dur)
  # where occupied_count = number of time points in [s, s+dur) where profile >= 1
  # and base_without = penalty from other tasks only

  var baseWithout = 0
  for t in 0..<profileLen:
    if profile[t] > 1:
      baseWithout += profile[t] - 1

  # Prefix sum of min(profile[t], 1) for range queries
  var prefixOccupied = newSeq[int](profileLen + 1)
  for t in 0..<profileLen:
    prefixOccupied[t+1] = prefixOccupied[t] + (if profile[t] >= 1: 1 else: 0)

  for i in 0..<domain.len:
    let s = int(domain[i])
    if s == int(currentValue):
      result[i] = 0
      continue
    let sClamp = max(0, s)
    let eClamp = min(s + dur, profileLen)
    if eClamp <= sClamp:
      result[i] = baseWithout - baseCost
    else:
      let occupiedCount = prefixOccupied[eClamp] - prefixOccupied[sClamp]
      let newMachineCost = baseWithout + occupiedCount
      result[i] = newMachineCost - baseCost


################################################################################
# Deep copy for parallel workers
################################################################################

proc deepCopy*[T](c: MultiMachineNoOverlapConstraint[T]): MultiMachineNoOverlapConstraint[T] =
  new(result)
  result.taskCount = c.taskCount
  result.startPositions = c.startPositions
  result.machinePositions = c.machinePositions
  result.fixedMachines = c.fixedMachines
  result.durations = c.durations
  result.setupMatrix = c.setupMatrix
  result.numMachineValues = c.numMachineValues
  result.maxTime = c.maxTime
  result.cost = 0
  result.lastChangedPosition = -1
  result.currentStarts = newSeq[T](c.taskCount)
  result.currentMachines = newSeq[T](c.taskCount)
  result.machineCosts = newSeq[int](c.numMachineValues)
  result.startPosToTask = c.startPosToTask
  result.machinePosToTask = c.machinePosToTask
