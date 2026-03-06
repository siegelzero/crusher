# Conditional No-Overlap Pair Constraint
#
# Enforces: if both entities are active and share the same resource,
# their time intervals must not overlap.
#
# Specifically: if condA AND condB AND (resourceA == resourceB):
#   then startA + durationA <= startB OR startB + durationB <= startA
#
# Used for gender-mixing constraints: if both patients are selected and
# assigned to the same room, their stays must not overlap.
#
# Performance: O(1) penalty and moveDelta.

import std/[packedsets]

type
  ConditionalNoOverlapPairConstraint*[T] = ref object
    # Entity A
    startAPos*: int          # position of start time (admission day)
    durationA*: int          # constant duration (length of stay)
    resourceAPos*: int       # position of resource variable (room), -1 if fixed
    resourceAFixed*: int     # fixed resource value (if resourceAPos == -1)
    condAPos*: int           # position of condition variable (selection), -1 if always true
    # Entity B
    startBPos*: int          # position of start time
    durationB*: int          # constant duration
    resourceBPos*: int       # position of resource variable, -1 if fixed
    resourceBFixed*: int     # fixed resource value
    condBPos*: int           # position of condition variable, -1 if always true
    # Cached current values (avoid full assignment copy)
    startAVal*: T
    startBVal*: T
    resAVal*: T
    resBVal*: T
    condAVal*: T
    condBVal*: T
    # State
    cost*: int
    lastChangedPosition*: int
    lastOldValue*: T


func isViolatedCached[T](c: ConditionalNoOverlapPairConstraint[T]): bool {.inline.} =
  if c.condAPos >= 0 and c.condAVal != T(1): return false
  if c.condBPos >= 0 and c.condBVal != T(1): return false
  let resA = if c.resourceAPos >= 0: int(c.resAVal) else: c.resourceAFixed
  let resB = if c.resourceBPos >= 0: int(c.resBVal) else: c.resourceBFixed
  if resA != resB: return false
  let startA = int(c.startAVal)
  let startB = int(c.startBVal)
  return startA < startB + c.durationB and startB < startA + c.durationA


func newConditionalNoOverlapPairConstraint*[T](
    startAPos, startBPos: int,
    durationA, durationB: int,
    resourceAPos, resourceBPos: int,
    resourceAFixed, resourceBFixed: int,
    condAPos, condBPos: int): ConditionalNoOverlapPairConstraint[T] =
  new(result)
  result.startAPos = startAPos
  result.startBPos = startBPos
  result.durationA = durationA
  result.durationB = durationB
  result.resourceAPos = resourceAPos
  result.resourceBPos = resourceBPos
  result.resourceAFixed = resourceAFixed
  result.resourceBFixed = resourceBFixed
  result.condAPos = condAPos
  result.condBPos = condBPos
  result.cost = 0
  result.lastChangedPosition = -1


proc initialize*[T](c: ConditionalNoOverlapPairConstraint[T], assignment: seq[T]) =
  c.startAVal = assignment[c.startAPos]
  c.startBVal = assignment[c.startBPos]
  if c.resourceAPos >= 0: c.resAVal = assignment[c.resourceAPos]
  if c.resourceBPos >= 0: c.resBVal = assignment[c.resourceBPos]
  if c.condAPos >= 0: c.condAVal = assignment[c.condAPos]
  if c.condBPos >= 0: c.condBVal = assignment[c.condBPos]
  c.cost = if c.isViolatedCached(): 1 else: 0

template setCachedVal[T](c: ConditionalNoOverlapPairConstraint[T], position: int, value: T) =
  if position == c.startAPos: c.startAVal = value
  if position == c.startBPos: c.startBVal = value
  if position == c.resourceAPos: c.resAVal = value
  if position == c.resourceBPos: c.resBVal = value
  if position == c.condAPos: c.condAVal = value
  if position == c.condBPos: c.condBVal = value

template getCachedVal[T](c: ConditionalNoOverlapPairConstraint[T], position: int): T =
  if position == c.startAPos: c.startAVal
  elif position == c.startBPos: c.startBVal
  elif position == c.resourceAPos: c.resAVal
  elif position == c.resourceBPos: c.resBVal
  elif position == c.condAPos: c.condAVal
  elif position == c.condBPos: c.condBVal
  else: T(0)

proc updatePosition*[T](c: ConditionalNoOverlapPairConstraint[T], position: int, newValue: T) =
  c.lastChangedPosition = position
  c.lastOldValue = c.getCachedVal(position)
  c.setCachedVal(position, newValue)
  c.cost = if c.isViolatedCached(): 1 else: 0


func moveDelta*[T](c: ConditionalNoOverlapPairConstraint[T], position: int, oldValue, newValue: T): int =
  if oldValue == newValue: return 0

  let oldCost = c.cost

  # Inline violation check with substituted value
  var condA = true
  if c.condAPos >= 0:
    let v = if position == c.condAPos: newValue else: c.condAVal
    if v != T(1): condA = false

  var condB = true
  if condA and c.condBPos >= 0:
    let v = if position == c.condBPos: newValue else: c.condBVal
    if v != T(1): condB = false

  var newCost = 0
  if condA and condB:
    let resA = if c.resourceAPos >= 0:
      int(if position == c.resourceAPos: newValue else: c.resAVal)
    else: c.resourceAFixed
    let resB = if c.resourceBPos >= 0:
      int(if position == c.resourceBPos: newValue else: c.resBVal)
    else: c.resourceBFixed

    if resA == resB:
      let startA = int(if position == c.startAPos: newValue else: c.startAVal)
      let startB = int(if position == c.startBPos: newValue else: c.startBVal)
      if startA < startB + c.durationB and startB < startA + c.durationA:
        newCost = 1

  return newCost - oldCost


proc getAffectedPositions*[T](c: ConditionalNoOverlapPairConstraint[T]): PackedSet[int] =
  result = initPackedSet[int]()
  result.incl(c.startAPos)
  result.incl(c.startBPos)
  if c.resourceAPos >= 0: result.incl(c.resourceAPos)
  if c.resourceBPos >= 0: result.incl(c.resourceBPos)
  if c.condAPos >= 0: result.incl(c.condAPos)
  if c.condBPos >= 0: result.incl(c.condBPos)


proc deepCopy*[T](c: ConditionalNoOverlapPairConstraint[T]): ConditionalNoOverlapPairConstraint[T] =
  new(result)
  result.startAPos = c.startAPos
  result.startBPos = c.startBPos
  result.durationA = c.durationA
  result.durationB = c.durationB
  result.resourceAPos = c.resourceAPos
  result.resourceBPos = c.resourceBPos
  result.resourceAFixed = c.resourceAFixed
  result.resourceBFixed = c.resourceBFixed
  result.condAPos = c.condAPos
  result.condBPos = c.condBPos
  result.cost = 0
  result.lastChangedPosition = -1
