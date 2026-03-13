# Multi-Resource No-Overlap Pair Constraint
#
# Groups multiple resource-conflict clauses for a single activity pair:
#   For each resource r: NOT(assign[i,r] AND assign[j,r] AND overlap[i,j])
#
# Equivalently: if activities i,j overlap in time, they cannot share any resource.
#
# The constraint monitors:
#   - An overlap position (channel or search variable, 1=overlapping, 0=separated)
#   - Multiple (assign[i,r], assign[j,r]) pairs (one per shared-resource candidate)
#
# Penalty: number of shared resources when overlapping, 0 otherwise.
# This gives graduated pressure — more shared resources means more urgency to separate.
#
# Performance: O(1) moveDelta.

import std/[packedsets]

type
  AssignPair* = object
    posA*: int  # position of assign[i,r]
    posB*: int  # position of assign[j,r]

  MultiResourceNoOverlapConstraint*[T] = ref object
    overlapPos*: int         # position of overlap variable (1=overlapping, 0=not)
    assignPairs*: seq[AssignPair]  # (assign[i,r], assign[j,r]) for each resource r
    # Cached current values
    overlapVal*: T
    assignAVals*: seq[T]     # cached assign[i,r] values
    assignBVals*: seq[T]     # cached assign[j,r] values
    # State
    nSharedResources*: int   # count of r where assign[i,r]=1 AND assign[j,r]=1
    cost*: int


func newMultiResourceNoOverlapConstraint*[T](
    overlapPos: int,
    assignPairs: seq[AssignPair]): MultiResourceNoOverlapConstraint[T] =
  new(result)
  result.overlapPos = overlapPos
  result.assignPairs = assignPairs
  result.assignAVals = newSeq[T](assignPairs.len)
  result.assignBVals = newSeq[T](assignPairs.len)
  result.nSharedResources = 0
  result.overlapVal = T(0)
  result.cost = 0


proc initialize*[T](c: MultiResourceNoOverlapConstraint[T], assignment: seq[T]) =
  c.overlapVal = assignment[c.overlapPos]
  for i in 0..<c.assignPairs.len:
    c.assignAVals[i] = assignment[c.assignPairs[i].posA]
    c.assignBVals[i] = assignment[c.assignPairs[i].posB]
  c.nSharedResources = 0
  for i in 0..<c.assignPairs.len:
    if c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1):
      inc c.nSharedResources
  c.cost = if c.overlapVal == T(1): c.nSharedResources else: 0


func moveDelta*[T](c: MultiResourceNoOverlapConstraint[T], position: int, oldValue, newValue: T): int =
  if oldValue == newValue: return 0
  let oldCost = c.cost

  var newOverlap = c.overlapVal
  if position == c.overlapPos:
    newOverlap = newValue

  if newOverlap != T(1):
    return 0 - oldCost

  # Compute new shared resource count
  var newShared = c.nSharedResources
  for i in 0..<c.assignPairs.len:
    if position == c.assignPairs[i].posA:
      let wasShared = c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1)
      let isShared = newValue == T(1) and c.assignBVals[i] == T(1)
      if wasShared and not isShared: dec newShared
      elif not wasShared and isShared: inc newShared
    elif position == c.assignPairs[i].posB:
      let wasShared = c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1)
      let isShared = c.assignAVals[i] == T(1) and newValue == T(1)
      if wasShared and not isShared: dec newShared
      elif not wasShared and isShared: inc newShared

  return newShared - oldCost


proc updatePosition*[T](c: MultiResourceNoOverlapConstraint[T], position: int, newValue: T) =
  if position == c.overlapPos:
    c.overlapVal = newValue
  else:
    for i in 0..<c.assignPairs.len:
      if position == c.assignPairs[i].posA:
        let wasShared = c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1)
        c.assignAVals[i] = newValue
        let isShared = c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1)
        if wasShared and not isShared: dec c.nSharedResources
        elif not wasShared and isShared: inc c.nSharedResources
      elif position == c.assignPairs[i].posB:
        let wasShared = c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1)
        c.assignBVals[i] = newValue
        let isShared = c.assignAVals[i] == T(1) and c.assignBVals[i] == T(1)
        if wasShared and not isShared: dec c.nSharedResources
        elif not wasShared and isShared: inc c.nSharedResources
  c.cost = if c.overlapVal == T(1): c.nSharedResources else: 0


proc getAffectedPositions*[T](c: MultiResourceNoOverlapConstraint[T]): PackedSet[int] =
  result = initPackedSet[int]()
  result.incl(c.overlapPos)
  for pair in c.assignPairs:
    result.incl(pair.posA)
    result.incl(pair.posB)


proc deepCopy*[T](c: MultiResourceNoOverlapConstraint[T]): MultiResourceNoOverlapConstraint[T] =
  new(result)
  result.overlapPos = c.overlapPos
  result.assignPairs = c.assignPairs
  result.assignAVals = newSeq[T](c.assignPairs.len)
  result.assignBVals = newSeq[T](c.assignPairs.len)
  result.nSharedResources = 0
  result.overlapVal = T(0)
  result.cost = 0
