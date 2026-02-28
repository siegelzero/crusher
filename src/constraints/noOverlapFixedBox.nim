# NoOverlapFixedBox Constraint - Variable box vs fixed box non-overlap in 3D
#
# Ensures that a variable 3D box (a pipe leg defined by two node endpoints
# and a radius) does not overlap a fixed 3D box (an obstacle with safety
# distance baked in).
#
# The variable box is defined by:
#   legLower_d = min(nodeA_d, nodeB_d) - radius
#   legUpper_d = max(nodeA_d, nodeB_d) + radius
#
# Penalty = min(overlap_0, overlap_1, overlap_2) when all 3 dims overlap
#         = 0 when separated in at least one dimension
#
# This gives gradient information (how far to move to separate).

import std/[packedsets, tables]

type
  FixedBoxEndpoint* = object
    isFixed*: bool
    fixedValue*: int     # used when isFixed=true
    position*: int       # position in assignment, used when isFixed=false

  NoOverlapFixedBoxConstraint*[T] = ref object
    # Per dimension (0=X, 1=Y, 2=Z):
    nodeA*: array[3, FixedBoxEndpoint]   # leg endpoint A coordinates
    nodeB*: array[3, FixedBoxEndpoint]   # leg endpoint B coordinates
    radius*: T
    boxLower*: array[3, T]  # fixed box lower bound (with safety distance baked in)
    boxUpper*: array[3, T]  # fixed box upper bound (with safety distance baked in)
    # Cached state
    cost*: T
    overlapPerDim*: array[3, T]  # cached overlap in each dimension
    positions*: PackedSet[int]
    posToDim*: Table[int, int]   # position -> dimension index for O(1) lookup
    currentAssignment*: seq[T]   # cached assignment values for relevant positions

func getVal[T](ep: FixedBoxEndpoint, assignment: seq[T]): T {.inline.} =
  if ep.isFixed: ep.fixedValue
  else: assignment[ep.position]

func computeOverlap[T](legLower, legUpper, boxLower, boxUpper: T): T {.inline.} =
  max(T(0), min(legUpper, boxUpper) - max(legLower, boxLower))

func dimOverlap[T](c: NoOverlapFixedBoxConstraint[T], dim: int,
                    assignment: seq[T]): T {.inline.} =
  let a = getVal(c.nodeA[dim], assignment)
  let b = getVal(c.nodeB[dim], assignment)
  let legLower = min(a, b) - c.radius
  let legUpper = max(a, b) + c.radius
  computeOverlap(legLower, legUpper, c.boxLower[dim], c.boxUpper[dim])

func overlapCost[T](o0, o1, o2: T): T {.inline.} =
  if o0 > 0 and o1 > 0 and o2 > 0:
    min(o0, min(o1, o2))
  else:
    T(0)

proc newNoOverlapFixedBoxConstraint*[T](
    nodeA, nodeB: array[3, FixedBoxEndpoint],
    radius: T,
    boxLower, boxUpper: array[3, T]): NoOverlapFixedBoxConstraint[T] =
  var positions: PackedSet[int]
  var posToDim = initTable[int, int]()
  var maxPos = 0

  for d in 0..2:
    if not nodeA[d].isFixed:
      positions.incl(nodeA[d].position)
      posToDim[nodeA[d].position] = d
      if nodeA[d].position > maxPos: maxPos = nodeA[d].position
    if not nodeB[d].isFixed:
      positions.incl(nodeB[d].position)
      posToDim[nodeB[d].position] = d
      if nodeB[d].position > maxPos: maxPos = nodeB[d].position

  result = NoOverlapFixedBoxConstraint[T](
    nodeA: nodeA,
    nodeB: nodeB,
    radius: radius,
    boxLower: boxLower,
    boxUpper: boxUpper,
    cost: T(0),
    positions: positions,
    posToDim: posToDim,
    currentAssignment: newSeq[T](maxPos + 1),
  )

proc initialize*[T](constraint: NoOverlapFixedBoxConstraint[T], assignment: seq[T]) =
  for pos in constraint.positions.items:
    constraint.currentAssignment[pos] = assignment[pos]
  for d in 0..2:
    constraint.overlapPerDim[d] = dimOverlap(constraint, d, constraint.currentAssignment)
  constraint.cost = overlapCost(
    constraint.overlapPerDim[0],
    constraint.overlapPerDim[1],
    constraint.overlapPerDim[2])

func moveDelta*[T](constraint: NoOverlapFixedBoxConstraint[T],
                    position: int, oldValue, newValue: T): int =
  if position notin constraint.posToDim:
    return 0

  let dim = constraint.posToDim[position]

  # Get both endpoints for this dimension, substituting newValue for position
  var a = getVal(constraint.nodeA[dim], constraint.currentAssignment)
  var b = getVal(constraint.nodeB[dim], constraint.currentAssignment)
  if not constraint.nodeA[dim].isFixed and constraint.nodeA[dim].position == position:
    a = newValue
  if not constraint.nodeB[dim].isFixed and constraint.nodeB[dim].position == position:
    b = newValue

  let legLower = min(a, b) - constraint.radius
  let legUpper = max(a, b) + constraint.radius
  let newDimOverlap = computeOverlap(legLower, legUpper,
                                      constraint.boxLower[dim], constraint.boxUpper[dim])

  # Compute new cost using cached overlaps for other dims
  var overlaps: array[3, T]
  for d in 0..2:
    overlaps[d] = if d == dim: newDimOverlap else: constraint.overlapPerDim[d]

  let newCost = overlapCost(overlaps[0], overlaps[1], overlaps[2])
  return int(newCost) - int(constraint.cost)

proc updatePosition*[T](constraint: NoOverlapFixedBoxConstraint[T],
                         position: int, newValue: T) =
  constraint.currentAssignment[position] = newValue
  if position in constraint.posToDim:
    let dim = constraint.posToDim[position]
    constraint.overlapPerDim[dim] = dimOverlap(constraint, dim, constraint.currentAssignment)
    constraint.cost = overlapCost(
      constraint.overlapPerDim[0],
      constraint.overlapPerDim[1],
      constraint.overlapPerDim[2])

func getAffectedPositions*[T](constraint: NoOverlapFixedBoxConstraint[T]): PackedSet[int] =
  # All positions (at most 6, usually 2-4). Cheap since set is tiny.
  return constraint.positions

func getAffectedDomainValues*[T](constraint: NoOverlapFixedBoxConstraint[T], position: int): seq[T] =
  return @[]

proc deepCopy*[T](constraint: NoOverlapFixedBoxConstraint[T]): NoOverlapFixedBoxConstraint[T] =
  result = NoOverlapFixedBoxConstraint[T](
    nodeA: constraint.nodeA,
    nodeB: constraint.nodeB,
    radius: constraint.radius,
    boxLower: constraint.boxLower,
    boxUpper: constraint.boxUpper,
    cost: constraint.cost,
    overlapPerDim: constraint.overlapPerDim,
    positions: constraint.positions,
    posToDim: constraint.posToDim,
    currentAssignment: constraint.currentAssignment,  # seq copied by value
  )
