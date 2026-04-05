## Set intersection cardinality constraint for binary variables.
## Constrains: minCard <= sum_i min(A[i], B[i]) <= maxCard
## where A and B are parallel arrays of 0/1 variable positions.
## O(1) moveDelta for binary variables using dense array lookup.

import std/packedsets

type
    SicEntry = object
        side: int8     # 0 = left, 1 = right
        index: int16   # index into left/right positions

    SetIntersectCardConstraint*[T] = ref object
        leftPositions*: seq[int]     # A.bools positions
        rightPositions*: seq[int]    # B.bools positions
        n*: int                      # length of both sequences
        maxCard*: int                # upper bound on intersection cardinality
        minCard*: int                # lower bound (usually 0)
        positions*: PackedSet[int]   # all positions
        # Dense array: posMap[pos - posBase] gives entries for that position
        posBase*: int                # minimum position value
        posMapLen*: int              # length of posMap
        posMap*: seq[seq[SicEntry]]  # dense mapping from (pos - posBase) -> entries
        # Dense assignment cache: vals[pos - posBase] gives current value
        vals*: seq[T]
        dotProduct*: int             # current sum of min(A[i], B[i])
        cost*: int

func newSetIntersectCardConstraint*[T](
    leftPositions, rightPositions: openArray[int],
    maxCard, minCard: int): SetIntersectCardConstraint[T] =
    assert leftPositions.len == rightPositions.len
    let n = leftPositions.len
    # Find position range for dense arrays
    var posMin = high(int)
    var posMax = low(int)
    for i in 0..<n:
        posMin = min(posMin, min(leftPositions[i], rightPositions[i]))
        posMax = max(posMax, max(leftPositions[i], rightPositions[i]))
    let mapLen = if n > 0: posMax - posMin + 1 else: 0
    result = SetIntersectCardConstraint[T](
        leftPositions: @leftPositions,
        rightPositions: @rightPositions,
        n: n,
        maxCard: maxCard,
        minCard: minCard,
        positions: initPackedSet[int](),
        posBase: posMin,
        posMapLen: mapLen,
        posMap: newSeq[seq[SicEntry]](mapLen),
        vals: newSeq[T](mapLen),
        dotProduct: 0,
        cost: 0
    )
    for i in 0..<n:
        result.positions.incl(leftPositions[i])
        result.positions.incl(rightPositions[i])
        result.posMap[leftPositions[i] - posMin].add(SicEntry(side: 0, index: int16(i)))
        result.posMap[rightPositions[i] - posMin].add(SicEntry(side: 1, index: int16(i)))

func computeCost[T](c: SetIntersectCardConstraint[T]): int {.inline.} =
    max(0, c.dotProduct - c.maxCard) + max(0, c.minCard - c.dotProduct)

proc initialize*[T](c: SetIntersectCardConstraint[T], assignment: seq[T]) =
    c.dotProduct = 0
    for pos in c.positions.items:
        let idx = pos - c.posBase
        c.vals[idx] = assignment[pos]
    for i in 0..<c.n:
        let a = c.vals[c.leftPositions[i] - c.posBase]
        let b = c.vals[c.rightPositions[i] - c.posBase]
        c.dotProduct += min(a, b)
    c.cost = computeCost(c)

proc moveDelta*[T](c: SetIntersectCardConstraint[T],
                    position: int, oldValue, newValue: T): int =
    let idx = position - c.posBase
    if idx < 0 or idx >= c.posMapLen: return 0
    let entries = c.posMap[idx]
    if entries.len == 0: return 0
    var newDot = c.dotProduct
    for entry in entries:
        let i = int(entry.index)
        let otherPos = if entry.side == 0: c.rightPositions[i]
                       else: c.leftPositions[i]
        let otherVal = c.vals[otherPos - c.posBase]
        newDot += min(newValue, otherVal) - min(oldValue, otherVal)
    let newCost = max(0, newDot - c.maxCard) + max(0, c.minCard - newDot)
    return newCost - c.cost

proc deepCopy*[T](c: SetIntersectCardConstraint[T]): SetIntersectCardConstraint[T] =
    result = newSetIntersectCardConstraint[T](
        c.leftPositions, c.rightPositions, c.maxCard, c.minCard)

proc updatePosition*[T](c: SetIntersectCardConstraint[T],
                         position: int, newValue: T) =
    let idx = position - c.posBase
    if idx < 0 or idx >= c.posMapLen: return
    let entries = c.posMap[idx]
    if entries.len == 0: return
    let oldValue = c.vals[idx]
    for entry in entries:
        let i = int(entry.index)
        let otherPos = if entry.side == 0: c.rightPositions[i]
                       else: c.leftPositions[i]
        let otherVal = c.vals[otherPos - c.posBase]
        c.dotProduct += min(newValue, otherVal) - min(oldValue, otherVal)
    c.vals[idx] = newValue
    c.cost = computeCost(c)
