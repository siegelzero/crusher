## Set intersection cardinality constraint for binary variables.
## Constrains: minCard <= sum_i min(A[i], B[i]) <= maxCard
## where A and B are parallel arrays of 0/1 variable positions.
## O(1) moveDelta for binary variables using dense array lookup.

import std/[packedsets, algorithm]

type
    SicEntry = object
        side: int8     # 0 = left, 1 = right
        index: int16   # index into left/right positions

    SicRun = object
        startPos, endPos: int   # inclusive range of covered positions
        slotBase: int           # slot of startPos

    SetIntersectCardConstraint*[T] = ref object
        leftPositions*: seq[int]     # A.bools positions
        rightPositions*: seq[int]    # B.bools positions
        n*: int                      # length of both sequences
        maxCard*: int                # upper bound on intersection cardinality
        minCard*: int                # lower bound (usually 0)
        positions*: PackedSet[int]   # all positions
        # Positions -> dense slots via contiguous runs. The two sides are usually
        # two blocks of set-var bools that can be far apart in the position space,
        # so a single [min..max] dense map wasted O(span) memory per constraint
        # (hundreds of KB each with thousands of disjoint() pairs).
        runs: seq[SicRun]
        posMap*: seq[seq[SicEntry]]  # slot -> entries for that position
        vals*: seq[T]                # slot -> current value
        leftSlots, rightSlots: seq[int]
        dotProduct*: int             # current sum of min(A[i], B[i])
        cost*: int

const SicRunGap = 8   # positions closer than this share a run (small gaps padded)

func slotOf[T](c: SetIntersectCardConstraint[T], pos: int): int {.inline.} =
    for r in c.runs:
        if pos < r.startPos: return -1
        if pos <= r.endPos: return r.slotBase + (pos - r.startPos)
    -1

func newSetIntersectCardConstraint*[T](
    leftPositions, rightPositions: openArray[int],
    maxCard, minCard: int): SetIntersectCardConstraint[T] =
    assert leftPositions.len == rightPositions.len
    let n = leftPositions.len
    var all = newSeqOfCap[int](2 * n)
    for p in leftPositions: all.add(p)
    for p in rightPositions: all.add(p)
    all.sort()
    var runs: seq[SicRun]
    var nSlots = 0
    for p in all:
        if runs.len > 0 and p <= runs[^1].endPos + SicRunGap:
            if p > runs[^1].endPos:
                nSlots += p - runs[^1].endPos
                runs[^1].endPos = p
        else:
            runs.add(SicRun(startPos: p, endPos: p, slotBase: nSlots))
            nSlots += 1
    result = SetIntersectCardConstraint[T](
        leftPositions: @leftPositions,
        rightPositions: @rightPositions,
        n: n,
        maxCard: maxCard,
        minCard: minCard,
        positions: initPackedSet[int](),
        runs: runs,
        posMap: newSeq[seq[SicEntry]](nSlots),
        vals: newSeq[T](nSlots),
        dotProduct: 0,
        cost: 0
    )
    result.leftSlots = newSeq[int](n)
    result.rightSlots = newSeq[int](n)
    for i in 0..<n:
        result.positions.incl(leftPositions[i])
        result.positions.incl(rightPositions[i])
        let ls = result.slotOf(leftPositions[i])
        let rs = result.slotOf(rightPositions[i])
        result.leftSlots[i] = ls
        result.rightSlots[i] = rs
        result.posMap[ls].add(SicEntry(side: 0, index: int16(i)))
        result.posMap[rs].add(SicEntry(side: 1, index: int16(i)))

func computeCost[T](c: SetIntersectCardConstraint[T]): int {.inline.} =
    max(0, c.dotProduct - c.maxCard) + max(0, c.minCard - c.dotProduct)

proc initialize*[T](c: SetIntersectCardConstraint[T], assignment: seq[T]) =
    c.dotProduct = 0
    for pos in c.positions.items:
        c.vals[c.slotOf(pos)] = assignment[pos]
    for i in 0..<c.n:
        let a = c.vals[c.leftSlots[i]]
        let b = c.vals[c.rightSlots[i]]
        c.dotProduct += min(a, b)
    c.cost = computeCost(c)

proc moveDelta*[T](c: SetIntersectCardConstraint[T],
                    position: int, oldValue, newValue: T): int =
    let slot = c.slotOf(position)
    if slot < 0: return 0
    let entries {.cursor.} = c.posMap[slot]
    if entries.len == 0: return 0
    var newDot = c.dotProduct
    for entry in entries:
        let i = int(entry.index)
        let otherVal = if entry.side == 0: c.vals[c.rightSlots[i]]
                       else: c.vals[c.leftSlots[i]]
        newDot += min(newValue, otherVal) - min(oldValue, otherVal)
    let newCost = max(0, newDot - c.maxCard) + max(0, c.minCard - newDot)
    return newCost - c.cost

proc deepCopy*[T](c: SetIntersectCardConstraint[T]): SetIntersectCardConstraint[T] =
    result = newSetIntersectCardConstraint[T](
        c.leftPositions, c.rightPositions, c.maxCard, c.minCard)

proc updatePosition*[T](c: SetIntersectCardConstraint[T],
                         position: int, newValue: T) =
    let slot = c.slotOf(position)
    if slot < 0: return
    let entries {.cursor.} = c.posMap[slot]
    if entries.len == 0: return
    let oldValue = c.vals[slot]
    for entry in entries:
        let i = int(entry.index)
        let otherVal = if entry.side == 0: c.vals[c.rightSlots[i]]
                       else: c.vals[c.leftSlots[i]]
        c.dotProduct += min(newValue, otherVal) - min(oldValue, otherVal)
    c.vals[slot] = newValue
    c.cost = computeCost(c)

