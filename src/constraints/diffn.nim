# Diffn Constraint - Non-overlapping rectangles
#
# Ensures that n rectangles with positions (x[i], y[i]) and sizes (dx[i], dy[i])
# do not overlap pairwise.
#
# Two rectangles i,j overlap iff:
#   x[i] < x[j] + dx[j] AND x[j] < x[i] + dx[i]  (horizontal overlap)
#   y[i] < y[j] + dy[j] AND y[j] < y[i] + dy[i]  (vertical overlap)
#
# Penalty = number of overlapping pairs.

import std/[packedsets, tables, sequtils]
import ../expressions/expressions

################################################################################
# Type definitions
################################################################################

type
    DiffnConstraint*[T] = ref object
        n*: int  # number of rectangles
        xExprs*, yExprs*, dxExprs*, dyExprs*: seq[AlgebraicExpression[T]]
        positions*: PackedSet[int]
        posToRects*: Table[int, seq[int]]  # position -> rectangle indices using it
        currentAssignment*: seq[T]
        cost*: int
        lastAffectedPositions*: PackedSet[int]

################################################################################
# Helper functions
################################################################################

func rectsOverlap[T](xi, yi, dxi, dyi, xj, yj, dxj, dyj: T): bool {.inline.} =
    ## Check if two rectangles overlap (both must have positive dimensions)
    if dxi <= 0 or dyi <= 0 or dxj <= 0 or dyj <= 0:
        return false
    xi < xj + dxj and xj < xi + dxi and
    yi < yj + dyj and yj < yi + dyi

proc evalRect[T](constraint: DiffnConstraint[T], rectIdx: int, assignment: seq[T]): (T, T, T, T) {.inline.} =
    ## Evaluate rectangle coordinates from current assignment
    let x = constraint.xExprs[rectIdx].evaluate(assignment)
    let y = constraint.yExprs[rectIdx].evaluate(assignment)
    let dx = constraint.dxExprs[rectIdx].evaluate(assignment)
    let dy = constraint.dyExprs[rectIdx].evaluate(assignment)
    (x, y, dx, dy)

proc countOverlaps[T](constraint: DiffnConstraint[T], assignment: seq[T]): int =
    ## Count all pairwise overlaps
    result = 0
    for i in 0 ..< constraint.n:
        let (xi, yi, dxi, dyi) = constraint.evalRect(i, assignment)
        for j in i + 1 ..< constraint.n:
            let (xj, yj, dxj, dyj) = constraint.evalRect(j, assignment)
            if rectsOverlap(xi, yi, dxi, dyi, xj, yj, dxj, dyj):
                inc result

################################################################################
# Constructor
################################################################################

proc newDiffnConstraint*[T](xExprs, yExprs, dxExprs, dyExprs: seq[AlgebraicExpression[T]]): DiffnConstraint[T] =
    let n = xExprs.len
    doAssert yExprs.len == n and dxExprs.len == n and dyExprs.len == n,
        "All arrays must have the same length"

    var positions: PackedSet[int]
    var posToRects = initTable[int, seq[int]]()

    for i in 0 ..< n:
        for expr in [xExprs[i], yExprs[i], dxExprs[i], dyExprs[i]]:
            for pos in expr.positions.items:
                positions.incl(pos)
                posToRects.mgetOrPut(pos, @[]).add(i)

    # Deduplicate rectangle indices per position
    for pos in posToRects.keys:
        var seen: PackedSet[int]
        var deduped: seq[int]
        for r in posToRects[pos]:
            if r notin seen:
                seen.incl(r)
                deduped.add(r)
        posToRects[pos] = deduped

    # Find max position to size currentAssignment
    var maxPos = 0
    for pos in positions.items:
        if pos > maxPos:
            maxPos = pos

    result = DiffnConstraint[T](
        n: n,
        xExprs: xExprs,
        yExprs: yExprs,
        dxExprs: dxExprs,
        dyExprs: dyExprs,
        positions: positions,
        posToRects: posToRects,
        currentAssignment: newSeq[T](maxPos + 1),
        cost: 0,
    )

################################################################################
# Constraint interface
################################################################################

proc initialize*[T](constraint: DiffnConstraint[T], assignment: seq[T]) =
    ## Initialize with a complete assignment
    for pos in constraint.positions.items:
        constraint.currentAssignment[pos] = assignment[pos]
    constraint.cost = countOverlaps(constraint, constraint.currentAssignment)

proc moveDelta*[T](constraint: DiffnConstraint[T], position: int, oldValue, newValue: T): int =
    ## Compute change in cost if position changes from oldValue to newValue
    if position notin constraint.posToRects:
        return 0

    # Get rectangles affected by this position
    let affectedRects = constraint.posToRects[position]

    # Count overlaps with old value (only pairs involving affected rectangles)
    var oldOverlaps = 0
    for i in affectedRects:
        let (xi, yi, dxi, dyi) = constraint.evalRect(i, constraint.currentAssignment)
        for j in 0 ..< constraint.n:
            if j == i:
                continue
            # Only count each pair once: skip if both are affected and j < i
            if j in affectedRects and j < i:
                continue
            let (xj, yj, dxj, dyj) = constraint.evalRect(j, constraint.currentAssignment)
            if rectsOverlap(xi, yi, dxi, dyi, xj, yj, dxj, dyj):
                inc oldOverlaps

    # Temporarily apply new value
    let saved = constraint.currentAssignment[position]
    constraint.currentAssignment[position] = newValue

    # Count overlaps with new value
    var newOverlaps = 0
    for i in affectedRects:
        let (xi, yi, dxi, dyi) = constraint.evalRect(i, constraint.currentAssignment)
        for j in 0 ..< constraint.n:
            if j == i:
                continue
            if j in affectedRects and j < i:
                continue
            let (xj, yj, dxj, dyj) = constraint.evalRect(j, constraint.currentAssignment)
            if rectsOverlap(xi, yi, dxi, dyi, xj, yj, dxj, dyj):
                inc newOverlaps

    # Restore old value
    constraint.currentAssignment[position] = saved

    return newOverlaps - oldOverlaps

proc addRectPositions[T](constraint: DiffnConstraint[T], dest: var PackedSet[int], rectIdx: int) {.inline.} =
    for pos in constraint.xExprs[rectIdx].positions.items:
        dest.incl(pos)
    for pos in constraint.yExprs[rectIdx].positions.items:
        dest.incl(pos)
    for pos in constraint.dxExprs[rectIdx].positions.items:
        dest.incl(pos)
    for pos in constraint.dyExprs[rectIdx].positions.items:
        dest.incl(pos)

proc updatePosition*[T](constraint: DiffnConstraint[T], position: int, newValue: T) =
    ## Update assignment and recompute cost
    constraint.lastAffectedPositions = initPackedSet[int]()

    if position in constraint.posToRects:
        let affectedRects = constraint.posToRects[position]

        # Collect overlap neighbors BEFORE the change
        var neighborRects: PackedSet[int]
        for i in affectedRects:
            neighborRects.incl(i)
            let (xi, yi, dxi, dyi) = constraint.evalRect(i, constraint.currentAssignment)
            for j in 0 ..< constraint.n:
                if j == i: continue
                let (xj, yj, dxj, dyj) = constraint.evalRect(j, constraint.currentAssignment)
                if rectsOverlap(xi, yi, dxi, dyi, xj, yj, dxj, dyj):
                    neighborRects.incl(j)

        # Apply the change
        constraint.currentAssignment[position] = newValue

        # Collect overlap neighbors AFTER the change
        for i in affectedRects:
            let (xi, yi, dxi, dyi) = constraint.evalRect(i, constraint.currentAssignment)
            for j in 0 ..< constraint.n:
                if j == i: continue
                let (xj, yj, dxj, dyj) = constraint.evalRect(j, constraint.currentAssignment)
                if rectsOverlap(xi, yi, dxi, dyi, xj, yj, dxj, dyj):
                    neighborRects.incl(j)

        # Add positions of all affected + neighbor rectangles
        for r in neighborRects.items:
            constraint.addRectPositions(constraint.lastAffectedPositions, r)
    else:
        constraint.currentAssignment[position] = newValue

    constraint.cost = countOverlaps(constraint, constraint.currentAssignment)

func getAffectedPositions*[T](constraint: DiffnConstraint[T]): PackedSet[int] =
    ## Return positions that need penalty recalculation after last update
    return constraint.lastAffectedPositions

func getAffectedDomainValues*[T](constraint: DiffnConstraint[T], position: int): seq[T] =
    ## Return all domain values (no optimization here)
    return @[]

proc deepCopy*[T](constraint: DiffnConstraint[T]): DiffnConstraint[T] =
    ## Deep copy for parallel search
    var copiedX = newSeq[AlgebraicExpression[T]](constraint.n)
    var copiedY = newSeq[AlgebraicExpression[T]](constraint.n)
    var copiedDX = newSeq[AlgebraicExpression[T]](constraint.n)
    var copiedDY = newSeq[AlgebraicExpression[T]](constraint.n)
    for i in 0 ..< constraint.n:
        copiedX[i] = constraint.xExprs[i].deepCopy()
        copiedY[i] = constraint.yExprs[i].deepCopy()
        copiedDX[i] = constraint.dxExprs[i].deepCopy()
        copiedDY[i] = constraint.dyExprs[i].deepCopy()
    result = DiffnConstraint[T](
        n: constraint.n,
        xExprs: copiedX,
        yExprs: copiedY,
        dxExprs: copiedDX,
        dyExprs: copiedDY,
        positions: constraint.positions,
        posToRects: constraint.posToRects,  # read-only after construction
        currentAssignment: constraint.currentAssignment,  # seq copied by value
        cost: constraint.cost,
        lastAffectedPositions: constraint.lastAffectedPositions,
    )
