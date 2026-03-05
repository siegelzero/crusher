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
    RectCoords[T] = tuple[x, y, dx, dy: T]

    DiffnConstraint*[T] = ref object
        n*: int  # number of rectangles
        xExprs*, yExprs*, dxExprs*, dyExprs*: seq[AlgebraicExpression[T]]
        positions*: PackedSet[int]
        posToRects*: Table[int, seq[int]]  # position -> rectangle indices using it
        currentAssignment*: seq[T]
        cost*: int
        lastAffectedPositions*: PackedSet[int]
        # Incremental state
        cachedRects*: seq[RectCoords[T]]   # evaluated rectangle coords
        overlaps*: seq[PackedSet[int]]      # overlaps[i] = set of rects overlapping rect i
        # Position classification per rect: which dimension does each position affect?
        posIsX: Table[int, seq[int]]    # pos -> rect indices where pos is in xExpr
        posIsY: Table[int, seq[int]]    # pos -> rect indices where pos is in yExpr
        posIsDX: Table[int, seq[int]]   # pos -> rect indices where pos is in dxExpr
        posIsDY: Table[int, seq[int]]   # pos -> rect indices where pos is in dyExpr

################################################################################
# Helper functions
################################################################################

func rectsOverlap[T](xi, yi, dxi, dyi, xj, yj, dxj, dyj: T): bool {.inline.} =
    ## Check if two rectangles overlap (both must have positive dimensions)
    if dxi <= 0 or dyi <= 0 or dxj <= 0 or dyj <= 0:
        return false
    xi < xj + dxj and xj < xi + dxi and
    yi < yj + dyj and yj < yi + dyi

func rectsOverlapCoords[T](a, b: RectCoords[T]): bool {.inline.} =
    rectsOverlap(a.x, a.y, a.dx, a.dy, b.x, b.y, b.dx, b.dy)

proc evalRect[T](constraint: DiffnConstraint[T], rectIdx: int, assignment: seq[T]): RectCoords[T] {.inline.} =
    ## Evaluate rectangle coordinates from current assignment
    let x = constraint.xExprs[rectIdx].evaluate(assignment)
    let y = constraint.yExprs[rectIdx].evaluate(assignment)
    let dx = constraint.dxExprs[rectIdx].evaluate(assignment)
    let dy = constraint.dyExprs[rectIdx].evaluate(assignment)
    (x, y, dx, dy)

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

    # Build per-dimension position maps
    var posIsX = initTable[int, seq[int]]()
    var posIsY = initTable[int, seq[int]]()
    var posIsDX = initTable[int, seq[int]]()
    var posIsDY = initTable[int, seq[int]]()
    for i in 0 ..< n:
        for pos in xExprs[i].positions.items:
            posIsX.mgetOrPut(pos, @[]).add(i)
        for pos in yExprs[i].positions.items:
            posIsY.mgetOrPut(pos, @[]).add(i)
        for pos in dxExprs[i].positions.items:
            posIsDX.mgetOrPut(pos, @[]).add(i)
        for pos in dyExprs[i].positions.items:
            posIsDY.mgetOrPut(pos, @[]).add(i)

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
        cachedRects: newSeq[RectCoords[T]](n),
        overlaps: newSeq[PackedSet[int]](n),
        posIsX: posIsX,
        posIsY: posIsY,
        posIsDX: posIsDX,
        posIsDY: posIsDY,
    )

################################################################################
# Constraint interface
################################################################################

proc buildOverlaps[T](constraint: DiffnConstraint[T]) =
    ## Build overlap adjacency from cachedRects
    let n = constraint.n
    for i in 0 ..< n:
        constraint.overlaps[i] = initPackedSet[int]()
    for i in 0 ..< n:
        for j in i + 1 ..< n:
            if rectsOverlapCoords(constraint.cachedRects[i], constraint.cachedRects[j]):
                constraint.overlaps[i].incl(j)
                constraint.overlaps[j].incl(i)

proc countOverlapPairs[T](constraint: DiffnConstraint[T]): int =
    ## Count pairs from overlap adjacency (each pair counted once)
    result = 0
    for i in 0 ..< constraint.n:
        result += constraint.overlaps[i].len
    result = result div 2

proc initialize*[T](constraint: DiffnConstraint[T], assignment: seq[T]) =
    ## Initialize with a complete assignment
    for pos in constraint.positions.items:
        constraint.currentAssignment[pos] = assignment[pos]
    for i in 0 ..< constraint.n:
        constraint.cachedRects[i] = constraint.evalRect(i, constraint.currentAssignment)
    constraint.buildOverlaps()
    constraint.cost = constraint.countOverlapPairs()

proc addRectPositions[T](constraint: DiffnConstraint[T], dest: var PackedSet[int], rectIdx: int) {.inline.} =
    for pos in constraint.xExprs[rectIdx].positions.items:
        dest.incl(pos)
    for pos in constraint.yExprs[rectIdx].positions.items:
        dest.incl(pos)
    for pos in constraint.dxExprs[rectIdx].positions.items:
        dest.incl(pos)
    for pos in constraint.dyExprs[rectIdx].positions.items:
        dest.incl(pos)

proc moveDelta*[T](constraint: DiffnConstraint[T], position: int, oldValue, newValue: T): int =
    ## Compute change in cost if position changes from oldValue to newValue
    if position notin constraint.posToRects:
        return 0

    let affectedRects = constraint.posToRects[position]
    let n = constraint.n

    # Build affected set for dedup
    var affectedSet: PackedSet[int]
    for r in affectedRects:
        affectedSet.incl(r)

    # Count overlaps with old value using cached rects
    var oldOverlaps = 0
    for i in affectedRects:
        for j in 0 ..< n:
            if j == i: continue
            if j in affectedSet and j < i: continue
            if rectsOverlapCoords(constraint.cachedRects[i], constraint.cachedRects[j]):
                inc oldOverlaps

    # Temporarily apply new value, re-evaluate affected rects
    let saved = constraint.currentAssignment[position]
    constraint.currentAssignment[position] = newValue

    var newRects: seq[RectCoords[T]]
    newRects.setLen(affectedRects.len)
    for idx, r in affectedRects:
        newRects[idx] = constraint.evalRect(r, constraint.currentAssignment)

    # Count overlaps with new value
    var newOverlaps = 0
    for idx, i in affectedRects:
        for j in 0 ..< n:
            if j == i: continue
            if j in affectedSet and j < i: continue
            let ri = newRects[idx]
            let rj = if j in affectedSet:
                var jRect: RectCoords[T]
                for idx2, r2 in affectedRects:
                    if r2 == j:
                        jRect = newRects[idx2]
                        break
                jRect
            else:
                constraint.cachedRects[j]
            if rectsOverlapCoords(ri, rj):
                inc newOverlaps

    # Restore old value
    constraint.currentAssignment[position] = saved

    return newOverlaps - oldOverlaps

proc updatePosition*[T](constraint: DiffnConstraint[T], position: int, newValue: T) =
    ## Update assignment incrementally
    constraint.lastAffectedPositions = initPackedSet[int]()

    if position in constraint.posToRects:
        let affectedRects = constraint.posToRects[position]

        # Apply the change
        constraint.currentAssignment[position] = newValue

        # For each affected rect: re-evaluate, update overlaps incrementally
        for r in affectedRects:
            let newRect = constraint.evalRect(r, constraint.currentAssignment)
            constraint.cachedRects[r] = newRect

            for j in 0 ..< constraint.n:
                if j == r: continue
                let wasOverlapping = j in constraint.overlaps[r]
                let isOverlapping = rectsOverlapCoords(newRect, constraint.cachedRects[j])

                if wasOverlapping != isOverlapping:
                    if isOverlapping:
                        constraint.overlaps[r].incl(j)
                        constraint.overlaps[j].incl(r)
                    else:
                        constraint.overlaps[r].excl(j)
                        constraint.overlaps[j].excl(r)
                    # Overlap status changed — j's penalty map needs updating
                    constraint.addRectPositions(constraint.lastAffectedPositions, j)

            # The affected rect itself always needs updating
            constraint.addRectPositions(constraint.lastAffectedPositions, r)

        constraint.cost = constraint.countOverlapPairs()
    else:
        constraint.currentAssignment[position] = newValue

proc batchMovePenalty*[T](constraint: DiffnConstraint[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
    ## Compute moveDelta for all domain values at once.
    ## Uses sweep-line when position affects a single rect's x or y.
    let dLen = domain.len
    result = newSeq[int](dLen)

    if position notin constraint.posToRects:
        return

    let n = constraint.n

    # Determine which dimensions this position affects
    let xRects = constraint.posIsX.getOrDefault(position)
    let yRects = constraint.posIsY.getOrDefault(position)
    let dxRects = constraint.posIsDX.getOrDefault(position)
    let dyRects = constraint.posIsDY.getOrDefault(position)

    # Sweep-line: position affects exactly one rect's x (and nothing else for this rect's other dims)
    if xRects.len == 1 and yRects.len == 0 and dxRects.len == 0 and dyRects.len == 0:
        let r = xRects[0]
        let rc = constraint.cachedRects[r]
        let dxr = rc.dx
        let dyr = rc.dy
        let yr = rc.y
        if dxr <= 0 or dyr <= 0:
            return  # zero-size rect can't overlap anything

        let oldOverlaps = constraint.overlaps[r].len

        # Pre-compute candidate x values by evaluating expression for each domain value
        var candidateXs = newSeq[T](dLen)
        for di in 0 ..< dLen:
            constraint.currentAssignment[position] = domain[di]
            candidateXs[di] = constraint.xExprs[r].evaluate(constraint.currentAssignment)
        constraint.currentAssignment[position] = currentValue

        # For each other rect j with y-overlap, compute x-overlap interval
        # Rect r overlaps j in x when: xr < xj + dxj AND xj < xr + dxr
        # => xj - dxr + 1 <= xr <= xj + dxj - 1
        # Collect (lo, hi) intervals for y-relevant rects
        type Interval = tuple[lo, hi: T]
        var intervals: seq[Interval]
        for j in 0 ..< n:
            if j == r: continue
            let rj = constraint.cachedRects[j]
            if rj.dx <= 0 or rj.dy <= 0: continue
            # Check y-overlap (fixed since only x varies)
            if yr < rj.y + rj.dy and rj.y < yr + dyr:
                intervals.add((lo: rj.x - dxr + 1, hi: rj.x + rj.dx - 1))

        if intervals.len == 0:
            # No y-overlapping rects — all candidates have 0 overlaps
            for di in 0 ..< dLen:
                result[di] = -oldOverlaps
                if domain[di] == currentValue:
                    result[di] = 0
            return

        # For each candidate, count how many intervals contain candidateX
        for di in 0 ..< dLen:
            if domain[di] == currentValue:
                continue
            let cx = candidateXs[di]
            var count = 0
            for iv in intervals:
                if cx >= iv.lo and cx <= iv.hi:
                    inc count
            result[di] = count - oldOverlaps
        return

    # Sweep-line: position affects exactly one rect's y (and nothing else)
    if yRects.len == 1 and xRects.len == 0 and dxRects.len == 0 and dyRects.len == 0:
        let r = yRects[0]
        let rc = constraint.cachedRects[r]
        let dxr = rc.dx
        let dyr = rc.dy
        let xr = rc.x
        if dxr <= 0 or dyr <= 0:
            return

        let oldOverlaps = constraint.overlaps[r].len

        var candidateYs = newSeq[T](dLen)
        for di in 0 ..< dLen:
            constraint.currentAssignment[position] = domain[di]
            candidateYs[di] = constraint.yExprs[r].evaluate(constraint.currentAssignment)
        constraint.currentAssignment[position] = currentValue

        type Interval = tuple[lo, hi: T]
        var intervals: seq[Interval]
        for j in 0 ..< n:
            if j == r: continue
            let rj = constraint.cachedRects[j]
            if rj.dx <= 0 or rj.dy <= 0: continue
            if xr < rj.x + rj.dx and rj.x < xr + dxr:
                intervals.add((lo: rj.y - dyr + 1, hi: rj.y + rj.dy - 1))

        if intervals.len == 0:
            for di in 0 ..< dLen:
                result[di] = -oldOverlaps
                if domain[di] == currentValue:
                    result[di] = 0
            return

        for di in 0 ..< dLen:
            if domain[di] == currentValue:
                continue
            let cy = candidateYs[di]
            var count = 0
            for iv in intervals:
                if cy >= iv.lo and cy <= iv.hi:
                    inc count
            result[di] = count - oldOverlaps
        return

    # General fallback: per-value evaluation using cachedRects
    let affectedRects = constraint.posToRects[position]
    var affectedSet: PackedSet[int]
    for r in affectedRects:
        affectedSet.incl(r)

    # Count current overlaps involving affected rects
    var oldOverlaps = 0
    for i in affectedRects:
        for j in 0 ..< n:
            if j == i: continue
            if j in affectedSet and j < i: continue
            if rectsOverlapCoords(constraint.cachedRects[i], constraint.cachedRects[j]):
                inc oldOverlaps

    var tempRects = newSeq[RectCoords[T]](affectedRects.len)

    for di in 0 ..< dLen:
        let v = domain[di]
        if v == currentValue:
            continue

        constraint.currentAssignment[position] = v

        for idx, r in affectedRects:
            tempRects[idx] = constraint.evalRect(r, constraint.currentAssignment)

        var newOverlaps = 0
        for idx, i in affectedRects:
            for j in 0 ..< n:
                if j == i: continue
                if j in affectedSet and j < i: continue
                let ri = tempRects[idx]
                let rj = if j in affectedSet:
                    var jRect: RectCoords[T]
                    for idx2, r2 in affectedRects:
                        if r2 == j:
                            jRect = tempRects[idx2]
                            break
                    jRect
                else:
                    constraint.cachedRects[j]
                if rectsOverlapCoords(ri, rj):
                    inc newOverlaps

        result[di] = newOverlaps - oldOverlaps

    constraint.currentAssignment[position] = currentValue


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

    var copiedOverlaps = newSeq[PackedSet[int]](constraint.n)
    for i in 0 ..< constraint.n:
        copiedOverlaps[i] = constraint.overlaps[i]

    result = DiffnConstraint[T](
        n: constraint.n,
        xExprs: copiedX,
        yExprs: copiedY,
        dxExprs: copiedDX,
        dyExprs: copiedDY,
        positions: constraint.positions,
        posToRects: constraint.posToRects,
        currentAssignment: constraint.currentAssignment,
        cost: constraint.cost,
        lastAffectedPositions: constraint.lastAffectedPositions,
        cachedRects: constraint.cachedRects,
        overlaps: copiedOverlaps,
        posIsX: constraint.posIsX,
        posIsY: constraint.posIsY,
        posIsDX: constraint.posIsDX,
        posIsDY: constraint.posIsDY,
    )
