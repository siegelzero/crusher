# DiffnK Constraint - Non-overlapping k-dimensional boxes
#
# Generalization of diffn from 2D to k dimensions.
# Ensures that n boxes with positions pos[i][d] and sizes size[i][d]
# do not overlap pairwise across all k dimensions.
#
# Two boxes i,j overlap iff for ALL dimensions d:
#   pos[i][d] < pos[j][d] + size[j][d] AND pos[j][d] < pos[i][d] + size[i][d]
#
# Nonstrict semantics: boxes with zero size in any dimension cannot overlap.
#
# Penalty = number of overlapping pairs.

import std/[packedsets, tables, sequtils]
import ../expressions/expressions

################################################################################
# Type definitions
################################################################################

type
    BoxCoords[T] = object
        pos: seq[T]
        size: seq[T]

    DiffnKConstraint*[T] = ref object
        n*, k*: int
        posExprs*: seq[seq[AlgebraicExpression[T]]]   # [box][dim]
        sizeExprs*: seq[seq[AlgebraicExpression[T]]]  # [box][dim]
        positions*: PackedSet[int]
        posToBoxes*: Table[int, seq[int]]
        currentAssignment*: seq[T]
        cost*: int
        lastAffectedPositions*: PackedSet[int]
        cachedBoxes*: seq[BoxCoords[T]]
        overlaps*: seq[PackedSet[int]]
        posIsPosDim*: seq[Table[int, seq[int]]]   # [dim] pos -> box indices
        posIsSizeDim*: seq[Table[int, seq[int]]]  # [dim] pos -> box indices

################################################################################
# Helper functions
################################################################################

func boxesOverlap[T](a, b: BoxCoords[T], k: int): bool {.inline.} =
    ## Check if two k-dimensional boxes overlap (nonstrict: zero-size => no overlap)
    for d in 0 ..< k:
        if a.size[d] <= 0 or b.size[d] <= 0:
            return false
        if not (a.pos[d] < b.pos[d] + b.size[d] and b.pos[d] < a.pos[d] + a.size[d]):
            return false
    return true

proc evalBox[T](constraint: DiffnKConstraint[T], boxIdx: int, assignment: seq[T]): BoxCoords[T] {.inline.} =
    let k = constraint.k
    result.pos = newSeq[T](k)
    result.size = newSeq[T](k)
    for d in 0 ..< k:
        result.pos[d] = constraint.posExprs[boxIdx][d].evaluate(assignment)
        result.size[d] = constraint.sizeExprs[boxIdx][d].evaluate(assignment)

################################################################################
# Constructor
################################################################################

proc newDiffnKConstraint*[T](n, k: int, posExprs, sizeExprs: seq[seq[AlgebraicExpression[T]]]): DiffnKConstraint[T] =
    doAssert posExprs.len == n and sizeExprs.len == n,
        "posExprs and sizeExprs must have n elements"
    for i in 0 ..< n:
        doAssert posExprs[i].len == k and sizeExprs[i].len == k,
            "Each box must have k dimensions"

    var positions: PackedSet[int]
    var posToBoxes = initTable[int, seq[int]]()

    for i in 0 ..< n:
        for d in 0 ..< k:
            for expr in [posExprs[i][d], sizeExprs[i][d]]:
                for pos in expr.positions.items:
                    positions.incl(pos)
                    posToBoxes.mgetOrPut(pos, @[]).add(i)

    # Deduplicate box indices per position
    for pos in posToBoxes.keys:
        var seen: PackedSet[int]
        var deduped: seq[int]
        for r in posToBoxes[pos]:
            if r notin seen:
                seen.incl(r)
                deduped.add(r)
        posToBoxes[pos] = deduped

    # Build per-dimension position maps
    var posIsPosDim = newSeq[Table[int, seq[int]]](k)
    var posIsSizeDim = newSeq[Table[int, seq[int]]](k)
    for d in 0 ..< k:
        posIsPosDim[d] = initTable[int, seq[int]]()
        posIsSizeDim[d] = initTable[int, seq[int]]()
    for i in 0 ..< n:
        for d in 0 ..< k:
            for pos in posExprs[i][d].positions.items:
                posIsPosDim[d].mgetOrPut(pos, @[]).add(i)
            for pos in sizeExprs[i][d].positions.items:
                posIsSizeDim[d].mgetOrPut(pos, @[]).add(i)

    # Find max position
    var maxPos = 0
    for pos in positions.items:
        if pos > maxPos:
            maxPos = pos

    result = DiffnKConstraint[T](
        n: n,
        k: k,
        posExprs: posExprs,
        sizeExprs: sizeExprs,
        positions: positions,
        posToBoxes: posToBoxes,
        currentAssignment: newSeq[T](maxPos + 1),
        cost: 0,
        cachedBoxes: newSeq[BoxCoords[T]](n),
        overlaps: newSeq[PackedSet[int]](n),
        posIsPosDim: posIsPosDim,
        posIsSizeDim: posIsSizeDim,
    )

################################################################################
# Constraint interface
################################################################################

proc buildOverlaps[T](constraint: DiffnKConstraint[T]) =
    let n = constraint.n
    let k = constraint.k
    for i in 0 ..< n:
        constraint.overlaps[i] = initPackedSet[int]()
    for i in 0 ..< n:
        for j in i + 1 ..< n:
            if boxesOverlap(constraint.cachedBoxes[i], constraint.cachedBoxes[j], k):
                constraint.overlaps[i].incl(j)
                constraint.overlaps[j].incl(i)

proc countOverlapPairs[T](constraint: DiffnKConstraint[T]): int =
    result = 0
    for i in 0 ..< constraint.n:
        result += constraint.overlaps[i].len
    result = result div 2

proc initialize*[T](constraint: DiffnKConstraint[T], assignment: seq[T]) =
    for pos in constraint.positions.items:
        constraint.currentAssignment[pos] = assignment[pos]
    for i in 0 ..< constraint.n:
        constraint.cachedBoxes[i] = constraint.evalBox(i, constraint.currentAssignment)
    constraint.buildOverlaps()
    constraint.cost = constraint.countOverlapPairs()

proc addBoxPositions[T](constraint: DiffnKConstraint[T], dest: var PackedSet[int], boxIdx: int) {.inline.} =
    for d in 0 ..< constraint.k:
        for pos in constraint.posExprs[boxIdx][d].positions.items:
            dest.incl(pos)
        for pos in constraint.sizeExprs[boxIdx][d].positions.items:
            dest.incl(pos)

proc moveDelta*[T](constraint: DiffnKConstraint[T], position: int, oldValue, newValue: T): int =
    if position notin constraint.posToBoxes:
        return 0

    let affectedBoxes = constraint.posToBoxes[position]
    let n = constraint.n
    let k = constraint.k

    var affectedSet: PackedSet[int]
    var affectedIdx: Table[int, int]  # box index → position in affectedBoxes
    for idx, r in affectedBoxes:
        affectedSet.incl(r)
        affectedIdx[r] = idx

    # Count overlaps with old value
    var oldOverlaps = 0
    for i in affectedBoxes:
        for j in 0 ..< n:
            if j == i: continue
            if j in affectedSet and j < i: continue
            if boxesOverlap(constraint.cachedBoxes[i], constraint.cachedBoxes[j], k):
                inc oldOverlaps

    # Temporarily apply new value
    let saved = constraint.currentAssignment[position]
    constraint.currentAssignment[position] = newValue

    var newBoxes: seq[BoxCoords[T]]
    newBoxes.setLen(affectedBoxes.len)
    for idx, r in affectedBoxes:
        newBoxes[idx] = constraint.evalBox(r, constraint.currentAssignment)

    # Count overlaps with new value
    var newOverlaps = 0
    for idx, i in affectedBoxes:
        for j in 0 ..< n:
            if j == i: continue
            if j in affectedSet and j < i: continue
            let bi = newBoxes[idx]
            let bj = if j in affectedSet:
                newBoxes[affectedIdx[j]]
            else:
                constraint.cachedBoxes[j]
            if boxesOverlap(bi, bj, k):
                inc newOverlaps

    constraint.currentAssignment[position] = saved
    return newOverlaps - oldOverlaps

proc updatePosition*[T](constraint: DiffnKConstraint[T], position: int, newValue: T) =
    constraint.lastAffectedPositions = initPackedSet[int]()

    if position in constraint.posToBoxes:
        let affectedBoxes = constraint.posToBoxes[position]
        let k = constraint.k

        constraint.currentAssignment[position] = newValue

        for r in affectedBoxes:
            let newBox = constraint.evalBox(r, constraint.currentAssignment)
            constraint.cachedBoxes[r] = newBox

            for j in 0 ..< constraint.n:
                if j == r: continue
                let wasOverlapping = j in constraint.overlaps[r]
                let isOverlapping = boxesOverlap(newBox, constraint.cachedBoxes[j], k)

                if wasOverlapping != isOverlapping:
                    if isOverlapping:
                        constraint.overlaps[r].incl(j)
                        constraint.overlaps[j].incl(r)
                    else:
                        constraint.overlaps[r].excl(j)
                        constraint.overlaps[j].excl(r)
                    constraint.addBoxPositions(constraint.lastAffectedPositions, j)

            constraint.addBoxPositions(constraint.lastAffectedPositions, r)

        constraint.cost = constraint.countOverlapPairs()
    else:
        constraint.currentAssignment[position] = newValue

proc batchMovePenalty*[T](constraint: DiffnKConstraint[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
    let dLen = domain.len
    result = newSeq[int](dLen)

    if position notin constraint.posToBoxes:
        return

    let n = constraint.n
    let k = constraint.k

    # General fallback: per-value evaluation
    let affectedBoxes = constraint.posToBoxes[position]
    var affectedSet: PackedSet[int]
    var affectedIdx: Table[int, int]  # box index → position in affectedBoxes
    for idx, r in affectedBoxes:
        affectedSet.incl(r)
        affectedIdx[r] = idx

    var oldOverlaps = 0
    for i in affectedBoxes:
        for j in 0 ..< n:
            if j == i: continue
            if j in affectedSet and j < i: continue
            if boxesOverlap(constraint.cachedBoxes[i], constraint.cachedBoxes[j], k):
                inc oldOverlaps

    var tempBoxes = newSeq[BoxCoords[T]](affectedBoxes.len)

    for di in 0 ..< dLen:
        let v = domain[di]
        if v == currentValue:
            continue

        constraint.currentAssignment[position] = v

        for idx, r in affectedBoxes:
            tempBoxes[idx] = constraint.evalBox(r, constraint.currentAssignment)

        var newOverlaps = 0
        for idx, i in affectedBoxes:
            for j in 0 ..< n:
                if j == i: continue
                if j in affectedSet and j < i: continue
                let bi = tempBoxes[idx]
                let bj = if j in affectedSet:
                    tempBoxes[affectedIdx[j]]
                else:
                    constraint.cachedBoxes[j]
                if boxesOverlap(bi, bj, k):
                    inc newOverlaps

        result[di] = newOverlaps - oldOverlaps

    constraint.currentAssignment[position] = currentValue


func getAffectedPositions*[T](constraint: DiffnKConstraint[T]): PackedSet[int] =
    return constraint.lastAffectedPositions

func getAffectedDomainValues*[T](constraint: DiffnKConstraint[T], position: int): seq[T] =
    return @[]

proc deepCopy*[T](constraint: DiffnKConstraint[T]): DiffnKConstraint[T] =
    var copiedPos = newSeq[seq[AlgebraicExpression[T]]](constraint.n)
    var copiedSize = newSeq[seq[AlgebraicExpression[T]]](constraint.n)
    for i in 0 ..< constraint.n:
        copiedPos[i] = newSeq[AlgebraicExpression[T]](constraint.k)
        copiedSize[i] = newSeq[AlgebraicExpression[T]](constraint.k)
        for d in 0 ..< constraint.k:
            copiedPos[i][d] = constraint.posExprs[i][d].deepCopy()
            copiedSize[i][d] = constraint.sizeExprs[i][d].deepCopy()

    var copiedOverlaps = newSeq[PackedSet[int]](constraint.n)
    for i in 0 ..< constraint.n:
        copiedOverlaps[i] = constraint.overlaps[i]

    # Deep copy mutable seqs to avoid shared state between parallel workers
    var copiedCachedBoxes = newSeq[BoxCoords[T]](constraint.n)
    for i in 0 ..< constraint.n:
        copiedCachedBoxes[i] = BoxCoords[T](
            pos: @(constraint.cachedBoxes[i].pos),
            size: @(constraint.cachedBoxes[i].size))

    result = DiffnKConstraint[T](
        n: constraint.n,
        k: constraint.k,
        posExprs: copiedPos,
        sizeExprs: copiedSize,
        positions: constraint.positions,
        posToBoxes: constraint.posToBoxes,
        currentAssignment: @(constraint.currentAssignment),
        cost: constraint.cost,
        lastAffectedPositions: constraint.lastAffectedPositions,
        cachedBoxes: copiedCachedBoxes,
        overlaps: copiedOverlaps,
        posIsPosDim: constraint.posIsPosDim,
        posIsSizeDim: constraint.posIsSizeDim,
    )
