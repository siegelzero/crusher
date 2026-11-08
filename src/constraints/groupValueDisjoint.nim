## Pairwise value-disjointness between groups of variables.
##
## Groups are lists of variable positions (plus optional constant members).
## For each incompatible pair (g, h) the sets of values taken by g's members
## and h's members must be disjoint:
##
##     cost = sum over pairs (g, h) of |values(g) ∩ values(h)|
##
## This is the search-variable form of `disjoint(S_g, S_h)` where each set
## variable S_g is only bounded from below by `x in S_g` constraints and from
## above by disjointness, so its minimal value is exactly {x : x in group g}.
## (MiniZinc Challenge 2026 "warehouse": incompatible customers may not share
## a facility; the customer's facility set is the union over its tokens.)
##
## State per group g and value v:
##   cnt[g][v]      number of members of g currently at v
##   conflict[g][v] number of partners h of g with cnt[h][v] > 0
##
## moveDelta for a member of g moving old -> new is O(1):
##   + conflict[g][new] if g does not yet use new
##   - conflict[g][old] if the mover is g's only member at old
## updatePosition is O(#partners of g) and only when g gains or loses a value.

import std/[packedsets]

type
    GroupValueDisjointConstraint*[T] = ref object
        groups*: seq[seq[int]]          # group -> member positions
        constMembers*: seq[seq[T]]      # group -> constant member values
        pairs*: seq[(int, int)]         # incompatible group pairs (g < h, deduplicated)
        partners: seq[seq[int32]]       # group -> partner groups
        lo*, hi*: T                     # value universe
        nVals: int
        posBase: int                    # positions are mapped densely from posBase
        groupOfPos: seq[int32]          # (pos - posBase) -> group, -1 if none
        vals: seq[T]                    # (pos - posBase) -> current value
        cnt: seq[int32]                 # g*nVals + (v-lo)
        conflict: seq[int32]            # g*nVals + (v-lo)
        positions*: PackedSet[int]
        cost*: int
        # Last accepted move (for incremental neighbor penalty updates).
        lastGroup: int
        lastOld, lastNew: T
        lastPartnersTouched: bool      # g lost lastOld entirely or newly gained lastNew
        groupMembers: seq[PackedSet[int]]    # group -> its positions
        groupAndPartners: seq[PackedSet[int]] # group -> its positions ∪ partners' positions

func vIdx[T](c: GroupValueDisjointConstraint[T], v: T): int {.inline.} =
    ## Dense index of value v, or -1 when v lies outside the universe.
    if v < c.lo or v > c.hi: -1 else: int(v - c.lo)

func newGroupValueDisjointConstraint*[T](
    groups: seq[seq[int]], constMembers: seq[seq[T]],
    pairs: seq[(int, int)], lo, hi: T): GroupValueDisjointConstraint[T] =
    assert constMembers.len == groups.len
    var minPos = int.high
    var maxPos = -1
    var positions = initPackedSet[int]()
    for g in groups:
        for p in g:
            positions.incl(p)
            minPos = min(minPos, p)
            maxPos = max(maxPos, p)
    if maxPos < 0:
        minPos = 0
    let span = maxPos - minPos + 1
    var groupOfPos = newSeq[int32](span)
    for i in 0 ..< span: groupOfPos[i] = -1
    for gi, g in groups:
        for p in g:
            groupOfPos[p - minPos] = int32(gi)
    # Deduplicate pairs and build partner lists.
    var seen = initPackedSet[int]()
    var dedup: seq[(int, int)]
    var partners = newSeq[seq[int32]](groups.len)
    for (a, b) in pairs:
        if a == b: continue
        let g = min(a, b)
        let h = max(a, b)
        let key = g * groups.len + h
        if key in seen: continue
        seen.incl(key)
        dedup.add((g, h))
        partners[g].add(int32(h))
        partners[h].add(int32(g))
    let nVals = int(hi - lo) + 1
    var groupMembers = newSeq[PackedSet[int]](groups.len)
    var groupAndPartners = newSeq[PackedSet[int]](groups.len)
    for gi, g in groups:
        groupMembers[gi] = initPackedSet[int]()
        for p in g: groupMembers[gi].incl(p)
    for gi in 0 ..< groups.len:
        groupAndPartners[gi] = groupMembers[gi]
        for h in partners[gi]:
            for p in groups[int(h)]: groupAndPartners[gi].incl(p)
    result = GroupValueDisjointConstraint[T](
        groups: groups,
        constMembers: constMembers,
        pairs: dedup,
        partners: partners,
        lo: lo, hi: hi,
        nVals: nVals,
        posBase: minPos,
        groupOfPos: groupOfPos,
        vals: newSeq[T](span),
        cnt: newSeq[int32](groups.len * nVals),
        conflict: newSeq[int32](groups.len * nVals),
        positions: positions,
        cost: 0,
        lastGroup: -1,
        groupMembers: groupMembers,
        groupAndPartners: groupAndPartners)

proc initialize*[T](c: GroupValueDisjointConstraint[T], assignment: seq[T]) =
    for i in 0 ..< c.cnt.len:
        c.cnt[i] = 0
        c.conflict[i] = 0
    for gi, g in c.groups:
        for v in c.constMembers[gi]:
            let vi = c.vIdx(v)
            if vi >= 0: inc c.cnt[gi * c.nVals + vi]
        for p in g:
            let v = assignment[p]
            c.vals[p - c.posBase] = v
            let vi = c.vIdx(v)
            if vi >= 0: inc c.cnt[gi * c.nVals + vi]
    c.cost = 0
    for (g, h) in c.pairs:
        for vi in 0 ..< c.nVals:
            let gUses = c.cnt[g * c.nVals + vi] > 0
            let hUses = c.cnt[h * c.nVals + vi] > 0
            if gUses: inc c.conflict[h * c.nVals + vi]
            if hUses: inc c.conflict[g * c.nVals + vi]
            if gUses and hUses: inc c.cost

proc moveDelta*[T](c: GroupValueDisjointConstraint[T],
                    position: int, oldValue, newValue: T): int =
    if oldValue == newValue: return 0
    let rel = position - c.posBase
    if rel < 0 or rel >= c.groupOfPos.len: return 0
    let g = int(c.groupOfPos[rel])
    if g < 0: return 0
    let base = g * c.nVals
    var delta = 0
    let ni = c.vIdx(newValue)
    if ni >= 0 and c.cnt[base + ni] == 0:
        delta += int(c.conflict[base + ni])
    let oi = c.vIdx(oldValue)
    if oi >= 0 and c.cnt[base + oi] == 1:
        delta -= int(c.conflict[base + oi])
    return delta

proc updatePosition*[T](c: GroupValueDisjointConstraint[T],
                         position: int, newValue: T) =
    let rel = position - c.posBase
    if rel < 0 or rel >= c.groupOfPos.len: return
    let g = int(c.groupOfPos[rel])
    if g < 0: return
    let oldValue = c.vals[rel]
    c.lastGroup = g
    c.lastOld = oldValue
    c.lastNew = newValue
    c.lastPartnersTouched = false
    if oldValue == newValue: return
    c.vals[rel] = newValue
    let base = g * c.nVals
    let oi = c.vIdx(oldValue)
    if oi >= 0:
        dec c.cnt[base + oi]
        if c.cnt[base + oi] == 0:
            # g no longer uses oldValue: every partner using it loses a conflict.
            c.cost -= int(c.conflict[base + oi])
            for h in c.partners[g]:
                dec c.conflict[int(h) * c.nVals + oi]
            c.lastPartnersTouched = true
    let ni = c.vIdx(newValue)
    if ni >= 0:
        inc c.cnt[base + ni]
        if c.cnt[base + ni] == 1:
            c.cost += int(c.conflict[base + ni])
            for h in c.partners[g]:
                inc c.conflict[int(h) * c.nVals + ni]
            c.lastPartnersTouched = true

proc getAffectedPositions*[T](c: GroupValueDisjointConstraint[T]): PackedSet[int] =
    ## Positions whose cached deltas may have changed after the last move of a
    ## member of group g from lastOld to lastNew: g's own members always (their
    ## cnt[g][old/new] changed); partners' members only when g released old or
    ## newly acquired new (their conflict[h][old/new] changed).
    if c.lastGroup < 0 or c.lastOld == c.lastNew:
        return initPackedSet[int]()
    if c.lastPartnersTouched: c.groupAndPartners[c.lastGroup]
    else: c.groupMembers[c.lastGroup]

proc getAffectedDomainValues*[T](c: GroupValueDisjointConstraint[T], position: int): seq[T] =
    ## A neighbor currently at lastOld or lastNew has its baseline term changed,
    ## so every value needs recomputing (@[] = all); any other neighbor only
    ## sees different deltas for the values lastOld and lastNew.
    let rel = position - c.posBase
    if rel < 0 or rel >= c.vals.len: return @[]
    let cur = c.vals[rel]
    if cur == c.lastOld or cur == c.lastNew: return @[]
    @[c.lastOld, c.lastNew]

proc batchMovePenalty*[T](c: GroupValueDisjointConstraint[T], position: int,
                          oldValue: T, domain: seq[T]): seq[int] =
    ## moveDelta for every domain value at once (same arithmetic, no dispatch).
    result = newSeq[int](domain.len)
    let rel = position - c.posBase
    if rel < 0 or rel >= c.groupOfPos.len: return
    let g = int(c.groupOfPos[rel])
    if g < 0: return
    let base = g * c.nVals
    var leave = 0
    let oi = c.vIdx(oldValue)
    if oi >= 0 and c.cnt[base + oi] == 1:
        leave = -int(c.conflict[base + oi])
    for i, v in domain:
        if v == oldValue: continue
        let vi = c.vIdx(v)
        var d = leave
        if vi >= 0 and c.cnt[base + vi] == 0:
            d += int(c.conflict[base + vi])
        result[i] = d

proc deepCopy*[T](c: GroupValueDisjointConstraint[T]): GroupValueDisjointConstraint[T] =
    result = newGroupValueDisjointConstraint[T](
        c.groups, c.constMembers, c.pairs, c.lo, c.hi)
