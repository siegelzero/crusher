## AdjacencyEqualConstraint: incremental evaluation for grouped pairwise
## "no adjacent different-label items" clauses.
##
## For each directed pair (a, b): coord(a) = coord(b) + 1 implies the pair's
## label equality holds. Each violated pair contributes penalty 1, matching
## the min-violation of the 3-literal disjunctive clause decomposition
## (labelEq ∨ coordDiff ≤ r ∨ coordDiff ≥ r+2) it replaces.
##
## coord(i) is an affine form over positions: constant + Σ coeff·pos —
## typically a row-major 1-D projection like (W+1)·y + x. The pair's label
## equality is a linear equation Σ labelCoeffs·pos == labelRhs (an empty
## form means the pair is never exempt). Items are indexed by current
## coordinate in `itemsAtCoord`, so a coordinate change only re-checks the
## ±1 neighborhoods of the old and new values — O(items at those values)
## per move instead of O(pairs).
##
## Hot-path discipline: this constraint is evaluated inside channel-dep
## cascade batches (updatePosition + penalty + revert per domain value), so
## the update/delta paths must not allocate. Index access goes through
## `withValue` (no seq copies), per-(a,b) pair lookup is a first-index table
## plus an intrusive `nextSamePair` chain, and computeMoveDelta reuses
## per-constraint scratch buffers.

import std/[tables]

type
    AdjItemForm*[T] = object
        ## Affine coordinate form: constant + Σ coeffs[k]·assignment[positions[k]]
        positions*: seq[int]
        coeffs*: seq[T]
        constant*: T

    AdjPairSpec*[T] = object
        ## Directed pair: violated iff coord[a] == coord[b] + 1 and the label
        ## equation does not hold.
        a*, b*: int32
        labelPositions*: seq[int]
        labelCoeffs*: seq[T]
        labelRhs*: T

    AdjacencyEqualConstraint*[T] = ref object
        items*: seq[AdjItemForm[T]]
        pairs*: seq[AdjPairSpec[T]]
        # (a, b) -> first index into pairs; duplicates chained via nextSamePair
        firstPair*: Table[(int32, int32), int32]
        nextSamePair*: seq[int32]
        # position -> [(item, coeff)] across item coordinate forms (net coeffs)
        coordEntries*: Table[int, seq[tuple[item: int32, coeff: T]]]
        # position -> pair indices whose label equation references it
        labelEntries*: Table[int, seq[int32]]
        coordVals*: seq[T]
        # coordinate value -> items currently at it. Emptied entries are kept
        # (capacity reuse) rather than deleted.
        itemsAtCoord*: Table[T, seq[int32]]
        violated*: seq[bool]
        currentAssignment*: Table[int, T]
        cost*: int
        # Scratch buffers for computeMoveDelta (capacity persists across calls)
        scratchAffected: seq[tuple[item: int32, newCoord: T]]
        scratchCandidates: seq[int32]

func newAdjacencyEqualConstraint*[T](
    items: seq[AdjItemForm[T]],
    pairs: seq[AdjPairSpec[T]]
): AdjacencyEqualConstraint[T] =
    new(result)
    result.items = items
    result.pairs = pairs
    result.coordVals = newSeq[T](items.len)
    result.violated = newSeq[bool](pairs.len)
    result.nextSamePair = newSeq[int32](pairs.len)
    for i in 0..<items.len:
        # Merge duplicate positions within a form so each (position, item)
        # produces exactly one entry with the net coefficient — moveDelta
        # computes an item's new coordinate from a single entry.
        var net = initTable[int, T]()
        for k in 0..<items[i].positions.len:
            let pos = items[i].positions[k]
            net[pos] = net.getOrDefault(pos, T(0)) + items[i].coeffs[k]
        for pos, coeff in net.pairs:
            if coeff != T(0):
                result.coordEntries.mgetOrPut(pos, @[]).add(
                    (item: int32(i), coeff: coeff))
    for pi in 0..<pairs.len:
        result.nextSamePair[pi] = -1
    for pi in countdown(pairs.len - 1, 0):
        # Prepend so firstPair holds the lowest index and chains the rest
        let key = (pairs[pi].a, pairs[pi].b)
        result.nextSamePair[pi] = result.firstPair.getOrDefault(key, -1'i32)
        result.firstPair[key] = int32(pi)
        var seen: seq[int]
        for pos in pairs[pi].labelPositions:
            if pos notin seen:
                seen.add(pos)
                result.labelEntries.mgetOrPut(pos, @[]).add(int32(pi))

iterator pairIdxs[T](state: AdjacencyEqualConstraint[T], a, b: int32): int32 =
    var pi = state.firstPair.getOrDefault((a, b), -1'i32)
    while pi >= 0:
        yield pi
        pi = state.nextSamePair[pi]

func pairExempt[T](state: AdjacencyEqualConstraint[T], pi: int32): bool {.inline.} =
    let p = addr state.pairs[pi]
    if p.labelPositions.len == 0:
        return false
    var s: T = 0
    for k in 0..<p.labelPositions.len:
        s += p.labelCoeffs[k] * state.currentAssignment.getOrDefault(p.labelPositions[k], T(0))
    return s == p.labelRhs

func pairViolatedNow[T](state: AdjacencyEqualConstraint[T], pi: int32): bool {.inline.} =
    let p = addr state.pairs[pi]
    if state.coordVals[p.a] != state.coordVals[p.b] + 1:
        return false
    return not state.pairExempt(pi)

func removeFromCoordIndex[T](state: AdjacencyEqualConstraint[T], item: int32, coord: T) {.inline.} =
    state.itemsAtCoord.withValue(coord, entry):
        for k in 0..<entry[].len:
            if entry[][k] == item:
                entry[].del(k)  # order-irrelevant swap-remove
                break

func initialize*[T](state: AdjacencyEqualConstraint[T], assignment: seq[T]) =
    state.currentAssignment.clear()
    for pos in state.coordEntries.keys:
        state.currentAssignment[pos] = assignment[pos]
    for pos in state.labelEntries.keys:
        state.currentAssignment[pos] = assignment[pos]
    state.itemsAtCoord.clear()
    for i in 0..<state.items.len:
        var c = state.items[i].constant
        for k in 0..<state.items[i].positions.len:
            c += state.items[i].coeffs[k] * assignment[state.items[i].positions[k]]
        state.coordVals[i] = c
        state.itemsAtCoord.mgetOrPut(c, @[]).add(int32(i))
    state.cost = 0
    for pi in 0..<state.pairs.len:
        state.violated[pi] = state.pairViolatedNow(int32(pi))
        if state.violated[pi]:
            inc state.cost

iterator candidatePairsAt[T](state: AdjacencyEqualConstraint[T], item: int32, coord: T): int32 =
    ## Pairs involving `item` that can be violated while `item` sits at `coord`:
    ## (item, j) with j at coord-1 and (j, item) with j at coord+1.
    state.itemsAtCoord.withValue(coord - 1, below):
        for j in below[]:
            for pi in state.pairIdxs(item, j):
                yield pi
    state.itemsAtCoord.withValue(coord + 1, above):
        for j in above[]:
            for pi in state.pairIdxs(j, item):
                yield pi

func refreshPair[T](state: AdjacencyEqualConstraint[T], pi: int32) {.inline.} =
    let nowViolated = state.pairViolatedNow(pi)
    if nowViolated != state.violated[pi]:
        state.violated[pi] = nowViolated
        if nowViolated: inc state.cost else: dec state.cost

func updatePosition*[T](state: AdjacencyEqualConstraint[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment.getOrDefault(position, T(0))
    if newValue == oldValue and position in state.currentAssignment:
        return
    state.currentAssignment[position] = newValue

    state.coordEntries.withValue(position, entries):
        let delta = newValue - oldValue
        # Items are moved one at a time; refreshPair always reads the live
        # coordVals/index, so shared-position multi-item moves stay consistent.
        for entry in entries[]:
            let i = entry.item
            let oldCoord = state.coordVals[i]
            let newCoord = oldCoord + entry.coeff * delta
            if newCoord == oldCoord: continue
            # Clear violations that involved the old placement
            for pi in state.candidatePairsAt(i, oldCoord):
                if state.violated[pi]:
                    state.violated[pi] = false
                    dec state.cost
            state.removeFromCoordIndex(i, oldCoord)
            state.coordVals[i] = newCoord
            state.itemsAtCoord.mgetOrPut(newCoord, @[]).add(i)
            for pi in state.candidatePairsAt(i, newCoord):
                state.refreshPair(pi)

    state.labelEntries.withValue(position, pis):
        for pi in pis[]:
            state.refreshPair(pi)

func computeMoveDelta[T](state: AdjacencyEqualConstraint[T],
                         position: int, oldValue, newValue: T): int =
    ## Non-mutating delta. Collects the small set of pairs whose status can
    ## change, then evaluates each once against the hypothetical assignment.
    ## Uses per-constraint scratch buffers — no allocation in steady state.
    let valueDelta = newValue - oldValue
    state.scratchAffected.setLen(0)
    state.scratchCandidates.setLen(0)

    state.coordEntries.withValue(position, entries):
        for entry in entries[]:
            let nc = state.coordVals[entry.item] + entry.coeff * valueDelta
            if nc != state.coordVals[entry.item]:
                state.scratchAffected.add((item: entry.item, newCoord: nc))

    template addCandidate(pi: int32) =
        if pi notin state.scratchCandidates:
            state.scratchCandidates.add(pi)
    for (i, newCoord) in state.scratchAffected.items:
        for pi in state.candidatePairsAt(i, state.coordVals[i]):
            addCandidate(pi)
        for pi in state.candidatePairsAt(i, newCoord):
            addCandidate(pi)
        # Pairs among affected items are not necessarily in the index
        # neighborhoods scanned above (both endpoints move); check directly.
        for (j, _) in state.scratchAffected.items:
            for pi in state.pairIdxs(i, j):
                addCandidate(pi)
            for pi in state.pairIdxs(j, i):
                addCandidate(pi)
    state.labelEntries.withValue(position, pis):
        for pi in pis[]:
            addCandidate(pi)

    if state.scratchCandidates.len == 0:
        return 0

    result = 0
    for pi in state.scratchCandidates:
        let p = addr state.pairs[pi]
        var coordA = state.coordVals[p.a]
        var coordB = state.coordVals[p.b]
        for (i, newCoord) in state.scratchAffected.items:
            if i == p.a: coordA = newCoord
            if i == p.b: coordB = newCoord
        var newViolated = false
        if coordA == coordB + 1:
            if p.labelPositions.len == 0:
                newViolated = true
            else:
                var s: T = 0
                for k in 0..<p.labelPositions.len:
                    let lp = p.labelPositions[k]
                    let v = if lp == position: newValue
                            else: state.currentAssignment.getOrDefault(lp, T(0))
                    s += p.labelCoeffs[k] * v
                newViolated = s != p.labelRhs
        if newViolated != state.violated[pi]:
            result += (if newViolated: 1 else: -1)

func moveDelta*[T](state: AdjacencyEqualConstraint[T],
                   position: int, oldValue, newValue: T): int {.inline.} =
    if newValue == oldValue: return 0
    if position notin state.coordEntries and position notin state.labelEntries:
        return 0
    state.computeMoveDelta(position, oldValue, newValue)

proc batchMovePenalty*[T](state: AdjacencyEqualConstraint[T],
                          position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    ## Penalty deltas (relative to current cost) for all domain values.
    result = newSeq[int](domain.len)
    if position notin state.coordEntries and position notin state.labelEntries:
        return
    for i in 0..<domain.len:
        if domain[i] != currentValue:
            result[i] = state.computeMoveDelta(position, currentValue, domain[i])

proc deepCopy*[T](state: AdjacencyEqualConstraint[T]): AdjacencyEqualConstraint[T] =
    new(result)
    result.items = state.items
    result.pairs = state.pairs
    result.firstPair = state.firstPair
    result.nextSamePair = state.nextSamePair
    result.coordEntries = state.coordEntries
    result.labelEntries = state.labelEntries
    result.coordVals = state.coordVals
    result.itemsAtCoord = state.itemsAtCoord
    result.violated = state.violated
    result.cost = state.cost
    result.currentAssignment = initTable[int, T]()
    for k, v in state.currentAssignment.pairs:
        result.currentAssignment[k] = v
