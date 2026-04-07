## ConjunctSumAtMost Constraint Implementation
## ============================================
##
## Counts how many "conjunct groups" of positions have ALL members equal to a
## target value, with an at-most bound on that count.
##
## **Constraint Definition**:
## `|{ g ∈ groups : ∀ p ∈ g . assignment[p] = targetValue }| ≤ maxOccurrences`
##
## This is the position-based, dispatch-light version of:
##   atMost([ a_11 * a_12 * ... , a_21 * a_22 * ... , ... ], 1, maxOccurrences)
## (when each factor is a binary 0/1 variable).
##
## **Layout**:
## A first pass through the constructor assigns each unique absolute position a
## *local index* in `[0, nLocal)`. All hot-path lookups go through dense seqs
## indexed by this local index — no `Table[int, …]` lookups in the inner loop.
##
## - `localToPosition[li]`: local index → absolute position (only used by
##   `initialize` and `getAffectedPositions`).
## - `positionToLocal[abs]`: absolute → local. Touched once at the entry of
##   `moveDelta` / `updatePosition` to translate the caller's `position`.
## - `localAssignment[li]`: cached current value at each local index. Replaces
##   the previous `Table[int, T] currentAssignment` and is the dominant access
##   inside the truth-recompute inner loop.
## - `groupOffsets[i .. i+1]`: slice into `groupLocalPositions` for group `i`.
## - `groupLocalPositions`: concatenated lists of *local indices* (not absolute
##   positions) for every group.
## - `groupTruth[i]`: 1 if every position in group `i` currently equals
##   `targetValue`, else 0. `actualOccurrences = sum(groupTruth)`.
## - `groupsAtLocal[li]`: precomputed list of group indices that contain local
##   index `li`. Used to walk the small set of affected groups when one position
##   changes.
##
## **Performance**:
## - `moveDelta`: one Table lookup at entry, then dense-seq accesses only.
##   For binary groups (size 2) the inner loop is two array reads + a compare.
## - `initialize`: O(nLocal + total group sizes).
## - Cost: max(0, actualOccurrences - maxOccurrences).

import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    ConjunctSumAtMostConstraint*[T] = ref object
        targetValue*: T
        maxOccurrences*: int
        actualOccurrences*: int
        cost*: int
        lastOldOccurrences*: int
        lastNewOccurrences*: int

        # Local-index storage (the hot path uses these exclusively)
        nLocal*: int
        localToPosition*: seq[int]      # local index → absolute position
        positionToLocal*: Table[int, int]  # absolute → local (entry point only)
        localAssignment*: seq[T]        # local index → current value
        groupsAtLocal*: seq[seq[int]]   # local index → group indices containing it

        # Group storage (CSR), keyed by local indices
        groupOffsets*: seq[int]         # length numGroups + 1
        groupLocalPositions*: seq[int]  # concatenated local-index lists
        groupTruth*: seq[uint8]         # 1 if group's conjunction holds

        # Union of all referenced *absolute* positions, used by the system to
        # track which positions this constraint touches.
        positions*: PackedSet[int]

################################################################################
# Construction
################################################################################

func newConjunctSumAtMostConstraint*[T](groups: seq[seq[int]],
                                        targetValue: T,
                                        maxOccurrences: int): ConjunctSumAtMostConstraint[T] =
    ## `groups[i]` is the list of *absolute* positions whose conjunction we count.
    new(result)
    result = ConjunctSumAtMostConstraint[T](
        targetValue: targetValue,
        maxOccurrences: maxOccurrences,
        actualOccurrences: 0,
        cost: 0,
        positionToLocal: initTable[int, int]()
    )

    # Pass 1: Assign local indices to each unique absolute position.
    for g in groups:
        for p in g:
            if p notin result.positionToLocal:
                let li = result.localToPosition.len
                result.positionToLocal[p] = li
                result.localToPosition.add(p)
                result.positions.incl(p)
    result.nLocal = result.localToPosition.len
    result.localAssignment = newSeq[T](result.nLocal)
    result.groupsAtLocal = newSeq[seq[int]](result.nLocal)

    # Pass 2: Materialise the CSR group store with local indices.
    result.groupOffsets = newSeq[int](groups.len + 1)
    var totalLen = 0
    for g in groups:
        totalLen += g.len
    result.groupLocalPositions = newSeq[int](totalLen)
    result.groupTruth = newSeq[uint8](groups.len)
    var cursor = 0
    for gi, g in groups:
        result.groupOffsets[gi] = cursor
        for p in g:
            let li = result.positionToLocal[p]
            result.groupLocalPositions[cursor] = li
            inc cursor
            result.groupsAtLocal[li].add(gi)
    result.groupOffsets[groups.len] = cursor

################################################################################
# Initialization & updates
################################################################################

proc initialize*[T](state: ConjunctSumAtMostConstraint[T], assignment: seq[T]) =
    ## Cache current values for every referenced position and tally the initial cost.
    state.actualOccurrences = 0
    for li in 0 ..< state.nLocal:
        state.localAssignment[li] = assignment[state.localToPosition[li]]
    let nGroups = state.groupTruth.len
    let target = state.targetValue
    for gi in 0 ..< nGroups:
        let gStart = state.groupOffsets[gi]
        let gEnd = state.groupOffsets[gi + 1]
        var allMatch: uint8 = 1
        for k in gStart ..< gEnd:
            if state.localAssignment[state.groupLocalPositions[k]] != target:
                allMatch = 0
                break
        state.groupTruth[gi] = allMatch
        if allMatch == 1:
            inc state.actualOccurrences
    state.cost = max(0, state.actualOccurrences - state.maxOccurrences)
    state.lastOldOccurrences = state.actualOccurrences
    state.lastNewOccurrences = state.actualOccurrences

proc updatePosition*[T](state: ConjunctSumAtMostConstraint[T], position: int, newValue: T) =
    ## Apply an assignment change in place.
    state.lastOldOccurrences = state.actualOccurrences
    let localOfPos = state.positionToLocal.getOrDefault(position, -1)
    if localOfPos < 0:
        state.lastNewOccurrences = state.actualOccurrences
        return
    let oldValue = state.localAssignment[localOfPos]
    if oldValue != newValue:
        state.localAssignment[localOfPos] = newValue
        let target = state.targetValue
        for gi in state.groupsAtLocal[localOfPos]:
            let oldTruth = state.groupTruth[gi]
            let gStart = state.groupOffsets[gi]
            let gEnd = state.groupOffsets[gi + 1]
            var newTruth: uint8 = 1
            for k in gStart ..< gEnd:
                if state.localAssignment[state.groupLocalPositions[k]] != target:
                    newTruth = 0
                    break
            if newTruth != oldTruth:
                state.groupTruth[gi] = newTruth
                if newTruth == 1:
                    inc state.actualOccurrences
                else:
                    dec state.actualOccurrences
        state.cost = max(0, state.actualOccurrences - state.maxOccurrences)
    state.lastNewOccurrences = state.actualOccurrences

proc moveDelta*[T](state: ConjunctSumAtMostConstraint[T], position: int, oldValue, newValue: T): int =
    ## Cost change if `position` were assigned `newValue` (without mutating state).
    ##
    ## A position change can only flip a group's truth in one direction at a time:
    ##   - If `oldValue == target`, then groups with `oldTruth == 1` are exactly the
    ##     groups that contain *only* target values, and any `newValue != target`
    ##     flips each of them to 0. Other groups (oldTruth = 0) stay at 0 because
    ##     they were already broken by some position other than this one.
    ##   - If `oldValue != target`, then every group containing this position has
    ##     `oldTruth == 0` (since this position breaks the conjunction). Setting
    ##     `newValue == target` flips a group to 1 iff every *other* position in
    ##     the group is already at target. Other `newValue != target` choices
    ##     keep every group at 0.
    ##
    ## So a single integer `changeCount` summarises the effect of *any* value
    ## flip away from `oldValue` — subtract it (leave-target case) or add it
    ## (enter-target case). This is the same observation `batchMovePenalty`
    ## exploits to evaluate the entire domain in O(group degree).
    if oldValue == newValue:
        return 0
    let localOfPos = state.positionToLocal.getOrDefault(position, -1)
    if localOfPos < 0:
        return 0
    let target = state.targetValue
    let curIsTarget = oldValue == target
    let newIsTarget = newValue == target
    var changeCount = 0
    if curIsTarget:
        # Leaving target: count groups currently all-target (truth=1).
        for gi in state.groupsAtLocal[localOfPos]:
            if state.groupTruth[gi] == 1:
                inc changeCount
    elif newIsTarget:
        # Entering target: count groups where every other factor is already target.
        for gi in state.groupsAtLocal[localOfPos]:
            let gStart = state.groupOffsets[gi]
            let gEnd = state.groupOffsets[gi + 1]
            var otherAllTarget = true
            for k in gStart ..< gEnd:
                let lp = state.groupLocalPositions[k]
                if lp == localOfPos: continue
                if state.localAssignment[lp] != target:
                    otherAllTarget = false
                    break
            if otherAllTarget:
                inc changeCount
    else:
        # Non-target → non-target: every group stays at truth = 0.
        return 0
    let deltaOcc =
        if curIsTarget: -changeCount
        else: changeCount
    let newActualOccurrences = state.actualOccurrences + deltaOcc
    let newCost = max(0, newActualOccurrences - state.maxOccurrences)
    return newCost - state.cost

proc batchMovePenalty*[T](state: ConjunctSumAtMostConstraint[T], position: int,
                          currentValue: T, domain: seq[T]): seq[int] =
    ## Compute the cost-delta for every domain value at `position` in one pass.
    ##
    ## Walks `groupsAtLocal[localOfPos]` exactly once, computes the single
    ## `changeCount` integer that drives every domain entry's delta, then fills
    ## the result array in a tight loop. Per-call work is `O(group degree)`
    ## *plus* `O(domain size)`, instead of the per-value `O(degree)` that
    ## individual `moveDelta` calls produce. For 36-degree constraints with a
    ## binary domain that's a ~36× reduction in inner-loop work for the same
    ## information.
    result = newSeq[int](domain.len)
    let localOfPos = state.positionToLocal.getOrDefault(position, -1)
    if localOfPos < 0:
        return  # constraint doesn't reference this position; all deltas are 0

    let target = state.targetValue
    let curIsTarget = currentValue == target

    # Compute changeCount once. The semantics mirror moveDelta:
    #   - curIsTarget: # groups currently all-target (will be broken by leaving target)
    #   - !curIsTarget: # groups whose other factors are all target (would complete on entering target)
    var changeCount = 0
    if curIsTarget:
        for gi in state.groupsAtLocal[localOfPos]:
            if state.groupTruth[gi] == 1:
                inc changeCount
    else:
        for gi in state.groupsAtLocal[localOfPos]:
            let gStart = state.groupOffsets[gi]
            let gEnd = state.groupOffsets[gi + 1]
            var otherAllTarget = true
            for k in gStart ..< gEnd:
                let lp = state.groupLocalPositions[k]
                if lp == localOfPos: continue
                if state.localAssignment[lp] != target:
                    otherAllTarget = false
                    break
            if otherAllTarget:
                inc changeCount

    let curActual = state.actualOccurrences
    let curCost = state.cost
    let maxOcc = state.maxOccurrences

    # Precompute the two possible cost deltas. Every domain value's penalty
    # is one of these (or 0 for the keep-current case):
    #   - leave-target case: cur == target, and ANY v != cur is also != target,
    #     so it always uses `leaveCostDelta`.
    #   - enter-target case: cur != target, and v == target uses `enterCostDelta`,
    #     while v != target (and v != cur) is a no-op (delta 0).
    let leaveCostDelta = max(0, curActual - changeCount - maxOcc) - curCost
    let enterCostDelta = max(0, curActual + changeCount - maxOcc) - curCost

    if curIsTarget:
        for i in 0 ..< domain.len:
            if domain[i] == currentValue:
                result[i] = 0
            else:
                result[i] = leaveCostDelta
    else:
        for i in 0 ..< domain.len:
            let v = domain[i]
            if v == currentValue:
                result[i] = 0
            elif v == target:
                result[i] = enterCostDelta
            else:
                result[i] = 0

proc getAffectedPositions*[T](state: ConjunctSumAtMostConstraint[T]): PackedSet[int] =
    ## Mirrors AtMost: only return positions when the at-most boundary was crossed.
    let old = state.lastOldOccurrences
    let new2 = state.lastNewOccurrences
    if old == new2:
        return initPackedSet[int]()
    let maxOcc = state.maxOccurrences
    let addMarginalChanged = (old < maxOcc) != (new2 < maxOcc)
    let removeMarginalChanged = (old <= maxOcc) != (new2 <= maxOcc)
    if not addMarginalChanged and not removeMarginalChanged:
        return initPackedSet[int]()
    return state.positions

proc getAffectedDomainValues*[T](state: ConjunctSumAtMostConstraint[T], position: int): seq[T] =
    ## Returns @[] (all values), routing the consumer through the
    ## `updateConstraintAtPosition` → `batchMovePenalty` path. The batch path
    ## reuses a single `O(group degree)` walk for the entire domain, which is
    ## strictly cheaper than the per-value `updateConstraintAtPositionValues`
    ## path even when the latter would only need to visit one value.
    return @[]

proc deepCopy*[T](state: ConjunctSumAtMostConstraint[T]): ConjunctSumAtMostConstraint[T] =
    ## Independent copy for parallel worker isolation. The local-index layout is
    ## immutable post-construction, so we share its conceptual content via fresh
    ## copies. Live state (`actualOccurrences`, `cost`, `groupTruth`,
    ## `localAssignment`) is reset; the copy is ready for a fresh `initialize`.
    new(result)
    result = ConjunctSumAtMostConstraint[T](
        targetValue: state.targetValue,
        maxOccurrences: state.maxOccurrences,
        actualOccurrences: 0,
        cost: 0,
        nLocal: state.nLocal,
        positionToLocal: initTable[int, int]()
    )
    result.localToPosition = state.localToPosition
    result.localAssignment = newSeq[T](state.nLocal)
    result.groupsAtLocal = state.groupsAtLocal
    result.groupOffsets = state.groupOffsets
    result.groupLocalPositions = state.groupLocalPositions
    result.groupTruth = newSeq[uint8](state.groupTruth.len)
    result.positions = state.positions
    for k, v in state.positionToLocal.pairs:
        result.positionToLocal[k] = v
