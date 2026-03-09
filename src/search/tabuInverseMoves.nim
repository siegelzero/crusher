## Inverse group compound move support.
## Included from tabu.nim — not a standalone module.

proc computeInverseForcedChanges[T](state: TabuState[T], position: int, newValue: T, oldValue: T = T(0), oldValueProvided: bool = false) =
    ## Compute the 3 forced changes for assigning newValue at position within an inverse group.
    ## Populates state.inverseForcedChanges with (pos, oldVal, newVal) triples.
    ## Does NOT modify the assignment.
    ## If oldValueProvided is true, uses oldValue instead of reading assignment[position].
    state.inverseForcedChanges.setLen(0)
    let gi = state.posToInverseGroup[position]
    let group = state.inverseGroups[gi]
    let offset = group.valueOffset
    let localIdx = state.posToGroupLocalIdx[position]  # i

    let prevValue = if oldValueProvided: oldValue else: state.assignment[position]
    let newJ = int(newValue) + offset   # new partner local index
    let oldJ = int(prevValue) + offset   # old partner local index

    if newJ == localIdx:
        # Assigning self-match (fixed point). Old partner becomes unpaired.
        # Old partner oldJ needs a new value. Set it to itself (fixed point).
        if oldJ != localIdx and oldJ >= 0 and oldJ < group.positions.len:
            let partnerPos = group.positions[oldJ]
            let partnerOld = state.assignment[partnerPos]
            let partnerNew = T(oldJ - offset)  # self-match
            if partnerOld != partnerNew:
                state.inverseForcedChanges.add((partnerPos, int(partnerOld), int(partnerNew)))
    elif oldJ == localIdx:
        # Was a fixed point, now pairing with newJ.
        # newJ's old partner needs to become a fixed point.
        if newJ >= 0 and newJ < group.positions.len:
            let newPartnerPos = group.positions[newJ]
            let newPartnerOld = state.assignment[newPartnerPos]
            # Set newJ to point back to us
            let newPartnerNew = T(localIdx - offset)
            if newPartnerOld != newPartnerNew:
                state.inverseForcedChanges.add((newPartnerPos, int(newPartnerOld), int(newPartnerNew)))
                # newJ's old partner (if not us and not itself) becomes a fixed point
                let newPartnerOldIdx = int(newPartnerOld) + offset
                if newPartnerOldIdx != newJ and newPartnerOldIdx != localIdx and
                   newPartnerOldIdx >= 0 and newPartnerOldIdx < group.positions.len:
                    let thirdPos = group.positions[newPartnerOldIdx]
                    let thirdOld = state.assignment[thirdPos]
                    let thirdNew = T(newPartnerOldIdx - offset)  # self-match
                    if thirdOld != thirdNew:
                        state.inverseForcedChanges.add((thirdPos, int(thirdOld), int(thirdNew)))
    else:
        # General case: was paired with oldJ, now pairing with newJ.
        # Need: position[newJ] → localIdx, position[oldJ] → old_partner_of_newJ
        if newJ >= 0 and newJ < group.positions.len and
           oldJ >= 0 and oldJ < group.positions.len:
            let newPartnerPos = group.positions[newJ]
            let oldPartnerPos = group.positions[oldJ]
            let newPartnerOld = state.assignment[newPartnerPos]
            let newPartnerOldIdx = int(newPartnerOld) + offset  # who newJ was pointing to

            # newJ now points to us (localIdx)
            let newPartnerNew = T(localIdx - offset)
            if newPartnerOld != newPartnerNew:
                state.inverseForcedChanges.add((newPartnerPos, int(newPartnerOld), int(newPartnerNew)))

            # oldJ now points to newJ's old partner (completing the swap)
            let oldPartnerOld = state.assignment[oldPartnerPos]
            if newPartnerOldIdx >= 0 and newPartnerOldIdx < group.positions.len and
               newPartnerOldIdx != localIdx and newPartnerOldIdx != newJ:
                let oldPartnerNew = T(newPartnerOldIdx - offset)
                if oldPartnerOld != oldPartnerNew:
                    state.inverseForcedChanges.add((oldPartnerPos, int(oldPartnerOld), int(oldPartnerNew)))
                # newJ's old partner now points to oldJ
                if newPartnerOldIdx != oldJ:
                    let thirdPos = group.positions[newPartnerOldIdx]
                    let thirdOld = state.assignment[thirdPos]
                    let thirdNew = T(oldJ - offset)
                    if thirdOld != thirdNew:
                        state.inverseForcedChanges.add((thirdPos, int(thirdOld), int(thirdNew)))
            else:
                # newJ was pointing to localIdx (meaning newJ was our "new" partner already)
                # oldJ just needs to become a fixed point
                let oldPartnerNew = T(oldJ - offset)
                if oldPartnerOld != oldPartnerNew:
                    state.inverseForcedChanges.add((oldPartnerPos, int(oldPartnerOld), int(oldPartnerNew)))


proc computeInverseDeltaAt[T](state: TabuState[T], position: int, candidateValue: T): int =
    ## Compute the cost delta from the forced changes of an inverse group compound move
    ## at the given position with candidateValue.
    ## Uses movePenalty at each forced position (independent of primary position changes).
    state.computeInverseForcedChanges(position, candidateValue)
    for (fPos, fOld, fNew) in state.inverseForcedChanges:
        for constraint in state.constraintsAtPosition[fPos]:
            result += state.movePenalty(constraint, fPos, T(fNew))


proc recomputeAllInverseDeltas[T](state: TabuState[T]) =
    ## Recompute inverseDelta[pos][domainIdx] for all inverse group positions.
    ## Used only during initialization.
    for group in state.inverseGroups:
        for pos in group.positions:
            if pos in state.carray.channelPositions:
                continue
            if state.isLazy[pos]:
                continue
            let domain = state.sharedDomain[][pos]
            for i in 0..<domain.len:
                state.inverseDelta[pos][i] = state.computeInverseDeltaAt(pos, domain[i])


proc recomputeInverseDeltasTargeted[T](state: TabuState[T],
                                        movedPosition: int,
                                        localForced: openArray[(int, int, int)]) =
    ## Targeted recomputation of inverseDelta after an inverse group move.
    ## Only recomputes entries within the moved group that could have changed:
    ##   - Changed positions (primary + forced): full domain recompute
    ##   - Positions whose current partner is a changed position: full recompute
    ##   - Other positions: only domain values mapping to a changed local index
    let gi = state.posToInverseGroup[movedPosition]
    let group = state.inverseGroups[gi]
    let offset = group.valueOffset

    # Collect changed local indices (primary + forced positions)
    var changedLocalIdxs: PackedSet[int]
    changedLocalIdxs.incl(state.posToGroupLocalIdx[movedPosition])
    for (fPos, _, _) in localForced:
        if state.posToGroupLocalIdx[fPos] >= 0:
            changedLocalIdxs.incl(state.posToGroupLocalIdx[fPos])

    for pos in group.positions:
        if pos in state.carray.channelPositions:
            continue
        if state.isLazy[pos]:
            continue
        let domain = state.sharedDomain[][pos]
        let localIdx = state.posToGroupLocalIdx[pos]
        let oldJ = int(state.assignment[pos]) + offset

        if localIdx in changedLocalIdxs or oldJ in changedLocalIdxs:
            # This position's assignment changed, or its partner's assignment changed
            # → full recompute since forced changes depend on both
            for i in 0..<domain.len:
                state.inverseDelta[pos][i] = state.computeInverseDeltaAt(pos, domain[i])
        else:
            # Only recompute the few domain values whose candidate maps to a changed position.
            # Convert changed local indices → domain values → domain indices via domainIndex.
            for cl in changedLocalIdxs.items:
                let targetValue = T(cl - offset)
                let domIdx = state.domainIndex[pos].getOrDefault(targetValue, -1)
                if domIdx >= 0:
                    state.inverseDelta[pos][domIdx] = state.computeInverseDeltaAt(pos, targetValue)


proc initInverseStructures[T](state: TabuState[T]) =
    ## Initialize inverse group compound move structures.
    state.inverseEnabled = false
    state.inverseGroups = state.carray.inverseGroups
    state.posToInverseGroup = newSeq[int](state.carray.len)
    state.posToGroupLocalIdx = newSeq[int](state.carray.len)
    for i in 0..<state.carray.len:
        state.posToInverseGroup[i] = -1
        state.posToGroupLocalIdx[i] = -1
    state.inverseForcedChanges = @[]
    state.inverseSavedBuf = @[]
    state.forcedChannelsBuf2 = @[]

    if state.inverseGroups.len == 0:
        return

    state.inverseEnabled = true

    # Build position lookup tables (flat arrays for O(1) access in hot paths)
    for gi, group in state.inverseGroups:
        for li, pos in group.positions:
            state.posToInverseGroup[pos] = gi
            state.posToGroupLocalIdx[pos] = li

    # Allocate inverseDelta arrays for inverse group positions
    state.inverseDelta = newSeq[seq[int]](state.carray.len)
    for group in state.inverseGroups:
        for pos in group.positions:
            if pos in state.carray.channelPositions:
                continue
            if state.isLazy[pos]:
                continue
            let dsize = state.sharedDomain[][pos].len
            state.inverseDelta[pos] = newSeq[int](dsize)

    # Compute initial inverse deltas
    state.recomputeAllInverseDeltas()

    if state.verbose and state.id == 0:
        var totalPositions = 0
        for group in state.inverseGroups:
            totalPositions += group.positions.len
        echo "[Init] Inverse groups: " & $state.inverseGroups.len &
             " groups, " & $totalPositions & " positions"
