## Channel-dependent constraint penalty routines.
## Included from tabu.nim — not a standalone module.

type LinearTerm[T] = tuple[pos: int, coeff: T]

proc tryExtractLinear[T](node: ExpressionNode[T]): tuple[ok: bool, terms: seq[LinearTerm[T]], offset: T] =
    ## Recursively decompose an expression tree into sum(coeff_i * assignment[pos_i]) + offset.
    ## Non-linear subtrees (min/max/abs) are only treated as constants when their
    ## children are purely constant (no variable references). If they depend on
    ## variables, we return ok=false so the entire input expression falls through
    ## to complexExprs for correct runtime evaluation.
    case node.kind
    of LiteralNode:
        return (true, @[], node.value)
    of RefNode:
        return (true, @[(pos: node.position, coeff: T(1))], T(0))
    of BinaryOpNode:
        case node.binaryOp
        of Addition:
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            return (true, lterms & rterms, loff + roff)
        of Subtraction:
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            var negTerms = newSeq[LinearTerm[T]](rterms.len)
            for i, t in rterms: negTerms[i] = (pos: t.pos, coeff: -t.coeff)
            return (true, lterms & negTerms, loff - roff)
        of Multiplication:
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            if lterms.len == 0 and rterms.len == 0:
                return (true, @[], loff * roff)
            if lterms.len == 0:
                var scaled = newSeq[LinearTerm[T]](rterms.len)
                for i, t in rterms: scaled[i] = (pos: t.pos, coeff: loff * t.coeff)
                return (true, scaled, loff * roff)
            if rterms.len == 0:
                var scaled = newSeq[LinearTerm[T]](lterms.len)
                for i, t in lterms: scaled[i] = (pos: t.pos, coeff: roff * t.coeff)
                return (true, scaled, roff * loff)
            return (false, @[], T(0))
        of Maximum, Minimum:
            # Only fold as constant if both children are purely constant (no terms).
            # Otherwise the result depends on variable values and would go stale.
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            if lterms.len == 0 and rterms.len == 0:
                let v = if node.binaryOp == Maximum: max(loff, roff) else: min(loff, roff)
                return (true, @[], v)
            return (false, @[], T(0))
    of UnaryOpNode:
        if node.unaryOp == Negation:
            let (ok, terms, off) = tryExtractLinear[T](node.target)
            if ok:
                var negTerms = newSeq[LinearTerm[T]](terms.len)
                for i, t in terms: negTerms[i] = (pos: t.pos, coeff: -t.coeff)
                return (true, negTerms, -off)
        elif node.unaryOp == AbsoluteValue:
            # Only fold as constant if the child is purely constant (no terms).
            let (ok, terms, off) = tryExtractLinear[T](node.target)
            if ok and terms.len == 0:
                return (true, @[], abs(off))
        return (false, @[], T(0))

proc evaluateFlatMinMax[T](fb: FlatMinMaxBinding[T], assignment: seq[T]): T {.inline.} =
    ## Evaluate a min/max channel binding using flat data (no tree traversal).
    let nInputs = fb.linearOffsets.len
    if fb.isMin:
        result = if fb.hasConstant: fb.constantVal else: high(T)
        for i in 0..<nInputs:
            var v = fb.linearOffsets[i]
            let start = fb.inputBounds[i]
            let stop = if i + 1 < nInputs: fb.inputBounds[i + 1] else: fb.linearPositions.len
            for j in start..<stop:
                v += fb.linearCoeffs[j] * assignment[fb.linearPositions[j]]
            if v < result: result = v
        for expr in fb.complexExprs:
            let v = expr.evaluate(assignment)
            if v < result: result = v
    else:
        result = if fb.hasConstant: fb.constantVal else: low(T)
        for i in 0..<nInputs:
            var v = fb.linearOffsets[i]
            let start = fb.inputBounds[i]
            let stop = if i + 1 < nInputs: fb.inputBounds[i + 1] else: fb.linearPositions.len
            for j in start..<stop:
                v += fb.linearCoeffs[j] * assignment[fb.linearPositions[j]]
            if v > result: result = v
        for expr in fb.complexExprs:
            let v = expr.evaluate(assignment)
            if v > result: result = v

proc evaluateCountEq[T](binding: CountEqChannelBinding[T], assignment: seq[T]): T {.inline.} =
    ## Evaluate a count-equals channel: constantOffset + count of positions where assignment equals targetValue.
    var count: T = binding.constantOffset
    for p in binding.inputPositions:
        if assignment[p] == binding.targetValue:
            inc count
    count

proc trackChannelChange[T](state: TabuState[T], chanPos: int, newChanVal: T) {.inline.} =
    ## Record a channel position change using position-indexed tracking.
    ## Saves original value on first change; cdDirtyPositions stays deduplicated.
    if not state.cdIsChanged[chanPos]:
        state.cdSavedVal[chanPos] = state.assignment[chanPos]
        state.cdIsChanged[chanPos] = true
        state.cdDirtyPositions.add(chanPos)
    state.assignment[chanPos] = newChanVal

proc computeChannelDepDelta[T](state: TabuState[T], pos: int, candidateValue: T): int =
    ## Compute the total penalty delta from channel-dep constraints if we were
    ## to assign candidateValue at pos. Simulates channel propagation via worklist,
    ## then uses precomputed coefficient arrays for fast arithmetic (no hash table
    ## lookups), falling back to simulate-restore for other constraint types.
    if pos notin state.carray.channelsAtPosition and
       pos notin state.carray.minMaxChannelsAtPosition and
       pos notin state.carray.countEqChannelsAtPosition and
       pos notin state.carray.inverseChannelsAtPosition:
        return 0

    # Fast path: use precomputed (static) cascade table for single-value lookup
    if pos in state.cdCascadePos:
        let cascadeIdx = state.cdCascadePos[pos]
        if state.cdCascadeIsStatic[cascadeIdx]:
            let di = state.domainIndex[pos].getOrDefault(candidateValue, -1)
            if di < 0: return 0
            let chans = state.cdCascadeChans[cascadeIdx]
            let chanVals = state.cdCascadeValues[cascadeIdx]
            let constraintIds = state.cdCascadeConstraintIds[cascadeIdx]
            let coeffsL = state.cdCascadeConstraintL[cascadeIdx]
            let coeffsR = state.cdCascadeConstraintR[cascadeIdx]
            let nChans = chans.len
            for cli in 0..<constraintIds.len:
                let ci = constraintIds[cli]
                var delta: int
                if state.cdConstraintCanFast[ci]:
                    let rc = state.channelDepConstraints[ci].relationalState
                    var newLeft = rc.leftValue
                    var newRight = rc.rightValue
                    for (cascIdx, coeff) in coeffsL[cli]:
                        let diff = chanVals[cascIdx][di] - state.assignment[chans[cascIdx]]
                        if diff != 0:
                            newLeft += coeff * diff
                    for (cascIdx, coeff) in coeffsR[cli]:
                        let diff = chanVals[cascIdx][di] - state.assignment[chans[cascIdx]]
                        if diff != 0:
                            newRight += coeff * diff
                    delta = rc.computeCost(newLeft, newRight) - rc.cost
                else:
                    let c = state.channelDepConstraints[ci]
                    let oldPenalty = c.penalty()
                    var anyChanged = false
                    for chanIdx in 0..<nChans:
                        let chanPos = chans[chanIdx]
                        let newVal = chanVals[chanIdx][di]
                        if newVal != state.assignment[chanPos] and chanPos in c.positions:
                            c.updatePosition(chanPos, newVal)
                            anyChanged = true
                    if anyChanged:
                        delta = c.penalty() - oldPenalty
                        for chanIdx in 0..<nChans:
                            let chanPos = chans[chanIdx]
                            if chanVals[chanIdx][di] != state.assignment[chanPos] and chanPos in c.positions:
                                c.updatePosition(chanPos, state.assignment[chanPos])
                    else:
                        delta = 0
                result += delta
                if state.cdTrackPerConstraint and delta != 0:
                    state.cdPerConstraintMaxDelta[ci] = max(state.cdPerConstraintMaxDelta[ci], abs(delta))
            return result

    assert not state.cdInUse, "computeChannelDepDelta is not reentrant"
    state.cdInUse = true
    defer: state.cdInUse = false

    # Clear reusable buffers from previous call
    state.cdVisited.clear()
    # cdDirtyPositions and cdIsChanged are already clean from previous call's restore
    when ProfileIteration:
        state.cdWorklistEntryCalls += 1
        let cdCallStart = epochTime()
    let savedPos = state.assignment[pos]
    state.assignment[pos] = candidateValue

    # Apply inverse group forced changes for simulation
    state.inverseSavedBuf.setLen(0)
    if state.inverseEnabled and state.posToInverseGroup[pos] >= 0:
        state.computeInverseForcedChanges(pos, candidateValue, savedPos, oldValueProvided = true)
        for (fPos, fOld, fNew) in state.inverseForcedChanges:
            state.inverseSavedBuf.add((fPos, state.assignment[fPos]))
            state.assignment[fPos] = T(fNew)

    # Fast path for one-hot source positions: directly compute the few changes
    # instead of evaluating all bindings through the worklist
    if pos in state.oneHotChanges:
        let changes = state.oneHotChanges[pos]
        let lo = state.oneHotLo[pos]
        let oldIdx = savedPos - lo
        let newIdx = candidateValue - lo

        if oldIdx == newIdx:
            state.assignment[pos] = savedPos
            return 0

        # Source leaving oldIdx: channels at oldIdx transition away from their active value
        if oldIdx >= 0 and oldIdx < changes.len:
            for (chanPos, activeVal) in changes[oldIdx]:
                let toVal = T(1 - activeVal)
                if state.assignment[chanPos] != toVal:
                    state.trackChannelChange(chanPos, toVal)
        # Source entering newIdx: channels at newIdx transition to their active value
        if newIdx >= 0 and newIdx < changes.len:
            for (chanPos, activeVal) in changes[newIdx]:
                let toVal = T(activeVal)
                if state.assignment[chanPos] != toVal:
                    state.trackChannelChange(chanPos, toVal)

        # Propagate downstream from the changed channel positions
        state.cdWorklist.setLen(0)
        state.cdVisited.incl(pos)
        for chanPos in state.cdDirtyPositions:
            state.cdWorklist.add(chanPos)
            state.cdVisited.incl(chanPos)
        # Add inverse forced positions to the worklist for channel propagation
        for (fPos, savedVal) in state.inverseSavedBuf:
            if fPos notin state.cdVisited:
                state.cdVisited.incl(fPos)
                state.cdWorklist.add(fPos)

        while state.cdWorklist.len > 0:
            let p = state.cdWorklist.pop()
            if p in state.carray.channelsAtPosition:
                for bi in state.carray.channelsAtPosition[p]:
                    let bindingPtr = addr state.carray.channelBindings[bi]
                    let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                    if idxVal < 0 or idxVal >= bindingPtr.arrayElements.len: continue
                    let elem = bindingPtr.arrayElements[idxVal]
                    let newChanVal = if elem.isConstant: elem.constantValue
                                     else: state.assignment[elem.variablePosition]
                    let chanPos = bindingPtr.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.minMaxChannelsAtPosition:
                for bi in state.carray.minMaxChannelsAtPosition[p]:
                    let fb = state.flatMinMaxBindings[bi]
                    let newChanVal = evaluateFlatMinMax(fb, state.assignment)
                    let chanPos = fb.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.countEqChannelsAtPosition:
                for bi in state.carray.countEqChannelsAtPosition[p]:
                    let binding = state.carray.countEqChannelBindings[bi]
                    let newChanVal = evaluateCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.inverseChannelsAtPosition:
                for gi in state.carray.inverseChannelsAtPosition[p]:
                    let group = state.carray.inverseChannelGroups[gi]
                    let newInverse = group.recomputeInverse(state.assignment)
                    for j, ipos in group.inversePositions:
                        if newInverse[j] != state.assignment[ipos]:
                            state.trackChannelChange(ipos, newInverse[j])
                            if ipos notin state.cdVisited:
                                state.cdVisited.incl(ipos)
                                state.cdWorklist.add(ipos)
    else:
        # General worklist propagation
        state.cdWorklist.setLen(0)
        state.cdWorklist.add(pos)
        state.cdVisited.incl(pos)
        # Add inverse forced positions to the worklist for channel propagation
        for (fPos, savedVal) in state.inverseSavedBuf:
            if fPos notin state.cdVisited:
                state.cdVisited.incl(fPos)
                state.cdWorklist.add(fPos)

        while state.cdWorklist.len > 0:
            let p = state.cdWorklist.pop()
            if p in state.carray.channelsAtPosition:
                for bi in state.carray.channelsAtPosition[p]:
                    let bindingPtr = addr state.carray.channelBindings[bi]
                    let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                    if idxVal < 0 or idxVal >= bindingPtr.arrayElements.len: continue
                    let elem = bindingPtr.arrayElements[idxVal]
                    let newChanVal = if elem.isConstant: elem.constantValue
                                     else: state.assignment[elem.variablePosition]
                    let chanPos = bindingPtr.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.minMaxChannelsAtPosition:
                for bi in state.carray.minMaxChannelsAtPosition[p]:
                    let fb = state.flatMinMaxBindings[bi]
                    let newChanVal = evaluateFlatMinMax(fb, state.assignment)
                    let chanPos = fb.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.countEqChannelsAtPosition:
                for bi in state.carray.countEqChannelsAtPosition[p]:
                    let binding = state.carray.countEqChannelBindings[bi]
                    let newChanVal = evaluateCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.inverseChannelsAtPosition:
                for gi in state.carray.inverseChannelsAtPosition[p]:
                    let group = state.carray.inverseChannelGroups[gi]
                    let newInverse = group.recomputeInverse(state.assignment)
                    for j, ipos in group.inversePositions:
                        if newInverse[j] != state.assignment[ipos]:
                            state.trackChannelChange(ipos, newInverse[j])
                            if ipos notin state.cdVisited:
                                state.cdVisited.incl(ipos)
                                state.cdWorklist.add(ipos)

    when ProfileIteration:
        let cdWorklistEnd = epochTime()
        state.cdDomainEvals += state.cdDirtyPositions.len

    if state.cdDirtyPositions.len == 0:
        # No channel changes — just restore pos and inverse
        state.assignment[pos] = savedPos
        for (fPos, savedVal) in state.inverseSavedBuf:
            state.assignment[fPos] = savedVal
        return 0

    # Compute penalty delta for affected channel-dep constraints.
    # Assignment still has simulated values so we can use position-indexed lookups.
    # Uses precomputed coefficient arrays (O(coefficients * array_access)) instead of
    # iterating cdChanges with hash table lookups (O(cdChanges * hash_lookup)).
    if state.chanPosToDepConstraintIdx.len > 0:
        state.cdProcessed.clear()
        for chanPos in state.cdDirtyPositions:
            if chanPos in state.chanPosToDepConstraintIdx:
                for ci in state.chanPosToDepConstraintIdx[chanPos]:
                    if ci in state.cdProcessed: continue
                    state.cdProcessed.incl(ci)
                    if not state.channelDepConstraintActive[ci]: continue

                    var delta: int
                    if state.cdConstraintCanFast[ci]:
                        # Fast path: iterate precomputed coefficient arrays, check position-indexed flags
                        let rc = state.channelDepConstraints[ci].relationalState
                        var newLeft = rc.leftValue
                        var newRight = rc.rightValue
                        for (cpos, coeff) in state.cdConstraintCoeffs[ci]:
                            if state.cdIsChanged[cpos]:
                                newLeft += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                        for (cpos, coeff) in state.cdConstraintCoeffsR[ci]:
                            if state.cdIsChanged[cpos]:
                                newRight += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                        delta = rc.computeCost(newLeft, newRight) - rc.cost
                    else:
                        # Fallback: simulate-restore on the constraint
                        let c = state.channelDepConstraints[ci]
                        let oldPenalty = c.penalty()
                        for dpos in state.cdDirtyPositions:
                            if dpos in c.positions:
                                c.updatePosition(dpos, state.assignment[dpos])
                        let newPenalty = c.penalty()
                        for dpos in state.cdDirtyPositions:
                            if dpos in c.positions:
                                c.updatePosition(dpos, state.cdSavedVal[dpos])
                        delta = newPenalty - oldPenalty

                    result += delta
                    if state.cdTrackPerConstraint and delta != 0:
                        state.cdPerConstraintMaxDelta[ci] = max(state.cdPerConstraintMaxDelta[ci], abs(delta))
    else:
        # Fallback: iterate all relevant constraints (no reverse index)
        let relevantConstraints = state.channelDepConstraintsForPos.getOrDefault(pos, @[])
        for c in relevantConstraints:
            var affected = false
            for dpos in state.cdDirtyPositions:
                if dpos in c.positions:
                    affected = true
                    break
            if not affected: continue
            let oldPenalty = c.penalty()
            for dpos in state.cdDirtyPositions:
                if dpos in c.positions:
                    c.updatePosition(dpos, state.assignment[dpos])
            let newPenalty = c.penalty()
            for dpos in state.cdDirtyPositions:
                if dpos in c.positions:
                    c.updatePosition(dpos, state.cdSavedVal[dpos])
            result += newPenalty - oldPenalty

    when ProfileIteration:
        let cdPenaltyEnd = epochTime()
        state.cdWorklistTime += cdWorklistEnd - cdCallStart
        state.cdPenaltyTime += cdPenaltyEnd - cdWorklistEnd

    # Restore all modified assignment values
    state.assignment[pos] = savedPos
    for (fPos, savedVal) in state.inverseSavedBuf:
        state.assignment[fPos] = savedVal
    for dpos in state.cdDirtyPositions:
        state.assignment[dpos] = state.cdSavedVal[dpos]
        state.cdIsChanged[dpos] = false
    state.cdDirtyPositions.setLen(0)


proc computeCascadePenalties[T](state: TabuState[T], cascadeIdx: int,
    chanVals: openArray[seq[T]], domain: openArray[T], penalties: var seq[int]) =
    ## Compute penalty deltas for all domain values given cascade channel values.
    ## chanVals[chanIdx][domainIdx] = the channel value for that domain entry.
    let chans = state.cdCascadeChans[cascadeIdx]
    let constraintIds = state.cdCascadeConstraintIds[cascadeIdx]
    let coeffsL = state.cdCascadeConstraintL[cascadeIdx]
    let coeffsR = state.cdCascadeConstraintR[cascadeIdx]
    let nChans = chans.len

    for di in 0..<domain.len:
        var totalDelta = 0
        for cli in 0..<constraintIds.len:
            let ci = constraintIds[cli]
            var delta: int
            if state.cdConstraintCanFast[ci]:
                let rc = state.channelDepConstraints[ci].relationalState
                var newLeft = rc.leftValue
                var newRight = rc.rightValue
                for (cascIdx, coeff) in coeffsL[cli]:
                    let diff = chanVals[cascIdx][di] - state.assignment[chans[cascIdx]]
                    if diff != 0:
                        newLeft += coeff * diff
                for (cascIdx, coeff) in coeffsR[cli]:
                    let diff = chanVals[cascIdx][di] - state.assignment[chans[cascIdx]]
                    if diff != 0:
                        newRight += coeff * diff
                delta = rc.computeCost(newLeft, newRight) - rc.cost
            else:
                let c = state.channelDepConstraints[ci]
                let oldPenalty = c.penalty()
                var anyChanged = false
                for chanIdx in 0..<nChans:
                    let chanPos = chans[chanIdx]
                    let newVal = chanVals[chanIdx][di]
                    if newVal != state.assignment[chanPos] and chanPos in c.positions:
                        c.updatePosition(chanPos, newVal)
                        anyChanged = true
                if anyChanged:
                    delta = c.penalty() - oldPenalty
                    for chanIdx in 0..<nChans:
                        let chanPos = chans[chanIdx]
                        if chanVals[chanIdx][di] != state.assignment[chanPos] and chanPos in c.positions:
                            c.updatePosition(chanPos, state.assignment[chanPos])
                else:
                    delta = 0
            totalDelta += delta
            if state.cdTrackPerConstraint and delta != 0:
                state.cdPerConstraintMaxDelta[ci] = max(state.cdPerConstraintMaxDelta[ci], abs(delta))
        penalties[di] = totalDelta

proc computeChannelDepPenaltiesAt[T](state: TabuState[T], pos: int) =
    ## Compute channelDepPenalties[pos] for all domain values.
    ## Uses cascade topology for batch evaluation (both static and dynamic).
    ## Static cascades use precomputed channel values; dynamic cascades evaluate at runtime.
    ## Falls back to per-value computeChannelDepDelta for positions without cascade topology.
    let domain = state.sharedDomain[][pos]
    if pos in state.cdCascadePos:
        let cascadeIdx = state.cdCascadePos[pos]
        let nChans = state.cdCascadeChans[cascadeIdx].len
        let nDom = domain.len

        if state.cdCascadeIsStatic[cascadeIdx]:
            # Static cascade: use precomputed values
            state.computeCascadePenalties(cascadeIdx,
                state.cdCascadeValues[cascadeIdx], domain, state.channelDepPenalties[pos])
            when ProfileIteration:
                state.cdCascadeCalls += 1
        else:
            when ProfileIteration:
                let tBind0CD = epochTime()
            # Dynamic cascade: evaluate bindings at runtime for all domain values
            let chans = state.cdCascadeChans[cascadeIdx]
            let bindings = state.cdCascadeBindings[cascadeIdx]

            # Save original assignment values
            let savedPos = state.assignment[pos]
            for ci in 0..<nChans:
                state.cdBatchSaved[ci] = state.assignment[chans[ci]]

            # Evaluate cascade for all domain values using in-place modify-restore
            for di in 0..<nDom:
                state.assignment[pos] = domain[di]
                for ci in 0..<nChans:
                    let bindingPtr = addr state.carray.channelBindings[bindings[ci]]
                    let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                    if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                        let elem = bindingPtr.arrayElements[idxVal]
                        state.cdBatchValues[ci][di] = if elem.isConstant: elem.constantValue
                                                       else: state.assignment[elem.variablePosition]
                    else:
                        state.cdBatchValues[ci][di] = state.cdBatchSaved[ci]
                    state.assignment[chans[ci]] = state.cdBatchValues[ci][di]

            # Restore assignment
            state.assignment[pos] = savedPos
            for ci in 0..<nChans:
                state.assignment[chans[ci]] = state.cdBatchSaved[ci]

            when ProfileIteration:
                let tBind1CD = epochTime()
                state.cdCascadeBindingTime += tBind1CD - tBind0CD

            # Compute penalties from batch channel values
            state.computeCascadePenalties(cascadeIdx,
                state.cdBatchValues, domain, state.channelDepPenalties[pos])
            when ProfileIteration:
                state.cdCascadePenaltyTime += epochTime() - tBind1CD
                state.cdCascadeCalls += 1
    else:
        when ProfileIteration:
            let tFall0CD = epochTime()
        for i in 0..<domain.len:
            state.channelDepPenalties[pos][i] = state.computeChannelDepDelta(pos, domain[i])
        when ProfileIteration:
            state.cdCascadeFallbackTime += epochTime() - tFall0CD


proc recomputeAllChannelDepPenalties[T](state: TabuState[T]) =
    ## Recompute channel-dep penalties at all relevant search positions and
    ## adjust penaltyMap by the delta (new - old). Called after propagateChannels
    ## when channel-dep constraint state has changed.
    for pos in state.channelDepSearchPositions:
        if state.isLazy[pos]: continue
        let domain = state.sharedDomain[][pos]
        for i in 0..<domain.len:
            let newDep = state.computeChannelDepDelta(pos, domain[i])
            let oldDep = state.channelDepPenalties[pos][i]
            if newDep != oldDep:
                state.penaltyMap[pos][i] += newDep - oldDep
                state.channelDepPenalties[pos][i] = newDep

proc applyUniformDelta[T](state: TabuState[T], pos: int) {.inline.} =
    ## Apply uniform cost delta for channel-dep penalties at position.
    ## For cascade positions: the penalty change is exactly (savedCost - newCost)
    ## applied uniformly to all domain values (exact for element-only cascades).
    ## For non-cascade positions (minMax/inverse): falls back to full per-value
    ## recomputation since cascade values are state-dependent.
    if pos notin state.cdCascadePos:
        # Non-cascade: full recomputation (minMax/inverse cascade values depend on state)
        let domain = state.sharedDomain[][pos]
        for i in 0..<domain.len:
            let newDep = state.computeChannelDepDelta(pos, domain[i])
            let oldDep = state.channelDepPenalties[pos][i]
            if newDep != oldDep:
                state.penaltyMap[pos][i] += newDep - oldDep
                state.channelDepPenalties[pos][i] = newDep
        return
    let cascadeIdx = state.cdCascadePos[pos]
    let constraintIds = state.cdCascadeConstraintIds[cascadeIdx]
    var uniformDelta = 0
    for ci in constraintIds:
        if not state.channelDepConstraintActive[ci]: continue
        let newCost = state.channelDepConstraints[ci].penalty()
        let savedCost = state.cdSavedConstraintCosts[ci]
        if savedCost != newCost:
            uniformDelta += savedCost - newCost
    if uniformDelta != 0:
        let domain = state.sharedDomain[][pos]
        for i in 0..<domain.len:
            state.channelDepPenalties[pos][i] += uniformDelta
            state.penaltyMap[pos][i] += uniformDelta

proc recomputeAffectedChannelDepPenalties[T](state: TabuState[T], changedChannels: seq[int], movedPosition: int = -1) =
    ## Targeted recomputation: update channel-dep penalties at search positions
    ## affected by the given changed channel positions.
    ## Uses uniform cost delta (exact for static cascades with linear constraints):
    ## since costAfterCascade(i) is unchanged by propagation, the penalty change
    ## is exactly (savedCost - newCost) applied uniformly to all domain values.
    ## For one-hot positions, targeted updates still use per-value computation
    ## since different domain values are affected non-uniformly.
    ## The movedPosition is skipped (its penalty map is fully rebuilt by updatePenaltiesForPosition).

    if state.depConstraintOneHotEntries.len > 0:
        # Find affected constraint indices from changed channels
        var affectedConstraintIds: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.chanPosToDepConstraintIdx:
                for ci in state.chanPosToDepConstraintIdx[chanPos]:
                    affectedConstraintIds.incl(ci)

        # Collect targeted (pos, domainIdx) pairs from affected constraints
        # This finds ALL one-hot positions sharing constraints with changed channels
        state.cdTargetedUpdates.clear()
        for ci in affectedConstraintIds.items:
            for entry in state.depConstraintOneHotEntries[ci]:
                if entry.pos == movedPosition: continue
                if entry.pos notin state.cdTargetedUpdates:
                    state.cdTargetedUpdates[entry.pos] = initPackedSet[int]()
                state.cdTargetedUpdates[entry.pos].incl(entry.domainIdx)

        for pos, affectedIndices in state.cdTargetedUpdates.pairs:
            if state.isLazy[pos]: continue
            let currentVal = state.assignment[pos]
            let currentIdx = state.domainIndex[pos].getOrDefault(currentVal, -1)
            if currentIdx >= 0 and currentIdx in affectedIndices:
                # Full recomputation — use uniform delta
                when ProfileIteration: state.cdFullPos += 1
                state.applyUniformDelta(pos)
            else:
                # Targeted recomputation — only affected domain values
                when ProfileIteration: state.cdTargetedPos += 1
                let domain = state.sharedDomain[][pos]
                for i in affectedIndices.items:
                    when ProfileIteration: state.cdTotalCalls += 1
                    let newDep = state.computeChannelDepDelta(pos, domain[i])
                    let oldDep = state.channelDepPenalties[pos][i]
                    if newDep != oldDep:
                        state.penaltyMap[pos][i] += newDep - oldDep
                        state.channelDepPenalties[pos][i] = newDep

        # Also handle non-one-hot positions via channelDepPosForChannel
        var nonOneHotPositions: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.channelDepPosForChannel:
                for pos in state.channelDepPosForChannel[chanPos]:
                    if pos != movedPosition and pos notin state.cdTargetedUpdates:
                        nonOneHotPositions.incl(pos)
        for pos in nonOneHotPositions.items:
            if state.isLazy[pos]: continue
            when ProfileIteration: state.cdNonOneHotPos += 1
            state.applyUniformDelta(pos)
    else:
        # No reverse index — use channelDepPosForChannel with uniform delta
        var affectedPositions: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.channelDepPosForChannel:
                for pos in state.channelDepPosForChannel[chanPos]:
                    affectedPositions.incl(pos)
        for pos in affectedPositions.items:
            if pos == movedPosition: continue
            if state.isLazy[pos]: continue
            state.applyUniformDelta(pos)
