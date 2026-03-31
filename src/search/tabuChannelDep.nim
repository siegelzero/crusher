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
        of IntegerDivision, Modulo:
            # Only fold as constant if both children are purely constant.
            let (lok, lterms, loff) = tryExtractLinear[T](node.left)
            if not lok: return (false, @[], T(0))
            let (rok, rterms, roff) = tryExtractLinear[T](node.right)
            if not rok: return (false, @[], T(0))
            if lterms.len == 0 and rterms.len == 0 and roff != 0:
                let v = if node.binaryOp == IntegerDivision: loff div roff else: loff mod roff
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

proc evaluateWeightedCountEq[T](binding: WeightedCountEqChannelBinding[T], assignment: seq[T]): T {.inline.} =
    ## Evaluate a weighted count-equals channel:
    ## constantOffset + sum(weights[i] for i where assignment[inputPositions[i]] == targetValue).
    var total: T = binding.constantOffset
    for i in 0..<binding.inputPositions.len:
        if assignment[binding.inputPositions[i]] == binding.targetValue:
            total += binding.weights[i]
    total

proc evaluateWeightedCountEqDelta[T](binding: WeightedCountEqChannelBinding[T],
                                      currentVal: T, changedPos: int,
                                      oldVal: T, newVal: T): T {.inline.} =
    ## O(1) delta evaluation: adjust current value when a single input position changes.
    result = currentVal
    if changedPos in binding.positionWeight:
        let w = binding.positionWeight[changedPos]
        if oldVal == binding.targetValue: result -= w
        if newVal == binding.targetValue: result += w

proc evaluateConditionalCountEq[T](binding: ConditionalCountEqChannelBinding[T],
                                    assignment: seq[T]): T {.inline.} =
    ## Evaluate a conditional count-equals channel:
    ## constantOffset + #{paired: primary==target AND filter==filterVal} + #{primaryOnly: ==target}.
    var count: T = binding.constantOffset
    for i in 0..<binding.primaryPositions.len:
        if assignment[binding.primaryPositions[i]] == binding.targetValue and
           assignment[binding.filterPositions[i]] == binding.filterValue:
            inc count
    for pos in binding.primaryOnlyPositions:
        if assignment[pos] == binding.targetValue:
            inc count
    count

proc evaluateArgmax[T](binding: ArgmaxChannelBinding[T], assignment: seq[T]): T {.inline.} =
    ## Evaluate argmax channel: returns valueOffset + index of first maximum in inputExprs.
    var bestVal = binding.inputExprs[0].evaluate(assignment)
    var bestIdx = 0
    for i in 1..<binding.inputExprs.len:
        let v = binding.inputExprs[i].evaluate(assignment)
        if v > bestVal:
            bestVal = v
            bestIdx = i
    T(bestIdx + binding.valueOffset)

proc evaluateCrossingCountMax[T](binding: CrossingCountMaxChannelBinding[T],
                                  assignment: seq[T]): T {.inline.} =
    ## Evaluate crossing count max channel using sweep-line in O(numCables + k) time.
    ## crossing(v) = |{j : min(a_j, b_j) < v < max(a_j, b_j)}| for cables (a_j, b_j).
    ## Returns max_v crossing(v).
    let k = binding.k
    var events = newSeq[T](k + 2)
    for cable in binding.cables:
        let a = assignment[cable.startPos]
        let b = assignment[cable.endPos]
        let lo = min(a, b)
        let hi = max(a, b)
        if hi - lo > 1:
            events[lo + 1] += 1
            events[hi] -= 1
    result = T(0)
    var current = T(0)
    for v in 1..k:
        current += events[v]
        if current > result: result = current

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
       pos notin state.carray.weightedCountEqChannelsAtPosition and
       pos notin state.carray.conditionalCountEqChannelsAtPosition and
       pos notin state.carray.inverseChannelsAtPosition and
       pos notin state.carray.argmaxChannelsAtPosition and
       pos notin state.carray.crossingCountMaxChannelsAtPosition:
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
                                     else: state.assignment[elem.variablePosition] + elem.offset
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
            if p in state.carray.weightedCountEqChannelsAtPosition:
                for bi in state.carray.weightedCountEqChannelsAtPosition[p]:
                    let binding = state.carray.weightedCountEqChannelBindings[bi]
                    let newChanVal = evaluateWeightedCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.conditionalCountEqChannelsAtPosition:
                for bi in state.carray.conditionalCountEqChannelsAtPosition[p]:
                    let binding = state.carray.conditionalCountEqChannelBindings[bi]
                    let newChanVal = evaluateConditionalCountEq(binding, state.assignment)
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
            if p in state.carray.argmaxChannelsAtPosition:
                for bi in state.carray.argmaxChannelsAtPosition[p]:
                    let binding = state.carray.argmaxChannelBindings[bi]
                    let newChanVal = evaluateArgmax(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
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
                                     else: state.assignment[elem.variablePosition] + elem.offset
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
            if p in state.carray.weightedCountEqChannelsAtPosition:
                for bi in state.carray.weightedCountEqChannelsAtPosition[p]:
                    let binding = state.carray.weightedCountEqChannelBindings[bi]
                    let newChanVal = evaluateWeightedCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.conditionalCountEqChannelsAtPosition:
                for bi in state.carray.conditionalCountEqChannelsAtPosition[p]:
                    let binding = state.carray.conditionalCountEqChannelBindings[bi]
                    let newChanVal = evaluateConditionalCountEq(binding, state.assignment)
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
            if p in state.carray.argmaxChannelsAtPosition:
                for bi in state.carray.argmaxChannelsAtPosition[p]:
                    let binding = state.carray.argmaxChannelBindings[bi]
                    let newChanVal = evaluateArgmax(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)

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
            elif state.channelDepConstraints[ci].stateType == DisjunctiveClauseType:
                # Fast DC path: compute penalty directly from precomputed cascade-to-term mappings
                let dc = state.channelDepConstraints[ci].disjunctiveClauseState
                let termCoeffs = state.cdCascadeDCTermCoeffs[cascadeIdx][cli]
                var newPenalty = high(int)
                for d in 0..<dc.disjuncts.len:
                    var conjPenalty = dc.disjunctPenalties[d]
                    for t in 0..<dc.disjuncts[d].len:
                        let term = addr dc.disjuncts[d][t]
                        var sumDelta: T = 0
                        for entry in termCoeffs[d][t]:
                            sumDelta += term.coeffs[entry.coeffIdx] * (chanVals[entry.cascIdx][di] - state.assignment[chans[entry.cascIdx]])
                        if sumDelta != 0:
                            let oldViolation = max(0, int(term.currentSum) - int(term.rhs))
                            let newViolation = max(0, int(term.currentSum + sumDelta) - int(term.rhs))
                            conjPenalty += newViolation - oldViolation
                    if conjPenalty < newPenalty:
                        newPenalty = conjPenalty
                        if newPenalty == 0: break
                delta = newPenalty - dc.cost
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

proc computeChannelDepPenaltiesInc[T](state: TabuState[T], pos: int, changedExternals: ptr PackedSet[int]) =
    ## Incremental cascade evaluation: only re-evaluate entries affected by changed
    ## external positions. Uses cached values for unaffected entries, with dirty
    ## propagation through forward deps when an entry's value changes.
    let domain = state.sharedDomain[][pos]
    let cascadeIdx = state.cdCascadePos[pos]
    let nChans = state.cdCascadeChans[cascadeIdx].len
    let nDom = domain.len
    let chans = state.cdCascadeChans[cascadeIdx]
    let bindings = state.cdCascadeBindings[cascadeIdx]
    let entryKinds = state.cdCascadeEntryKind[cascadeIdx]
    let forwardDeps = state.cdCascadeForwardDeps[cascadeIdx]
    let extPosToEntries = state.cdCascadeExtPosToEntries[cascadeIdx]

    when ProfileIteration:
        let tBind0 = epochTime()

    # Determine initially dirty entries from changed externals
    for ci in 0..<nChans:
        state.cdCascadeDirtyBase[ci] = false
    for chanPos in changedExternals[].items:
        if chanPos in extPosToEntries:
            for ci in extPosToEntries[chanPos]:
                state.cdCascadeDirtyBase[ci] = true

    # Propagate dirty forward to find maximal dirty set (superset across all domain values)
    for ci in 0..<nChans:
        state.cdCascadeDirtyDV[ci] = state.cdCascadeDirtyBase[ci]
    for ci in 0..<nChans:
        if state.cdCascadeDirtyDV[ci]:
            for downstream in forwardDeps[ci]:
                state.cdCascadeDirtyDV[downstream] = true

    # Build compact work list: maxDirty entries + needed clean predecessors
    # A clean entry is "needed" if it has a maxDirty entry downstream (via forwardDeps)
    var workListLen = 0
    for ci in 0..<nChans:
        if state.cdCascadeDirtyDV[ci]:
            state.cdCascadeInWorkList[ci] = true
        else:
            state.cdCascadeInWorkList[ci] = false
            for downstream in forwardDeps[ci]:
                if state.cdCascadeDirtyDV[downstream]:
                    state.cdCascadeInWorkList[ci] = true
                    break
    for ci in 0..<nChans:
        if state.cdCascadeInWorkList[ci]:
            state.cdCascadeWorkList[workListLen] = ci
            inc workListLen

    # Save original assignment values only for work list entries
    let savedPos = state.assignment[pos]
    for wi in 0..<workListLen:
        let ci = state.cdCascadeWorkList[wi]
        state.cdBatchSaved[ci] = state.assignment[chans[ci]]

    # Incremental evaluation: iterate only work list entries per domain value.
    # Write dirty entry results directly to the cache (cdCascadeCachedValues)
    # and pass cache to computeCascadePenalties — no cdBatchValues needed.
    for di in 0..<nDom:
        state.assignment[pos] = domain[di]
        # Reset per-domain-value dirty for maxDirty entries only
        for wi in 0..<workListLen:
            let ci = state.cdCascadeWorkList[wi]
            state.cdCascadeDirtyDV[ci] = state.cdCascadeDirtyBase[ci]
        for wi in 0..<workListLen:
            let ci = state.cdCascadeWorkList[wi]
            if not state.cdCascadeDirtyDV[ci]:
                # Clean predecessor: set assignment from cache
                state.assignment[chans[ci]] = state.cdCascadeCachedValues[cascadeIdx][ci][di]
                when ProfileIteration: state.cdIncSkipped += 1
            else:
                # Dirty: re-evaluate
                when ProfileIteration: state.cdIncEvaluated += 1
                var newVal: T
                case entryKinds[ci]
                of ceMinMax:
                    let fb = state.flatMinMaxBindings[bindings[ci]]
                    newVal = evaluateFlatMinMax(fb, state.assignment)
                of ceCountEq:
                    let binding = state.carray.countEqChannelBindings[bindings[ci]]
                    newVal = evaluateCountEq(binding, state.assignment)
                of ceConditionalCountEq:
                    let binding = state.carray.conditionalCountEqChannelBindings[bindings[ci]]
                    newVal = evaluateConditionalCountEq(binding, state.assignment)
                of ceWeightedCountEq:
                    let binding = state.carray.weightedCountEqChannelBindings[bindings[ci]]
                    newVal = evaluateWeightedCountEq(binding, state.assignment)
                of ceArgmax:
                    let binding = state.carray.argmaxChannelBindings[bindings[ci]]
                    newVal = evaluateArgmax(binding, state.assignment)
                of ceCrossingCountMax:
                    let binding = state.carray.crossingCountMaxChannelBindings[bindings[ci]]
                    newVal = evaluateCrossingCountMax(binding, state.assignment)
                of ceElement:
                    let bindingPtr = addr state.carray.channelBindings[bindings[ci]]
                    let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                    if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                        let elem = bindingPtr.arrayElements[idxVal]
                        newVal = if elem.isConstant: elem.constantValue
                                 else: state.assignment[elem.variablePosition] + elem.offset
                    else:
                        newVal = state.cdBatchSaved[ci]
                state.assignment[chans[ci]] = newVal
                # Propagate dirtiness if value changed from cache
                if newVal != state.cdCascadeCachedValues[cascadeIdx][ci][di]:
                    state.cdCascadeCachedValues[cascadeIdx][ci][di] = newVal
                    for downstream in forwardDeps[ci]:
                        state.cdCascadeDirtyDV[downstream] = true

    # Restore assignment only for work list entries
    state.assignment[pos] = savedPos
    for wi in 0..<workListLen:
        let ci = state.cdCascadeWorkList[wi]
        state.assignment[chans[ci]] = state.cdBatchSaved[ci]

    when ProfileIteration:
        state.cdCascadeBindingTime += epochTime() - tBind0
        let tPen0 = epochTime()

    # Compute penalties using cached values (updated in-place for dirty entries)
    state.computeCascadePenalties(cascadeIdx,
        state.cdCascadeCachedValues[cascadeIdx], domain, state.channelDepPenalties[pos])

    when ProfileIteration:
        state.cdCascadePenaltyTime += epochTime() - tPen0
        state.cdCascadeCalls += 1

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
            let entryKinds = state.cdCascadeEntryKind[cascadeIdx]

            # Save original assignment values
            let savedPos = state.assignment[pos]
            for ci in 0..<nChans:
                state.cdBatchSaved[ci] = state.assignment[chans[ci]]

            # Evaluate cascade for all domain values using in-place modify-restore
            for di in 0..<nDom:
                state.assignment[pos] = domain[di]
                for ci in 0..<nChans:
                    case entryKinds[ci]
                    of ceMinMax:
                        # Min/max binding: evaluate using flat linear representation
                        let fb = state.flatMinMaxBindings[bindings[ci]]
                        state.cdBatchValues[ci][di] = evaluateFlatMinMax(fb, state.assignment)
                    of ceCountEq:
                        # CountEq binding: count matching values over input positions
                        let binding = state.carray.countEqChannelBindings[bindings[ci]]
                        state.cdBatchValues[ci][di] = evaluateCountEq(binding, state.assignment)
                    of ceConditionalCountEq:
                        # ConditionalCountEq binding: count matching with filter condition
                        let binding = state.carray.conditionalCountEqChannelBindings[bindings[ci]]
                        state.cdBatchValues[ci][di] = evaluateConditionalCountEq(binding, state.assignment)
                    of ceWeightedCountEq:
                        # WeightedCountEq binding: sum weights for matching values
                        let binding = state.carray.weightedCountEqChannelBindings[bindings[ci]]
                        state.cdBatchValues[ci][di] = evaluateWeightedCountEq(binding, state.assignment)
                    of ceArgmax:
                        # Argmax binding: evaluate input expressions and find max index
                        let binding = state.carray.argmaxChannelBindings[bindings[ci]]
                        state.cdBatchValues[ci][di] = evaluateArgmax(binding, state.assignment)
                    of ceCrossingCountMax:
                        # Crossing count max: sweep-line evaluation
                        let binding = state.carray.crossingCountMaxChannelBindings[bindings[ci]]
                        state.cdBatchValues[ci][di] = evaluateCrossingCountMax(binding, state.assignment)
                    of ceElement:
                        # Element binding: evaluate index expression and look up array
                        let bindingPtr = addr state.carray.channelBindings[bindings[ci]]
                        let idxVal = bindingPtr.indexExpression.evaluate(state.assignment)
                        if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                            let elem = bindingPtr.arrayElements[idxVal]
                            state.cdBatchValues[ci][di] = if elem.isConstant: elem.constantValue
                                                           else: state.assignment[elem.variablePosition] + elem.offset
                        else:
                            state.cdBatchValues[ci][di] = state.cdBatchSaved[ci]
                    state.assignment[chans[ci]] = state.cdBatchValues[ci][di]

            # Restore assignment
            state.assignment[pos] = savedPos
            for ci in 0..<nChans:
                state.assignment[chans[ci]] = state.cdBatchSaved[ci]

            # Cache batch values for incremental cascade eval and min/max fast-path
            for ci in 0..<nChans:
                for di in 0..<nDom:
                    state.cdCascadeCachedValues[cascadeIdx][ci][di] = state.cdBatchValues[ci][di]

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


proc applyUniformDelta[T](state: TabuState[T], pos: int, changedChannels: seq[int]) {.inline.} =
    ## Apply uniform cost delta for channel-dep penalties at position.
    ## For cascade positions: checks if external dependencies changed. If not,
    ## applies uniform delta (exact). If only min/max external deps changed (not
    ## element deps), re-evaluates only the min/max entries using cached element
    ## cascade values. Falls back to full cascade recomputation if element deps changed.
    ## For non-cascade positions: falls back to full per-value recomputation.
    if pos notin state.cdCascadePos:
        # Non-cascade: full recomputation
        let domain = state.sharedDomain[][pos]
        for i in 0..<domain.len:
            let newDep = state.computeChannelDepDelta(pos, domain[i])
            let oldDep = state.channelDepPenalties[pos][i]
            if newDep != oldDep:
                state.penaltyMap[pos][i] += newDep - oldDep
                state.channelDepPenalties[pos][i] = newDep
        return
    let cascadeIdx = state.cdCascadePos[pos]
    # Check which external deps changed: element deps vs min/max-only deps
    var elemDepChanged = false
    var anyDepChanged = false
    let elemExtDeps = state.cdCascadeElemExtDeps[cascadeIdx]
    let externalDeps = state.cdCascadeExternalDeps[cascadeIdx]
    if externalDeps.len > 0:
        for chanPos in changedChannels:
            if chanPos in externalDeps:
                anyDepChanged = true
                if chanPos in elemExtDeps:
                    elemDepChanged = true
                    break
    if elemDepChanged:
        # Element deps changed — incremental cascade recomputation
        when ProfileIteration: state.cdIncCalls += 1
        # Collect changed external positions
        var changedExternals: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in externalDeps:
                changedExternals.incl(chanPos)
        let domain = state.sharedDomain[][pos]
        var oldPenalties = newSeq[int](domain.len)
        for i in 0..<domain.len:
            oldPenalties[i] = state.channelDepPenalties[pos][i]
        state.computeChannelDepPenaltiesInc(pos, addr changedExternals)
        for i in 0..<domain.len:
            let delta = state.channelDepPenalties[pos][i] - oldPenalties[i]
            if delta != 0:
                state.penaltyMap[pos][i] += delta
        return
    if anyDepChanged and state.cdCascadeMinMaxIdx[cascadeIdx].len > 0:
        # Only min/max deps changed — use cached element values, re-evaluate min/max only.
        when ProfileIteration: state.cdFastPathCalls += 1
        # Element cascade values are stable (no element deps changed). For each domain value,
        # set the min/max's cascade inputs from cache, evaluate min/max, store in cache.
        # Pass cache directly to computeCascadePenalties (it only reads min/max entries).
        let domain = state.sharedDomain[][pos]
        let nDom = domain.len
        let bindings = state.cdCascadeBindings[cascadeIdx]
        let mmIndices = state.cdCascadeMinMaxIdx[cascadeIdx]
        let mmInputs = state.cdCascadeMinMaxInputs[cascadeIdx]
        # Save assignment values at positions that will be temporarily modified
        var savedAssignment: seq[tuple[pos: int, val: T]]
        var savedSet: PackedSet[int]
        for mmLocalIdx in 0..<mmIndices.len:
            let mmTopoIdx = mmIndices[mmLocalIdx]
            let fb = state.flatMinMaxBindings[bindings[mmTopoIdx]]
            for (linearIdx, topoIdx) in mmInputs[mmLocalIdx]:
                let lp = fb.linearPositions[linearIdx]
                if lp notin savedSet:
                    savedSet.incl(lp)
                    savedAssignment.add((pos: lp, val: state.assignment[lp]))
        for di in 0..<nDom:
            for mmLocalIdx in 0..<mmIndices.len:
                let mmTopoIdx = mmIndices[mmLocalIdx]
                let fb = state.flatMinMaxBindings[bindings[mmTopoIdx]]
                # Set cascade inputs from cache for this domain value
                for (linearIdx, topoIdx) in mmInputs[mmLocalIdx]:
                    state.assignment[fb.linearPositions[linearIdx]] = state.cdCascadeCachedValues[cascadeIdx][topoIdx][di]
                # Re-evaluate min/max (reads cached cascade + current external from assignment)
                state.cdCascadeCachedValues[cascadeIdx][mmTopoIdx][di] = evaluateFlatMinMax(fb, state.assignment)
        # Restore assignment
        for (p, v) in savedAssignment:
            state.assignment[p] = v
        # Compute penalties using cached values (min/max updated, elements unchanged)
        var oldPenalties = newSeq[int](nDom)
        for i in 0..<nDom:
            oldPenalties[i] = state.channelDepPenalties[pos][i]
        state.computeCascadePenalties(cascadeIdx,
            state.cdCascadeCachedValues[cascadeIdx], domain, state.channelDepPenalties[pos])
        for i in 0..<nDom:
            let delta = state.channelDepPenalties[pos][i] - oldPenalties[i]
            if delta != 0:
                state.penaltyMap[pos][i] += delta
        when ProfileIteration: state.cdCascadeCalls += 1
        return
    if anyDepChanged:
        # External deps changed but no min/max entries to fast-path — full cascade recompute.
        # (Shouldn't happen: min/max-only deps imply min/max entries, but handle defensively.)
        let domain = state.sharedDomain[][pos]
        var oldPenalties = newSeq[int](domain.len)
        for i in 0..<domain.len:
            oldPenalties[i] = state.channelDepPenalties[pos][i]
        state.computeChannelDepPenaltiesAt(pos)
        for i in 0..<domain.len:
            let delta = state.channelDepPenalties[pos][i] - oldPenalties[i]
            if delta != 0:
                state.penaltyMap[pos][i] += delta
        return
    if not anyDepChanged:
        # No external deps changed — uniform delta is exact
        when ProfileIteration: state.cdUniformCalls += 1
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
                state.applyUniformDelta(pos, changedChannels)
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
            state.applyUniformDelta(pos, changedChannels)
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
            state.applyUniformDelta(pos, changedChannels)
