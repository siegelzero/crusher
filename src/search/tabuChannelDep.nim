## Channel-dependent constraint penalty routines.
## Included from tabu.nim — not a standalone module.

# abs() in Nim always checks for low(int) even with -d:release, raising
# OverflowDefect. During intermediate search states, wrapped arithmetic can
# produce low(int). This unchecked variant avoids the crash.
{.push overflowChecks: off.}
func safeAbs(x: int): int {.inline.} =
    if x < 0: -x else: x
{.pop.}

type LinearTerm[T] = tuple[pos: int, coeff: T]

proc singlePosPenalty[T](state: TabuState[T], ci: int, value: T): int =
    ## Penalty of single-position relational channel-dep constraint ci when its
    ## position holds `value`. Pure function of the value: evaluated once on a
    ## one-entry assignment table, then memoized.
    if value in state.cdSingleCache[ci]:
        return state.cdSingleCache[ci][value]
    let rc = state.channelDepConstraints[ci].relationalState
    var tbl = initTable[int, T]()
    tbl[state.cdSinglePos[ci]] = value
    template side(e: untyped): T =
        (if e.kind == ConstantExpr: e.constantValue
         else: e.algebraicExpr.algebraicExpr.evaluate(tbl))
    result = rc.computeCost(side(rc.leftExpr), side(rc.rightExpr))
    state.cdSingleCache[ci][value] = result

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

const IncCountMinInputs = 16

proc countEqAfterSrc[T](state: TabuState[T], bi: int, p: int, oldV: T): T {.inline.} =
    ## countEq channel bi after source position p changed from oldV to its current
    ## value, given the channel still holds its pre-change value. O(1) for wide
    ## bindings, full rescan otherwise.
    let binding {.cursor.} = state.carray.countEqChannelBindings[bi]
    if state.ceqPosMult[bi].len > 0:
        let m = state.ceqPosMult[bi].getOrDefault(p, 0)
        let t = binding.targetValue
        return state.assignment[binding.channelPosition] +
               T(m) * (T(ord(state.assignment[p] == t)) - T(ord(oldV == t)))
    evaluateCountEq(binding, state.assignment)

proc wCountEqAfterSrc[T](state: TabuState[T], bi: int, p: int, oldV: T): T {.inline.} =
    ## weightedCountEq analogue of countEqAfterSrc.
    let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bi]
    if state.wceqPosWeight[bi].len > 0:
        let w = state.wceqPosWeight[bi].getOrDefault(p, T(0))
        let t = binding.targetValue
        return state.assignment[binding.channelPosition] +
               w * (T(ord(state.assignment[p] == t)) - T(ord(oldV == t)))
    evaluateWeightedCountEq(binding, state.assignment)

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
    ## Unweighted: max_v |{j : min(a_j, b_j) < v < max(a_j, b_j)}|
    ## Weighted:   max_v (offset_v + Σ_j w_j * [min(a_j, b_j) < v < max(a_j, b_j)])
    let k = binding.k
    var events = newSeq[T](k + 2)
    if binding.weights.len > 0:
        for ci in 0..<binding.cables.len:
            let cable = binding.cables[ci]
            let a = assignment[cable.startPos]
            let b = assignment[cable.endPos]
            let lo = min(a, b)
            let hi = max(a, b)
            if hi - lo > 1:
                let evStart = max(1, lo + 1)
                let evEnd = min(k + 1, hi)
                if evStart <= k:
                    events[evStart] += binding.weights[ci]
                    events[evEnd] -= binding.weights[ci]
    else:
        for cable in binding.cables:
            let a = assignment[cable.startPos]
            let b = assignment[cable.endPos]
            let lo = min(a, b)
            let hi = max(a, b)
            if hi - lo > 1:
                let evStart = max(1, lo + 1)
                let evEnd = min(k + 1, hi)
                if evStart <= k:
                    events[evStart] += 1
                    events[evEnd] -= 1
    result = T(0)
    var current = T(0)
    if binding.permPositions.len > 0:
        # Weighted version with per-position offsets from inverse permutation
        var invPerm = newSeq[int](k + 1)  # invPerm[position] = nodeIndex
        for nodeIdx in 0..<binding.permPositions.len:
            let posVal = assignment[binding.permPositions[nodeIdx]]
            if posVal >= 1 and posVal <= k:
                invPerm[posVal] = nodeIdx
        for v in 1..k:
            current += events[v]
            let nodeIdx = invPerm[v]
            let total = current + (if nodeIdx < binding.sweepCosts.len: binding.sweepCosts[nodeIdx] else: T(0))
            if total > result: result = total
    else:
        for v in 1..k:
            current += events[v]
            if current > result: result = current

# ---------------------------------------------------------------------------
# Profile max channels: max over slots of cached loads (max-tree per binding).
# The cache mirrors the committed assignment: rebuilt at init, synced on every
# propagated move (O(#groups) compare). Candidate evaluations apply the moved
# source's groups to the tree temporarily and revert.

proc pmTreeSet[T](tree: var seq[T], sz: int, s: int, v: T) {.inline.} =
    var i = sz + s
    tree[i] = v
    i = i shr 1
    while i >= 1:
        tree[i] = max(tree[2 * i], tree[2 * i + 1])
        i = i shr 1

proc pmShift[T](state: TabuState[T], bi, g: int, x, y: T, sign: T, record: bool) =
    ## Add (sign = 1) or remove (sign = -1) group g's contributions at (x, y).
    ## With `record`, the old load of every touched slot goes to pmUndo.
    let b {.cursor.} = state.carray.profileMaxChannelBindings[bi]
    let k = int(x - b.groupLo[g])
    if k < 0 or k >= b.groupN[g]: return
    let vi = b.groupStart[g] + k
    let sz = state.pmTreeSize[bi]
    for c in b.valStart[vi] ..< b.valStart[vi + 1]:
        let s = int(b.contribSlot[c])
        let d = sign * (b.contribA[c] * y + b.contribB[c])
        if d == 0: continue
        if record: state.pmUndo.add((s, state.pmLoads[bi][s]))
        state.pmLoads[bi][s] += d
        pmTreeSet(state.pmTree[bi], sz, s, state.pmLoads[bi][s])

proc pmGroupY[T](state: TabuState[T], b: ProfileMaxChannelBinding[T], g: int): T {.inline.} =
    if b.groupY[g] >= 0: state.assignment[b.groupY[g]] else: T(0)

proc pmRebuild[T](state: TabuState[T], bi: int): T =
    ## Rebuild binding bi's cache from the current assignment; returns the max.
    let b {.cursor.} = state.carray.profileMaxChannelBindings[bi]
    let nSlots = b.slotBase.len
    var sz = 1
    while sz < max(1, nSlots): sz = sz * 2
    state.pmTreeSize[bi] = sz
    state.pmLoads[bi] = b.slotBase
    state.pmTree[bi] = newSeq[T](2 * sz)
    for i in 0..<2 * sz: state.pmTree[bi][i] = low(T)
    let nG = b.groupX.len
    state.pmCacheX[bi].setLen(nG)
    state.pmCacheY[bi].setLen(nG)
    for g in 0..<nG:
        let x = state.assignment[b.groupX[g]]
        let y = state.pmGroupY(b, g)
        state.pmCacheX[bi][g] = x
        state.pmCacheY[bi][g] = y
        let k = int(x - b.groupLo[g])
        if k < 0 or k >= b.groupN[g]: continue
        let vi = b.groupStart[g] + k
        for c in b.valStart[vi] ..< b.valStart[vi + 1]:
            state.pmLoads[bi][int(b.contribSlot[c])] += b.contribA[c] * y + b.contribB[c]
    for s in 0..<nSlots: state.pmTree[bi][sz + s] = state.pmLoads[bi][s]
    for i in countdown(sz - 1, 1):
        state.pmTree[bi][i] = max(state.pmTree[bi][2 * i], state.pmTree[bi][2 * i + 1])
    state.pmTree[bi][1]

proc pmSyncGroup[T](state: TabuState[T], bi, g: int, record: bool) {.inline.} =
    let b {.cursor.} = state.carray.profileMaxChannelBindings[bi]
    let x = state.assignment[b.groupX[g]]
    let y = state.pmGroupY(b, g)
    let cx = state.pmCacheX[bi][g]
    let cy = state.pmCacheY[bi][g]
    if x == cx and y == cy: return
    state.pmShift(bi, g, cx, cy, T(-1), record)
    state.pmShift(bi, g, x, y, T(1), record)
    if not record:
        state.pmCacheX[bi][g] = x
        state.pmCacheY[bi][g] = y

proc pmSync[T](state: TabuState[T], bi: int): T =
    ## Commit: bring the cache to the current assignment; returns the max.
    for g in 0..<state.carray.profileMaxChannelBindings[bi].groupX.len:
        state.pmSyncGroup(bi, g, record = false)
    state.pmTree[bi][1]

proc pmRevert[T](state: TabuState[T], bi: int) {.inline.} =
    let sz = state.pmTreeSize[bi]
    for i in countdown(state.pmUndo.len - 1, 0):
        let (s, old) = state.pmUndo[i]
        state.pmLoads[bi][s] = old
        pmTreeSet(state.pmTree[bi], sz, s, old)
    state.pmUndo.setLen(0)

proc pmEvalFull[T](state: TabuState[T], bi: int): T =
    ## Max for the current (possibly tentative) assignment; cache unchanged.
    state.pmUndo.setLen(0)
    for g in 0..<state.carray.profileMaxChannelBindings[bi].groupX.len:
        state.pmSyncGroup(bi, g, record = true)
    result = state.pmTree[bi][1]
    state.pmRevert(bi)

proc pmEvalAt[T](state: TabuState[T], bi: int, pos: int): T =
    ## Max for the current assignment when only `pos` (a search position)
    ## differs from the committed one; cache unchanged.
    if not state.pmHintOk[bi]: return state.pmEvalFull(bi)
    let b {.cursor.} = state.carray.profileMaxChannelBindings[bi]
    state.pmUndo.setLen(0)
    b.groupsAtPos.withValue(pos, gs):
        for g in gs:
            state.pmSyncGroup(bi, g, record = true)
    result = state.pmTree[bi][1]
    state.pmRevert(bi)

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
       pos notin state.carray.crossingCountMaxChannelsAtPosition and
       pos notin state.carray.profileMaxChannelsAtPosition and
       pos notin state.carray.expressionChannelsAtPosition and
       pos notin state.ctpAtLink:
        return 0

    # Fast path: use precomputed (static) cascade table for single-value lookup
    if pos in state.cdCascadePos:
        let cascadeIdx = state.cdCascadePos[pos]
        if state.cdCascadeIsStatic[cascadeIdx]:
            let di = state.domIdx(pos, candidateValue)
            if di < 0: return 0
            let chans {.cursor.} = state.cdCascadeChans[cascadeIdx]
            let chanVals {.cursor.} = state.cdCascadeValues[cascadeIdx]
            let constraintIds {.cursor.} = state.cdCascadeConstraintIds[cascadeIdx]
            let coeffsL {.cursor.} = state.cdCascadeConstraintL[cascadeIdx]
            let coeffsR {.cursor.} = state.cdCascadeConstraintR[cascadeIdx]
            let nChans = chans.len
            for cli in 0..<constraintIds.len:
                let ci = constraintIds[cli]
                var delta: int
                if state.cdConstraintCanFast[ci]:
                    let cfast = state.channelDepConstraints[ci]
                    if cfast.stateType == PseudoBoolLinLeType:
                        let pb = cfast.pseudoBoolLinLeState
                        var newSum = pb.currentSum
                        for (cascIdx, coeff) in coeffsL[cli]:
                            let diff = chanVals[cascIdx][di] - state.assignment[chans[cascIdx]]
                            if diff != 0:
                                newSum += coeff * diff
                        delta = max(0, newSum - pb.rhs) - pb.cost
                    else:
                        let rc = cfast.relationalState
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
                elif state.cdSinglePos[ci] >= 0:
                    let sp = state.cdSinglePos[ci]
                    var newVal = state.assignment[sp]
                    for chanIdx in 0..<nChans:
                        if chans[chanIdx] == sp:
                            newVal = chanVals[chanIdx][di]
                            break
                    delta = state.singlePosPenalty(ci, newVal) -
                            state.channelDepConstraints[ci].penalty()
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
                    state.cdPerConstraintMaxDelta[ci] = max(state.cdPerConstraintMaxDelta[ci], safeAbs(delta))
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
    let hasMixed = state.cdMixedAt.len > pos and state.cdMixedAt[pos].len > 0
    if pos in state.oneHotChanges and pos notin state.ctpAtLink and not hasMixed:
        let changes {.cursor.} = state.oneHotChanges[pos]
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
                    let idxVal = bindingPtr[].evalIndex(state.assignment)
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
                    let fb {.cursor.} = state.flatMinMaxBindings[bi]
                    let newChanVal = evaluateFlatMinMax(fb, state.assignment)
                    let chanPos = fb.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            let srcInc = p == pos and state.inverseSavedBuf.len == 0
            if p in state.carray.profileMaxChannelsAtPosition:
                for bi in state.carray.profileMaxChannelsAtPosition[p]:
                    let newChanVal = if srcInc: state.pmEvalAt(bi, pos) else: state.pmEvalFull(bi)
                    let chanPos = state.carray.profileMaxChannelBindings[bi].channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.countEqChannelsAtPosition:
                for bi in state.carray.countEqChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.countEqChannelBindings[bi]
                    let newChanVal = if srcInc: state.countEqAfterSrc(bi, p, savedPos)
                                     else: evaluateCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.weightedCountEqChannelsAtPosition:
                for bi in state.carray.weightedCountEqChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bi]
                    let newChanVal = if srcInc: state.wCountEqAfterSrc(bi, p, savedPos)
                                     else: evaluateWeightedCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.conditionalCountEqChannelsAtPosition:
                for bi in state.carray.conditionalCountEqChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bi]
                    let newChanVal = evaluateConditionalCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.inverseChannelsAtPosition:
                for gi in state.carray.inverseChannelsAtPosition[p]:
                    let group {.cursor.} = state.carray.inverseChannelGroups[gi]
                    let newInverse = group.recomputeInverse(state.assignment)
                    for j, ipos in group.inversePositions:
                        if newInverse[j] != state.assignment[ipos]:
                            state.trackChannelChange(ipos, newInverse[j])
                            if ipos notin state.cdVisited:
                                state.cdVisited.incl(ipos)
                                state.cdWorklist.add(ipos)
            if p in state.carray.argmaxChannelsAtPosition:
                for bi in state.carray.argmaxChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.argmaxChannelBindings[bi]
                    let newChanVal = evaluateArgmax(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            # Expression channels (int_times/div/mod/plus): without this, effects
            # through e.g. squared loads were invisible to per-value move scoring.
            if p in state.carray.expressionChannelsAtPosition:
                for bi in state.carray.expressionChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.expressionChannelBindings[bi]
                    let newChanVal = binding.evalExpr(state.assignment)
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
            if p == pos and p in state.ctpAtLink:
                # Re-walk each circuit-time chain with the candidate link and treat
                # its changed time/accumulator positions as changed channels, so
                # constraints downstream of the chain see successor moves.
                for k in state.ctpAtLink[p]:
                    let ctc = state.circuitTimePropConstraints[k]
                    if p in ctc.positionToIndex:
                        for q in 0..<ctc.n: ctc.scratchLinks[q] = ctc.links[q]
                        let nodeIdx = ctc.positionToIndex[p]
                        ctc.scratchLinks[nodeIdx] = int(state.assignment[p]) - ctc.valueOffset
                        discard ctc.computePenalties(ctc.scratchLinks, ctc.scratchArrival, ctc.scratchDeparture)
                    elif ctc.releaseFastOk:
                        # Release (waiting) position on a valid tour: bounded re-walk,
                        # only the changed nodes' times can differ
                        let ri = ctc.releaseToIndex[p]
                        discard ctc.releaseRewalk(ri, state.assignment[p])
                        for q in ctc.relChangedNodes:
                            for (tp, v) in [(ctc.arrivalPositions[q], ctc.scratchArrival[q]),
                                            (ctc.departurePositions[q], ctc.scratchDeparture[q])]:
                                if tp >= 0 and v != state.assignment[tp]:
                                    state.trackChannelChange(tp, v)
                                    if tp notin state.cdVisited:
                                        state.cdVisited.incl(tp)
                                        state.cdWorklist.add(tp)
                        continue
                    else:
                        # Release (waiting) position: re-walk with the candidate release
                        for q in 0..<ctc.n: ctc.scratchLinks[q] = ctc.links[q]
                        let ri = ctc.releaseToIndex[p]
                        let saved = ctc.releaseVal[ri]
                        ctc.releaseVal[ri] = state.assignment[p]
                        discard ctc.computePenalties(ctc.scratchLinks, ctc.scratchArrival, ctc.scratchDeparture)
                        ctc.releaseVal[ri] = saved
                    for q in 0..<ctc.n:
                        for (tp, v) in [(ctc.arrivalPositions[q], ctc.scratchArrival[q]),
                                        (ctc.departurePositions[q], ctc.scratchDeparture[q])]:
                            if tp >= 0 and v != state.assignment[tp]:
                                state.trackChannelChange(tp, v)
                                if tp notin state.cdVisited:
                                    state.cdVisited.incl(tp)
                                    state.cdWorklist.add(tp)
            if p in state.carray.channelsAtPosition:
                for bi in state.carray.channelsAtPosition[p]:
                    let bindingPtr = addr state.carray.channelBindings[bi]
                    let idxVal = bindingPtr[].evalIndex(state.assignment)
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
                    let fb {.cursor.} = state.flatMinMaxBindings[bi]
                    let newChanVal = evaluateFlatMinMax(fb, state.assignment)
                    let chanPos = fb.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            let srcInc = p == pos and state.inverseSavedBuf.len == 0
            if p in state.carray.profileMaxChannelsAtPosition:
                for bi in state.carray.profileMaxChannelsAtPosition[p]:
                    let newChanVal = if srcInc: state.pmEvalAt(bi, pos) else: state.pmEvalFull(bi)
                    let chanPos = state.carray.profileMaxChannelBindings[bi].channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.countEqChannelsAtPosition:
                for bi in state.carray.countEqChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.countEqChannelBindings[bi]
                    let newChanVal = if srcInc: state.countEqAfterSrc(bi, p, savedPos)
                                     else: evaluateCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.weightedCountEqChannelsAtPosition:
                for bi in state.carray.weightedCountEqChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bi]
                    let newChanVal = if srcInc: state.wCountEqAfterSrc(bi, p, savedPos)
                                     else: evaluateWeightedCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.conditionalCountEqChannelsAtPosition:
                for bi in state.carray.conditionalCountEqChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bi]
                    let newChanVal = evaluateConditionalCountEq(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            if p in state.carray.inverseChannelsAtPosition:
                for gi in state.carray.inverseChannelsAtPosition[p]:
                    let group {.cursor.} = state.carray.inverseChannelGroups[gi]
                    let newInverse = group.recomputeInverse(state.assignment)
                    for j, ipos in group.inversePositions:
                        if newInverse[j] != state.assignment[ipos]:
                            state.trackChannelChange(ipos, newInverse[j])
                            if ipos notin state.cdVisited:
                                state.cdVisited.incl(ipos)
                                state.cdWorklist.add(ipos)
            if p in state.carray.argmaxChannelsAtPosition:
                for bi in state.carray.argmaxChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.argmaxChannelBindings[bi]
                    let newChanVal = evaluateArgmax(binding, state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)
            # Expression channels (int_times/div/mod/plus): without this, effects
            # through e.g. squared loads were invisible to per-value move scoring.
            if p in state.carray.expressionChannelsAtPosition:
                for bi in state.carray.expressionChannelsAtPosition[p]:
                    let binding {.cursor.} = state.carray.expressionChannelBindings[bi]
                    let newChanVal = binding.evalExpr(state.assignment)
                    let chanPos = binding.channelPosition
                    if newChanVal != state.assignment[chanPos]:
                        state.trackChannelChange(chanPos, newChanVal)
                        if chanPos notin state.cdVisited:
                            state.cdVisited.incl(chanPos)
                            state.cdWorklist.add(chanPos)

    when ProfileIteration:
        let cdWorklistEnd = epochTime()
        state.cdDomainEvals += state.cdDirtyPositions.len

    # Mixed constraints (see cdMixedAt): joint delta of the source change and
    # the simulated channel changes; movePenalty contributes nothing for them.
    var mixedDelta = 0
    if hasMixed:
        state.cdProcessed.clear()
        let sd = candidateValue - savedPos
        for m in state.cdMixedAt[pos]:
            state.cdProcessed.incl(m.ci)
            if not state.channelDepConstraintActive[m.ci]: continue
            let cfast = state.channelDepConstraints[m.ci]
            if cfast.stateType == PseudoBoolLinLeType:
                let pb = cfast.pseudoBoolLinLeState
                var newSum = pb.currentSum + m.l * sd
                for (cpos, coeff) in state.cdConstraintCoeffs[m.ci]:
                    if state.cdIsChanged[cpos]:
                        newSum += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                mixedDelta += max(0, newSum - pb.rhs) - pb.cost
            else:
                let rc = cfast.relationalState
                var newLeft = rc.leftValue + m.l * sd
                var newRight = rc.rightValue + m.r * sd
                for (cpos, coeff) in state.cdConstraintCoeffs[m.ci]:
                    if state.cdIsChanged[cpos]:
                        newLeft += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                for (cpos, coeff) in state.cdConstraintCoeffsR[m.ci]:
                    if state.cdIsChanged[cpos]:
                        newRight += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                mixedDelta += rc.computeCost(newLeft, newRight) - rc.cost

    if state.cdDirtyPositions.len == 0:
        # No channel changes — just restore pos and inverse
        state.assignment[pos] = savedPos
        for (fPos, savedVal) in state.inverseSavedBuf:
            state.assignment[fPos] = savedVal
        return mixedDelta

    # Compute penalty delta for affected channel-dep constraints.
    # Assignment still has simulated values so we can use position-indexed lookups.
    # Uses precomputed coefficient arrays (O(coefficients * array_access)) instead of
    # iterating cdChanges with hash table lookups (O(cdChanges * hash_lookup)).
    result = mixedDelta
    if state.chanPosToDepConstraintIdx.len > 0:
        if not hasMixed:
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
                        let cfast = state.channelDepConstraints[ci]
                        if cfast.stateType == PseudoBoolLinLeType:
                            let pb = cfast.pseudoBoolLinLeState
                            var newSum = pb.currentSum
                            for (cpos, coeff) in state.cdConstraintCoeffs[ci]:
                                if state.cdIsChanged[cpos]:
                                    newSum += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                            delta = max(0, newSum - pb.rhs) - pb.cost
                        else:
                            let rc = cfast.relationalState
                            var newLeft = rc.leftValue
                            var newRight = rc.rightValue
                            for (cpos, coeff) in state.cdConstraintCoeffs[ci]:
                                if state.cdIsChanged[cpos]:
                                    newLeft += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                            for (cpos, coeff) in state.cdConstraintCoeffsR[ci]:
                                if state.cdIsChanged[cpos]:
                                    newRight += coeff * (state.assignment[cpos] - state.cdSavedVal[cpos])
                            delta = rc.computeCost(newLeft, newRight) - rc.cost
                    elif state.cdSinglePos[ci] >= 0:
                        delta = state.singlePosPenalty(ci, state.assignment[state.cdSinglePos[ci]]) -
                                state.channelDepConstraints[ci].penalty()
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
                        state.cdPerConstraintMaxDelta[ci] = max(state.cdPerConstraintMaxDelta[ci], safeAbs(delta))
    else:
        # Fallback: iterate all relevant constraints (no reverse index)
        let relevantConstraints = state.channelDepConstraintsForPos.getOrDefault(pos, @[])
        for c in relevantConstraints:
            if hasMixed:
                var isMixed = false
                for m in state.cdMixedAt[pos]:
                    if cast[pointer](state.channelDepConstraints[m.ci]) == cast[pointer](c):
                        isMixed = true; break
                if isMixed: continue   # already scored jointly above
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
    chanVals: openArray[seq[T]], domain: openArray[T], penalties: var seq[int],
    sparse: bool = false) =
    ## Compute penalty deltas for all domain values given cascade channel values.
    ## chanVals[chanIdx][domainIdx] = the channel value for that domain entry.
    ## sparse=true: state.cdBatchChanged[di] lists the cascade entries whose value
    ## differs from the current assignment for domain value di (built by the
    ## dynamic cascade evaluation); only constraints touching those entries are
    ## scored. Exact: a constraint with no changed channel has zero delta.
    let chans {.cursor.} = state.cdCascadeChans[cascadeIdx]
    let constraintIds {.cursor.} = state.cdCascadeConstraintIds[cascadeIdx]
    let coeffsL {.cursor.} = state.cdCascadeConstraintL[cascadeIdx]
    let coeffsR {.cursor.} = state.cdCascadeConstraintR[cascadeIdx]
    let entryCons {.cursor.} = state.cdCascadeEntryCons[cascadeIdx]
    let nChans = chans.len

    let singleChanIdx {.cursor.} = state.cdCascadeSingleIdx[cascadeIdx]
    let srcCoeff {.cursor.} = state.cdCascadeSrcCoeff[cascadeIdx]
    let mixedClis {.cursor.} = state.cdCascadeMixedClis[cascadeIdx]
    let srcCur = state.assignment[state.cdCascadeSrcPos[cascadeIdx]]

    template cliDelta(cliArg, diArg: int, changedArg: ptr seq[int]): int =
        block:
            let cli = cliArg
            let di = diArg
            let changed: ptr seq[int] = changedArg
            let ci = constraintIds[cli]
            var delta: int
            if state.cdConstraintCanFast[ci]:
                let cfast = state.channelDepConstraints[ci]
                # Mixed constraint: apply the source position's own coefficient
                # together with the channel diffs (joint delta, see cdMixedAt).
                let sd = domain[di] - srcCur
                if cfast.stateType == PseudoBoolLinLeType:
                    let pb = cfast.pseudoBoolLinLeState
                    var newSum = pb.currentSum
                    for (cascIdx, coeff) in coeffsL[cli]:
                        let diff = chanVals[cascIdx][di] - state.assignment[chans[cascIdx]]
                        if diff != 0:
                            newSum += coeff * diff
                    if srcCoeff[cli].l != 0: newSum += srcCoeff[cli].l * sd
                    delta = max(0, newSum - pb.rhs) - pb.cost
                else:
                    let rc = cfast.relationalState
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
                    if srcCoeff[cli].l != 0: newLeft += srcCoeff[cli].l * sd
                    if srcCoeff[cli].r != 0: newRight += srcCoeff[cli].r * sd
                    delta = rc.computeCost(newLeft, newRight) - rc.cost
            elif state.channelDepConstraints[ci].stateType == DisjunctiveClauseType:
                # Fast DC path: compute penalty directly from precomputed cascade-to-term mappings
                let dc = state.channelDepConstraints[ci].disjunctiveClauseState
                let termCoeffs {.cursor.} = state.cdCascadeDCTermCoeffs[cascadeIdx][cli]
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
            elif state.cdSinglePos[ci] >= 0:
                let sp = state.cdSinglePos[ci]
                let k = singleChanIdx[cli]
                let newVal = if k >= 0: chanVals[k][di] else: state.assignment[sp]
                delta = state.singlePosPenalty(ci, newVal) -
                        state.channelDepConstraints[ci].penalty()
            else:
                let c = state.channelDepConstraints[ci]
                let oldPenalty = c.penalty()
                var anyChanged = false
                let useList = changed != nil
                let nIter = if useList: changed[].len else: nChans
                for k in 0..<nIter:
                    let chanIdx = if useList: changed[][k] else: k
                    let chanPos = chans[chanIdx]
                    let newVal = chanVals[chanIdx][di]
                    if newVal != state.assignment[chanPos] and chanPos in c.positions:
                        c.updatePosition(chanPos, newVal)
                        anyChanged = true
                if anyChanged:
                    delta = c.penalty() - oldPenalty
                    for k in 0..<nIter:
                        let chanIdx = if useList: changed[][k] else: k
                        let chanPos = chans[chanIdx]
                        if chanVals[chanIdx][di] != state.assignment[chanPos] and chanPos in c.positions:
                            c.updatePosition(chanPos, state.assignment[chanPos])
                else:
                    delta = 0
            if state.cdTrackPerConstraint and delta != 0:
                state.cdPerConstraintMaxDelta[ci] = max(state.cdPerConstraintMaxDelta[ci], safeAbs(delta))
            delta

    if not sparse:
        for di in 0..<domain.len:
            var totalDelta = 0
            for cli in 0..<constraintIds.len:
                totalDelta += cliDelta(cli, di, nil)
            penalties[di] = totalDelta
    else:
        if state.cdCliStamp.len < constraintIds.len:
            state.cdCliStamp.setLen(constraintIds.len)
        for di in 0..<domain.len:
            let changed = addr state.cdBatchChanged[di]
            if changed[].len == 0 and mixedClis.len == 0:
                penalties[di] = 0
                continue
            inc state.cdCliStampGen
            let gen = state.cdCliStampGen
            var totalDelta = 0
            for e in changed[]:
                for cli in entryCons[e]:
                    if state.cdCliStamp[cli] == gen: continue
                    state.cdCliStamp[cli] = gen
                    totalDelta += cliDelta(cli, di, changed)
            # Mixed constraints change with the source value even when no
            # channel does.
            for cli in mixedClis:
                if state.cdCliStamp[cli] == gen: continue
                state.cdCliStamp[cli] = gen
                totalDelta += cliDelta(cli, di, changed)
            penalties[di] = totalDelta

proc computeChannelDepPenaltiesInc[T](state: TabuState[T], pos: int, changedExternals: ptr PackedSet[int]) =
    ## Incremental cascade evaluation: only re-evaluate entries affected by changed
    ## external positions. Uses cached values for unaffected entries, with dirty
    ## propagation through forward deps when an entry's value changes.
    let domain {.cursor.} = state.sharedDomain[][pos]
    let cascadeIdx = state.cdCascadePos[pos]
    let nChans = state.cdCascadeChans[cascadeIdx].len
    let nDom = domain.len
    let chans {.cursor.} = state.cdCascadeChans[cascadeIdx]
    let bindings {.cursor.} = state.cdCascadeBindings[cascadeIdx]
    let entryKinds {.cursor.} = state.cdCascadeEntryKind[cascadeIdx]
    let forwardDeps {.cursor.} = state.cdCascadeForwardDeps[cascadeIdx]
    let extPosToEntries {.cursor.} = state.cdCascadeExtPosToEntries[cascadeIdx]

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
                    let fb {.cursor.} = state.flatMinMaxBindings[bindings[ci]]
                    newVal = evaluateFlatMinMax(fb, state.assignment)
                of ceCountEq:
                    let binding {.cursor.} = state.carray.countEqChannelBindings[bindings[ci]]
                    newVal = evaluateCountEq(binding, state.assignment)
                of ceConditionalCountEq:
                    let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bindings[ci]]
                    newVal = evaluateConditionalCountEq(binding, state.assignment)
                of ceExpression:
                    newVal = state.carray.expressionChannelBindings[bindings[ci]].evalExpr(state.assignment)
                of ceWeightedCountEq:
                    let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bindings[ci]]
                    newVal = evaluateWeightedCountEq(binding, state.assignment)
                of ceArgmax:
                    let binding {.cursor.} = state.carray.argmaxChannelBindings[bindings[ci]]
                    newVal = evaluateArgmax(binding, state.assignment)
                of ceCrossingCountMax:
                    let binding {.cursor.} = state.carray.crossingCountMaxChannelBindings[bindings[ci]]
                    newVal = evaluateCrossingCountMax(binding, state.assignment)
                of ceProfileMax:
                    newVal = state.pmEvalAt(bindings[ci], pos)
                of ceElement:
                    let bindingPtr = addr state.carray.channelBindings[bindings[ci]]
                    let idxVal = bindingPtr[].evalIndex(state.assignment)
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

proc cdCascadeScoresConstraint[T](state: TabuState[T], pos: int, c: StatefulConstraint[T]): bool =
    ## Debug: is constraint c scored by pos's cascade?
    if pos notin state.cdCascadePos: return false
    for dci in state.cdCascadeConstraintIds[state.cdCascadePos[pos]]:
        if cast[pointer](state.channelDepConstraints[dci]) == cast[pointer](c): return true
    false

proc cdCascadeCacheValid[T](state: TabuState[T], pos: int): bool {.inline.} =
    ## True when pos has a cascade whose cached per-value channel values (or
    ## static table) reflect the current values of every external input.
    if pos notin state.cdCascadePos: return false
    let cascadeIdx = state.cdCascadePos[pos]
    if state.cdCascadeIsStatic[cascadeIdx]: return true
    state.cdCacheStamp[pos] >= 0 and state.cdCacheStamp[pos] >= state.cdCacheDirty[pos]

proc rescoreCascadeFromCache[T](state: TabuState[T], pos: int) =
    ## Recompute channelDepPenalties[pos] from the cascade's cached channel
    ## values (valid per cdCascadeCacheValid): constraints x domain work
    ## instead of entries x domain evaluations.
    let cascadeIdx = state.cdCascadePos[pos]
    let domain {.cursor.} = state.sharedDomain[][pos]
    if state.cdCascadeIsStatic[cascadeIdx]:
        state.computeCascadePenalties(cascadeIdx,
            state.cdCascadeValues[cascadeIdx], domain, state.channelDepPenalties[pos])
    else:
        state.computeCascadePenalties(cascadeIdx,
            state.cdCascadeCachedValues[cascadeIdx], domain, state.channelDepPenalties[pos])

proc computeChannelDepPenaltiesAt[T](state: TabuState[T], pos: int) =
    ## Compute channelDepPenalties[pos] for all domain values.
    ## Uses cascade topology for batch evaluation (both static and dynamic).
    ## Static cascades use precomputed channel values; dynamic cascades evaluate at runtime.
    ## Falls back to per-value computeChannelDepDelta for positions without cascade topology.
    let domain {.cursor.} = state.sharedDomain[][pos]
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
            let chans {.cursor.} = state.cdCascadeChans[cascadeIdx]
            let bindings {.cursor.} = state.cdCascadeBindings[cascadeIdx]
            let entryKinds {.cursor.} = state.cdCascadeEntryKind[cascadeIdx]

            # Save original assignment values
            let savedPos = state.assignment[pos]
            for ci in 0..<nChans:
                state.cdBatchSaved[ci] = state.assignment[chans[ci]]

            # Sparse evaluation: per domain value, only entries downstream of a
            # changed input are re-evaluated (dirty propagation in topological
            # order), and the entries whose value changed are recorded for the
            # sparse penalty pass. Falls back to dense when the cascade has a
            # backward dependency (reader ordered before the entry it reads).
            let useSparse = not state.cdCascadeHasBackEdge[cascadeIdx]
            if state.cdBatchChanged.len < nDom: state.cdBatchChanged.setLen(nDom)
            if useSparse:
                let nSrc = state.cdCascadeNSrcReaders[cascadeIdx]
                let fwd {.cursor.} = state.cdCascadeForwardDeps[cascadeIdx]
                # Source-reader element entries with a linear index: in the
                # sparse path their other inputs are all external (a cascade
                # channel input would be a back edge), so the index is an
                # affine function of the probed value: one dot product per
                # batch instead of one per domain value (kitchen widths: 71
                # values x ~30 reified offset comparisons per batch).
                if state.cdSrcLinOk.len < nSrc:
                    state.cdSrcLinOk.setLen(nSrc)
                    state.cdSrcLinBase.setLen(nSrc)
                    state.cdSrcLinCoeff.setLen(nSrc)
                for ci in 0..<nSrc:
                    state.cdSrcLinOk[ci] = false
                    if entryKinds[ci] == ceElement and not gNoSrcLin:
                        let b = addr state.carray.channelBindings[bindings[ci]]
                        if b.linearIndex:
                            for k in 0..<b.linPositions.len:
                                if b.linPositions[k] == pos:
                                    let coeff = b.linCoeffs[k]
                                    state.cdSrcLinBase[ci] = b[].evalIndex(state.assignment) - coeff * savedPos
                                    state.cdSrcLinCoeff[ci] = coeff
                                    state.cdSrcLinOk[ci] = true
                                    break
                for di in 0..<nDom:
                    state.cdBatchChanged[di].setLen(0)
                    if domain[di] == savedPos:
                        for ci in 0..<nChans: state.cdBatchValues[ci][di] = state.cdBatchSaved[ci]
                        continue
                    state.assignment[pos] = domain[di]
                    for ci in 0..<nSrc: state.cdCascadeDirtyDV[ci] = true
                    for ci in 0..<nChans:
                        if not state.cdCascadeDirtyDV[ci]:
                            state.cdBatchValues[ci][di] = state.cdBatchSaved[ci]
                            continue
                        state.cdCascadeDirtyDV[ci] = false
                        case entryKinds[ci]
                        of ceMinMax:
                            # Min/max binding: evaluate using flat linear representation
                            let fb {.cursor.} = state.flatMinMaxBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateFlatMinMax(fb, state.assignment)
                        of ceCountEq:
                            # Source readers update incrementally (pos is the only change)
                            if ci < nSrc:
                                state.cdBatchValues[ci][di] = state.countEqAfterSrc(bindings[ci], pos, savedPos)
                            else:
                                let binding {.cursor.} = state.carray.countEqChannelBindings[bindings[ci]]
                                state.cdBatchValues[ci][di] = evaluateCountEq(binding, state.assignment)
                        of ceConditionalCountEq:
                            # ConditionalCountEq binding: count matching with filter condition
                            let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateConditionalCountEq(binding, state.assignment)
                        of ceExpression:
                            state.cdBatchValues[ci][di] = state.carray.expressionChannelBindings[bindings[ci]].evalExpr(state.assignment)
                        of ceWeightedCountEq:
                            if ci < nSrc:
                                state.cdBatchValues[ci][di] = state.wCountEqAfterSrc(bindings[ci], pos, savedPos)
                            else:
                                let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bindings[ci]]
                                state.cdBatchValues[ci][di] = evaluateWeightedCountEq(binding, state.assignment)
                        of ceArgmax:
                            # Argmax binding: evaluate input expressions and find max index
                            let binding {.cursor.} = state.carray.argmaxChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateArgmax(binding, state.assignment)
                        of ceCrossingCountMax:
                            # Crossing count max: sweep-line evaluation
                            let binding {.cursor.} = state.carray.crossingCountMaxChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateCrossingCountMax(binding, state.assignment)
                        of ceProfileMax:
                            state.cdBatchValues[ci][di] = state.pmEvalAt(bindings[ci], pos)
                        of ceElement:
                            # Element binding: evaluate index expression and look up array
                            let bindingPtr = addr state.carray.channelBindings[bindings[ci]]
                            let idxVal = if ci < nSrc and state.cdSrcLinOk[ci]:
                                             state.cdSrcLinBase[ci] + state.cdSrcLinCoeff[ci] * domain[di]
                                         else:
                                             bindingPtr[].evalIndex(state.assignment)
                            if idxVal >= 0 and idxVal < bindingPtr.arrayElements.len:
                                let elem = bindingPtr.arrayElements[idxVal]
                                state.cdBatchValues[ci][di] = if elem.isConstant: elem.constantValue
                                                               else: state.assignment[elem.variablePosition] + elem.offset
                            else:
                                state.cdBatchValues[ci][di] = state.cdBatchSaved[ci]
                        if state.cdBatchValues[ci][di] != state.cdBatchSaved[ci]:
                            state.assignment[chans[ci]] = state.cdBatchValues[ci][di]
                            state.cdBatchChanged[di].add(ci)
                            for r in fwd[ci]: state.cdCascadeDirtyDV[r] = true
                    for ci in state.cdBatchChanged[di]:
                        state.assignment[chans[ci]] = state.cdBatchSaved[ci]
                    state.assignment[pos] = savedPos
            else:
                # Evaluate cascade for all domain values using in-place modify-restore
                for di in 0..<nDom:
                    state.assignment[pos] = domain[di]
                    for ci in 0..<nChans:
                        case entryKinds[ci]
                        of ceMinMax:
                            # Min/max binding: evaluate using flat linear representation
                            let fb {.cursor.} = state.flatMinMaxBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateFlatMinMax(fb, state.assignment)
                        of ceCountEq:
                            # CountEq binding: count matching values over input positions
                            let binding {.cursor.} = state.carray.countEqChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateCountEq(binding, state.assignment)
                        of ceConditionalCountEq:
                            # ConditionalCountEq binding: count matching with filter condition
                            let binding {.cursor.} = state.carray.conditionalCountEqChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateConditionalCountEq(binding, state.assignment)
                        of ceExpression:
                            state.cdBatchValues[ci][di] = state.carray.expressionChannelBindings[bindings[ci]].evalExpr(state.assignment)
                        of ceWeightedCountEq:
                            # WeightedCountEq binding: sum weights for matching values
                            let binding {.cursor.} = state.carray.weightedCountEqChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateWeightedCountEq(binding, state.assignment)
                        of ceArgmax:
                            # Argmax binding: evaluate input expressions and find max index
                            let binding {.cursor.} = state.carray.argmaxChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateArgmax(binding, state.assignment)
                        of ceCrossingCountMax:
                            # Crossing count max: sweep-line evaluation
                            let binding {.cursor.} = state.carray.crossingCountMaxChannelBindings[bindings[ci]]
                            state.cdBatchValues[ci][di] = evaluateCrossingCountMax(binding, state.assignment)
                        of ceProfileMax:
                            state.cdBatchValues[ci][di] = state.pmEvalAt(bindings[ci], pos)
                        of ceElement:
                            # Element binding: evaluate index expression and look up array
                            let bindingPtr = addr state.carray.channelBindings[bindings[ci]]
                            let idxVal = bindingPtr[].evalIndex(state.assignment)
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
            state.cdCacheStamp[pos] = state.cdMoveSeq

            when ProfileIteration:
                let tBind1CD = epochTime()
                state.cdCascadeBindingTime += tBind1CD - tBind0CD

            # Compute penalties from batch channel values
            state.computeCascadePenalties(cascadeIdx,
                state.cdBatchValues, domain, state.channelDepPenalties[pos], sparse = useSparse)
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


proc applyUniformDelta[T](state: TabuState[T], pos: int, changedChannels: seq[int],
                          movedPosition: int = -1) {.inline.} =
    ## Apply uniform cost delta for channel-dep penalties at position.
    ## For cascade positions: checks if external dependencies changed. If not,
    ## applies uniform delta (exact). If only min/max external deps changed (not
    ## element deps), re-evaluates only the min/max entries using cached element
    ## cascade values. Falls back to full cascade recomputation if element deps changed.
    ## For non-cascade positions: falls back to full per-value recomputation.
    if pos notin state.cdCascadePos:
        # Non-cascade: full recomputation
        let domain {.cursor.} = state.sharedDomain[][pos]
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
    let elemExtDeps {.cursor.} = state.cdCascadeElemExtDeps[cascadeIdx]
    let externalDeps {.cursor.} = state.cdCascadeExternalDeps[cascadeIdx]
    # The moved search position itself is an external input of other cascades
    # whose entries read several search positions (count / weighted-count loads,
    # element arrays). It is not in changedChannels, so it must be checked
    # explicitly — otherwise the uniform shortcut below keeps stale per-value
    # channel values (wrong move scores in non-lean search).
    let movedIsExt = movedPosition >= 0 and movedPosition in externalDeps
    if movedIsExt:
        anyDepChanged = true
        if movedPosition in elemExtDeps: elemDepChanged = true
    if externalDeps.len > 0 and not elemDepChanged:
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
        if movedIsExt: changedExternals.incl(movedPosition)
        for chanPos in changedChannels:
            if chanPos in externalDeps:
                changedExternals.incl(chanPos)
        let domain {.cursor.} = state.sharedDomain[][pos]
        var oldPenalties = newSeq[int](domain.len)
        for i in 0..<domain.len:
            oldPenalties[i] = state.channelDepPenalties[pos][i]
        state.computeChannelDepPenaltiesInc(pos, addr changedExternals)
        state.cdCacheStamp[pos] = state.cdMoveSeq
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
        let domain {.cursor.} = state.sharedDomain[][pos]
        let nDom = domain.len
        let bindings {.cursor.} = state.cdCascadeBindings[cascadeIdx]
        let mmIndices {.cursor.} = state.cdCascadeMinMaxIdx[cascadeIdx]
        let mmInputs {.cursor.} = state.cdCascadeMinMaxInputs[cascadeIdx]
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
        let domain {.cursor.} = state.sharedDomain[][pos]
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
        # A constraint of this cascade also reads a changed position outside it
        # (e.g. a clause over a cascade channel AND a CTP-written indicator):
        # per-value deltas shift non-uniformly — recompute fully.
        let consExt {.cursor.} = state.cdCascadeConsExt[cascadeIdx]
        var consInputChanged = movedPosition >= 0 and movedPosition in consExt
        if not consInputChanged and consExt.len > 0:
            for chanPos in changedChannels:
                if chanPos in consExt:
                    consInputChanged = true
                    break
        # A hinged/scaled objective bound (costScale > 1) is not linear in its
        # value: when its cost moved, the per-value deltas at this position
        # shift non-uniformly (knee + rounding), so a uniform shift would leave
        # stale scores (kitchen under scaling: 45 CHECK_DELTA mismatches/30 s).
        var scaledChanged = false
        if not consInputChanged:
            for ci in state.cdCascadeConstraintIds[cascadeIdx]:
                if not state.channelDepConstraintActive[ci]: continue
                let c = state.channelDepConstraints[ci]
                if c.stateType == RelationalType and c.relationalState.costScale > 1 and
                        c.penalty() != state.cdSavedConstraintCosts[ci]:
                    scaledChanged = true
                    break
        if consInputChanged or scaledChanged:
            # No cascade input changed, so the per-value channel values cached
            # by the last full evaluation are still exact: re-score the
            # constraints from the cache instead of re-evaluating every entry
            # for every domain value. An objective bound over hundreds of
            # search variables otherwise forces that full pass on EVERY move
            # (kitchen probes: 60 it/s vs 500 without the bound).
            when ProfileIteration: state.cdConsRescoreCalls += 1
            let domain {.cursor.} = state.sharedDomain[][pos]
            var oldPenalties = newSeq[int](domain.len)
            for i in 0..<domain.len:
                oldPenalties[i] = state.channelDepPenalties[pos][i]
            if not gNoCacheRescore and state.cdCascadeCacheValid(pos):
                state.rescoreCascadeFromCache(pos)
            else:
                state.computeChannelDepPenaltiesAt(pos)
            for i in 0..<domain.len:
                let delta = state.channelDepPenalties[pos][i] - oldPenalties[i]
                if delta != 0:
                    state.penaltyMap[pos][i] += delta
            return
    if not anyDepChanged:
        # No external deps changed — uniform delta is exact
        when ProfileIteration: state.cdUniformCalls += 1
        let constraintIds {.cursor.} = state.cdCascadeConstraintIds[cascadeIdx]
        var uniformDelta = 0
        for ci in constraintIds:
            if not state.channelDepConstraintActive[ci]: continue
            let newCost = state.channelDepConstraints[ci].penalty()
            let savedCost = state.cdSavedConstraintCosts[ci]
            if savedCost != newCost:
                uniformDelta += savedCost - newCost
        if uniformDelta != 0:
            let domain {.cursor.} = state.sharedDomain[][pos]
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
            let currentIdx = state.domIdx(pos, currentVal)
            if currentIdx >= 0 and currentIdx in affectedIndices:
                # Full recomputation — use uniform delta
                when ProfileIteration: state.cdFullPos += 1
                state.applyUniformDelta(pos, changedChannels, movedPosition)
            else:
                # Targeted recomputation — only affected domain values
                when ProfileIteration: state.cdTargetedPos += 1
                let domain {.cursor.} = state.sharedDomain[][pos]
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
            if chanPos in state.cdReadersOf:
                for pos in state.cdReadersOf[chanPos]:
                    if pos != movedPosition and pos notin state.cdTargetedUpdates:
                        nonOneHotPositions.incl(pos)
        for pos in nonOneHotPositions.items:
            if state.isLazy[pos]: continue
            when ProfileIteration: state.cdNonOneHotPos += 1
            state.applyUniformDelta(pos, changedChannels, movedPosition)
    else:
        # No reverse index — use channelDepPosForChannel with uniform delta
        var affectedPositions: PackedSet[int]
        for chanPos in changedChannels:
            if chanPos in state.channelDepPosForChannel:
                for pos in state.channelDepPosForChannel[chanPos]:
                    affectedPositions.incl(pos)
            if chanPos in state.cdReadersOf:
                for pos in state.cdReadersOf[chanPos]:
                    affectedPositions.incl(pos)
        for pos in affectedPositions.items:
            if pos == movedPosition: continue
            if state.isLazy[pos]: continue
            state.applyUniformDelta(pos, changedChannels, movedPosition)
