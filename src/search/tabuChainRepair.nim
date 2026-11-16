## Chain repair moves for binary implication webs.
## Included from tabu.nim — not a standalone module.
##
## Selecting one link in a service chain (sdn-chain) needs its node selected,
## which breaks the exact count of selected nodes, which needs another node
## deselected, which breaks the link that held that node... Each single flip
## along the way has delta >= 0, so tabu never strings them together. A chain
## move changes one input of a violated constraint (the anchor), then
## repeatedly repairs one constraint the chain has broken, from that
## constraint's own inputs (sideways steps allowed). The chain is kept only
## when it ends below the starting cost without adding hard violations.
## Only two-value inputs take part: moving many-valued inputs (which node
## hosts a VNF) to their best costDelta value gained nothing on sdn-chain
## and cost workforce-alloc up to 2x.

const ChainMaxSteps = 32         # follow-up moves after the anchor
const ChainMaxPartners = 48      # sources scored per broken constraint
const ChainMaxAnchors = 24       # anchors tried per violated constraint
const ChainMaxConstraints = 8    # violated constraints sampled per call

proc chainFlipValue[T](state: TabuState[T], p: int, v: var T): bool {.inline.} =
    ## The other value of a two-value search position.
    if p in state.carray.fixedPositions or p in state.carray.channelPositions: return false
    let dom {.cursor.} = state.sharedDomain[][p]
    if dom.len != 2: return false
    v = if state.assignment[p] == dom[0]: dom[1] else: dom[0]
    true

proc chainAddSources[T](state: TabuState[T], c: StatefulConstraint[T], dest: var PackedSet[int]) =
    ## Search positions that drive constraint c, directly or through channels.
    for q in c.positions.items:
        if q in state.carray.channelPositions:
            state.channelDepPosForChannel.withValue(q, srcs):
                for s in srcs[]: dest.incl(s)
        else:
            dest.incl(q)

proc tryChainRepair[T](state: TabuState[T]): bool =
    ## One chain move that lowers the cost, from a sample of the violated
    ## constraints; false when none of the sampled chains improves.
    if state.cost == 0: return false
    var violated: seq[StatefulConstraint[T]]
    for c in state.constraints:
        if c.penalty() > 0: violated.add(c)
    shuffle(violated)
    if violated.len > ChainMaxConstraints: violated.setLen(ChainMaxConstraints)
    let origCost = state.cost
    # Hard violations (all but the optimizer's objective bound) must not grow:
    # under a scaled bound a chain could otherwise buy objective with a hard
    # violation, steering probes away from feasibility.
    template hardCost(): int =
        (if state.boundConstraint != nil: state.cost - state.boundConstraint.penalty()
         else: state.cost)
    let origHard = hardCost()
    # Under a scaled bound most objective gains are invisible in the cost
    # (one unit per costScale objective units): compare the raw bound slack
    # too, so a chain that lowers the objective without a visible cost drop
    # still counts.
    let scaled = state.scaledObjectiveBound()
    template slack(): T = (if scaled: state.boundSlack() else: T(0))
    let origSlack = slack()
    template accepted(): bool =
        hardCost() <= origHard and
            (state.cost < origCost or (scaled and state.cost == origCost and slack() < origSlack))
    var changes: seq[(int, T)]
    for c in violated:
        var srcSet: PackedSet[int]
        state.chainAddSources(c, srcSet)
        # A position read directly by c is an anchor only when its flip lowers
        # c (cheap moveDelta: of an objective bound's 625 link terms, the ~20
        # selected ones); channel-driven sources cannot be pre-scored this way.
        var direct: PackedSet[int]
        for q in c.positions.items:
            if q notin state.carray.channelPositions: direct.incl(q)
        var anchors: seq[(int, T)]
        for p in srcSet:
            var v: T
            if not state.chainFlipValue(p, v): continue
            if p in direct:
                if scaled and c == state.boundConstraint:
                    # The scaled delta rounds most link drops to 0: use the raw coefficient
                    let rc = c.relationalState
                    if rc.leftExpr.kind == SumExpr and rc.leftExpr.sumExpr.evalMethod == PositionBased:
                        let k = rc.leftExpr.sumExpr.coefficient.getOrDefault(p, T(0))
                        let dir: T = (if rc.relation in {LessThan, LessThanEq}: T(1) else: T(-1))
                        if dir * k * (v - state.assignment[p]) >= 0: continue
                    elif c.moveDelta(p, state.assignment[p], v) >= 0: continue
                elif c.moveDelta(p, state.assignment[p], v) >= 0: continue
            anchors.add((p, v))
        shuffle(anchors)
        if anchors.len > ChainMaxAnchors:
            # Too many to try (a 1543-term "some selected link enters this
            # node" sum): keep the cheapest flips by costDelta. The repairing
            # link costs at most the count it unbalances; a random one costs
            # more, and a random sample of 24 found it ~1.5% of the time.
            var scored: seq[(int, int)]
            for i, (p, v) in anchors: scored.add((state.costDelta(p, v), i))
            scored.sort()
            var kept: seq[(int, T)]
            for k in 0 ..< ChainMaxAnchors: kept.add(anchors[scored[k][1]])
            anchors = kept
        if anchors.len > ChainMaxAnchors: anchors.setLen(ChainMaxAnchors)
        for (anchor, av) in anchors:
            if (state.stopSignal != nil and state.stopSignal[].load()) or
                    (state.searchDeadline > 0 and epochTime() > state.searchDeadline):
                return false
            let cBefore = c.penalty()
            let slackBefore = slack()
            changes.setLen(0)
            state.simLean(changes, anchor, av)
            # The anchor must start repairing the constraint it came from
            let repairs = c.penalty() < cBefore or
                (scaled and c == state.boundConstraint and c.penalty() == cBefore and slack() < slackBefore)
            if not repairs:
                state.rollbackSim(changes, 0)
                continue
            var touched: PackedSet[int]
            touched.incl(anchor)
            for step in 0 ..< ChainMaxSteps:
                if accepted(): break
                # Constraints the chain has broken (the objective bound aside:
                # the anchor lowered it, the steps restore feasibility)
                var broken: seq[StatefulConstraint[T]]
                var seenC: HashSet[pointer]
                template consider(cc: StatefulConstraint[T]) =
                    if cc.penalty() > 0 and cc != state.boundConstraint and
                            not seenC.containsOrIncl(cast[pointer](cc)):
                        broken.add(cc)
                for (q, _) in changes:
                    for cc in state.constraintsAtPosition[q]: consider(cc)
                    state.channelDepConstraintsForPos.withValue(q, cs):
                        for cc in cs[]: consider(cc)
                if broken.len == 0: break
                shuffle(broken)
                # Each step repairs one broken constraint from its own sources,
                # scored by (hard delta, cost delta, raw slack). Scoring the
                # union of all broken constraints' sources by cost alone drowned
                # the few repairing flips (one domain_path entry per broken
                # reachability iff) and traded objective for hard violations
                # one for one under an unscaled bound.
                var moved = false
                for bc in broken:
                    if moved: break
                    var srcs: PackedSet[int]
                    state.chainAddSources(bc, srcs)
                    var cands: seq[int]
                    for p in srcs:
                        if p notin touched: cands.add(p)
                    shuffle(cands)
                    if cands.len > ChainMaxPartners: cands.setLen(ChainMaxPartners)
                    var bestHard = high(int)
                    var bestDelta = high(int)
                    var bestSlack = high(T)
                    var bestPos = -1
                    var bestVal: T
                    for p in cands:
                        var v: T
                        if not state.chainFlipValue(p, v): continue
                        let old = state.assignment[p]
                        let before = state.cost
                        let hBefore = hardCost()
                        state.assignValueLean(p, v)
                        let d = state.cost - before
                        let dh = hardCost() - hBefore
                        let sl = slack()
                        state.assignValueLean(p, old)
                        if dh < bestHard or (dh == bestHard and
                                (d < bestDelta or (d == bestDelta and sl < bestSlack))):
                            bestHard = dh
                            bestDelta = d
                            bestSlack = sl
                            bestPos = p
                            bestVal = v
                    # Sideways steps are fine; one that adds hard cost, or cost
                    # without repairing anything hard, is no repair
                    if bestPos < 0 or bestHard > 0 or (bestHard == 0 and bestDelta > 0): continue
                    state.simLean(changes, bestPos, bestVal)
                    touched.incl(bestPos)
                    moved = true
                if not moved: break
            if accepted():
                inc state.chainRepairApplied
                state.settleSim(changes, keep = true)
                return true
            state.rollbackSim(changes, 0)
    false
