## Rip-up-and-reroute moves for subcircuit routing models.
## Included from tabu.nim — not a standalone module.
##
## Grid routing models (orthorio: belts carrying agents from fixed starts to
## fixed ends) encode the routes as a subcircuit over cell successors whose
## domains are the grid moves (neighbours, tunnel jumps), plus per-cell side
## variables (belt type, agent label) tied to the successor by tables. A
## route can only move as a whole: changing one cell's successor or belt
## type breaks the path, so single-variable tabu search ends in a state with
## no path structure at all.
##
## The move keeps one route per free segment of the circuit, from a node
## that must be on the circuit and whose successor is free (a source) to a
## node that must be on the circuit and whose predecessor is free (a
## target), pairing sources with targets by the values the successors carry
## (agent labels). It rips up a route, or a stretch of it, and replaces it
## with a shortest path over (cell, type) states, where a cell's type is the
## side variable tied to its successor by a two-input constraint (the belt
## type through its successor table). Which types a cell may take for each
## outgoing edge, and which pairs of types consecutive cells may take, are
## read off the model's own constraints once, so the router only builds
## routes whose consecutive cells fit together (no turn out of a tunnel
## exit). The remaining constraints (tunnel clearance, forbidden shapes) are
## learnt: violated constraints after a move add history cost to the cells
## and edges they read (negotiated congestion, as in PathFinder FPGA
## routing). Routes may share a cell at a congestion cost that grows over
## time; crusher's state holds whichever route was written last there, and
## the shared cell shows up as violations until the routes separate.

import std/heapqueue

const
    RerouteRestartAfter = 600     # non-improving reroutes before a fresh construction
    RerouteAcceptWorse = 0.2      # chance to keep a worsening reroute
    ReroutePresGrowth = 1.02      # present-congestion growth per reroute
    RerouteHistStep = 0.3         # history added per violated constraint read, per reroute
    RerouteBlameEvery = 4         # reroutes between history updates
    ReroutePresMax = 50.0
    RerouteNoise = 0.3            # random node-cost jitter (route diversity)
    RerouteMaxSideSources = 6     # node blame only for constraints this small
    RerouteMaxTypes = 32          # type domains are bit masks
    RerouteClearCost = 10.0       # router cost of a required neighbour left empty

proc rrIsSearch[T](state: TabuState[T], p: int): bool {.inline.} =
    p >= 0 and p notin state.carray.fixedPositions and
        p notin state.carray.channelPositions and not state.isLazy[p]

proc rrSources[T](state: TabuState[T], c: StatefulConstraint[T], dest: var PackedSet[int]) =
    ## Positions that drive c: direct ones and the sources of its channels.
    for q in c.positions.items:
        if q in state.carray.channelPositions:
            state.channelDepPosForChannel.withValue(q, srcs):
                for s in srcs[]: dest.incl(s)
        else:
            dest.incl(q)

proc rrSucc[T](state: TabuState[T], net: RerouteNet[T], i: int): int {.inline.} =
    int(state.assignment[net.pos[i]]) - net.offset

proc rrTypeIdx[T](state: TabuState[T], net: RerouteNet[T], i: int): int =
    ## Index of node i's current type in its type domain (0 when untyped,
    ## -1 when the value is outside it).
    if net.typePos[i] < 0: return 0
    let v = state.assignment[net.typePos[i]]
    for k, x in net.typeDom[i]:
        if x == v: return k
    -1

proc rrAllTypes[T](net: RerouteNet[T], i: int): uint32 {.inline.} =
    if net.typePos[i] < 0: 1'u32
    else: (if net.typeDom[i].len >= 32: high(uint32) else: (1'u32 shl net.typeDom[i].len) - 1)

proc rrBuildTypes[T](state: TabuState[T], net: RerouteNet[T], circuitPos: PackedSet[int]) =
    ## Per node: which types fit each outgoing edge (its links), and which
    ## types of the successor fit each (edge, type) (its transition rules:
    ## constraints over the node's successor, its type and element channels
    ## indexed by its successor, i.e. the successor's type).
    let n = net.n
    net.allowMask = newSeq[seq[uint32]](n)
    net.compat = newSeq[seq[seq[uint32]]](n)
    net.anyAllow = newSeq[uint32](n)
    # Element channels indexed by each node's successor alone
    var elemOf = newSeq[PackedSet[int]](n)
    for i in 0 ..< n:
        let p = net.pos[i]
        if p in state.carray.channelsAtPosition:
            for bi in state.carray.channelsAtPosition[p]:
                let b = addr state.carray.channelBindings[bi]
                var only = b.indexExpression.positions.len > 0
                for q in b.indexExpression.positions.items:
                    if q != p: only = false
                if only: elemOf[i].incl(b.channelPosition)
    for i in 0 ..< n:
        let p = net.pos[i]
        let tp = net.typePos[i]
        # Transition constraints of node i
        var trans: seq[StatefulConstraint[T]]
        var seenC: HashSet[pointer]
        template consider(cc: StatefulConstraint[T]) =
            if not seenC.containsOrIncl(cast[pointer](cc)):
                var readsElem = false
                var ok = true
                for q in cc.positions.items:
                    if q == p or q == tp or q in state.carray.fixedPositions: continue
                    if q in elemOf[i]:
                        readsElem = true
                        continue
                    if q in state.carray.channelPositions:
                        var onlyP = false
                        state.channelDepPosForChannel.withValue(q, srcs):
                            onlyP = true
                            for s in srcs[]:
                                if s != p: onlyP = false
                        if onlyP: continue
                    ok = false
                    break
                if ok and readsElem: trans.add(cc)
        for cc in state.constraintsAtPosition[p]: consider(cc)
        state.channelDepConstraintsForPos.withValue(p, cs):
            for cc in cs[]: consider(cc)
        let links = if tp >= 0: net.typeLinks[i] else: @[]
        let pFixed = p in state.carray.fixedPositions
        let savedP = state.assignment[p]
        let savedT = if tp >= 0: state.assignment[tp] else: T(0)
        let nb = max(1, net.typeDom[i].len)
        net.allowMask[i] = newSeq[uint32](net.succ[i].len)
        net.compat[i] = newSeq[seq[uint32]](net.succ[i].len)
        for k, j in net.succ[i]:
            net.compat[i][k] = newSeq[uint32](nb)
            if not pFixed: state.assignValueLean(p, T(j + net.offset))
            elif int(savedP) - net.offset != j: continue
            let tj = net.typePos[j]
            let savedJ = if tj >= 0: state.assignment[tj] else: T(0)
            for b in 0 ..< nb:
                if tp >= 0: state.assignValueLean(tp, net.typeDom[i][b])
                var linkOk = true
                for cc in links:
                    if cc.penalty() > 0: linkOk = false
                if not linkOk: continue
                net.allowMask[i][k] = net.allowMask[i][k] or (1'u32 shl b)
                var mask = 0'u32
                for c in 0 ..< max(1, net.typeDom[j].len):
                    if tj >= 0 and tj != tp: state.assignValueLean(tj, net.typeDom[j][c])
                    var ok = true
                    for cc in trans:
                        if cc.penalty() > 0:
                            ok = false
                            break
                    if ok: mask = mask or (1'u32 shl c)
                net.compat[i][k][b] = mask
            if tj >= 0 and state.assignment[tj] != savedJ: state.assignValueLean(tj, savedJ)
            net.anyAllow[i] = net.anyAllow[i] or net.allowMask[i][k]
        if tp >= 0 and state.assignment[tp] != savedT: state.assignValueLean(tp, savedT)
        if not pFixed and state.assignment[p] != savedP: state.assignValueLean(p, savedP)
        if net.typePos[i] < 0: net.anyAllow[i] = 1'u32
    # Occupancy requirements: a constraint over node j's type and node m's
    # type alone that fails when m idles (a tunnel entry needs something to
    # pass under). The router charges for such m left empty.
    var nodeOfType: Table[int, int]
    for i in 0 ..< n:
        if net.typePos[i] >= 0: nodeOfType[net.typePos[i]] = i
    var idleType = newSeqWith(n, -1)
    for m in 0 ..< n:
        let tp = net.typePos[m]
        if tp < 0 or not net.canIdle[m]: continue
        let p = net.pos[m]
        let savedP = state.assignment[p]
        let savedT = state.assignment[tp]
        state.assignValueLean(p, T(m + net.offset))
        for b, v in net.typeDom[m]:
            state.assignValueLean(tp, v)
            var ok = true
            for cc in net.typeLinks[m]:
                if cc.penalty() > 0: ok = false
            if ok:
                idleType[m] = b
                break
        state.assignValueLean(tp, savedT)
        state.assignValueLean(p, savedP)
    net.occReq = newSeq[seq[seq[int]]](n)
    for j in 0 ..< n:
        let tj = net.typePos[j]
        net.occReq[j] = newSeq[seq[int]](max(1, net.typeDom[j].len))
        if tj < 0: continue
        # constraints over exactly {type_j, type_m}
        var pairs: seq[(StatefulConstraint[T], int)]
        for cc in state.constraintsAtPosition[tj]:
            var srcs: PackedSet[int]
            state.rrSources(cc, srcs)
            if srcs.len != 2: continue
            for q in srcs:
                if q != tj:
                    nodeOfType.withValue(q, m):
                        if idleType[m[]] >= 0: pairs.add((cc, m[]))
        state.channelDepConstraintsForPos.withValue(tj, cs):
            for cc in cs[]:
                var srcs: PackedSet[int]
                state.rrSources(cc, srcs)
                if srcs.len != 2: continue
                for q in srcs:
                    if q != tj:
                        nodeOfType.withValue(q, m):
                            if idleType[m[]] >= 0: pairs.add((cc, m[]))
        if pairs.len == 0: continue
        let savedJ = state.assignment[tj]
        for c, v in net.typeDom[j]:
            state.assignValueLean(tj, v)
            for (cc, m) in pairs:
                let tm = net.typePos[m]
                let savedM = state.assignment[tm]
                state.assignValueLean(tm, net.typeDom[m][idleType[m]])
                if cc.penalty() > 0 and m notin net.occReq[j][c]: net.occReq[j][c].add(m)
                state.assignValueLean(tm, savedM)
        state.assignValueLean(tj, savedJ)

proc rrBuild[T](state: TabuState[T]) =
    state.rerouteBuilt = true
    let tb = epochTime()
    for c in state.constraints:
        if c.stateType != SubcircuitType: continue
        let sc = c.subcircuitState
        let n = sc.n
        if n < 4: continue
        var net = RerouteNet[T](n: n, offset: sc.valueOffset)
        net.pos = sc.positionArray
        net.succ = newSeq[seq[int]](n)
        net.succIdx = newSeq[Table[int, int]](n)
        net.canIdle = newSeq[bool](n)
        net.fixedSucc = newSeqWith(n, -1)
        var ok = true
        var idle = 0
        for i in 0 ..< n:
            let p = net.pos[i]
            if p < 0 or p in state.carray.channelPositions or state.isLazy[p]:
                ok = false
                break
            let dom {.cursor.} = state.sharedDomain[][p]
            for v in dom:
                let j = int(v) - net.offset
                if j == i: net.canIdle[i] = true
                elif j >= 0 and j < n:
                    net.succIdx[i][j] = net.succ[i].len
                    net.succ[i].add(j)
            if dom.len == 1 and not net.canIdle[i] and net.succ[i].len == 1:
                net.fixedSucc[i] = net.succ[i][0]
            if net.canIdle[i]: inc idle
        # Routing needs optional cells to route through
        if not ok or idle * 4 < n: continue
        var fixedTarget = newSeq[bool](n)
        net.fixedPred = newSeqWith(n, -1)
        for i in 0 ..< n:
            if net.fixedSucc[i] >= 0:
                fixedTarget[net.fixedSucc[i]] = true
                net.fixedPred[net.fixedSucc[i]] = i
        for i in 0 ..< n:
            if net.canIdle[i]: continue
            if net.fixedSucc[i] < 0: net.sources.add(i)
            if not fixedTarget[i]: net.targets.add(i)
        if net.sources.len == 0 or net.sources.len != net.targets.len: continue
        # Routing skeleton: free segments between fixed links (each agent's
        # end is tied to the next agent's start). A subcircuit whose
        # mandatory nodes are free (a tour with optional visits) is not a
        # routing problem.
        var skeleton = true
        for s in net.sources:
            if net.fixedPred[s] < 0: skeleton = false
        for t in net.targets:
            if net.fixedSucc[t] < 0: skeleton = false
        if not skeleton: continue
        # Side variables of node i: search positions tied to its successor by
        # a two-input constraint (its type, e.g. the belt type through the
        # successor table), and results of element constraints indexed by
        # its successor (a value carried along the route, e.g. an agent label).
        var circuitPos: PackedSet[int]
        for p in net.pos: circuitPos.incl(p)
        net.sides = newSeq[seq[int]](n)
        net.sideLinks = newSeq[seq[seq[StatefulConstraint[T]]]](n)
        net.typePos = newSeqWith(n, -1)
        net.typeDom = newSeq[seq[T]](n)
        net.typeLinks = newSeq[seq[StatefulConstraint[T]]](n)
        for i in 0 ..< n:
            let p = net.pos[i]
            var seen: PackedSet[int]
            var links: Table[int, seq[StatefulConstraint[T]]]
            var typeCand: seq[int]
            template addSide(q: int, cc: StatefulConstraint[T], isType: bool) =
                if q != p and q notin circuitPos and state.rrIsSearch(q):
                    if not seen.containsOrIncl(q): net.sides[i].add(q)
                    links.mgetOrPut(q, @[]).add(cc)
                    if isType and q notin typeCand: typeCand.add(q)
            template consider(cc: StatefulConstraint[T]) =
                if cc.stateType == ElementType:
                    let es = cc.elementState
                    if es.evalMethod == PositionBased:
                        if es.indexPosition == p: addSide(es.valuePosition, cc, false)
                    elif es.indexExprPositions.len == 1 and p in es.indexExprPositions and
                            es.valueExprPositions.len == 1:
                        for q in es.valueExprPositions.keys: addSide(q, cc, false)
                else:
                    var srcs: PackedSet[int]
                    state.rrSources(cc, srcs)
                    if srcs.len == 2 and p in srcs:
                        for q in srcs: addSide(q, cc, true)
            for cc in state.constraintsAtPosition[p]: consider(cc)
            state.channelDepConstraintsForPos.withValue(p, cs):
                for cc in cs[]: consider(cc)
            for q in net.sides[i]: net.sideLinks[i].add(links.getOrDefault(q))
            if typeCand.len > 0 and state.sharedDomain[][typeCand[0]].len <= RerouteMaxTypes:
                net.typePos[i] = typeCand[0]
                net.typeDom[i] = state.sharedDomain[][typeCand[0]]
                net.typeLinks[i] = links[typeCand[0]]
        state.rrBuildTypes(net, circuitPos)
        # Side values of an idle node, from the constraints over that node's
        # own variables alone (empty belt, no agent): written directly when a
        # route frees the node.
        net.idleVals = newSeq[seq[T]](n)
        for m in 0 ..< n:
            if not net.canIdle[m]: continue
            let p = net.pos[m]
            var own: PackedSet[int]
            own.incl(p)
            for q in net.sides[m]: own.incl(q)
            var saved: seq[(int, T)]
            saved.add((p, state.assignment[p]))
            for q in net.sides[m]: saved.add((q, state.assignment[q]))
            state.assignValueLean(p, T(m + net.offset))
            var order = net.sides[m]
            let tp = net.typePos[m]
            if tp >= 0:
                order.keepItIf(it != tp)
                order.insert(tp, 0)
            var vals: Table[int, T]
            for q in order:
                var local: seq[StatefulConstraint[T]]
                var seenC: HashSet[pointer]
                template consider(cc: StatefulConstraint[T]) =
                    if not seenC.containsOrIncl(cast[pointer](cc)):
                        var srcs: PackedSet[int]
                        state.rrSources(cc, srcs)
                        var inside = true
                        for x in srcs:
                            if x notin own and x notin state.carray.fixedPositions: inside = false
                        if inside: local.add(cc)
                for cc in state.constraintsAtPosition[q]: consider(cc)
                state.channelDepConstraintsForPos.withValue(q, cs):
                    for cc in cs[]: consider(cc)
                var bestV = state.assignment[q]
                var bestL = high(int)
                for v in state.sharedDomain[][q]:
                    state.assignValueLean(q, v)
                    var lv = 0
                    for cc in local:
                        if cc.penalty() > 0: inc lv
                    if lv < bestL:
                        bestL = lv
                        bestV = v
                state.assignValueLean(q, bestV)
                vals[q] = bestV
            for q in net.sides[m]: net.idleVals[m].add(vals[q])
            for k in countdown(saved.len - 1, 0):
                state.assignValueLean(saved[k][0], saved[k][1])
        # Blame lists: which nodes' edges / cells each constraint reads
        net.blameEdges = newSeq[seq[int]](state.constraints.len)
        net.blameNodes = newSeq[seq[int]](state.constraints.len)
        var nodeOfPos: Table[int, int]
        for i in 0 ..< n:
            nodeOfPos[net.pos[i]] = i
            for s in net.sides[i]: nodeOfPos[s] = i
        for ci, cc in state.constraints:
            if cc == c or cc == state.boundConstraint: continue
            var srcs: PackedSet[int]
            state.rrSources(cc, srcs)
            var edges, nodes: seq[int]
            for s in srcs:
                if s in circuitPos: edges.add(nodeOfPos[s])
            if edges.len > 2: continue          # global over the circuit (alldifferent)
            if srcs.len - edges.len <= RerouteMaxSideSources:
                for s in srcs:
                    if s notin circuitPos:
                        nodeOfPos.withValue(s, k):
                            if k[] notin nodes: nodes.add(k[])
            net.blameEdges[ci] = edges
            net.blameNodes[ci] = nodes
        # Constraints over the whole successor array (the subcircuit and its
        # alldifferent): a shared cell blows them up, so the move scores
        # shared cells itself instead
        for cc in state.constraints:
            if cc.stateType in {SubcircuitType, AllDifferentType} and
                    cc.positions.len == n and cc.positions == circuitPos:
                net.circuitCons.add(cc)
        # Element constraints indexed by a successor: values carried along
        for ci, cc in state.constraints:
            if cc.stateType != ElementType: continue
            let es = cc.elementState
            var nd = -1
            if es.evalMethod == PositionBased:
                nd = nodeOfPos.getOrDefault(es.indexPosition, -1)
                if es.indexPosition notin circuitPos: nd = -1
            else:
                for q in es.indexExprPositions.keys:
                    if q in circuitPos: nd = nodeOfPos.getOrDefault(q, -1)
            if nd >= 0:
                net.carried.add(ci)
                net.carriedNode.add(nd)
        net.nodeHist = newSeq[float](n)
        net.edgeHist = newSeq[Table[int, float]](n)
        net.tgt = newSeqWith(net.sources.len, -1)
        net.route = newSeq[seq[int]](net.sources.len)
        net.rtype = newSeq[seq[int]](net.sources.len)
        for p in net.pos: net.touchPos.add(p)
        for i in 0 ..< n:
            for s in net.sides[i]: net.touchPos.add(s)
        state.rerouteNets.add(net)
        if state.verbose:
            var sideCount, typed = 0
            for i in 0 ..< n:
                sideCount += net.sides[i].len
                if net.typePos[i] >= 0: inc typed
            let buildSecs = epochTime() - tb
            echo &"[Init] Reroute net: {n} nodes, {net.sources.len} routes, {idle} optional, " &
                 &"{sideCount} side positions, {typed} typed, built in {buildSecs:.2f}s"

proc rrParse[T](state: TabuState[T], net: RerouteNet[T]): bool =
    ## Read the routes from the current assignment: every source must reach a
    ## distinct target through optional cells, without revisiting a cell.
    var isTarget = newSeq[bool](net.n)
    for t in net.targets: isTarget[t] = true
    var used = newSeq[bool](net.n)
    var routes = newSeq[seq[int]](net.sources.len)
    var tgts = newSeq[int](net.sources.len)
    for r, s in net.sources:
        var path = @[s]
        used[s] = true
        var cur = s
        var reached = false
        for _ in 0 ..< net.n:
            let nx = state.rrSucc(net, cur)
            if nx < 0 or nx >= net.n or nx == cur: break
            if isTarget[nx]:
                if used[nx] and nx != s: break
                path.add(nx)
                used[nx] = true
                reached = true
                break
            if used[nx] or not net.canIdle[nx]: break
            used[nx] = true
            path.add(nx)
            cur = nx
        if not reached: return false
        if net.paired and path[^1] != net.tgt[r]: return false
        routes[r] = path
        tgts[r] = path[^1]
    net.route = routes
    net.tgt = tgts
    for r in 0 ..< routes.len:
        net.rtype[r] = routes[r].mapIt(state.rrTypeIdx(net, it))
    true

proc rrSetSides[T](state: TabuState[T], net: RerouteNet[T], node: int, skipType: bool) =
    ## Move each side variable of `node` to its best value (lean): first
    ## the fewest violated links with the node's successor, then the lowest
    ## cost.
    for k, p in net.sides[node]:
        if skipType and p == net.typePos[node]: continue
        let links {.cursor.} = net.sideLinks[node][k]
        template linkViol(): int =
            var lv = 0
            for cc in links:
                if cc.penalty() > 0: inc lv
            lv
        let cur = state.assignment[p]
        # A value carried along the successor (an element constraint whose
        # result is this side): copy it from the successor's entry. Idle
        # nodes select themselves and carry nothing.
        if state.rrSucc(net, node) != node:
            var copied = false
            for cc in links:
                if cc.stateType != ElementType: continue
                let es = cc.elementState
                let target = es.getArrayValue(int(es.getIndexValue()))
                if target == cur and cc.penalty() == 0:
                    copied = true
                    break
                if state.domIdx(p, target) < 0: continue
                state.assignValueLean(p, target)
                if cc.penalty() == 0:
                    copied = true
                    break
                state.assignValueLean(p, cur)
            if copied: continue
        var bestV = cur
        var bestL = linkViol()
        var bestC = state.cost
        for v in state.sharedDomain[][p]:
            if v == cur: continue
            state.assignValueLean(p, v)
            let lv = linkViol()
            if lv < bestL or (lv == bestL and state.cost < bestC):
                bestL = lv
                bestC = state.cost
                bestV = v
            state.assignValueLean(p, cur)
        if bestV != cur: state.assignValueLean(p, bestV)

proc rrProject[T](state: TabuState[T], net: RerouteNet[T]) =
    ## Write the routes (successors and routed types) into the assignment;
    ## later routes win shared cells, uncovered optional cells idle. Then
    ## settle the remaining side variables of every cell whose successor or
    ## predecessor changed.
    var want = newSeqWith(net.n, -1)
    var wantType = newSeqWith(net.n, -1)
    for i in 0 ..< net.n:
        if net.canIdle[i]: want[i] = i
    for r, path in net.route:
        for k in 0 ..< path.len:
            if k < path.len - 1: want[path[k]] = path[k + 1]
            if k < net.rtype[r].len: wantType[path[k]] = net.rtype[r][k]
    var changed = newSeq[bool](net.n)
    for i in 0 ..< net.n:
        if want[i] < 0 or net.fixedSucc[i] >= 0: continue
        let v = T(want[i] + net.offset)
        if state.assignment[net.pos[i]] != v:
            state.assignValueLean(net.pos[i], v)
            changed[i] = true
    for i in 0 ..< net.n:
        let tp = net.typePos[i]
        if tp < 0 or wantType[i] < 0 or want[i] == i: continue
        let v = net.typeDom[i][wantType[i]]
        if state.assignment[tp] != v:
            state.assignValueLean(tp, v)
            changed[i] = true
    # Side settling along each changed route (values carried along a route,
    # e.g. its agent label, depend on the whole route), then idle cells,
    # then in reverse (values flow back from fixed targets).
    var order: seq[int]
    var inOrder = newSeq[bool](net.n)
    for r in net.route:
        var touched = false
        for i in r:
            if changed[i]: touched = true
        if not touched: continue
        for i in r:
            if inOrder[i]: continue
            order.add(i)
            inOrder[i] = true
    for i in 0 ..< net.n:
        if changed[i] and not inOrder[i]:
            order.add(i)
            inOrder[i] = true
    for i in order:
        if want[i] == i:
            # idle: its precomputed empty values
            for k, q in net.sides[i]:
                let v = net.idleVals[i][k]
                if state.assignment[q] != v: state.assignValueLean(q, v)
        else:
            state.rrSetSides(net, i, wantType[i] >= 0)
    for k in countdown(order.len - 1, 0):
        let i = order[k]
        if want[i] != i: state.rrSetSides(net, i, wantType[i] >= 0)

proc rrRoute[T](state: TabuState[T], net: RerouteNet[T], src: int, srcMask: uint32,
                dst: seq[int], dstMask: seq[uint32], blocked: seq[bool], occ: seq[int],
                pres: float): seq[(seq[int], seq[int])] =
    ## Dijkstra over (cell, type) states from src (types in srcMask) through
    ## optional cells; returns (cells, type indices) per entry of dst, empty
    ## when unreachable (arrival types in dstMask). Each step needs the
    ## current type to fit the edge and the next type to fit the current
    ## one. Cells held by other routes cost `pres` per route.
    let n = net.n
    var K = 1
    for d in net.typeDom: K = max(K, d.len)
    var dstIdx = newSeqWith(n, -1)
    for k, d in dst: dstIdx[d] = k
    let states = n * K
    var dist = newSeqWith(states, Inf)
    var prev = newSeqWith(states, -1)
    var bestD = newSeqWith(dst.len, Inf)
    var bestK = newSeqWith(dst.len, -1)
    var found = 0
    var heap = initHeapQueue[(float, int)]()
    for b in 0 ..< K:
        if (srcMask and (1'u32 shl b)) != 0 and (net.anyAllow[src] and (1'u32 shl b)) != 0:
            dist[src * K + b] = 0.0
            heap.push((0.0, src * K + b))
    while heap.len > 0:
        let (d, kk) = heap.pop()
        if d > dist[kk]: continue
        let i = kk div K
        let b = kk mod K
        if i != src and dstIdx[i] >= 0:
            let t = dstIdx[i]
            if d < bestD[t]:
                if bestK[t] < 0: inc found
                bestD[t] = d
                bestK[t] = kk
            if found == dst.len: break
            continue
        if i != src and not net.canIdle[i]: continue
        let eh {.cursor.} = net.edgeHist[i]
        for k, j in net.succ[i]:
            if blocked[j] or (net.allowMask[i][k] and (1'u32 shl b)) == 0: continue
            let isD = dstIdx[j] >= 0
            if not isD and not net.canIdle[j]: continue
            var mask = net.compat[i][k][b]
            if isD: mask = mask and dstMask[dstIdx[j]]
            else: mask = mask and net.anyAllow[j]
            if mask == 0: continue
            var c = 1.0 + net.nodeHist[j] + rand(RerouteNoise)
            if occ[j] > 0 and not isD:
                if pres < 0: continue
                c += pres * occ[j].float
            c += eh.getOrDefault(j, 0.0)
            var m = mask
            var cIdx = 0
            while m != 0:
                if (m and 1'u32) != 0:
                    var nd = d + c
                    for q in net.occReq[j][cIdx]:
                        if occ[q] == 0 and not blocked[q]: nd += RerouteClearCost
                    let nk = j * K + cIdx
                    if nd < dist[nk]:
                        dist[nk] = nd
                        prev[nk] = kk
                        heap.push((nd, nk))
                m = m shr 1
                inc cIdx
    result = newSeq[(seq[int], seq[int])](dst.len)
    for t in 0 ..< dst.len:
        if bestK[t] < 0: continue
        var path, types: seq[int]
        var seen: PackedSet[int]
        var kk = bestK[t]
        var ok = true
        while kk >= 0:
            let i = kk div K
            if seen.containsOrIncl(i):
                ok = false
                break
            path.add(i)
            types.add(if net.typePos[i] >= 0: kk mod K else: -1)
            if i == src and dist[kk] == 0.0: break
            kk = prev[kk]
        if not ok or path[^1] != src: continue
        path.reverse()
        types.reverse()
        result[t] = (path, types)

proc rrInMask[T](state: TabuState[T], net: RerouteNet[T], q, i: int): uint32 =
    ## Types node i may take after predecessor q (q keeps its current type).
    if q < 0: return net.rrAllTypes(i)
    let k = net.succIdx[q].getOrDefault(i, -1)
    let b = state.rrTypeIdx(net, q)
    if k < 0 or b < 0: return net.rrAllTypes(i)
    net.compat[q][k][b]

proc rrOutMask[T](state: TabuState[T], net: RerouteNet[T], i, o: int): uint32 =
    ## Types node i may take when it keeps successor o (o keeps its type).
    if o < 0: return net.rrAllTypes(i)
    let k = net.succIdx[i].getOrDefault(o, -1)
    if k < 0: return 0
    let c = state.rrTypeIdx(net, o)
    result = 0
    for b in 0 ..< max(1, net.typeDom[i].len):
        if (net.allowMask[i][k] and (1'u32 shl b)) != 0 and
                (c < 0 or (net.compat[i][k][b] and (1'u32 shl c)) != 0):
            result = result or (1'u32 shl b)

proc rrOccupancy[T](net: RerouteNet[T], skip: int): seq[int] =
    result = newSeq[int](net.n)
    for r, path in net.route:
        if r == skip: continue
        for i in path: inc result[i]

proc rrScore[T](state: TabuState[T], net: RerouteNet[T]): int =
    ## The move's own cost: one unit per extra route on a shared cell in
    ## place of the circuit constraints (which a shared cell turns into a
    ## penalty for every cell feeding into it).
    result = state.cost
    for cc in net.circuitCons: result -= cc.penalty()
    let occ = rrOccupancy(net, -1)
    for o in occ:
        if o > 1: result += o - 1

proc rrBlame[T](state: TabuState[T], net: RerouteNet[T]) =
    ## Negotiated congestion: violated constraints make the cells and edges
    ## they read more expensive for the router.
    template blameEdge(i: int) =
        let j = state.rrSucc(net, i)
        if j != i and j >= 0 and j < net.n:
            net.edgeHist[i].mgetOrPut(j, 0.0) += RerouteHistStep * RerouteBlameEvery.float
    for ci, cc in state.constraints:
        if cc.penalty() == 0: continue
        for i in net.blameEdges[ci]: blameEdge(i)
        for i in net.blameNodes[ci]:
            if state.rrSucc(net, i) == i: continue   # idle: occupying it may be the fix
            net.nodeHist[i] += RerouteHistStep * RerouteBlameEvery.float
            # A cell's type follows from its outgoing edge (a tunnel entry
            # over an empty cell): blame that edge too
            blameEdge(i)
    let occ = rrOccupancy(net, -1)
    for i in 0 ..< net.n:
        if occ[i] > 1: net.nodeHist[i] += RerouteHistStep * RerouteBlameEvery.float

proc rrSnapshot[T](state: TabuState[T], net: RerouteNet[T]): seq[T] =
    result = newSeq[T](net.touchPos.len)
    for k, p in net.touchPos: result[k] = state.assignment[p]

template rrRestore[T](state: TabuState[T], net: RerouteNet[T], snap: seq[T]) =
    for k, p in net.touchPos:
        if state.assignment[p] != snap[k]: state.assignValueLean(p, snap[k])

proc rrRouteWhole[T](state: TabuState[T], net: RerouteNet[T], r: int, cands: seq[int],
                     blocked: seq[bool], occ: seq[int], pres: float): seq[(seq[int], seq[int])] =
    let src = net.sources[r]
    let inM = state.rrInMask(net, net.fixedPred[src], src)
    let outM = cands.mapIt(state.rrOutMask(net, it, net.fixedSucc[it]))
    state.rrRoute(net, src, inM, cands, outM, blocked, occ, pres)

proc rrPair[T](state: TabuState[T], net: RerouteNet[T]) =
    ## Decide which target each source routes to. Values carried along the
    ## successors (element constraints indexed by a successor: an agent
    ## label) make a wrong pairing infeasible, so route each source alone to
    ## each target and pick the assignment that breaks the fewest of those
    ## constraints on the route (total cost breaks ties).
    let m = net.sources.len
    for r in 0 ..< m:
        net.route[r] = @[]
        net.rtype[r] = @[]
    state.rrProject(net)
    let empty = state.rrSnapshot(net)
    let big = high(int) div (4 * m + 4)
    var carriedCost = newSeqWith(m, newSeqWith(m, big))
    var totalCost = newSeqWith(m, newSeqWith(m, big))
    let zero = newSeq[int](net.n)
    let blocked = newSeq[bool](net.n)
    for r in 0 ..< m:
        let paths = state.rrRouteWhole(net, r, net.targets, blocked, zero, 1.0)
        for k, (path, types) in paths:
            if path.len == 0: continue
            net.route[r] = path
            net.rtype[r] = types
            state.rrProject(net)
            var onRoute = newSeq[bool](net.n)
            for i in path: onRoute[i] = true
            # the fixed cells before the source carry its value in
            var q = net.fixedPred[path[0]]
            while q >= 0 and not onRoute[q]:
                onRoute[q] = true
                q = net.fixedPred[q]
            var cv = 0
            for x, ci in net.carried:
                let nd = net.carriedNode[x]
                if nd >= 0 and onRoute[nd] and state.constraints[ci].penalty() > 0: inc cv
            carriedCost[r][k] = cv
            totalCost[r][k] = state.cost
            net.route[r] = @[]
            net.rtype[r] = @[]
            state.rrRestore(net, empty)
    # Exhaustive over assignments for small m, greedy otherwise
    var perm = toSeq(0 ..< m)
    var bestPerm = perm
    var bestKey = (high(int), high(int))
    proc keyOf(pm: seq[int]): (int, int) =
        var a, b = 0
        for r in 0 ..< m:
            a += carriedCost[r][pm[r]]
            b += totalCost[r][pm[r]]
        (a, b)
    if m <= 8:
        while true:
            let key = keyOf(perm)
            if key < bestKey:
                bestKey = key
                bestPerm = perm
            if not perm.nextPermutation(): break
    else:
        var taken = newSeq[bool](m)
        for r in 0 ..< m:
            var bk = -1
            for k in 0 ..< m:
                if taken[k]: continue
                if bk < 0 or (carriedCost[r][k], totalCost[r][k]) < (carriedCost[r][bk], totalCost[r][bk]):
                    bk = k
            taken[bk] = true
            bestPerm[r] = bk
    for r in 0 ..< m: net.tgt[r] = net.targets[bestPerm[r]]
    net.paired = true
    if state.verbose:
        echo &"[Tabu S{state.id}] Reroute pairing: carried violations={keyOf(bestPerm)[0]} targets={net.tgt}"

proc rrConstruct[T](state: TabuState[T], net: RerouteNet[T], pres: float) =
    ## Route every source to its target from scratch, in random order.
    if not net.paired: state.rrPair(net)
    var order = toSeq(0 ..< net.sources.len)
    shuffle(order)
    for r in 0 ..< net.route.len:
        net.route[r] = @[]
        net.rtype[r] = @[]
    state.rrProject(net)
    let blocked = newSeq[bool](net.n)
    for r in order:
        let occ = rrOccupancy(net, r)
        let (path, types) = state.rrRouteWhole(net, r, @[net.tgt[r]], blocked, occ, pres)[0]
        net.route[r] = path
        net.rtype[r] = types
        state.rrProject(net)
template rrAccept(c, cur: int): bool =
    c <= cur or rand(1.0) < RerouteAcceptWorse

proc rrRerouteOne[T](state: TabuState[T], net: RerouteNet[T], cur: var int, pres: float) =
    ## Rip up one route, or a stretch of it between two of its cells, and
    ## route it again.
    let r = rand(net.route.len - 1)
    let old = net.route[r]
    let oldT = net.rtype[r]
    if old.len < 2:
        # Unrouted (no path at construction): try the whole route again
        let occ = rrOccupancy(net, r)
        let (path, types) = state.rrRouteWhole(net, r, @[net.tgt[r]], newSeq[bool](net.n), occ, pres)[0]
        if path.len == 0: return
        let snap = state.rrSnapshot(net)
        net.route[r] = path
        net.rtype[r] = types
        state.rrProject(net)
        let c = state.rrScore(net)
        if rrAccept(c, cur): cur = c
        else:
            net.route[r] = old
            net.rtype[r] = oldT
            state.rrRestore(net, snap)
        return
    var a = 0
    var b = old.len - 1
    if old.len > 3 and rand(1.0) < 0.5:
        a = rand(old.len - 3)
        b = a + 2 + rand(old.len - 1 - (a + 2))
    var blocked = newSeq[bool](net.n)
    for k in 0 ..< old.len:
        if k < a or k > b: blocked[old[k]] = true
    let occ = rrOccupancy(net, r)
    let before = if a > 0: old[a - 1] else: net.fixedPred[old[0]]
    let after = if b + 1 < old.len: old[b + 1] else: net.fixedSucc[old[b]]
    let (path, types) = state.rrRoute(net, old[a], state.rrInMask(net, before, old[a]),
                                      @[old[b]], @[state.rrOutMask(net, old[b], after)],
                                      blocked, occ, pres)[0]
    if path.len == 0: return
    var nr = old[0 ..< a] & path
    var nt = oldT[0 ..< a] & types
    if b + 1 < old.len:
        nr.add(old[b + 1 .. ^1])
        nt.add(oldT[b + 1 .. ^1])
    if nr == old and nt == oldT: return
    let snap = state.rrSnapshot(net)
    net.route[r] = nr
    net.rtype[r] = nt
    state.rrProject(net)
    let c = state.rrScore(net)
    if rrAccept(c, cur):
        cur = c
    else:
        net.route[r] = old
        net.rtype[r] = oldT
        state.rrRestore(net, snap)

proc tryRerouteMoves[T](state: TabuState[T], budget: float): bool =
    ## Negotiated-congestion rerouting for `budget` seconds; commits the best
    ## state found when it is cheaper than the current one.
    if not state.rerouteBuilt: state.rrBuild()
    if state.rerouteNets.len == 0: return false
    let t0 = epochTime()
    var deadline = t0 + budget
    if state.searchDeadline > 0: deadline = min(deadline, state.searchDeadline)
    template stopNow(): bool =
        epochTime() > deadline or (state.stopSignal != nil and state.stopSignal[].load())
    inc state.rerouteCalls
    var improved = false
    for net in state.rerouteNets:
        let entryCost = state.cost
        let entry = state.rrSnapshot(net)
        var pres = 1.0
        if not net.paired: state.rrPair(net)
        if not state.rrParse(net):
            # Keep the routes of an earlier call when tabu has broken them;
            # build fresh ones otherwise
            var haveRoutes = true
            for r in net.route:
                if r.len == 0: haveRoutes = false
            if haveRoutes: state.rrProject(net)
            else: state.rrConstruct(net, pres)
        var cur = state.rrScore(net)
        var bestScore = cur
        var best = state.cost
        var bestSnap = state.rrSnapshot(net)
        var bestRoutes = net.route
        var bestTypes = net.rtype
        var it = 0
        var lastImp = 0
        while not stopNow():
            inc it
            inc state.rerouteTries
            if it - lastImp > RerouteRestartAfter:
                for h in net.nodeHist.mitems: h = 0.0
                for e in net.edgeHist.mitems: e.clear()
                pres = 1.0
                state.rrConstruct(net, pres)
                cur = state.rrScore(net)
                lastImp = it
            state.rrRerouteOne(net, cur, pres)
            # Scanning every constraint costs as much as the reroute itself:
            # blame every few reroutes with a proportionally larger step
            if it mod RerouteBlameEvery == 0: state.rrBlame(net)
            pres = min(pres * ReroutePresGrowth, ReroutePresMax)
            if cur < bestScore:
                bestScore = cur
                lastImp = it
            if state.cost < best:
                best = state.cost
                bestSnap = state.rrSnapshot(net)
                bestRoutes = net.route
                bestTypes = net.rtype
                lastImp = it
                if best == 0: break
        # Back to the entry state (exact, so the penalty maps stay valid),
        # then commit the best state found if it beats the entry
        state.rrRestore(net, entry)
        if best < entryCost:
            for k, p in net.touchPos:
                if state.assignment[p] != bestSnap[k]:
                    let oldIdx = state.domIdx(p, state.assignment[p])
                    if oldIdx >= 0 and not state.isLazy[p]:
                        state.tabu[p][oldIdx] = state.iteration + 1 + state.iteration mod 10
                    state.commitValue(p, bestSnap[k])
            net.route = bestRoutes
            net.rtype = bestTypes
            inc state.rerouteApplied
            improved = true
    state.rerouteTime += epochTime() - t0
    improved
