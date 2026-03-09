## Flow structure initialization and negative-cost cycle detection (Bellman-Ford).
## Included from tabu.nim — not a standalone module.

proc initFlowStructure[T](state: TabuState[T]) =
    ## Detect flow network structure for ejection chain moves.
    ## A "flow node" is an EqualTo RelationalConstraint with PositionBased SumExpr
    ## where all coefficients are ±1 and all positions are binary.
    state.flowEnabled = false
    state.flowNodePositions = @[]
    state.posFlowNodes = newSeq[seq[(int, int)]](state.carray.len)

    if not state.swapEnabled:
        return

    let binaryPosSet = block:
        var s = initPackedSet[int]()
        for p in state.binaryPositions: s.incl(p)
        s

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo:
            continue
        if rc.leftExpr.kind != SumExpr:
            continue
        let sumExpr = rc.leftExpr.sumExpr
        if sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue

        # Check all coefficients are ±1 and all positions are binary
        var allValid = true
        var posCoeffs: seq[(int, int)] = @[]
        for pos, coeff in sumExpr.coefficient.pairs:
            if (coeff != 1 and coeff != -1) or pos notin binaryPosSet:
                allValid = false
                break
            posCoeffs.add((pos, coeff))

        if not allValid or posCoeffs.len < 2:
            continue

        # This is a flow node
        let fnIdx = state.flowNodePositions.len
        state.flowNodePositions.add(posCoeffs)
        for (pos, coeff) in posCoeffs:
            state.posFlowNodes[pos].add((fnIdx, coeff))

    if state.flowNodePositions.len > 0:
        var flowEdgeCount = 0
        for pos in state.binaryPositions:
            if state.posFlowNodes[pos].len >= 2:
                flowEdgeCount += 1
        if flowEdgeCount > 0:
            state.flowEnabled = true
            if state.verbose and state.id == 0:
                echo "[Init] Flow structure: " & $state.flowNodePositions.len &
                     " flow nodes, " & $flowEdgeCount & " flow edges"

    # Extract objective coefficients for guided chain construction.
    # Look for LessThanEq/GreaterThanEq RelationalConstraint with PositionBased SumExpr
    # covering many binary positions — this is the objective bound constraint.
    state.edgeObjectiveWeight = initTable[int, int]()
    if state.flowEnabled:
        var bestObjConstraint: RelationalConstraint[T] = nil
        var bestObjCoverage = 0
        for constraint in state.constraints:
            if constraint.stateType != RelationalType:
                continue
            let rc = constraint.relationalState
            if rc.relation notin {LessThanEq, GreaterThanEq}:
                continue
            if rc.leftExpr.kind != SumExpr:
                continue
            let sumExpr = rc.leftExpr.sumExpr
            if sumExpr.evalMethod != PositionBased:
                continue
            # Count how many binary positions this constraint covers
            var coverage = 0
            for pos in sumExpr.coefficient.keys:
                if pos in binaryPosSet:
                    coverage += 1
            if coverage > bestObjCoverage:
                bestObjCoverage = coverage
                bestObjConstraint = rc
        if bestObjConstraint != nil and bestObjCoverage >= 4:
            let sumExpr = bestObjConstraint.leftExpr.sumExpr
            for pos, coeff in sumExpr.coefficient.pairs:
                if pos in binaryPosSet:
                    state.edgeObjectiveWeight[pos] = coeff
            if state.verbose and state.id == 0:
                echo "[Init] Objective weights: " & $state.edgeObjectiveWeight.len &
                     " binary edges with objective coefficients"


type
    ResidualEdge = object
        src, dst: int       # flow node indices
        cost: int           # residual cost (negative = improving)
        pos: int            # original position (edge variable)
        newVal: int         # value to assign (0 or 1) when using this edge

proc findNegativeCycle[T](state: TabuState[T]): (seq[(int, T)], int) =
    ## Find a negative-cost cycle in the residual flow graph using Bellman-Ford.
    ## Returns (chain, cycleCost) where chain is a list of (position, newValue)
    ## flips and cycleCost is the sum of residual edge costs in the cycle.
    ## Each binary edge variable maps to a residual edge:
    ##   - Currently ON (1): reverse edge with cost = -weight (removing saves weight)
    ##   - Currently OFF (0): forward edge with cost = +weight (adding costs weight)
    ## A negative cycle corresponds to a set of edge flips that improve the objective
    ## while maintaining flow conservation.
    if state.edgeObjectiveWeight.len == 0:
        return (@[], 0)

    let n = state.flowNodePositions.len  # number of flow nodes
    if n == 0:
        return (@[], 0)

    # Build residual edges
    var edges: seq[ResidualEdge] = @[]
    for pos in state.binaryPositions:
        let flowNodes = state.posFlowNodes[pos]
        if flowNodes.len != 2:
            continue
        let w = state.edgeObjectiveWeight.getOrDefault(pos, 0)
        let val = int(state.assignment[pos])

        # Determine direction: +1 coeff = outgoing from that node, -1 = incoming
        var srcNode, dstNode: int
        if flowNodes[0][1] > 0:
            srcNode = flowNodes[0][0]
            dstNode = flowNodes[1][0]
        else:
            srcNode = flowNodes[1][0]
            dstNode = flowNodes[0][0]

        if val == 1:
            # ON edge: residual goes backward (dst→src) with negative cost
            edges.add(ResidualEdge(src: dstNode, dst: srcNode, cost: -w, pos: pos, newVal: 0))
        else:
            # OFF edge: residual goes forward (src→dst) with positive cost
            edges.add(ResidualEdge(src: srcNode, dst: dstNode, cost: w, pos: pos, newVal: 1))

    if edges.len == 0:
        return (@[], 0)

    # Bellman-Ford: detect negative-cost cycle
    var dist = newSeq[int](n)
    var pred = newSeq[int](n)    # predecessor edge index
    for i in 0..<n:
        dist[i] = 0
        pred[i] = -1

    # Relax edges n times; on the n-th pass, any relaxation indicates a negative cycle
    var lastRelaxed = -1
    for iter in 0..<n:
        lastRelaxed = -1
        for ei in 0..<edges.len:
            let e = edges[ei]
            if dist[e.src] + e.cost < dist[e.dst]:
                dist[e.dst] = dist[e.src] + e.cost
                pred[e.dst] = ei
                lastRelaxed = e.dst

    if lastRelaxed < 0:
        return (@[], 0)  # No negative cycle

    # Trace back to find the cycle
    var node = lastRelaxed
    # Walk back n steps to ensure we're in the cycle
    for i in 0..<n:
        node = edges[pred[node]].src

    # Now trace the cycle from this node
    let cycleStart = node
    var cycle: seq[ResidualEdge] = @[]
    var current = cycleStart
    var visited = initPackedSet[int]()
    while true:
        let ei = pred[current]
        if ei < 0:
            return (@[], 0)  # broken chain
        cycle.add(edges[ei])
        visited.incl(current)
        current = edges[ei].src
        if current == cycleStart:
            break
        if current in visited:
            return (@[], 0)  # unexpected loop structure

    if cycle.len < 2:
        return (@[], 0)

    # Compute cycle cost and convert to position flips
    var cycleCost = 0
    var chain: seq[(int, T)] = @[]
    for e in cycle:
        cycleCost += e.cost
        chain.add((e.pos, T(e.newVal)))
    return (chain, cycleCost)


proc tryChainMoves*[T](state: TabuState[T]): bool =
    ## Find and apply negative-cost cycles in the flow residual graph.
    ## Returns true if an improving cycle was applied.
    if not state.flowEnabled:
        return false

    let (chain, cycleCost) = state.findNegativeCycle()
    if chain.len < 2:
        return false

    # Skip cycles that aren't negative in the flow subproblem — these can't
    # improve the full cost and applying+restoring them wastes penalty rebuilds.
    if cycleCost >= 0:
        return false

    # Apply chain and measure actual delta (may differ from cycleCost due to
    # non-flow constraints like cardinality bounds or side constraints).
    let costBefore = state.cost
    var oldValues: seq[T] = @[]
    for (pos, newVal) in chain:
        oldValues.add(state.assignment[pos])
        state.assignValue(pos, newVal)
    let delta = state.cost - costBefore

    if delta < 0:
        if state.verbose:
            echo &"[Chain S{state.id}] Applying negative cycle: len={chain.len} delta={delta} cycleCost={cycleCost} (cost {costBefore} -> {costBefore + delta})"
        # Set tabu for all flipped positions
        for i in 0..<chain.len:
            let (pos, _) = chain[i]
            let oldVal = oldValues[i]
            let oldIdx = state.domainIndex[pos].getOrDefault(oldVal, -1)
            if oldIdx >= 0 and not state.isLazy[pos]:
                state.tabu[pos][oldIdx] = state.iteration + 1 + state.iteration mod 10
        return true
    else:
        # Restore — cycle wasn't actually improving (due to non-flow constraints)
        if state.verbose:
            echo &"[Chain S{state.id}] Negative cycle not improving: len={chain.len} delta={delta} cycleCost={cycleCost}"
        for i in countdown(chain.len - 1, 0):
            state.assignValue(chain[i][0], oldValues[i])
        return false
