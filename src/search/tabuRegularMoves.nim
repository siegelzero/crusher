## Regular-constraint line repair moves.
## Included from tabu.nim — not a standalone module.
##
## For a regular constraint over positions x_0..x_{n-1}, the best rewrite of the
## whole sequence (other variables fixed) is a shortest path through the DFA's
## layered graph where taking input v at layer i costs w[i][v] = the change in
## every OTHER constraint's penalty from setting x_i = v alone. After the
## rewrite the regular constraint itself is satisfied, so
##
##     predicted delta = sum_i w[i][v_i] - cost(regular).
##
## The prediction is exact when no other constraint touches two positions of
## the line (e.g. nonogram: every column crosses a row in exactly one cell);
## otherwise it is a sum-of-singles approximation. Either way the move is
## simulated and only applied if the true delta improves (or, for sideways
## moves under deep stagnation, does not worsen). This is an exponentially
## large neighborhood explored in O(n * states * inputs) — single-cell flips
## cannot shift a nonogram block, a line rewrite can.

proc tryRegularLineMoves[T](state: TabuState[T], allowSideways: bool): bool =
    if state.regularConstraintIndices.len == 0: return false
    inc state.regLineCalls

    const MAX_LINES = 4
    const INF = high(int) div 4

    var candidates = state.regularConstraintIndices
    shuffle(candidates)
    # Violated lines first: they are where the gain is
    var ordered: seq[int]
    for ci in candidates:
        if state.constraints[ci].regularState.cost > 0: ordered.add(ci)
    for ci in candidates:
        if state.constraints[ci].regularState.cost == 0: ordered.add(ci)

    var tried = 0
    for ci in ordered:
        if tried >= MAX_LINES: break
        inc tried
        let constraint = state.constraints[ci]
        let reg = constraint.regularState
        let n = reg.n
        let S = reg.nStates
        let V = int(reg.inputMax) - int(reg.inputMin) + 1
        if n == 0 or V <= 0: continue

        # Weights: other-constraint delta of each (layer, input). INF when the
        # value is outside the variable's current domain.
        var w = newSeq[int](n * V)
        for i in 0..<n:
            let pos = reg.sortedPositions[i]
            let cur = state.assignment[pos]
            for k in 0..<V:
                let v = T(int(reg.inputMin) + k)
                if v == cur:
                    w[i * V + k] = 0
                elif state.domIdx(pos, v) < 0:
                    w[i * V + k] = INF
                else:
                    w[i * V + k] = state.costDelta(pos, v) -
                                   state.movePenalty(constraint, pos, v)

        # Layered shortest path with random tie-breaking (reservoir sampling
        # over equal-cost parents) so repeated calls explore different optima.
        let stride = S + 1
        var dist = newSeq[int]((n + 1) * stride)
        var parent = newSeq[int32]((n + 1) * stride)   # prevState * V + k
        var ties = newSeq[int32]((n + 1) * stride)
        for x in 0..<dist.len: dist[x] = INF
        dist[reg.initialState] = 0
        for i in 0..<n:
            let base = i * stride
            let nb = base + stride
            for s in 1..S:
                let d = dist[base + s]
                if d >= INF: continue
                let row {.cursor.} = reg.transition[s - 1]
                for k in 0..<min(V, row.len):
                    let ns = row[k]
                    if ns <= 0: continue
                    let wk = w[i * V + k]
                    if wk >= INF: continue
                    let c = d + wk
                    let cell = nb + ns
                    if c < dist[cell]:
                        dist[cell] = c
                        parent[cell] = int32(s * V + k)
                        ties[cell] = 1
                    elif c == dist[cell]:
                        inc ties[cell]
                        if rand(int(ties[cell]) - 1) == 0:
                            parent[cell] = int32(s * V + k)

        var bestF = -1
        var bestD = INF
        var fTies = 0
        let last = n * stride
        for f in reg.finalStates.items:
            if f < 1 or f > S: continue
            let d = dist[last + f]
            if d < bestD:
                bestD = d; bestF = f; fTies = 1
            elif d == bestD and d < INF:
                inc fTies
                if rand(fTies - 1) == 0: bestF = f
        if bestF < 0 or bestD >= INF: continue

        let predicted = bestD - reg.cost
        if predicted > 0 or (predicted == 0 and not allowSideways): continue

        # Trace back the chosen string
        var newVals = newSeq[T](n)
        var s = bestF
        for i in countdown(n - 1, 0):
            let p = int(parent[(i + 1) * stride + s])
            newVals[i] = T(int(reg.inputMin) + p mod V)
            s = p div V

        # Simulate (lean), measure the true delta, restore. Budget: the caller
        # checks between calls; one call is at most MAX_LINES simulations.
        let origCost = state.cost
        var changes: seq[(int, T)]
        for i in 0..<n:
            let pos = reg.sortedPositions[i]
            if state.assignment[pos] != newVals[i]:
                changes.add((pos, state.assignment[pos]))
                state.assignValueLean(pos, newVals[i])
        if changes.len == 0: continue
        let delta = state.cost - origCost
        for j in countdown(changes.len - 1, 0):
            state.assignValueLean(changes[j][0], changes[j][1])

        if delta < 0 or (delta == 0 and allowSideways):
            let tabuTenure = state.iteration + 1 + state.iteration mod 10
            for (pos, oldVal) in changes:
                let oldIdx = state.domIdx(pos, oldVal)
                if oldIdx >= 0 and not state.isLazy[pos]:
                    state.tabu[pos][oldIdx] = tabuTenure
                # commitValue: under lean search the penalty map is never read,
                # and a full assignValue per line cell (n * neighbor-penalty
                # cascades, each through the channel fixpoint) ran for seconds
                # past the deadline on channel-heavy models (work-task-variation).
                state.commitValue(pos, newVals[reg.positionToIndex[pos]])
            return true
    return false
