# Included by cpEngine.nim: orientation search over the difference-logic
# propagator (DiffLogicProp) with an LP bound.
#
# With the disjunctions of a difference-logic model fixed to one alternative
# each (an "orientation"), what is left is a difference system, and the best
# placement for an objective over it is an LP. rect-euler EU: the engine's LNS
# over values (a share of the variables kept at the incumbent's values) stalls
# at 11421, while the LP for that solution's own orientation gives 10759, and
# re-deciding the disjunctions around a few rectangles with every coordinate
# free reaches 8558 in 120 s (Python prototype; best known 7780). Fixing
# values boxes the freed rectangles in; fixing orientations lets the whole
# layout shift.
#
# dlImprove keeps the incumbent's orientation outside a set of free
# disjunctions and runs a depth-first branch and bound over the free ones:
# the bound at a node is the LP over the current closure (a relaxation: every
# row is implied by the propagators), the branching disjunction is the one
# the LP point violates most, its alternatives are tried by increasing
# violation, and a node whose LP point satisfies every disjunction is a leaf:
# its point is rounded onto the variables and the engine completes and checks
# it (so a solution never rests on the LP).

import std/math
import ../search/lpSimplex

const
    DlOrientMaxCone = 512      # objective variables outside the graph (LP columns)
    DlLpTol = 1e-6

type
    DlConeRow = object
        vars: seq[int]             # engine variables
        val: seq[float]
        lo, hi: float
    DlOrient* = ref object
        p: DiffLogicProp
        obj: int
        sense: float               # 1 minimize, -1 maximize
        coneVars: seq[int]         # objective variables outside the graph
        coneRows: seq[DlConeRow]
        disj*: seq[seq[DlEdge]]    # at least one alternative holds
        disjNodes*: seq[seq[int]]  # graph nodes of each disjunction
        nodeOfVar: seq[int]
        colOf: seq[int]            # engine variable -> LP column (-1: none)
        derived: seq[bool]         # per node: a max / abs result, left to the engine at a leaf
        lps*, bbNodes*, leaves*, leafFails*: int

proc dlOrientation*(s: CpSolver, obj: int, maximize: bool): DlOrient =
    ## The orientation search for objective variable obj over the model's
    ## difference-logic propagator (call after prepare), or nil: no such
    ## propagator, no disjunction, or an objective that reaches more than
    ## DlOrientMaxCone variables outside the graph. Disjunctions: diffn pairs
    ## and clauses whose literals all reify difference constraints.
    var p: DiffLogicProp = nil
    for q in s.props:
        if q of DiffLogicProp:
            p = DiffLogicProp(q)
            break
    if p == nil: return nil
    let o = DlOrient(p: p, obj: obj, sense: (if maximize: -1.0 else: 1.0))
    o.nodeOfVar = newSeq[int](s.vars.len)
    for v in 0 ..< s.vars.len: o.nodeOfVar[v] = -1
    for i in 1 ..< p.n: o.nodeOfVar[p.nodeVar[i]] = i
    for d in p.disj: o.disj.add d
    # The LP relaxes m = max(xs) to m >= xs (and |a| alike), so its value
    # for such a node can be loose (rect-euler: mx above every width where
    # |mx - my| makes raising it free): a leaf leaves these to propagation
    o.derived = newSeq[bool](p.n)
    for q in s.props:
        let r = (if q of MaxProp: q.vs[0] elif q of AbsProp: q.vs[1] else: -1)
        if r >= 0 and o.nodeOfVar[r] > 0: o.derived[o.nodeOfVar[r]] = true
    var litOf = newSeq[int](s.vars.len)
    for v in 0 ..< s.vars.len: litOf[v] = -1
    for k, l in p.lits:
        if litOf[l.r] < 0: litOf[l.r] = k
    for q in s.props:
        if not (q of OrProp): continue
        let c = OrProp(q)
        if c.r >= 0 and not (s.isFixed(c.r) and (s.value(c.r) == 1) == c.rp): continue
        var d: seq[DlEdge]
        var ok = true
        var sat = false
        for i, v in c.lv:
            if s.isFixed(v):
                if (s.value(v) == 1) == c.lp[i]:
                    sat = true
                    break
                continue
            let k = litOf[v]
            if k < 0:
                ok = false
                break
            let l = p.lits[k]
            if c.lp[i]: d.add l.e
            elif l.full: d.add DlEdge(a: l.e.b, b: l.e.a, k: 1 - l.e.k)
            else:
                ok = false
                break
        if ok and not sat and d.len > 0: o.disj.add d
    if o.disj.len == 0: return nil
    for d in o.disj:
        var ns: seq[int]
        for e in d:
            for i in [e.a, e.b]:
                if i > 0 and i notin ns: ns.add i
        o.disjNodes.add ns
    # Objective cone: the hard linear, max and abs constraints that define
    # the objective from the graph's variables (their LP relaxations)
    o.colOf = newSeq[int](s.vars.len)
    for v in 0 ..< s.vars.len: o.colOf[v] = -1
    for i in 1 ..< p.n: o.colOf[p.nodeVar[i]] = i - 1
    var used = newSeq[bool](s.props.len)
    var queue: seq[int]
    var queued = newSeq[bool](s.vars.len)
    proc reach(v: int): bool =
        ## v becomes an LP column (false: the cone is too large); a graph
        ## node is expanded only when a max / abs defines it (rect-euler mx)
        if s.isFixed(v): return true
        if o.colOf[v] >= 0:
            let i = o.nodeOfVar[v]
            if i > 0 and o.derived[i] and not queued[v]:
                queued[v] = true
                queue.add v
            return true
        if o.coneVars.len >= DlOrientMaxCone: return false
        o.colOf[v] = p.n - 1 + o.coneVars.len
        o.coneVars.add v
        queued[v] = true
        queue.add v
        true
    if not reach(obj): return nil
    if not queued[obj]:
        queued[obj] = true
        queue.add obj
    while queue.len > 0:
        let v = queue.pop()
        for pid in s.watch[v]:
            if used[pid]: continue
            let q = s.props[pid]
            if q of LinProp:
                let l = LinProp(q)
                if l.rel == lrNe or (l.r >= 0 and not (s.isFixed(l.r) and s.value(l.r) == 1)): continue
                used[pid] = true
                var row = DlConeRow(lo: (if l.rel == lrEq: float(l.c) else: -LpInf), hi: float(l.c))
                for k in 0 ..< l.x.len:
                    row.vars.add l.x[k]
                    row.val.add float(l.a[k])
                    if not reach(l.x[k]): return nil
                o.coneRows.add row
            elif q of MaxProp:
                if q.vs[0] != v: continue
                used[pid] = true
                let isMin = MaxProp(q).isMin
                for k in 1 ..< q.vs.len:
                    # m - x_k >= 0 (max) or <= 0 (min)
                    o.coneRows.add DlConeRow(vars: @[v, q.vs[k]], val: @[1.0, -1.0],
                                             lo: (if isMin: -LpInf else: 0.0), hi: (if isMin: 0.0 else: LpInf))
                    if not reach(q.vs[k]): return nil
            elif q of AbsProp:
                if q.vs[1] != v: continue
                used[pid] = true
                let a = q.vs[0]
                o.coneRows.add DlConeRow(vars: @[v, a], val: @[1.0, -1.0], lo: 0.0, hi: LpInf)
                o.coneRows.add DlConeRow(vars: @[v, a], val: @[1.0, 1.0], lo: 0.0, hi: LpInf)
                if not reach(a): return nil
    o

proc dlNodeLp(s: CpSolver, o: DlOrient, x: var seq[float], deadline: float): (LpStatus, float) =
    ## The LP at the current state: minimize (sense) the objective over the
    ## variables' bounds, the closure of the graph (without edges the bounds
    ## or other edges imply) and the objective cone. x: the graph nodes'
    ## values (x[i - 1] for node i). Returns the status and the objective.
    let p = o.p
    let n = p.n
    template D(i, j: int): int = s.cells[p.base + (i) * n + (j)]
    let nc = n - 1 + o.coneVars.len
    var m = LpModel(n: nc, lb: newSeq[float](nc), ub: newSeq[float](nc), cost: newSeq[float](nc))
    for i in 1 ..< n:
        m.lb[i - 1] = float(s.lo(p.nodeVar[i]))
        m.ub[i - 1] = float(s.hi(p.nodeVar[i]))
    for k, v in o.coneVars:
        m.lb[n - 1 + k] = float(s.lo(v))
        m.ub[n - 1 + k] = float(s.hi(v))
    m.cost[o.colOf[o.obj]] = o.sense
    # Ties go to the lowest coordinates (an LP optimum can shift a whole
    # layout; rect-euler's min(cx_min) = 0 is not in the LP), with a weight
    # whose total stays below 1/4 so it never changes the objective
    var span = 1.0
    for i in 1 ..< n: span += m.ub[i - 1] - m.lb[i - 1]
    let eps = 0.25 / span
    for i in 1 ..< n: m.cost[i - 1] += eps
    # Nodes at fixed offsets from one another (zero cycles) are tied to the
    # first of their class; the rest of the closure is reduced to the edges
    # no path through a third class implies (no zero cycle remains, so the
    # reduced edges imply the closure)
    var rep = newSeq[int](n)
    var reps: seq[int]
    for i in 1 ..< n:
        rep[i] = i
        for j in reps:
            if D(i, j) > DlNeg and D(j, i) > DlNeg and D(i, j) + D(j, i) == 0:
                rep[i] = j
                break
        if rep[i] == i: reps.add i
        else: m.addRow(@[i - 1, rep[i] - 1], @[1.0, -1.0], float(D(rep[i], i)), float(D(rep[i], i)))
    for a in reps:
        let ha = s.hi(p.nodeVar[a])
        for b in reps:
            if a == b: continue
            let k = D(a, b)
            if k <= DlNeg or s.lo(p.nodeVar[b]) - ha >= k: continue
            var redundant = false
            for c in reps:
                if c == a or c == b: continue
                let dac = D(a, c)
                if dac <= DlNeg: continue
                let dcb = D(c, b)
                if dcb > DlNeg and dac + dcb >= k:
                    redundant = true
                    break
            if not redundant: m.addRow(@[b - 1, a - 1], @[1.0, -1.0], float(k), LpInf)
    for r in o.coneRows:
        var idx: seq[int]
        var val: seq[float]
        var c = 0.0
        for k, v in r.vars:
            if o.colOf[v] >= 0:
                idx.add o.colOf[v]
                val.add r.val[k]
            else: c += r.val[k] * float(s.lo(v))
        m.addRow(idx, val, (if r.lo <= -LpInf: -LpInf else: r.lo - c), (if r.hi >= LpInf: LpInf else: r.hi - c))
    var lp = initSolver(m)
    inc o.lps
    let st = lp.solve(maxIter = 50_000, deadline = deadline)
    x.setLen nc
    for j in 0 ..< nc: x[j] = lp.value(j)
    (st, lp.value(o.colOf[o.obj]))

proc nearestValue(s: CpSolver, v: int, f: float): int =
    ## The value of v's domain nearest to f.
    let x = s.vars[v]
    let t = clamp(int(round(f)), x.lo, x.hi)
    if x.w0 < 0 or s.hasBit(x, t): return t
    let up = s.nextSet(x, t)
    let down = s.prevSet(x, t)
    if up > x.hi: down
    elif down < x.lo: up
    elif float(up) - f < f - float(down): up
    else: down

proc dlForce(s: CpSolver, p: DiffLogicProp, e: DlEdge): bool =
    ## Adds edge e and propagates (bounds along every node's paths).
    if not s.dlAdd(p, e): return false
    for i in 1 ..< p.n: s.setCell(p.seen + 2 * i, DlNeg)
    s.enqueue(p.id)
    s.propagateAll()

proc dlImprove*(s: CpSolver, o: DlOrient, cur: seq[int], free: seq[bool],
                maxNodes: int, deadline: float, nodesUsed: var int): seq[int] =
    ## Branch and bound over the free disjunctions with the others kept at the
    ## alternative the incumbent cur (all variable values) satisfies with the
    ## largest slack: the values of the best solution found that beats cur's
    ## objective, or empty. Restores the current level. nodesUsed: the LP
    ## nodes searched (maxNodes when the limit cut the search short).
    let p = o.p
    let base = s.level
    nodesUsed = 0
    s.pushLevel()
    defer: s.popTo(base)
    var bound = cur[o.obj]            # a solution must beat this
    if not (if o.sense > 0: s.setMax(o.obj, bound - 1) else: s.setMin(o.obj, bound + 1)): return
    proc nv(i: int): int = (if i == 0: 0 else: cur[p.nodeVar[i]])
    for k, d in o.disj:
        if free[k]: continue
        var best = -1
        var bs = low(int)
        for t, e in d:
            let sl = nv(e.b) - nv(e.a) - e.k
            if sl >= 0 and sl > bs:
                bs = sl
                best = t
        if best >= 0 and not s.dlAdd(p, d[best]): return
    for i in 1 ..< p.n: s.setCell(p.seen + 2 * i, DlNeg)
    s.enqueue(p.id)
    if not s.propagateAll(): return
    var nodes = 0
    var found: seq[int]
    proc xv(x: seq[float], i: int): float = (if i == 0: 0.0 else: x[i - 1])
    proc complete(x: seq[float]) =
        ## Rounds the LP point onto the graph's variables; the engine
        ## completes the rest and checks every constraint.
        inc o.leaves
        let lvl = s.level
        s.pushLevel()
        var ok = true
        for i in 1 ..< p.n:
            let v = p.nodeVar[i]
            if o.derived[i]: continue
            if not s.assign(v, s.nearestValue(v, x[i - 1])):
                ok = false
                break
        ok = ok and s.propagateAll()
        if not ok:
            # one at a time, each value moved to what the earlier ones left
            s.popTo(lvl)
            s.pushLevel()
            ok = true
            for i in 1 ..< p.n:
                let v = p.nodeVar[i]
                if o.derived[i] or s.isFixed(v): continue
                if not (s.assign(v, s.nearestValue(v, x[i - 1])) and s.propagateAll()):
                    ok = false
                    break
        if ok and s.search(deadline = deadline, maxNodes = 1000) == cpSat:
            let val = s.value(o.obj)
            if (o.sense > 0 and val < bound) or (o.sense < 0 and val > bound):
                bound = val
                found.setLen s.vars.len
                for v in 0 ..< s.vars.len: found[v] = s.value(v)
        else: inc o.leafFails
        s.popTo(lvl)
    proc rec() =
        if nodes >= maxNodes or (deadline > 0 and epochTime() > deadline): return
        inc nodes
        inc o.bbNodes
        var x: seq[float]
        let (st, ov) = s.dlNodeLp(o, x, deadline)
        if st != lpOptimal: return
        if (o.sense > 0 and ov > float(bound - 1) + DlLpTol) or
           (o.sense < 0 and ov < float(bound + 1) - DlLpTol): return
        var worst = -1
        var worstV = DlLpTol
        for k, d in o.disj:
            var mv = Inf
            for e in d: mv = min(mv, max(0.0, float(e.k) - (xv(x, e.b) - xv(x, e.a))))
            if mv > worstV:
                worstV = mv
                worst = k
        if worst < 0:
            complete(x)
            return
        var alts = o.disj[worst]
        alts.sort(proc(e, f: DlEdge): int =
            cmp(float(e.k) - (xv(x, e.b) - xv(x, e.a)), float(f.k) - (xv(x, f.b) - xv(x, f.a))))
        for e in alts:
            let lvl = s.level
            s.pushLevel()
            if s.dlForce(p, e): rec()
            s.popTo(lvl)
            if nodes >= maxNodes: return
    rec()
    nodesUsed = nodes
    found
