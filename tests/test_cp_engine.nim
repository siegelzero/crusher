## Tests for the propagation + DFS engine (src/cp/cpEngine.nim): small
## models per propagator, and random small models checked against brute
## force (status and solution validity).

import unittest
import std/[random, sequtils, times]
import cp/cpEngine

proc queens(n: int): (CpStatus, seq[int]) =
    let s = newCpSolver()
    var q: seq[int]
    for i in 0 ..< n: q.add s.newVar(1, n)
    for i in 0 ..< n:
        for j in i + 1 ..< n:
            s.addLinear(@[1, -1], @[q[i], q[j]], 0, lrNe)
            s.addLinear(@[1, -1], @[q[i], q[j]], i - j, lrNe)
            s.addLinear(@[1, -1], @[q[i], q[j]], j - i, lrNe)
    s.addBranchGroup(q, vsFirstFail, valMin)
    let st = s.solve()
    (st, q.mapIt(s.value(it)))

suite "CP engine":

    test "8 queens":
        let (st, q) = queens(8)
        check st == cpSat
        for i in 0 ..< 8:
            for j in i + 1 ..< 8:
                check q[i] != q[j]
                check abs(q[i] - q[j]) != j - i

    test "3 queens is unsatisfiable":
        check queens(3)[0] == cpUnsat

    test "linear infeasibility":
        let s = newCpSolver()
        let x = s.newVar(2, 5)
        let y = s.newVar(2, 5)
        s.addLinear(@[1, 1], @[x, y], 3, lrLe)
        check s.solve() == cpUnsat

    test "reified bounds and clause":
        # b <-> x <= 3, c <-> x >= 7, b \/ c, x in 4..6: unsatisfiable
        let s = newCpSolver()
        let x = s.newVar(4, 6)
        let b = s.newVar(0, 1)
        let c = s.newVar(0, 1)
        s.addLinear(@[1], @[x], 3, lrLe, b)
        s.addLinear(@[-1], @[x], -7, lrLe, c)
        s.addOr(@[b, c], @[true, true])
        check s.solve() == cpUnsat
        let s2 = newCpSolver()
        let x2 = s2.newVar(1, 10)
        let b2 = s2.newVar(0, 1)
        let c2 = s2.newVar(0, 1)
        s2.addLinear(@[1], @[x2], 3, lrLe, b2)
        s2.addLinear(@[-1], @[x2], -7, lrLe, c2)
        s2.addOr(@[b2, c2], @[true, true])
        s2.addLinear(@[1], @[x2], 2, lrNe)
        s2.addLinear(@[1], @[x2], 1, lrNe)
        s2.addLinear(@[1], @[x2], 3, lrNe)
        check s2.solve() == cpSat
        check s2.value(x2) >= 7

    test "bitset domain with holes":
        let s = newCpSolver()
        let x = s.newVarValues(@[1, 5, 9, 5])
        s.addLinear(@[1], @[x], 5, lrNe)
        s.addLinear(@[-1], @[x], -2, lrLe)     # x >= 2
        check s.solve() == cpSat
        check s.value(x) == 9

    test "regular: one block of two filled cells":
        # values 1 = empty, 2 = filled; states: 1 start, 2 after one filled,
        # 3 after the block, accepting 3
        let d = @[1, 2,   # state 1: empty -> 1, filled -> 2
                  0, 3,   # state 2: empty -> dead, filled -> 3
                  3, 0]   # state 3: empty -> 3, filled -> dead
        let s = newCpSolver()
        var xs: seq[int]
        for i in 0 ..< 5: xs.add s.newVar(1, 2)
        s.addRegular(xs, 3, 2, d, 1, @[3])
        discard s.assign(xs[3], 2)
        check s.solve() == cpSat
        let v = xs.mapIt(s.value(it))
        check v.countIt(it == 2) == 2
        check v[3] == 2
        check (v[2] == 2 or v[4] == 2)

    test "element, times, max, abs":
        let s = newCpSolver()
        let i = s.newVar(1, 4)
        let r = s.newVar(0, 100)
        s.addElement(i, @[7, 3, 9, 3], r)
        let k = s.newVar(-3, 3)
        let p = s.newVar(-100, 100)
        s.addTimes(r, k, p)
        let a = s.newVar(-30, 30)
        s.addAbs(p, a)
        let m = s.newVar(0, 100)
        s.addMax(m, @[r, a])
        s.addLinear(@[1], @[m], 27, lrEq)
        s.addLinear(@[1], @[k], 0, lrLe)
        check s.solve() == cpSat
        check s.value(r) == [7, 3, 9, 3][s.value(i) - 1]
        check s.value(p) == s.value(r) * s.value(k)
        check s.value(a) == abs(s.value(p))
        check s.value(m) == max(s.value(r), s.value(a))
        check s.value(m) == 27

    test "depth stall cutoff":
        # 14 pigeons in 13 holes with pairwise disequalities: the search
        # reaches its full depth at once and then thrashes below it
        let s = newCpSolver()
        var p: seq[int]
        for i in 0 ..< 14: p.add s.newVar(1, 13)
        for i in 0 ..< 14:
            for j in i + 1 ..< 14:
                s.addLinear(@[1, -1], @[p[i], p[j]], 0, lrNe)
        s.addBranchGroup(p, vsInputOrder, valMin)
        let t0 = epochTime()
        check s.solve(deadline = t0 + 30.0, stallMin = 0.2) == cpLimit
        check s.stalled
        check epochTime() - t0 < 5.0

    test "root shaving: a bound only fixed values refute":
        # zephyrus' unicity shape: n = i -> bind <= i * m (i < 10), bind = 10 * m,
        # m >= 1; bounds propagation alone keeps n >= 0, shaving finds n >= 10
        let s = newCpSolver()
        let n = s.newVar(0, 20)
        let m = s.newVar(1, 5)
        let bnd = s.newVar(0, 100)
        s.addLinear(@[1, -10], @[bnd, m], 0, lrEq)
        for i in 0 ..< 10:
            let b = s.newVar(0, 1)
            s.addLinear(@[1], @[n], i, lrEq, b)
            s.addLinear(@[1, -i], @[bnd, m], 0, lrLe, b, imp = true)
        let removed = s.shaveBounds()
        check removed > 0
        check s.lo(n) == 10
        check s.hi(n) == 20
        check s.solve() == cpSat
        check s.value(n) >= 10

    test "search under assumptions, node limit, popTo":
        # x + y + z = 6 over 0..3: improving neighbourhoods as the CP LNS runs them
        let s = newCpSolver()
        let x = s.newVar(0, 3)
        let y = s.newVar(0, 3)
        let z = s.newVar(0, 3)
        s.addLinear(@[1, 1, 1], @[x, y, z], 6, lrEq)
        s.addBranchGroup(@[x, y, z], vsInputOrder, valMin)
        check s.prepare()
        check s.level == 0
        # x = 3 assumed: solution below the assumption level, discarded with popTo
        s.pushAssume()
        check s.assign(x, 3) and s.propagate()
        check s.search() == cpSat
        check s.value(x) == 3
        check s.value(y) + s.value(z) == 3
        s.popTo(0)
        check s.level == 0
        check s.lo(x) == 0 and s.hi(x) == 3
        # x = 0 and y = 0: z would be 6, unsatisfiable; state restored
        s.pushAssume()
        let ok = s.assign(x, 0) and s.assign(y, 0) and s.propagate()
        if ok: check s.search() == cpUnsat
        s.popTo(0)
        check s.lo(y) == 0 and s.hi(y) == 3
        # a node limit gives up (cpLimit) and restores the level it started from
        let q = newCpSolver()
        var p: seq[int]
        for i in 0 ..< 9: p.add q.newVar(1, 8)
        for i in 0 ..< 9:
            for j in i + 1 ..< 9:
                q.addLinear(@[1, -1], @[p[i], p[j]], 0, lrNe)
        q.addBranchGroup(p, vsInputOrder, valMin)
        check q.prepare()
        check q.search(maxNodes = 50) == cpLimit
        check q.level == 0
        for v in p: check q.lo(v) == 1 and q.hi(v) == 8

    test "table, div and gcc propagation":
        let s = newCpSolver()
        let x = s.newVar(0, 3)
        let y = s.newVar(0, 3)
        s.addTable(@[x, y], @[0, 1, 2, 3, 3, 3, 5, 1])
        let a = s.newVar(0, 100)
        let q = s.newVar(3, 3)
        s.addDiv(a, s.constVar(7), q)
        let n = s.newVar(-50, -1)
        let qn = s.newVar(-100, 100)
        s.addDiv(n, s.constVar(10), qn)
        var g: seq[int]
        for i in 0 ..< 3: g.add s.newVar(1, 3)
        s.addGcc(g, @[1, 2], @[2, 1], @[2, 1], closed = true)
        check s.prepare()
        check toSeq(s.values(x)) == @[0, 2, 3]
        check toSeq(s.values(y)) == @[1, 3]
        check s.lo(a) == 21 and s.hi(a) == 27
        check s.lo(qn) == -5 and s.hi(qn) == 0      # -50 div 10 .. -1 div 10, truncating
        for v in g: check s.hi(v) == 2              # closed: 3 is not a cover value
        s.pushAssume()
        check s.assign(g[0], 2) and s.propagate()
        check s.value(g[1]) == 1 and s.value(g[2]) == 1
        s.popTo(0)

    test "diffn propagation and packing":
        let s = newCpSolver()
        let two = s.constVar(2)
        let x1 = s.newVar(0, 5)
        s.addDiffn(@[s.constVar(0), x1], @[s.constVar(0), s.constVar(0)], @[two, two], @[two, two])
        check s.prepare()
        check s.lo(x1) == 2                     # same row: only "right of" is left
        # strict: a zero-size rectangle may not lie inside another
        let s2 = newCpSolver()
        s2.addDiffn(@[s2.constVar(0), s2.constVar(1)], @[s2.constVar(0), s2.constVar(1)],
                    @[s2.constVar(3), s2.constVar(0)], @[s2.constVar(3), s2.constVar(0)])
        check not s2.prepare()
        # four 2x2 squares fill a 4x4 square, five do not
        for k in [4, 5]:
            let p = newCpSolver()
            var xs, ys, ds: seq[int]
            for i in 0 ..< k:
                xs.add p.newVar(0, 2)
                ys.add p.newVar(0, 2)
                ds.add p.constVar(2)
            p.addDiffn(xs, ys, ds, ds)
            p.addBranchGroup(xs & ys, vsInputOrder, valMin)
            check p.solve() == (if k == 4: cpSat else: cpUnsat)

    test "diffn: random small instances agree with brute force":
        var rng = initRand(4242)
        for trial in 0 ..< 400:
            # 3 rectangles; coordinates in random sub-ranges of 0..2, sizes
            # constant 0..2 except rectangle 0, whose sizes range over -1..2
            var lo, hi: seq[int]           # per variable: x0..x2, y0..y2, dx0..dx2, dy0..dy2
            for k in 0 ..< 12:
                if k < 6:
                    let a = rng.rand(0 .. 2)
                    lo.add a
                    hi.add rng.rand(a .. 2)
                elif k == 6 or k == 9:
                    lo.add -1
                    hi.add 2
                else:
                    let c = rng.rand(0 .. 2)
                    lo.add c
                    hi.add c
            proc ok(v: seq[int]): bool =
                for i in 0 ..< 3:
                    for j in i + 1 ..< 3:
                        if not (v[i] + v[6 + i] <= v[j] or v[3 + i] + v[9 + i] <= v[3 + j] or
                                v[j] + v[6 + j] <= v[i] or v[3 + j] + v[9 + j] <= v[3 + i]):
                            return false
                true
            var v = newSeq[int](12)
            proc rec(k: int): bool =
                if k == 12: return ok(v)
                for val in lo[k] .. hi[k]:
                    v[k] = val
                    if rec(k + 1): return true
                false
            let expected = rec(0)
            let s = newCpSolver()
            var ids: seq[int]
            for k in 0 ..< 12: ids.add s.newVar(lo[k], hi[k])
            s.addDiffn(ids[0 ..< 3], ids[3 ..< 6], ids[6 ..< 9], ids[9 ..< 12])
            s.addBranchGroup(ids, vsFirstFail, valMin)
            let st = s.solve()
            check st == (if expected: cpSat else: cpUnsat)
            if st == cpSat:
                check ok(ids.mapIt(s.value(it)))

    test "difference logic: paths fix literals and close cycles":
        # x < y < z over a wide range; b <-> z < x is false by the path x -> z,
        # which bounds propagation alone cannot see
        let s = newCpSolver()
        let x = s.newVar(0, 1_000_000)
        let y = s.newVar(0, 1_000_000)
        let z = s.newVar(0, 1_000_000)
        let b = s.newVar(0, 1)
        s.addLinear(@[1, -1], @[x, y], -1, lrLe)
        s.addLinear(@[1, -1], @[y, z], -1, lrLe)
        s.addLinear(@[1, -1], @[z, x], -1, lrLe, b)
        check s.addDifferenceLogic() == 4
        check s.prepare()
        check s.isFixed(b) and s.value(b) == 0
        # a defined variable is substituted: w = z - x, and c <-> w <= 1 is false
        let s2 = newCpSolver()
        let x2 = s2.newVar(0, 1_000_000)
        let y2 = s2.newVar(0, 1_000_000)
        let z2 = s2.newVar(0, 1_000_000)
        let w2 = s2.newVar(-2_000_000, 2_000_000)
        let c2 = s2.newVar(0, 1)
        s2.addLinear(@[1, -1], @[x2, y2], -1, lrLe)
        s2.addLinear(@[1, -1], @[y2, z2], -1, lrLe)
        s2.addLinear(@[1, -1, 1], @[w2, z2, x2], 0, lrEq)
        s2.addLinear(@[1], @[w2], 1, lrLe, c2)
        check s2.addDifferenceLogic(@[DlDef(v: w2, a: @[1, -1], x: @[z2, x2], c: 0)]) == 4
        check s2.prepare()
        check s2.isFixed(c2) and s2.value(c2) == 0

    test "difference logic: random small models agree with brute force":
        var rng = initRand(777)
        var sats = 0
        var withDl = 0
        for trial in 0 ..< 400:
            # ints x0..x3 in sub-ranges of 0..4, w = x_wa - x_wb + wc (defined),
            # hard differences, (half-)reified differences, clauses over the
            # literals, and a 2-rectangle diffn with constant sizes
            var lo, hi: seq[int]
            for k in 0 ..< 4:
                let a = rng.rand(0 .. 4)
                lo.add a
                hi.add rng.rand(a .. 4)
            let wa = rng.rand(0 .. 3)
            let wb = (wa + 1 + rng.rand(0 .. 2)) mod 4
            let wc = rng.rand(-2 .. 2)
            type Dc = tuple[u, v, c: int]        # val(u) - val(v) <= c; index 4 = w
            var hard: seq[Dc]
            for _ in 0 ..< rng.rand(0 .. 2):
                let u = rng.rand(0 .. 4)
                hard.add (u, (u + 1 + rng.rand(0 .. 3)) mod 5, rng.rand(-2 .. 2))
            var lits: seq[(Dc, bool)]          # (difference, full reification)
            for _ in 0 ..< 3:
                let u = rng.rand(0 .. 4)
                lits.add ((u, (u + 1 + rng.rand(0 .. 3)) mod 5, rng.rand(-3 .. 2)), rng.rand(1.0) < 0.7)
            var clauses: seq[seq[(int, bool)]]
            for _ in 0 ..< 2:
                var cl: seq[(int, bool)]
                for _ in 0 ..< rng.rand(1 .. 3): cl.add (rng.rand(0 .. 2), rng.rand(1.0) < 0.6)
                clauses.add cl
            let sz = [rng.rand(1 .. 2), rng.rand(1 .. 2), rng.rand(1 .. 2), rng.rand(1 .. 2)]
            proc okAll(xv: seq[int], bv: seq[int]): bool =
                var v = xv
                v.add xv[wa] - xv[wb] + wc
                for h in hard:
                    if v[h.u] - v[h.v] > h.c: return false
                for k, (d, full) in lits:
                    let holds = v[d.u] - v[d.v] <= d.c
                    if bv[k] == 1 and not holds: return false
                    if full and bv[k] == 0 and holds: return false
                for cl in clauses:
                    var sat = false
                    for (k, pos) in cl:
                        if (bv[k] == 1) == pos: sat = true
                    if not sat: return false
                # rectangles at (x0, x2) size (sz0, sz1) and (x1, x3) size (sz2, sz3)
                v[0] + sz[0] <= v[1] or v[2] + sz[1] <= v[3] or
                    v[1] + sz[2] <= v[0] or v[3] + sz[3] <= v[2]
            var expected = false
            var xv = newSeq[int](4)
            proc rec(k: int): bool =
                if k == 4:
                    for m in 0 ..< 8:
                        if okAll(xv, @[m and 1, (m shr 1) and 1, (m shr 2) and 1]): return true
                    return false
                for val in lo[k] .. hi[k]:
                    xv[k] = val
                    if rec(k + 1): return true
                false
            expected = rec(0)
            let s = newCpSolver()
            var ids: seq[int]
            for k in 0 ..< 4: ids.add s.newVar(lo[k], hi[k])
            let w = s.newVar(-10, 10)
            ids.add w
            s.addLinear(@[1, -1, 1], @[w, ids[wa], ids[wb]], wc, lrEq)
            for h in hard: s.addLinear(@[1, -1], @[ids[h.u], ids[h.v]], h.c, lrLe)
            var bs: seq[int]
            for (d, full) in lits:
                let b = s.newVar(0, 1)
                bs.add b
                s.addLinear(@[1, -1], @[ids[d.u], ids[d.v]], d.c, lrLe, b, not full)
            for cl in clauses:
                var lv: seq[int]
                var lp: seq[bool]
                for (k, pos) in cl:
                    lv.add bs[k]
                    lp.add pos
                s.addOr(lv, lp)
            s.addDiffn(@[ids[0], ids[1]], @[ids[2], ids[3]],
                       @[s.constVar(sz[0]), s.constVar(sz[2])], @[s.constVar(sz[1]), s.constVar(sz[3])])
            let dlDefs = @[DlDef(v: w, a: @[1, -1], x: @[ids[wa], ids[wb]], c: wc)]
            if s.addDifferenceLogic(dlDefs) > 0: inc withDl
            let st = s.refute()
            check st == (if expected: cpSat else: cpUnsat)
            if st == cpSat:
                inc sats
                check okAll(ids[0 ..< 4].mapIt(s.value(it)), bs.mapIt(s.value(it)))
                check s.value(w) == s.value(ids[wa]) - s.value(ids[wb]) + wc
        check sats > 50 and sats < 350
        check withDl > 300

    test "orientation branch and bound: random packings reach the brute-force optimum":
        # 3 rectangles (diffn, sizes 1..2) on 0..4, hard differences, two
        # reified differences in a clause; objective mx + my + |mx - my| with
        # mx / my the maxima of the far edges (rect-euler's shape: max and abs
        # over defined variables, a max result that is a graph node)
        var rng = initRand(4242)
        var improvedRuns, exact, optimalStarts = 0
        for trial in 0 ..< 150:
            var w, h: seq[int]
            for i in 0 ..< 3:
                w.add rng.rand(1 .. 2)
                h.add rng.rand(1 .. 2)
            type Dc = tuple[u, v, c: int]        # val(u) - val(v) <= c over x0..x2, y0..y2
            var hard: seq[Dc]
            for _ in 0 ..< rng.rand(0 .. 2):
                let u = rng.rand(0 .. 5)
                hard.add (u, (u + 1 + rng.rand(0 .. 4)) mod 6, rng.rand(-1 .. 3))
            var lits: seq[Dc]
            for _ in 0 ..< 2:
                let u = rng.rand(0 .. 5)
                lits.add (u, (u + 1 + rng.rand(0 .. 4)) mod 6, rng.rand(-2 .. 1))
            proc cost(v: seq[int]): int =
                ## objective of positions v (x0..x2, y0..y2), or -1 if infeasible
                for hd in hard:
                    if v[hd.u] - v[hd.v] > hd.c: return -1
                if not (v[lits[0].u] - v[lits[0].v] <= lits[0].c or v[lits[1].u] - v[lits[1].v] <= lits[1].c):
                    return -1
                for i in 0 ..< 3:
                    for j in i + 1 ..< 3:
                        if not (v[i] + w[i] <= v[j] or v[j] + w[j] <= v[i] or
                                v[3 + i] + h[i] <= v[3 + j] or v[3 + j] + h[j] <= v[3 + i]): return -1
                var mx, my = 0
                for i in 0 ..< 3:
                    mx = max(mx, v[i] + w[i])
                    my = max(my, v[3 + i] + h[i])
                mx + my + abs(mx - my)
            var best = -1
            var pos = newSeq[int](6)
            proc brute(k: int) =
                if k == 6:
                    let c = cost(pos)
                    if c >= 0 and (best < 0 or c < best): best = c
                    return
                for val in 0 .. 4:
                    pos[k] = val
                    brute(k + 1)
            brute(0)
            let s = newCpSolver()
            var xs, ys: seq[int]
            for i in 0 ..< 3: xs.add s.newVar(0, 4)
            for i in 0 ..< 3: ys.add s.newVar(0, 4)
            let ids = xs & ys
            var defs: seq[DlDef]
            var ex, ey: seq[int]
            for i in 0 ..< 3:
                ex.add s.newVar(0, 10)
                s.addLinear(@[1, -1], @[ex[i], xs[i]], w[i], lrEq)
                defs.add DlDef(v: ex[i], a: @[1], x: @[xs[i]], c: w[i])
                ey.add s.newVar(0, 10)
                s.addLinear(@[1, -1], @[ey[i], ys[i]], h[i], lrEq)
                defs.add DlDef(v: ey[i], a: @[1], x: @[ys[i]], c: h[i])
            let mx = s.newVar(0, 10)
            let my = s.newVar(0, 10)
            s.addMax(mx, ex)
            s.addMax(my, ey)
            let t = s.newVar(-10, 10)
            s.addLinear(@[1, -1, 1], @[t, mx, my], 0, lrEq)
            defs.add DlDef(v: t, a: @[1, -1], x: @[mx, my], c: 0)
            let d = s.newVar(0, 10)
            s.addAbs(t, d)
            let obj = s.newVar(0, 40)
            s.addLinear(@[1, 1, 1, -1], @[mx, my, d, obj], 0, lrEq)
            for hd in hard: s.addLinear(@[1, -1], @[ids[hd.u], ids[hd.v]], hd.c, lrLe)
            var bs: seq[int]
            for l in lits:
                let b = s.newVar(0, 1)
                bs.add b
                s.addLinear(@[1, -1], @[ids[l.u], ids[l.v]], l.c, lrLe, b, rng.rand(1.0) < 0.5)
            s.addOr(bs, @[true, true])
            s.addDiffn(xs, ys, w.mapIt(s.constVar(it)), h.mapIt(s.constVar(it)))
            if s.addDifferenceLogic(defs) == 0 or not s.prepare():
                check best < 0
                continue
            if s.search() != cpSat:
                check best < 0
                continue
            var cur = newSeq[int](s.numVars)
            for v in 0 ..< s.numVars: cur[v] = s.value(v)
            s.popTo(0)
            check best >= 0 and cost(ids.mapIt(cur[it])) == cur[obj]
            let o = s.dlOrientation(obj, false)
            check o != nil
            if o == nil: continue
            var used = 0
            let found = s.dlImprove(o, cur, newSeq[bool](o.disj.len).mapIt(true), 100_000, 0.0, used)
            check s.level == 0
            if cur[obj] == best:
                inc optimalStarts
                check found.len == 0
            elif found.len > 0:
                inc improvedRuns
                let c = cost(ids.mapIt(found[it]))
                check c == found[obj] and c >= best and c < cur[obj]
                if c == best: inc exact
        check improvedRuns >= 30
        check exact >= improvedRuns - 2
        check optimalStarts + improvedRuns >= 100

    test "refute: pigeonhole through restarts, satisfiable model":
        let s = newCpSolver()
        var xs: seq[int]
        for i in 0 ..< 7: xs.add s.newVar(1, 6)
        for i in 0 ..< 7:
            for j in i + 1 ..< 7: s.addLinear(@[1, -1], @[xs[i], xs[j]], 0, lrNe)
        check s.refute() == cpUnsat
        check s.nodes > 100          # needed restarts (the first run stops at 100 nodes)
        let s2 = newCpSolver()
        var ys: seq[int]
        for i in 0 ..< 6: ys.add s2.newVar(1, 6)
        for i in 0 ..< 6:
            for j in i + 1 ..< 6: s2.addLinear(@[1, -1], @[ys[i], ys[j]], 0, lrNe)
        check s2.refute() == cpSat
        var seen: seq[int]
        for y in ys: seen.add s2.value(y)
        check seen.deduplicate.len == 6

    test "random models agree with brute force":
        var rng = initRand(12345)
        const nVars = 4
        const dLo = 0
        const dHi = 3
        type Con = object
            kind: int
            a: seq[int]
            x: seq[int]
            c: int
            r: int
            t: seq[int]     # table tuples (kind 9)
        for trial in 0 ..< 3000:
            var cons: seq[Con]
            let nCons = rng.rand(1 .. 5)
            for k in 0 ..< nCons:
                # table, div and gcc (kinds 9-11) have no reified form: never first
                var cn = Con(kind: (if k == 0: rng.rand(0 .. 8) else: rng.rand(0 .. 11)), r: -1)
                let ar = rng.rand(1 .. 3)
                for t in 0 ..< ar:
                    cn.a.add rng.rand(-3 .. 3)
                    cn.x.add rng.rand(0 ..< nVars)
                cn.c = rng.rand(-6 .. 6)
                if cn.kind == 9:
                    for _ in 0 ..< rng.rand(0 .. 6) * ar: cn.t.add rng.rand(-1 .. 4)
                cons.add cn
            # one boolean (var nVars, 0..1) reifies the first constraint
            let reif = rng.rand(1) == 1
            proc holds(cn: Con, v: seq[int]): bool =
                case cn.kind
                of 0, 1, 2:
                    var sum = 0
                    for t in 0 ..< cn.a.len: sum += cn.a[t] * v[cn.x[t]]
                    (if cn.kind == 0: sum <= cn.c elif cn.kind == 1: sum == cn.c else: sum != cn.c)
                of 3: v[cn.x[0]] * v[cn.x[^1]] == cn.c
                of 4: max(cn.x.mapIt(v[it])) == v[(cn.x[0] + 1) mod nVars]
                of 5: abs(v[cn.x[0]] - 2) == v[cn.x[^1]]
                of 6: (v[cn.x[0]] in [1, 3]) == (cn.c >= 0)
                of 7:
                    # r = xs[x0 + 1] over the array (x_1..x_3, x_0): 1-based index x0 + 1
                    let arr = @[v[1], v[2], v[3], v[0]]
                    arr[v[cn.x[0]]] == v[cn.x[^1]] + (cn.c mod 2)
                of 9:
                    var found = false
                    var t = 0
                    while t < cn.t.len:
                        var ok = true
                        for i in 0 ..< cn.x.len:
                            if v[cn.x[i]] != cn.t[t + i]: ok = false
                        if ok: found = true
                        t += cn.x.len
                    found
                of 10:
                    # (x0 - 1) div (x_last - 2) == c mod 3, truncating, divisor != 0
                    let bv = v[cn.x[^1]] - 2
                    bv != 0 and (v[cn.x[0]] - 1) div bv == cn.c mod 3
                of 11:
                    # gcc over cn.x with cover [1, 3]: even c -> bounds [0..1, 1..2],
                    # odd c -> counts equal; closed when |c| > 2
                    var n1, n3, outside = 0
                    for t in cn.x:
                        if v[t] == 1: inc n1
                        elif v[t] == 3: inc n3
                        else: inc outside
                    if abs(cn.c) > 2 and outside > 0: false
                    elif cn.c mod 2 == 0: n1 <= 1 and n3 >= 1 and n3 <= 2
                    else: n1 == n3
                else:
                    # clause: some x_i >= 2 (i in cn.x), or x_0 = 0 when c < 0
                    var any = cn.c < 0 and v[0] == 0
                    for t in cn.x:
                        if v[t] >= 2: any = true
                    any
            proc allHold(v: seq[int]): bool =
                for k, cn in cons:
                    let h = cn.holds(v)
                    if k == 0 and reif:
                        if (v[nVars] == 1) != h: return false
                    elif not h: return false
                true
            # brute force
            var anySol = false
            var v = newSeq[int](nVars + 1)
            proc rec(i: int): bool =
                if i == nVars + 1: return allHold(v)
                let top = if i == nVars: 1 else: dHi
                for val in (if i == nVars: 0 else: dLo) .. top:
                    v[i] = val
                    if rec(i + 1): return true
                false
            anySol = rec(0)
            # engine
            let s = newCpSolver()
            var xs: seq[int]
            for i in 0 ..< nVars: xs.add s.newVar(dLo, dHi)
            let b = s.newVar(0, 1)
            for k, cn in cons:
                let r = if k == 0 and reif: b else: -1
                case cn.kind
                of 0, 1, 2:
                    let rel = [lrLe, lrEq, lrNe][cn.kind]
                    s.addLinear(cn.a, cn.x.mapIt(xs[it]), cn.c, rel, r)
                of 3:
                    let p = s.newVar(-100, 100)
                    s.addTimes(xs[cn.x[0]], xs[cn.x[^1]], p)
                    s.addLinear(@[1], @[p], cn.c, lrEq, r)
                of 4:
                    let m = s.newVar(-100, 100)
                    s.addMax(m, cn.x.mapIt(xs[it]))
                    s.addLinear(@[1, -1], @[m, xs[(cn.x[0] + 1) mod nVars]], 0, lrEq, r)
                of 6:
                    if cn.c >= 0: s.addSetIn(xs[cn.x[0]], @[3, 1], r)
                    else:
                        let bb = s.newVar(0, 1)
                        s.addSetIn(xs[cn.x[0]], @[1, 3], bb)
                        s.addLinear(@[1], @[bb], 0, lrEq, r)
                of 7:
                    let idx = s.newVar(-100, 100)
                    s.addLinear(@[1, -1], @[idx, xs[cn.x[0]]], 1, lrEq)
                    let rr = s.newVar(-100, 100)
                    s.addVarElement(idx, @[xs[1], xs[2], xs[3], xs[0]], rr)
                    s.addLinear(@[1, -1], @[rr, xs[cn.x[^1]]], cn.c mod 2, lrEq, r)
                of 8:
                    var lits: seq[int]
                    var pols: seq[bool]
                    for t in cn.x:
                        let bb = s.newVar(0, 1)
                        s.addLinear(@[-1], @[xs[t]], -2, lrLe, bb)    # bb <-> x_t >= 2
                        lits.add bb; pols.add true
                    if cn.c < 0:
                        let z = s.newVar(0, 1)
                        s.addLinear(@[1], @[xs[0]], 0, lrEq, z)
                        lits.add z; pols.add true
                    if r < 0: s.addOr(lits, pols)
                    else: s.addOr(lits, pols, r, true)
                of 9:
                    if cn.t.len == 0:
                        s.addLinear(@[1], @[xs[0]], -1, lrLe)     # no tuple: infeasible
                    else:
                        s.addTable(cn.x.mapIt(xs[it]), cn.t)
                of 10:
                    let av = s.newVar(-100, 100)
                    s.addLinear(@[1, -1], @[av, xs[cn.x[0]]], -1, lrEq)
                    let bv = s.newVar(-100, 100)
                    s.addLinear(@[1, -1], @[bv, xs[cn.x[^1]]], -2, lrEq)
                    let q = s.newVar(-100, 100)
                    s.addDiv(av, bv, q)
                    s.addLinear(@[1], @[q], cn.c mod 3, lrEq)
                of 11:
                    let closed = abs(cn.c) > 2
                    let xv = cn.x.mapIt(xs[it])
                    if cn.c mod 2 == 0:
                        s.addGcc(xv, @[1, 3], @[0, 1], @[1, 2], closed = closed)
                    else:
                        let c1 = s.newVar(-100, 100)
                        let c3 = s.newVar(-100, 100)
                        s.addGcc(xv, @[3, 1], @[], @[], @[c3, c1], closed)
                        s.addLinear(@[1, -1], @[c1, c3], 0, lrEq)
                else:
                    let dv = s.newVar(-100, 100)
                    s.addLinear(@[1, -1], @[dv, xs[cn.x[0]]], -2, lrEq)
                    let ab = s.newVar(-100, 100)
                    s.addAbs(dv, ab)
                    s.addLinear(@[1, -1], @[ab, xs[cn.x[^1]]], 0, lrEq, r)
            # odd trials shave the root first: removals must keep every solution
            let shaved = if trial mod 2 == 1: s.shaveBounds() else: 0
            # every fourth trial uses the refutation search (dom/wdeg, restarts)
            let st = if shaved < 0: cpUnsat elif trial mod 4 == 3: s.refute() else: s.solve()
            check st == (if anySol: cpSat else: cpUnsat)
            if st == cpSat:
                var sol = xs.mapIt(s.value(it))
                sol.add s.value(b)
                check allHold(sol)
