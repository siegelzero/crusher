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
        for trial in 0 ..< 1500:
            var cons: seq[Con]
            let nCons = rng.rand(1 .. 5)
            for k in 0 ..< nCons:
                var cn = Con(kind: rng.rand(0 .. 8), r: -1)
                let ar = rng.rand(1 .. 3)
                for t in 0 ..< ar:
                    cn.a.add rng.rand(-3 .. 3)
                    cn.x.add rng.rand(0 ..< nVars)
                cn.c = rng.rand(-6 .. 6)
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
                else:
                    let dv = s.newVar(-100, 100)
                    s.addLinear(@[1, -1], @[dv, xs[cn.x[0]]], -2, lrEq)
                    let ab = s.newVar(-100, 100)
                    s.addAbs(dv, ab)
                    s.addLinear(@[1, -1], @[ab, xs[cn.x[^1]]], 0, lrEq, r)
            let st = s.solve()
            check st == (if anySol: cpSat else: cpUnsat)
            if st == cpSat:
                var sol = xs.mapIt(s.value(it))
                sol.add s.value(b)
                check allHold(sol)
