## Included from translator.nim -- not a standalone module.
##
## LP-guided construction (MIP-style diving) for models that are linear apart
## from reifications and clauses. The FlatZinc model is linearized directly:
## linear constraints as rows, bool_clause / array_bool_and/or as their
## standard 0-1 inequalities, reifications as big-M rows from the
## presolve-tightened variable bounds. Convex `x != c` halves become rows,
## the others are enforced by branching. The LP relaxation is solved with the
## bounded dual simplex and a depth-first dive rounds it to an integral point.
##
## It is a fallback only (`lpDiveFallback` → `ConstraintSystem.seedFallback`):
## when the first resolve finds nothing within part of its budget, the dive's
## point seeds state 0 of a restarted search.
##
## Local search struggles exactly where the relaxation is informative: in
## zephyrus, "one comp1 is present" implies ~10 comp3, ~20 comp4 and their
## bindings and placements, a long uphill chain for single-variable moves that
## the LP sees at once.

import ../search/lpSimplex

type
    LpBuild = object
        model: LpModel
        col: Table[string, int]      # FZN var name -> LP column
        names: seq[string]
        isInt: seq[bool]
        unsupported: string          # first constraint that could not be linearized
        fixed: seq[(string, float)]  # columns removed by the reduction (fixed value)
        # Non-convex `x != c` halves, enforced by branching in the dive:
        # when lit == litVal (lit -1: always), x must differ from c.
        neqs: seq[tuple[x: int, c: float, lit: int, litVal: float]]
        # Domain encodings of small-domain variables used in reifications
        # against constants: x = Σ v·y_v, Σ y_v = 1 (y column per value).
        enc: Table[int, seq[(int, int)]]   # x column -> [(value, y column)]

proc lpColumn(tr: var FznTranslator, b: var LpBuild, name: string): int =
    ## LP column of a scalar FZN variable, created on first use (-1: unbounded).
    if name in b.col: return b.col[name]
    # Bounds only: materializing a wide declared range per column is slow.
    var lo, hi: int
    if name in tr.presolveDomains:
        let dom {.cursor.} = tr.presolveDomains[name]
        if dom.len == 0: return -1
        lo = min(dom); hi = max(dom)
    else:
        tr.buildVarDomainIndex()
        let (known, dlo, dhi) = tr.declaredBounds(name)
        if not known: return -1
        lo = dlo; hi = dhi
    result = b.model.n
    inc b.model.n
    b.model.lb.add float(lo)
    b.model.ub.add float(hi)
    b.model.cost.add 0.0
    b.col[name] = result
    b.names.add name
    b.isInt.add true

type LinTerm = tuple[idx: seq[int], val: seq[float], konst: float, ok: bool]

proc lpTerms(tr: var FznTranslator, b: var LpBuild, coeffs: seq[int],
             elems: seq[FznExpr]): LinTerm =
    ## Σ coeffs·elems as LP columns plus a constant.
    result.ok = coeffs.len == elems.len
    if not result.ok: return
    var at: Table[int, int]
    for i, e in elems:
        let c = float(coeffs[i])
        case e.kind
        of FznIntLit: result.konst += c * float(e.intVal)
        of FznBoolLit: result.konst += c * (if e.boolVal: 1.0 else: 0.0)
        of FznIdent:
            if e.ident in tr.paramValues:
                result.konst += c * float(tr.paramValues[e.ident])
            else:
                let j = tr.lpColumn(b, e.ident)
                if j < 0:
                    result.ok = false; return
                if j in at:
                    result.val[at[j]] += c
                else:
                    at[j] = result.idx.len
                    result.idx.add j
                    result.val.add c
        else:
            result.ok = false; return

proc termRange(b: LpBuild, t: LinTerm): (float, float) =
    var lo = t.konst
    var hi = t.konst
    for k, j in t.idx:
        let v = t.val[k]
        if v >= 0: (lo += v * b.model.lb[j]; hi += v * b.model.ub[j])
        else: (lo += v * b.model.ub[j]; hi += v * b.model.lb[j])
    (lo, hi)

proc addLe(b: var LpBuild, t: LinTerm, c: float) =
    ## t <= c
    b.model.addRow(t.idx, t.val, -LpInf, c - t.konst)

proc addGe(b: var LpBuild, t: LinTerm, c: float) =
    b.model.addRow(t.idx, t.val, c - t.konst, LpInf)

proc addEq(b: var LpBuild, t: LinTerm, c: float) =
    b.model.addRow(t.idx, t.val, c - t.konst, c - t.konst)

proc addNeq(b: var LpBuild, t: LinTerm, c: float, lit: int, litVal: float) =
    ## t != c (when lit == litVal) for a single-variable t = k*x + konst.
    if t.idx.len != 1 or t.val[0] == 0: return
    let v = (c - t.konst) / t.val[0]
    if abs(v - round(v)) > 1e-9: return          # x can never hit it
    b.neqs.add((x: t.idx[0], c: round(v), lit: lit, litVal: litVal))

const LpEncodeMaxDomain = 64

proc encoding(tr: var FznTranslator, b: var LpBuild, x: int, name: string): seq[(int, int)] =
    ## Value indicators of column x (created on first use; empty if the
    ## domain is too large to encode).
    if x in b.enc: return b.enc[x]
    let dom = tr.lookupTightenedDomain(name)
    if dom.len < 2 or dom.len > LpEncodeMaxDomain: return
    var ys: seq[(int, int)]
    var idx = @[x]
    var val = @[1.0]
    var ones: seq[int]
    var onesV: seq[float]
    for v in dom:
        let y = b.model.n
        inc b.model.n
        b.model.lb.add 0.0; b.model.ub.add 1.0; b.model.cost.add 0.0
        b.names.add ""; b.isInt.add true
        ys.add((v, y))
        idx.add y; val.add -float(v)
        ones.add y; onesV.add 1.0
    b.model.addRow(idx, val, 0.0, 0.0)          # x = Σ v·y_v
    b.model.addRow(ones, onesV, 1.0, 1.0)      # Σ y_v = 1
    b.enc[x] = ys
    ys

proc addGuarded(b: var LpBuild, t: LinTerm, c: float, le: bool, lit: int, litTrue: bool) =
    ## (lit == litTrue) -> t <= c (le) or t >= c (not le), big-M from bounds.
    let (lo, hi) = b.termRange(t)
    if le:
        let m = hi - c
        if m <= 0: return                      # always true
        # t + m*g <= c + m, with g = lit (litTrue) or 1 - lit
        var t2 = t
        if litTrue:
            t2.idx.add lit; t2.val.add m
            b.addLe(t2, c + m)
        else:
            t2.idx.add lit; t2.val.add -m      # t + m(1 - lit) <= c + m
            b.addLe(t2, c)
    else:
        let m = c - lo
        if m <= 0: return
        var t2 = t
        if litTrue:
            t2.idx.add lit; t2.val.add -m      # t - m*lit >= c - m
            b.addGe(t2, c - m)
        else:
            t2.idx.add lit; t2.val.add m       # t - m(1 - lit) >= c - m
            b.addGe(t2, c)

proc buildLpModel(tr: var FznTranslator): LpBuild =
    var b: LpBuild
    proc elemsOf(tr: var FznTranslator, arg: FznExpr): seq[FznExpr] =
        result = tr.resolveVarArrayElems(arg)
        if result.len == 0 and arg.kind == FznIdent and arg.ident in tr.arrayValues:
            for v in tr.arrayValues[arg.ident]: result.add FznExpr(kind: FznIntLit, intVal: v)
    proc coeffsOf(tr: var FznTranslator, arg: FznExpr): (bool, seq[int]) =
        try: (true, tr.resolveIntArray(arg))
        except CatchableError: (false, newSeq[int]())
    proc litCol(tr: var FznTranslator, b: var LpBuild, e: FznExpr): int =
        if e.kind == FznIdent and e.ident notin tr.paramValues: tr.lpColumn(b, e.ident)
        else: -1
    # Cheap name pre-scan: most models have some global without a
    # linearization, and should not pay for building the rest.
    const LpSupported = ["int_lin_le", "int_lin_eq", "int_lin_ne", "bool_lin_le", "bool_lin_eq",
        "int_le", "int_lt", "int_eq", "int_ne", "bool_le", "bool_lt", "bool_eq",
        "bool2int", "bool_not", "bool_clause", "array_bool_and", "array_bool_or",
        "int_lin_le_reif", "int_lin_eq_reif", "int_lin_ne_reif",
        "int_le_reif", "int_lt_reif", "int_eq_reif", "int_ne_reif",
        "int_max", "int_min", "array_int_maximum", "array_int_minimum"]
    for con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin LpSupported:
            b.unsupported = name
            return b
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        template fail() =
            # One constraint without a linearization makes the LP unusable
            b.unsupported = name
            return b
        case name
        of "int_lin_le", "int_lin_eq", "int_lin_ne", "bool_lin_le", "bool_lin_eq":
            let (okc, cs) = tr.coeffsOf(con.args[0])
            if not okc or con.args[2].kind != FznIntLit: fail()
            let t = tr.lpTerms(b, cs, tr.elemsOf(con.args[1]))
            if not t.ok: fail()
            let c = float(con.args[2].intVal)
            if name.endsWith("_le"): b.addLe(t, c)
            elif name.endsWith("_eq"): b.addEq(t, c)
            else:
                let (tlo, thi) = b.termRange(t)
                if abs(c - tlo) < 0.5: b.addGe(t, c + 1)
                elif abs(c - thi) < 0.5: b.addLe(t, c - 1)
                else: b.addNeq(t, c, -1, 0)
        of "int_le", "int_lt", "int_eq", "int_ne", "bool_le", "bool_lt", "bool_eq":
            let t = tr.lpTerms(b, @[1, -1], @[con.args[0], con.args[1]])
            if not t.ok: fail()
            case name
            of "int_le", "bool_le": b.addLe(t, 0)
            of "int_lt", "bool_lt": b.addLe(t, -1)
            of "int_eq", "bool_eq": b.addEq(t, 0)
            else: b.addNeq(t, 0, -1, 0)
        of "bool2int":
            let t = tr.lpTerms(b, @[1, -1], @[con.args[0], con.args[1]])
            if not t.ok: fail()
            b.addEq(t, 0)
        of "bool_not":
            let t = tr.lpTerms(b, @[1, 1], @[con.args[0], con.args[1]])
            if not t.ok: fail()
            b.addEq(t, 1)
        of "bool_clause":
            let pos = tr.elemsOf(con.args[0])
            let neg = tr.elemsOf(con.args[1])
            var cs: seq[int]
            for _ in pos: cs.add 1
            for _ in neg: cs.add -1
            let t = tr.lpTerms(b, cs, pos & neg)
            if not t.ok: fail()
            b.addGe(t, 1.0 - float(neg.len))
        of "array_bool_and", "array_bool_or":
            let xs = tr.elemsOf(con.args[0])
            let r = tr.litCol(b, con.args[1])
            if r < 0: fail()
            let isAnd = name == "array_bool_and"
            var ok = true
            for e in xs:
                let t = tr.lpTerms(b, @[1, -1], @[e, con.args[1]])
                if not t.ok: ok = false; break
                if isAnd: b.addGe(t, 0) else: b.addLe(t, 0)   # r <= x_i  /  x_i <= r
            if not ok: fail()
            var cs = newSeq[int](xs.len)
            for k in 0..<cs.len: cs[k] = 1
            let t = tr.lpTerms(b, cs & @[-1], xs & @[con.args[1]])
            if not t.ok: fail()
            if isAnd: b.addLe(t, float(xs.len - 1))           # Σx - r <= n - 1
            else: b.addGe(t, 0)                               # Σx - r >= 0
        of "int_lin_le_reif", "int_lin_eq_reif", "int_lin_ne_reif",
           "int_le_reif", "int_lt_reif", "int_eq_reif", "int_ne_reif":
            var t: LinTerm
            var c = 0.0
            var lit: FznExpr
            if name.startsWith("int_lin"):
                let (okc, cs) = tr.coeffsOf(con.args[0])
                if not okc or con.args[2].kind != FznIntLit: fail()
                t = tr.lpTerms(b, cs, tr.elemsOf(con.args[1]))
                c = float(con.args[2].intVal)
                lit = con.args[3]
            else:
                t = tr.lpTerms(b, @[1, -1], @[con.args[0], con.args[1]])
                lit = con.args[2]
                if name == "int_lt_reif": c = -1
            if not t.ok: fail()
            let lc = tr.litCol(b, lit)
            # Single small-domain variable: the literal is exactly the sum of
            # the indicators of the values that satisfy the relation.
            if t.idx.len == 1 and t.val[0] != 0 and (lc >= 0 or lit.kind == FznBoolLit):
                let x = t.idx[0]
                let ys = tr.encoding(b, x, b.names[x])
                if ys.len > 0:
                    let kind = if name.contains("_le") or name.contains("_lt"): "le"
                               elif name.contains("_eq"): "eq" else: "ne"
                    var idx: seq[int]
                    var val: seq[float]
                    for (v, y) in ys:
                        let tv = t.val[0] * float(v) + t.konst
                        let sat = case kind
                            of "le": tv <= c + 1e-9
                            of "eq": abs(tv - c) < 1e-9
                            else: abs(tv - c) >= 1e-9
                        if sat: (idx.add y; val.add 1.0)
                    if lc >= 0:
                        idx.add lc; val.add -1.0
                        b.model.addRow(idx, val, 0.0, 0.0)     # lit = Σ_{v sat} y_v
                    else:
                        let r = if lit.boolVal: 1.0 else: 0.0
                        b.model.addRow(idx, val, r, r)
                    continue
            if lc < 0:
                # Fixed literal: the constraint or its negation holds outright
                if lit.kind != FznBoolLit: fail()
                let holds = lit.boolVal
                let kind = if name.contains("_le") or name.contains("_lt"): "le"
                           elif name.contains("_eq"): "eq" else: "ne"
                if (kind == "le" and holds): b.addLe(t, c)
                elif kind == "le": b.addGe(t, c + 1)
                elif (kind == "eq" and holds) or (kind == "ne" and not holds): b.addEq(t, c)
                else:
                    let (tlo, thi) = b.termRange(t)
                    if abs(c - tlo) < 0.5: b.addGe(t, c + 1)
                    elif abs(c - thi) < 0.5: b.addLe(t, c - 1)
                    else: b.addNeq(t, c, -1, 0)
                continue
            if name.contains("_le") or name.contains("_lt"):
                b.addGuarded(t, c, le = true, lc, true)        # b -> t <= c
                b.addGuarded(t, c + 1, le = false, lc, false)  # ¬b -> t >= c + 1
            else:
                # eq: b -> t == c, ¬b -> t != c; ne: the other way round. The
                # `!=` side is convex only when c is an end of t's range
                # (sum == 0 <-> unused: ¬b -> sum >= 1); otherwise dropped.
                let eqLit = name.contains("_eq")
                b.addGuarded(t, c, le = true, lc, eqLit)
                b.addGuarded(t, c, le = false, lc, eqLit)
                let (tlo, thi) = b.termRange(t)
                if abs(c - tlo) < 0.5: b.addGuarded(t, c + 1, le = false, lc, not eqLit)
                elif abs(c - thi) < 0.5: b.addGuarded(t, c - 1, le = true, lc, not eqLit)
                else: b.addNeq(t, c, lc, if eqLit: 0.0 else: 1.0)
        of "int_max", "int_min", "array_int_maximum", "array_int_minimum":
            # Relaxed to the convex side: m >= x_i (max) / m <= x_i (min)
            let isMax = name.contains("max")
            var m: FznExpr
            var xs: seq[FznExpr]
            if name.startsWith("int_"):
                xs = @[con.args[0], con.args[1]]; m = con.args[2]
            else:
                m = con.args[0]; xs = tr.elemsOf(con.args[1])
            var ok = true
            for e in xs:
                let t = tr.lpTerms(b, @[1, -1], @[m, e])
                if not t.ok: ok = false; break
                if isMax: b.addGe(t, 0) else: b.addLe(t, 0)
            if not ok: fail()
        else:
            fail()
    # Objective
    if tr.model.solve.kind in {Minimize, Maximize} and tr.model.solve.objective != nil and
       tr.model.solve.objective.kind == FznIdent:
        let j = tr.lpColumn(b, tr.model.solve.objective.ident)
        if j >= 0:
            b.model.cost[j] = if tr.model.solve.kind == Minimize: 1.0 else: -1.0
    b

type
    LpDivePlan = object
        b: LpBuild
        defaults: seq[int]       # position assignment outside the LP columns
        colPos: seq[int]         # LP column -> position (-1: none)
        colDom: seq[seq[int]]    # that position's domain

proc prepareLpDive(tr: var FznTranslator, plan: var LpDivePlan, verbose: bool,
                   maxCells = 40_000_000): bool =
    ## Linearizes and reduces the model; false if it is not linearizable,
    ## trivially infeasible or too large for the dense simplex.
    var b = tr.buildLpModel()
    if b.unsupported != "":
        if verbose: stderr.writeLine(&"[LP] skipped: unsupported constraint {b.unsupported}")
        return false
    # Reduction: substitute fixed columns, drop rows that their bounds already
    # satisfy (big-M rows on fixed literals, redundant inequalities), then
    # renumber the remaining columns.
    block:
        var keep = newSeq[int](b.model.n)          # old col -> new col (-1 fixed)
        var nn = 0
        for j in 0..<b.model.n:
            if b.model.ub[j] - b.model.lb[j] < 0.5: keep[j] = -1
            else: (keep[j] = nn; inc nn)
        var rows: seq[LpRow]
        for r in b.model.rows:
            var nr = LpRow(lo: r.lo, hi: r.hi)
            var lo, hi = 0.0
            for k, j in r.idx:
                let v = r.val[k]
                if keep[j] < 0:
                    let c = v * b.model.lb[j]
                    if nr.lo > -LpInf: nr.lo -= c
                    if nr.hi < LpInf: nr.hi -= c
                elif v != 0:
                    nr.idx.add keep[j]; nr.val.add v
                    if v > 0: (lo += v * b.model.lb[j]; hi += v * b.model.ub[j])
                    else: (lo += v * b.model.ub[j]; hi += v * b.model.lb[j])
            if lo >= nr.lo - 1e-9 and hi <= nr.hi + 1e-9: continue   # always satisfied
            if nr.idx.len == 0:
                if verbose: stderr.writeLine("[LP] relaxation infeasible (constant row)")
                return false
            rows.add nr
        var red = LpModel(n: nn)
        var names: seq[string]
        var isInt: seq[bool]
        var fixedVals: seq[(string, float)]
        for j in 0..<b.model.n:
            if keep[j] < 0:
                fixedVals.add((b.names[j], b.model.lb[j])); continue
            red.lb.add b.model.lb[j]; red.ub.add b.model.ub[j]; red.cost.add b.model.cost[j]
            names.add b.names[j]; isInt.add b.isInt[j]
        red.rows = rows
        var neqs: seq[tuple[x: int, c: float, lit: int, litVal: float]]
        for q in b.neqs:
            let litFixed = q.lit >= 0 and keep[q.lit] < 0
            if litFixed and abs(b.model.lb[q.lit] - q.litVal) > 0.5: continue   # never active
            let lit = if q.lit < 0 or litFixed: -1 else: keep[q.lit]
            if keep[q.x] < 0:
                if abs(b.model.lb[q.x] - q.c) < 0.5 and lit < 0:
                    if verbose: stderr.writeLine("[LP] relaxation infeasible (fixed x == c)")
                    return false
                continue     # (fixed x with a free literal: left to the rows/search)
            neqs.add((x: keep[q.x], c: q.c, lit: lit, litVal: q.litVal))
        b.neqs = neqs
        b.model = red
        b.names = names
        b.isInt = isInt
        b.fixed = fixedVals
    let m = b.model.rows.len
    let n = b.model.n
    if n == 0 or m == 0 or m * (n + m) > maxCells:
        if verbose: stderr.writeLine(&"[LP] skipped: {m} rows x {n} columns")
        return false
    # Position mapping, so the dive needs nothing from the translator
    plan.defaults = newSeq[int](tr.sys.baseArray.len)
    for p in 0..<plan.defaults.len:
        let d {.cursor.} = tr.sys.baseArray.domain[p]
        plan.defaults[p] = if d.len > 0: d[0] else: 0
    for (name, v) in b.fixed:
        if name in tr.varPositions:
            let p = tr.varPositions[name]
            if tr.sys.baseArray.domain[p].len > 0: plan.defaults[p] = int(round(v))
    plan.colPos = newSeq[int](n)
    plan.colDom = newSeq[seq[int]](n)
    for j in 0..<n:
        plan.colPos[j] = -1
        let name = b.names[j]
        if name notin tr.varPositions: continue
        let p = tr.varPositions[name]
        if tr.sys.baseArray.domain[p].len == 0: continue
        plan.colPos[j] = p
        plan.colDom[j] = tr.sys.baseArray.domain[p]
    plan.b = move b
    true

proc runLpDive(plan: var LpDivePlan, timeLimit: float, verbose: bool): seq[int] =
    ## Solves the LP relaxation, dives to an integral point and returns it as
    ## a full position assignment (empty if the relaxation is infeasible or
    ## out of time). A failed dive returns its last feasible LP point, rounded.
    let t0 = epochTime()
    template b: untyped = plan.b
    let m = b.model.rows.len
    let n = b.model.n
    var s = initSolver(b.model)
    let lpDeadline = t0 + timeLimit
    var st = s.solve(deadline = lpDeadline)
    if st != lpOptimal:
        stderr.writeLine(&"[LP] relaxation {st} ({m} rows, {n} columns)")
        return
    let rootObj = s.objective()
    # Depth-first dive: branch on the least fractional integer column, nearest
    # integer first, the other side on backtrack. Bounds are restored on
    # backtrack (the dual simplex warm-starts from any bounds), so no tableau
    # snapshots are kept.
    type Decision = object
        col: int
        oldLo, oldHi: float
        altLo, altHi: float
        triedAlt: bool
    var stack: seq[Decision]
    var nodes, backtracks = 0
    var nIterLimit, nInfeasible = 0
    var pivotsAtRefresh, totalPivots, refreshes = 0
    var lastFeasible = newSeq[float](n)
    for j in 0..<n: lastFeasible[j] = s.value(j)
    var diveOk = false
    const MaxNodes = 5000
    while true:
        if epochTime() - t0 > timeLimit or nodes >= MaxNodes: break
        if st == lpOptimal:
            for j in 0..<n: lastFeasible[j] = s.value(j)
            # Most fractional binary first, then most fractional integer:
            # the decisions that matter fail early, near the root.
            var best = -1
            var bestScore = -1.0
            for j in 0..<n:
                if not b.isInt[j]: continue
                let v = s.value(j)
                let f = abs(v - round(v))
                if f <= 1e-6: continue
                let binary = b.model.ub[j] - b.model.lb[j] <= 1.0 + 1e-9
                let score = f + (if binary: 1.0 else: 0.0)
                if score > bestScore:
                    bestScore = score; best = j
            if best < 0:
                # Integral: enforce a violated `x != c` by branching
                var q = -1
                for k, cond in b.neqs:
                    if cond.lit >= 0 and abs(s.value(cond.lit) - cond.litVal) > 0.5: continue
                    if abs(s.value(cond.x) - cond.c) < 0.5:
                        q = k; break
                if q < 0:
                    diveOk = true; break
                let x = b.neqs[q].x
                let c = b.neqs[q].c
                let lo = s.lb[x]
                let hi = s.ub[x]
                # Branch around c: x >= c + 1 (first) or x <= c - 1, skipping
                # values that are excluded unconditionally. A conditional
                # exclusion depends on a literal that may change below this
                # node, so skipping it would drop it from both branches.
                var excluded: HashSet[int]
                for cond in b.neqs:
                    if cond.x == x and cond.lit < 0: excluded.incl int(cond.c)
                var up = c + 1
                while up <= hi and int(up) in excluded: up += 1
                var dn = c - 1
                while dn >= lo and int(dn) in excluded: dn -= 1
                var d = Decision(col: x, oldLo: lo, oldHi: hi, altLo: lo, altHi: dn)
                if up > hi and dn < lo:
                    # Neither side: treat as an infeasible node
                    st = lpInfeasible
                    continue
                if up > hi:
                    d.triedAlt = true
                    stack.add d
                    s.setBounds(x, lo, dn)
                elif dn < lo:
                    d.triedAlt = true
                    stack.add d
                    s.setBounds(x, up, hi)
                else:
                    stack.add d
                    s.setBounds(x, up, hi)
                inc nodes
                st = s.solve(maxIter = 4 * (m + n), deadline = lpDeadline)
                continue
            let v = s.value(best)
            let fl = floor(v)
            let lo = s.lb[best]
            let hi = s.ub[best]
            # x <= floor(v) or x >= floor(v) + 1, the nearer side first
            var d = Decision(col: best, oldLo: lo, oldHi: hi)
            if v - fl >= 0.5:
                d.altLo = lo; d.altHi = fl
                s.setBounds(best, fl + 1, hi)
            else:
                d.altLo = fl + 1; d.altHi = hi
                s.setBounds(best, lo, fl)
            stack.add d
        else:
            # Backtrack to the deepest decision with an untried side
            while stack.len > 0 and stack[^1].triedAlt:
                let d = stack.pop()
                s.setBounds(d.col, d.oldLo, d.oldHi)
            if stack.len == 0: break
            inc backtracks
            stack[^1].triedAlt = true
            s.setBounds(stack[^1].col, stack[^1].altLo, stack[^1].altHi)
        inc nodes
        st = s.solve(maxIter = 4 * (m + n), deadline = lpDeadline)
        if st == lpInfeasible and s.iterations - pivotsAtRefresh > 1000:
            # The dense tableau accumulates pivot error over a long dive and
            # starts reporting false infeasibility: re-solve this node from
            # the slack basis (same bounds) and continue from the fresh one.
            var fresh = initSolver(b.model)
            for j in 0..<n: fresh.setBounds(j, s.lb[j], s.ub[j])
            totalPivots += s.iterations
            st = fresh.solve(deadline = lpDeadline)
            s = fresh
            pivotsAtRefresh = 0
            inc refreshes
        if st == lpIterLimit: inc nIterLimit
        elif st == lpInfeasible: inc nInfeasible
    if verbose or diveOk:
        stderr.writeLine(&"[LP] {m} rows x {n} cols: relaxation {rootObj:.1f}, dive " &
                         (if diveOk: "integral" else: "failed") &
                         &" ({nodes} nodes, {backtracks} backtracks, depth {stack.len}, " &
                         &"{nInfeasible} infeasible, {nIterLimit} iteration-limited, " &
                         &"{refreshes} refreshes, {totalPivots + s.iterations} pivots, {epochTime() - t0:.2f}s)")
    # On a failed dive the last feasible LP point, rounded, still carries the
    # relaxation's structure; the search repairs the rest.
    # Position assignment: dive values snapped into each position's domain
    result = plan.defaults
    for j in 0..<n:
        let p = plan.colPos[j]
        if p < 0: continue
        let d {.cursor.} = plan.colDom[j]
        let v = int(round(if diveOk: s.value(j) else: lastFeasible[j]))
        var bestV = d[0]
        for x in d:
            if abs(x - v) < abs(bestV - v): bestV = x
        result[p] = bestV

proc lpDiveFallback*(tr: var FznTranslator, verbose: bool): proc(budget: float): seq[int] {.closure.} =
    ## The LP dive as a one-shot seed source for an initial search that found
    ## nothing (nil when the model has no usable LP relaxation).
    var plan: LpDivePlan
    let t0 = epochTime()
    if not tr.prepareLpDive(plan, verbose): return nil
    if verbose:
        stderr.writeLine(&"[LP] fallback ready: {plan.b.model.rows.len} rows x {plan.b.model.n} cols ({epochTime() - t0:.2f}s)")
    result = proc(budget: float): seq[int] =
        stderr.writeLine(&"[LP] initial search found nothing; diving ({budget:.1f}s budget)")
        runLpDive(plan, budget, verbose)
