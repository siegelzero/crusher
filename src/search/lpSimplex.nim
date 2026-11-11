## Dense bounded dual simplex for small LP relaxations (MIP-style diving).
##
## Problem: minimize c·x subject to rows  lo_i <= a_i·x <= hi_i  (lo or hi may
## be ±Inf, lo == hi for equalities) and bounds  l_j <= x_j <= u_j, all finite.
##
## Every row gets a slack s_i = a_i·x with bounds [lo_i, hi_i], so the
## constraint matrix is [A | -I] x' = 0 and the slack basis is an identity.
## With every structural variable boxed, putting each nonbasic variable at the
## bound its cost prefers (lower if c_j >= 0, upper otherwise) makes the slack
## basis dual feasible, so the dual simplex needs no phase 1. Bound changes
## (fixing a variable during a dive) keep dual feasibility: re-solving is a
## warm start of a few dual pivots.
##
## The tableau is dense (m x (n + m) floats); intended for models with up to a
## few thousand rows and columns.

import std/[math, times]

const
    LpInf* = 1e30
    LpEps = 1e-9       # pivot / ratio tolerance
    LpFeasTol* = 1e-7  # primal feasibility tolerance

type
    LpStatus* = enum lpOptimal, lpInfeasible, lpIterLimit

    LpRow* = object
        idx*: seq[int]
        val*: seq[float]
        lo*, hi*: float

    LpModel* = object
        n*: int                     ## structural variables
        lb*, ub*: seq[float]
        cost*: seq[float]
        rows*: seq[LpRow]

    LpSolver* = object
        m, n, w: int                ## rows, structural columns, total columns
        t: seq[float]               ## tableau, row-major m x w
        d: seq[float]               ## reduced costs (w)
        cost: seq[float]            ## full cost vector (w)
        lb*, ub*: seq[float]        ## bounds of all w columns
        x*: seq[float]              ## values of all w columns
        basis: seq[int]             ## basic column of each row
        posOf: seq[int]             ## row of a basic column, -1 if nonbasic
        atUpper: seq[bool]          ## nonbasic at its upper bound
        a: seq[seq[(int, float)]]   ## original rows (for recomputing values)
        iterations*: int

proc addRow*(m: var LpModel, idx: seq[int], val: seq[float], lo, hi: float) =
    m.rows.add LpRow(idx: idx, val: val, lo: lo, hi: hi)

template T(s: LpSolver, r, c: int): float = s.t[r * s.w + c]

proc recomputeBasics(s: var LpSolver) =
    ## x_B from the nonbasic values: slack s_i - a_i·x = 0 per row, i.e.
    ## B x_B = -N x_N, and the slack columns of the tableau hold B^-1 (times -1
    ## convention below).
    # Residual of each original row with basic variables zeroed
    var r = newSeq[float](s.m)
    for i in 0..<s.m:
        var acc = 0.0
        for (j, v) in s.a[i]:
            if s.posOf[j] < 0: acc += v * s.x[j]
        let sl = s.n + i
        if s.posOf[sl] < 0: acc -= s.x[sl]
        r[i] = acc
    # Row equations: sum_j a_ij x_j - s_i = 0  ->  B x_B = -r. The tableau's
    # slack block is B^-1 * (-I) = -B^-1, so x_B = -B^-1 r = T_slack * r.
    for k in 0..<s.m:
        var acc = 0.0
        for i in 0..<s.m:
            acc += s.T(k, s.n + i) * r[i]
        s.x[s.basis[k]] = acc

proc initSolver*(model: LpModel): LpSolver =
    let m = model.rows.len
    let n = model.n
    result.m = m
    result.n = n
    result.w = n + m
    result.t = newSeq[float](m * (n + m))
    result.cost = newSeq[float](n + m)
    result.lb = newSeq[float](n + m)
    result.ub = newSeq[float](n + m)
    result.x = newSeq[float](n + m)
    result.basis = newSeq[int](m)
    result.posOf = newSeq[int](n + m)
    result.atUpper = newSeq[bool](n + m)
    result.a = newSeq[seq[(int, float)]](m)
    for j in 0..<n:
        result.cost[j] = model.cost[j]
        result.lb[j] = model.lb[j]
        result.ub[j] = model.ub[j]
        result.posOf[j] = -1
        result.atUpper[j] = model.cost[j] < 0
        result.x[j] = if result.atUpper[j]: model.ub[j] else: model.lb[j]
    # Row i: a_i·x - s_i = 0 with s_i basic. Tableau row (B = -I):
    # x_B + B^-1 N x_N = 0 -> row = -(a_i, -e_i) = (-a_i, e_i)
    for i in 0..<m:
        let row = model.rows[i]
        for k, j in row.idx:
            result.t[i * result.w + j] -= row.val[k]
            result.a[i].add((j, row.val[k]))
        result.t[i * result.w + n + i] = 1.0
        let sl = n + i
        result.lb[sl] = row.lo
        result.ub[sl] = row.hi
        result.basis[i] = sl
        result.posOf[sl] = i
    # Reduced costs: slack basis has zero cost, so d = c
    result.d = result.cost
    result.recomputeBasics()

proc pivot(s: var LpSolver, r, q: int) =
    let w = s.w
    let piv = s.T(r, q)
    let inv = 1.0 / piv
    let base = r * w
    # Nonzeros of the (normalized) pivot row: the row updates only touch these
    var nz = newSeqOfCap[int](64)
    for c in 0..<w:
        let v = s.t[base + c]
        if v != 0.0:
            if abs(v) < 1e-14: s.t[base + c] = 0.0
            else:
                s.t[base + c] = v * inv
                nz.add c
    s.t[base + q] = 1.0
    for i in 0..<s.m:
        if i == r: continue
        let bi = i * w
        let f = s.t[bi + q]
        if f == 0.0: continue
        for c in nz:
            s.t[bi + c] -= f * s.t[base + c]
        s.t[bi + q] = 0.0
    let fd = s.d[q]
    if fd != 0.0:
        for c in nz:
            s.d[c] -= fd * s.t[base + c]
        s.d[q] = 0.0
    let leaving = s.basis[r]
    s.posOf[leaving] = -1
    s.basis[r] = q
    s.posOf[q] = r

proc solve*(s: var LpSolver, maxIter = 100_000, deadline = 0.0): LpStatus =
    ## Dual simplex from the current (dual feasible) basis. Stops with
    ## lpIterLimit after maxIter pivots or past deadline (epochTime, 0 = none).
    # Basic values drift through warm starts (bound changes, few pivots per
    # dive node): recompute them from the nonbasic values first, or the drift
    # turns into false infeasibility deep in a dive.
    s.recomputeBasics()
    var it = 0
    while true:
        # Leaving row: largest primal infeasibility
        var r = -1
        var worst = LpFeasTol
        for i in 0..<s.m:
            let p = s.basis[i]
            let v = s.x[p]
            let viol = if v < s.lb[p]: s.lb[p] - v
                       elif v > s.ub[p]: v - s.ub[p]
                       else: 0.0
            if viol > worst:
                worst = viol; r = i
        if r < 0: return lpOptimal
        if it >= maxIter: return lpIterLimit
        if deadline > 0 and (it and 63) == 0 and epochTime() > deadline: return lpIterLimit
        inc it
        inc s.iterations
        let p = s.basis[r]
        let below = s.x[p] < s.lb[p]
        let target = if below: s.lb[p] else: s.ub[p]
        # Row r: x_p + sum_j T[r][j] x_j = const. Raising x_p (below) needs
        # nonbasic j moving inside its box with -T[r][j] * dx_j > 0.
        var q = -1
        var best = Inf
        var bestAbs = 0.0
        for j in 0..<s.w:
            if s.posOf[j] >= 0: continue
            if s.ub[j] - s.lb[j] <= LpEps: continue   # fixed
            let a = s.T(r, j)
            if abs(a) <= LpEps: continue
            let up = not s.atUpper[j]               # can increase
            let ok = if below: (up and a < 0) or ((not up) and a > 0)
                     else: (up and a > 0) or ((not up) and a < 0)
            if not ok: continue
            let ratio = abs(s.d[j]) / abs(a)
            if ratio < best - 1e-12 or (ratio <= best + 1e-12 and abs(a) > bestAbs):
                best = ratio; q = j; bestAbs = abs(a)
        if q < 0: return lpInfeasible
        # Primal step: x_p -> target via x_q
        let a = s.T(r, q)
        let delta = target - s.x[p]          # change of x_p
        let dq = -delta / a                  # change of x_q
        for i in 0..<s.m:
            let f = s.T(i, q)
            if f != 0.0: s.x[s.basis[i]] -= f * dq
        s.x[q] += dq
        s.x[p] = target
        s.atUpper[p] = not below
        s.pivot(r, q)
        if (it and 255) == 0: s.recomputeBasics()

proc setBounds*(s: var LpSolver, j: int, lo, hi: float) =
    ## Changes the bounds of structural column j (keeps dual feasibility).
    s.lb[j] = lo
    s.ub[j] = hi
    if s.posOf[j] < 0:
        # Nonbasic: move it to the bound its reduced cost prefers
        let up = if hi - lo <= LpEps: false else: s.d[j] < 0
        s.atUpper[j] = up
        let nv = if up: hi else: lo
        let dx = nv - s.x[j]
        if dx != 0.0:
            for i in 0..<s.m:
                let f = s.T(i, j)
                if f != 0.0: s.x[s.basis[i]] -= f * dx
            s.x[j] = nv

proc objective*(s: LpSolver): float =
    for j in 0..<s.n: result += s.cost[j] * s.x[j]

proc value*(s: LpSolver, j: int): float = s.x[j]

type
    LpSnapshot* = object
        t, d, lb, ub, x: seq[float]
        basis, posOf: seq[int]
        atUpper: seq[bool]

proc snapshot*(s: LpSolver): LpSnapshot =
    LpSnapshot(t: s.t, d: s.d, lb: s.lb, ub: s.ub, x: s.x, basis: s.basis,
               posOf: s.posOf, atUpper: s.atUpper)

proc restore*(s: var LpSolver, snap: LpSnapshot) =
    s.t = snap.t; s.d = snap.d; s.lb = snap.lb; s.ub = snap.ub; s.x = snap.x
    s.basis = snap.basis; s.posOf = snap.posOf; s.atUpper = snap.atUpper
