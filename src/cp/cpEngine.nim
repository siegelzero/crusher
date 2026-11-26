## A small propagation engine with depth-first search (constraint
## programming), for models local search cannot make feasible: kitchen
## b1 / real_b1 (Gecode's annotation DFS: 2 s / 0.6 s; tabu: no solution in
## 1200 s) and nonogram medium_05 (line propagation + input-order DFS).
##
## Integer variables keep bounds plus, for ranges up to BitsetMaxRange, a
## bitset of the remaining values; wider domains are intervals (interior
## removals are ignored, which only weakens propagation). Changes are
## trailed once per variable / bitset word and search level. Propagators
## wake on any change of a variable they watch; every propagator also fails
## once all its variables are fixed and the constraint is violated, so a
## solution satisfies every constraint whatever the strength of the
## individual propagators; a found solution is checked against every
## constraint once more (check), and rejected when one fails.
##
## Search: binary branching (x = v | x != v, or x <= m | x > m) over branch
## groups in order (the solve annotation's int_search / bool_search lists,
## then every other variable), each with its own variable and value choice.

import std/[times, bitops, algorithm]

const BitsetMaxRange* = 65536
const CpUnboundedLimit* = 1 shl 31   # bound for variables declared without one

type
    CpVarSel* = enum
        vsInputOrder, vsFirstFail, vsAntiFirstFail, vsSmallest, vsLargest
    CpValSel* = enum
        valMin, valMax, valSplit, valReverseSplit
    CpStatus* = enum
        cpSat, cpUnsat, cpLimit

    CpVar = object
        lo, hi, size: int
        base: int        # bitset: value of bit 0
        w0: int          # bitset: first word in CpSolver.words; -1 = interval

    TrailKind = enum tkVar, tkWord, tkCell
    TrailEntry = object
        kind: TrailKind
        i: int           # var id, word index or cell index
        a, b, c: int     # lo, hi, size, or the old word / cell value (a)

    Prop* = ref object of RootObj
        id: int
        heavy: bool
        vs: seq[int]     # watched variables (also checked when all fixed)

    BranchGroup = object
        vars: seq[int]
        varSel: CpVarSel
        valSel: CpValSel

    DecisionKind = enum dkEq, dkLe, dkGe
    Decision = object
        v, val: int
        kind: DecisionKind

    CpSolver* = ref object
        vars: seq[CpVar]
        words: seq[uint64]
        trail: seq[TrailEntry]
        trailLim: seq[int]
        levelIds: seq[int]
        curLevel, levelCounter: int
        varStamp, wordStamp: seq[int]
        cells: seq[int]               # trailed propagator state (newCells / setCell)
        cellStamp: seq[int]
        props: seq[Prop]
        watch: seq[seq[int32]]
        qLight, qHeavy: seq[int32]
        qlHead, qhHead: int
        inQueue: seq[bool]
        consts: seq[(int, int)]       # (value, var) of constant variables
        groups: seq[BranchGroup]
        buf, buf2: seq[int]           # propagator scratch (propagators never nest)
        grouped: seq[bool]
        nodes*, fails*: int
        maxDepth*: int
        stalled*: bool         # last solve gave up on a depth stall
        wdegAll: bool          # branch on dom/wdeg over all variables (refute)
        weight: seq[int]       # per propagator: 1 + its failures (dom/wdeg)

# ---------------------------------------------------------------- variables

proc newCpSolver*(): CpSolver = CpSolver()

proc numVars*(s: CpSolver): int = s.vars.len

proc addVarRaw(s: CpSolver, x: CpVar): int =
    result = s.vars.len
    s.vars.add x
    s.varStamp.add -1
    s.watch.add @[]
    s.grouped.add false

proc newVar*(s: CpSolver, lo, hi: int): int =
    ## Variable over lo..hi (empty when hi < lo: the model is infeasible).
    var x = CpVar(lo: lo, hi: hi, size: max(0, hi - lo + 1), base: lo, w0: -1)
    if hi >= lo and hi - lo + 1 <= BitsetMaxRange and hi > lo:
        x.w0 = s.words.len
        let n = hi - lo + 1
        let nw = (n + 63) div 64
        for k in 0 ..< nw:
            let bitsHere = min(64, n - 64 * k)
            s.words.add(if bitsHere == 64: not 0'u64 else: (1'u64 shl bitsHere) - 1)
            s.wordStamp.add -1
    s.addVarRaw(x)

proc newVarValues*(s: CpSolver, values: seq[int]): int =
    ## Variable over a set of values; -1 when the set has holes over a range
    ## too wide for a bitset.
    if values.len == 0: return s.newVar(1, 0)
    var sorted = values
    sorted.sort()
    var vals: seq[int]
    for v in sorted:
        if vals.len == 0 or vals[^1] != v: vals.add v
    let lo = vals[0]
    let hi = vals[^1]
    if hi - lo + 1 == vals.len: return s.newVar(lo, hi)
    if hi - lo + 1 > BitsetMaxRange: return -1
    result = s.newVar(lo, hi)
    var x = s.vars[result]
    for k in 0 ..< (hi - lo + 64) div 64: s.words[x.w0 + k] = 0
    var size = 0
    for v in vals:
        let idx = v - lo
        s.words[x.w0 + idx shr 6] = s.words[x.w0 + idx shr 6] or (1'u64 shl (idx and 63))
        inc size
    x.size = size
    s.vars[result] = x

proc constVar*(s: CpSolver, v: int): int =
    for (c, id) in s.consts:
        if c == v: return id
    result = s.newVar(v, v)
    s.consts.add (v, result)

proc lo*(s: CpSolver, v: int): int {.inline.} = s.vars[v].lo
proc hi*(s: CpSolver, v: int): int {.inline.} = s.vars[v].hi
proc size*(s: CpSolver, v: int): int {.inline.} = s.vars[v].size
proc isFixed*(s: CpSolver, v: int): bool {.inline.} = s.vars[v].size == 1
proc value*(s: CpSolver, v: int): int {.inline.} = s.vars[v].lo

proc hasBit(s: CpSolver, x: CpVar, val: int): bool {.inline.} =
    let idx = val - x.base
    (s.words[x.w0 + idx shr 6] and (1'u64 shl (idx and 63))) != 0

proc contains*(s: CpSolver, v, val: int): bool =
    let x = s.vars[v]
    if val < x.lo or val > x.hi: return false
    x.w0 < 0 or s.hasBit(x, val)

proc nextSet(s: CpSolver, x: CpVar, fromVal: int): int =
    ## Smallest value >= fromVal in the bitset (x.hi + 1 when none up to hi).
    var idx = fromVal - x.base
    let last = x.hi - x.base
    while idx <= last:
        let wi = idx shr 6
        let w = s.words[x.w0 + wi] shr (idx and 63)
        if w != 0: return x.base + idx + countTrailingZeroBits(w)
        idx = (wi + 1) shl 6
    x.hi + 1

proc prevSet(s: CpSolver, x: CpVar, fromVal: int): int =
    ## Largest value <= fromVal in the bitset (x.lo - 1 when none down to lo).
    var idx = fromVal - x.base
    let first = x.lo - x.base
    while idx >= first:
        let wi = idx shr 6
        let sh = 63 - (idx and 63)
        let w = s.words[x.w0 + wi] shl sh
        if w != 0: return x.base + idx - countLeadingZeroBits(w)
        idx = (wi shl 6) - 1
    x.lo - 1

iterator values*(s: CpSolver, v: int): int =
    let x = s.vars[v]
    if x.w0 < 0:
        for k in x.lo .. x.hi: yield k
    else:
        var k = x.lo
        while k <= x.hi:
            yield k
            if k == x.hi: break
            k = s.nextSet(s.vars[v], k + 1)

# -------------------------------------------------------------------- trail

proc saveVar(s: CpSolver, v: int) {.inline.} =
    if s.trailLim.len > 0 and s.varStamp[v] != s.curLevel:
        s.varStamp[v] = s.curLevel
        let x = s.vars[v]
        s.trail.add TrailEntry(kind: tkVar, i: v, a: x.lo, b: x.hi, c: x.size)

proc saveWord(s: CpSolver, w: int) {.inline.} =
    if s.trailLim.len > 0 and s.wordStamp[w] != s.curLevel:
        s.wordStamp[w] = s.curLevel
        s.trail.add TrailEntry(kind: tkWord, i: w, a: cast[int](s.words[w]))

proc newCells(s: CpSolver, n, init: int): int =
    ## n trailed integers for a propagator's state; returns the first index.
    result = s.cells.len
    for _ in 0 ..< n:
        s.cells.add init
        s.cellStamp.add -1

proc setCell(s: CpSolver, i, v: int) {.inline.} =
    if s.trailLim.len > 0 and s.cellStamp[i] != s.curLevel:
        s.cellStamp[i] = s.curLevel
        s.trail.add TrailEntry(kind: tkCell, i: i, a: s.cells[i])
    s.cells[i] = v

proc pushLevel(s: CpSolver) =
    s.trailLim.add s.trail.len
    s.levelIds.add s.curLevel
    inc s.levelCounter
    s.curLevel = s.levelCounter

proc popLevel(s: CpSolver) =
    let lim = s.trailLim.pop()
    var k = s.trail.len - 1
    while k >= lim:
        let e = s.trail[k]
        case e.kind
        of tkWord: s.words[e.i] = cast[uint64](e.a)
        of tkCell: s.cells[e.i] = e.a
        of tkVar:
            s.vars[e.i].lo = e.a
            s.vars[e.i].hi = e.b
            s.vars[e.i].size = e.c
        dec k
    s.trail.setLen lim
    s.curLevel = s.levelIds.pop()

# ------------------------------------------------------------ domain events

proc enqueue(s: CpSolver, p: int) {.inline.} =
    if not s.inQueue[p]:
        s.inQueue[p] = true
        if s.props[p].heavy: s.qHeavy.add int32(p) else: s.qLight.add int32(p)

proc changed(s: CpSolver, v: int) {.inline.} =
    for p in s.watch[v]: s.enqueue(p)

proc clearRange(s: CpSolver, v, a, b: int): int =
    ## Clears bitset values a..b (within the current bounds); returns how many
    ## were set.
    let x = s.vars[v]
    var idx = a - x.base
    let last = b - x.base
    while idx <= last:
        let wi = idx shr 6
        let lowBit = idx and 63
        let highBit = min(63, last - (wi shl 6))
        let width = highBit - lowBit + 1
        let mask = (if width == 64: not 0'u64 else: ((1'u64 shl width) - 1) shl lowBit)
        let w = s.words[x.w0 + wi]
        if (w and mask) != 0:
            s.saveWord(x.w0 + wi)
            result += popcount(w and mask)
            s.words[x.w0 + wi] = w and not mask
        idx = (wi + 1) shl 6

proc setMin*(s: CpSolver, v, m: int): bool =
    let x = s.vars[v]
    if m <= x.lo: return true
    if m > x.hi: return false
    s.saveVar(v)
    if x.w0 < 0:
        s.vars[v].lo = m
        s.vars[v].size = x.hi - m + 1
    else:
        let cleared = s.clearRange(v, x.lo, m - 1)
        s.vars[v].size = x.size - cleared
        if s.vars[v].size <= 0: return false
        s.vars[v].lo = s.nextSet(s.vars[v], m)
    s.changed(v)
    true

proc setMax*(s: CpSolver, v, m: int): bool =
    let x = s.vars[v]
    if m >= x.hi: return true
    if m < x.lo: return false
    s.saveVar(v)
    if x.w0 < 0:
        s.vars[v].hi = m
        s.vars[v].size = m - x.lo + 1
    else:
        let cleared = s.clearRange(v, m + 1, x.hi)
        s.vars[v].size = x.size - cleared
        if s.vars[v].size <= 0: return false
        s.vars[v].hi = s.prevSet(s.vars[v], m)
    s.changed(v)
    true

proc assign*(s: CpSolver, v, val: int): bool =
    if not s.contains(v, val): return false
    s.setMin(v, val) and s.setMax(v, val)

proc remove*(s: CpSolver, v, val: int): bool =
    let x = s.vars[v]
    if val < x.lo or val > x.hi: return true
    if val == x.lo: return s.setMin(v, val + 1)
    if val == x.hi: return s.setMax(v, val - 1)
    if x.w0 < 0 or not s.hasBit(x, val): return true   # interior of an interval: ignored
    s.saveVar(v)
    let idx = val - x.base
    s.saveWord(x.w0 + idx shr 6)
    s.words[x.w0 + idx shr 6] = s.words[x.w0 + idx shr 6] and not (1'u64 shl (idx and 63))
    s.vars[v].size = x.size - 1
    s.changed(v)
    true

# ------------------------------------------------------------- propagators

method propagate*(p: Prop, s: CpSolver): bool {.base.} = true
method check*(p: Prop, s: CpSolver): bool {.base.} = true
    ## The constraint holds (all of p.vs fixed).

proc addProp*(s: CpSolver, p: Prop) =
    p.id = s.props.len
    s.props.add p
    s.weight.add 1
    s.inQueue.add false
    var seen: seq[int]
    for v in p.vs:
        if v in seen: continue
        seen.add v
        s.watch[v].add int32(p.id)

proc clearQueues(s: CpSolver) =
    for p in s.qLight: s.inQueue[p] = false
    for p in s.qHeavy: s.inQueue[p] = false
    s.qLight.setLen 0
    s.qHeavy.setLen 0
    s.qlHead = 0
    s.qhHead = 0

proc propagateAll(s: CpSolver): bool =
    while true:
        var p: int
        if s.qlHead < s.qLight.len:
            p = s.qLight[s.qlHead]; inc s.qlHead
        elif s.qhHead < s.qHeavy.len:
            p = s.qHeavy[s.qhHead]; inc s.qhHead
        else:
            break
        s.inQueue[p] = false
        if not s.props[p].propagate(s):
            s.clearQueues()
            inc s.fails
            inc s.weight[p]
            return false
    s.qLight.setLen 0; s.qHeavy.setLen 0
    s.qlHead = 0; s.qhHead = 0
    true

proc floorDiv(n, d: int): int =
    ## floor(n / d), any signs (d != 0)
    var q = n div d
    if (n mod d != 0) and ((n < 0) != (d < 0)): dec q
    q

proc ceilDiv(n, d: int): int = -floorDiv(-n, d)

# Linear: sum a_i x_i (<= | = | !=) c, optionally (half-)reified by r

type
    CpLinRel* = enum lrLe, lrEq, lrNe
    LinProp = ref object of Prop
        a, x: seq[int]
        c: int
        rel: CpLinRel
        r: int
        imp: bool

proc linBounds(s: CpSolver, a, x: seq[int]): (int, int) =
    var mn, mx = 0
    for i in 0 ..< a.len:
        let k = a[i]
        if k >= 0:
            mn += k * s.vars[x[i]].lo; mx += k * s.vars[x[i]].hi
        else:
            mn += k * s.vars[x[i]].hi; mx += k * s.vars[x[i]].lo
    (mn, mx)

proc propLe(s: CpSolver, a, x: seq[int], c: int, neg: bool): bool =
    ## sum a_i x_i <= c (neg: sum -a_i x_i <= c)
    var mn = 0
    for i in 0 ..< a.len:
        let k = if neg: -a[i] else: a[i]
        mn += (if k >= 0: k * s.vars[x[i]].lo else: k * s.vars[x[i]].hi)
    if mn > c: return false
    let slack = c - mn
    for i in 0 ..< a.len:
        let k = if neg: -a[i] else: a[i]
        if k > 0:
            let xv = x[i]
            if s.vars[xv].hi - s.vars[xv].lo > slack div k:
                if not s.setMax(xv, s.vars[xv].lo + slack div k): return false
        elif k < 0:
            let xv = x[i]
            if s.vars[xv].hi - s.vars[xv].lo > slack div (-k):
                if not s.setMin(xv, s.vars[xv].hi - slack div (-k)): return false
    true

proc eqState(s: CpSolver, a, x: seq[int], c: int): int =
    ## 1 entailed, -1 disentailed, 0 unknown (for sum = c)
    let (mn, mx) = s.linBounds(a, x)
    if mn > c or mx < c: return -1
    if mn == mx: return 1
    var unfixed = -1
    var rest = 0
    for i in 0 ..< a.len:
        if s.vars[x[i]].size == 1: rest += a[i] * s.vars[x[i]].lo
        elif unfixed >= 0: return 0
        else: unfixed = i
    if unfixed >= 0:
        let need = c - rest
        if need mod a[unfixed] != 0 or not s.contains(x[unfixed], need div a[unfixed]): return -1
    0

proc propNe(s: CpSolver, a, x: seq[int], c: int): bool =
    var unfixed = -1
    var rest = 0
    for i in 0 ..< a.len:
        if s.vars[x[i]].size == 1: rest += a[i] * s.vars[x[i]].lo
        elif unfixed >= 0: return true
        else: unfixed = i
    if unfixed < 0: return rest != c
    let need = c - rest
    if need mod a[unfixed] != 0: return true
    s.remove(x[unfixed], need div a[unfixed])

proc enforce(s: CpSolver, p: LinProp, rel: CpLinRel, positive: bool): bool =
    case rel
    of lrLe:
        if positive: s.propLe(p.a, p.x, p.c, false)
        else: s.propLe(p.a, p.x, -p.c - 1, true)        # sum >= c + 1
    of lrEq:
        if positive: s.propLe(p.a, p.x, p.c, false) and s.propLe(p.a, p.x, -p.c, true)
        else: s.propNe(p.a, p.x, p.c)
    of lrNe:
        if positive: s.propNe(p.a, p.x, p.c)
        else: s.propLe(p.a, p.x, p.c, false) and s.propLe(p.a, p.x, -p.c, true)

method propagate(p: LinProp, s: CpSolver): bool =
    if p.r < 0: return s.enforce(p, p.rel, true)
    let rv = s.vars[p.r]
    if rv.size == 1:
        if rv.lo == 1: return s.enforce(p, p.rel, true)
        if p.imp: return true
        return s.enforce(p, p.rel, false)
    # r unknown: decide it from entailment
    var st: int
    case p.rel
    of lrLe:
        let (mn, mx) = s.linBounds(p.a, p.x)
        st = (if mx <= p.c: 1 elif mn > p.c: -1 else: 0)
    of lrEq: st = s.eqState(p.a, p.x, p.c)
    of lrNe: st = -s.eqState(p.a, p.x, p.c)
    if st < 0: return s.assign(p.r, 0)
    if st > 0 and not p.imp: return s.assign(p.r, 1)
    true

method check(p: LinProp, s: CpSolver): bool =
    var sum = 0
    for i in 0 ..< p.a.len: sum += p.a[i] * s.vars[p.x[i]].lo
    let holds = case p.rel
        of lrLe: sum <= p.c
        of lrEq: sum == p.c
        of lrNe: sum != p.c
    if p.r < 0: return holds
    let r = s.vars[p.r].lo
    if p.imp: r == 0 or holds else: (r == 1) == holds

proc addLinear*(s: CpSolver, a, x: seq[int], c: int, rel: CpLinRel, r = -1, imp = false) =
    var p = LinProp(c: c, rel: rel, r: r, imp: imp)
    for i in 0 ..< a.len:
        if a[i] != 0:
            p.a.add a[i]
            p.x.add x[i]
    p.vs = p.x
    if r >= 0: p.vs.add r
    # Long sums (an objective definition over thousands of terms) recompute
    # their bounds in O(n): run them once the cheap propagators settle
    p.heavy = p.x.len > 32
    s.addProp(p)

# Or: r <-> OR(lits) (r = -1: the clause itself); literal i is true when
# var lv[i] = 1 (lp[i]) or = 0 (not lp[i])

type OrProp = ref object of Prop
    lv: seq[int]
    lp: seq[bool]
    r: int
    rp: bool

proc setLit(s: CpSolver, v: int, pol, truth: bool): bool {.inline.} =
    s.assign(v, (if pol == truth: 1 else: 0))

method propagate(p: OrProp, s: CpSolver): bool =
    var rState = 1   # 1 true, 0 false, -1 unknown
    if p.r >= 0:
        let rv = s.vars[p.r]
        rState = (if rv.size != 1: -1 elif (rv.lo == 1) == p.rp: 1 else: 0)
    var unfixed = 0
    var last = -1
    for i in 0 ..< p.lv.len:
        let x = s.vars[p.lv[i]]
        if x.size == 1:
            if (x.lo == 1) == p.lp[i]:
                if rState == -1: return s.setLit(p.r, p.rp, true)
                if rState == 0: return false
                return true
        else:
            inc unfixed
            last = i
    if unfixed == 0:
        if rState == 1: return false
        if rState == -1: return s.setLit(p.r, p.rp, false)
        return true
    if rState == 1 and unfixed == 1: return s.setLit(p.lv[last], p.lp[last], true)
    if rState == 0:
        for i in 0 ..< p.lv.len:
            if not s.setLit(p.lv[i], p.lp[i], false): return false
    true

method check(p: OrProp, s: CpSolver): bool =
    var any = false
    for i in 0 ..< p.lv.len:
        if (s.vars[p.lv[i]].lo == 1) == p.lp[i]: any = true; break
    if p.r < 0: return any
    ((s.vars[p.r].lo == 1) == p.rp) == any

proc addOr*(s: CpSolver, lv: seq[int], lp: seq[bool], r = -1, rp = true) =
    var p = OrProp(lv: lv, lp: lp, r: r, rp: rp)
    p.vs = lv
    if r >= 0: p.vs.add r
    s.addProp(p)

# Boolean relation over <= 4 0/1 variables given by its allowed assignments
# (bit t of mask: assignment with x_i = (t shr i) and 1)

type BoolTableProp = ref object of Prop
    mask: uint32

method propagate(p: BoolTableProp, s: CpSolver): bool =
    let n = p.vs.len
    var sup: array[4, array[2, bool]]
    for t in 0 ..< (1 shl n):
        if (p.mask and (1'u32 shl t)) == 0: continue
        var ok = true
        for i in 0 ..< n:
            if not s.contains(p.vs[i], (t shr i) and 1): ok = false; break
        if ok:
            for i in 0 ..< n: sup[i][(t shr i) and 1] = true
    for i in 0 ..< n:
        for b in 0..1:
            if not sup[i][b] and not s.remove(p.vs[i], b): return false
    true

method check(p: BoolTableProp, s: CpSolver): bool =
    var t = 0
    for i in 0 ..< p.vs.len: t = t or (s.vars[p.vs[i]].lo shl i)
    (p.mask and (1'u32 shl t)) != 0

proc addBoolTable*(s: CpSolver, xs: seq[int], mask: uint32) =
    assert xs.len <= 4
    s.addProp(BoolTableProp(vs: xs, mask: mask))

# a * b = c (bounds)

type TimesProp = ref object of Prop

method propagate(p: TimesProp, s: CpSolver): bool =
    let a = p.vs[0]
    let b = p.vs[1]
    let c = p.vs[2]
    let pa = [s.lo(a) * s.lo(b), s.lo(a) * s.hi(b), s.hi(a) * s.lo(b), s.hi(a) * s.hi(b)]
    if not s.setMin(c, min(pa)) or not s.setMax(c, max(pa)): return false
    for (x, y) in [(a, b), (b, a)]:
        if s.isFixed(y):
            let k = s.value(y)
            if k == 0:
                if not s.assign(c, 0): return false
            elif k > 0:
                if not s.setMin(x, ceilDiv(s.lo(c), k)) or not s.setMax(x, floorDiv(s.hi(c), k)): return false
            else:
                if not s.setMin(x, ceilDiv(s.hi(c), k)) or not s.setMax(x, floorDiv(s.lo(c), k)): return false
    true

method check(p: TimesProp, s: CpSolver): bool =
    s.value(p.vs[0]) * s.value(p.vs[1]) == s.value(p.vs[2])

proc addTimes*(s: CpSolver, a, b, c: int) = s.addProp(TimesProp(vs: @[a, b, c]))

# r = arr[idx] (constant array, 1-based)

type ElemProp = ref object of Prop
    arr: seq[int]

method propagate(p: ElemProp, s: CpSolver): bool =
    let idx = p.vs[0]
    let r = p.vs[1]
    if not s.setMin(idx, 1) or not s.setMax(idx, p.arr.len): return false
    s.buf.setLen 0
    s.buf2.setLen 0
    for i in s.values(idx):
        let v = p.arr[i - 1]
        if s.contains(r, v): s.buf2.add v
        else: s.buf.add i
    for i in s.buf:
        if not s.remove(idx, i): return false
    if s.buf2.len == 0: return false
    s.buf2.sort()
    if not s.setMin(r, s.buf2[0]) or not s.setMax(r, s.buf2[^1]): return false
    if s.vars[r].w0 >= 0 and s.size(r) > 2:
        s.buf.setLen 0
        for v in s.values(r):
            if s.buf2.binarySearch(v) < 0: s.buf.add v
        for v in s.buf:
            if not s.remove(r, v): return false
    true

method check(p: ElemProp, s: CpSolver): bool =
    let i = s.value(p.vs[0])
    i >= 1 and i <= p.arr.len and p.arr[i - 1] == s.value(p.vs[1])

proc addElement*(s: CpSolver, idx: int, arr: seq[int], r: int) =
    s.addProp(ElemProp(vs: @[idx, r], arr: arr))

# r = xs[idx] (variable array, 1-based; vs = idx, r, xs...)

type VarElemProp = ref object of Prop

method propagate(p: VarElemProp, s: CpSolver): bool =
    let idx = p.vs[0]
    let r = p.vs[1]
    let n = p.vs.len - 2
    if not s.setMin(idx, 1) or not s.setMax(idx, n): return false
    s.buf.setLen 0
    var mn = high(int)
    var mx = low(int)
    for i in s.values(idx):
        let x = p.vs[1 + i]
        if s.hi(x) < s.lo(r) or s.lo(x) > s.hi(r): s.buf.add i
        else:
            mn = min(mn, s.lo(x)); mx = max(mx, s.hi(x))
    for i in s.buf:
        if not s.remove(idx, i): return false
    if mn > mx: return false
    if not s.setMin(r, mn) or not s.setMax(r, mx): return false
    if s.isFixed(idx):
        let x = p.vs[1 + s.value(idx)]
        if not s.setMin(x, s.lo(r)) or not s.setMax(x, s.hi(r)): return false
        if not s.setMin(r, s.lo(x)) or not s.setMax(r, s.hi(x)): return false
    true

method check(p: VarElemProp, s: CpSolver): bool =
    let i = s.value(p.vs[0])
    i >= 1 and i <= p.vs.len - 2 and s.value(p.vs[1 + i]) == s.value(p.vs[1])

proc addVarElement*(s: CpSolver, idx: int, xs: seq[int], r: int) =
    s.addProp(VarElemProp(vs: @[idx, r] & xs))

# m = max(xs) / min(xs) (vs = m, xs...)

type MaxProp = ref object of Prop
    isMin: bool

method propagate(p: MaxProp, s: CpSolver): bool =
    let m = p.vs[0]
    let n = p.vs.len - 1
    if not p.isMin:
        var mxLo = low(int)
        var mxHi = low(int)
        for k in 1 .. n:
            mxLo = max(mxLo, s.lo(p.vs[k])); mxHi = max(mxHi, s.hi(p.vs[k]))
        if not s.setMin(m, mxLo) or not s.setMax(m, mxHi): return false
        var cand = -1
        var nCand = 0
        for k in 1 .. n:
            let x = p.vs[k]
            if not s.setMax(x, s.hi(m)): return false
            if s.hi(x) >= s.lo(m): (inc nCand; cand = x)
        if nCand == 0: return false
        if nCand == 1 and not s.setMin(cand, s.lo(m)): return false
    else:
        var mnLo = high(int)
        var mnHi = high(int)
        for k in 1 .. n:
            mnLo = min(mnLo, s.lo(p.vs[k])); mnHi = min(mnHi, s.hi(p.vs[k]))
        if not s.setMin(m, mnLo) or not s.setMax(m, mnHi): return false
        var cand = -1
        var nCand = 0
        for k in 1 .. n:
            let x = p.vs[k]
            if not s.setMin(x, s.lo(m)): return false
            if s.lo(x) <= s.hi(m): (inc nCand; cand = x)
        if nCand == 0: return false
        if nCand == 1 and not s.setMax(cand, s.hi(m)): return false
    true

method check(p: MaxProp, s: CpSolver): bool =
    var best = s.value(p.vs[1])
    for k in 2 ..< p.vs.len:
        best = (if p.isMin: min(best, s.value(p.vs[k])) else: max(best, s.value(p.vs[k])))
    best == s.value(p.vs[0])

proc addMax*(s: CpSolver, m: int, xs: seq[int], isMin = false) =
    s.addProp(MaxProp(vs: @[m] & xs, isMin: isMin))

# b = |a|

type AbsProp = ref object of Prop

method propagate(p: AbsProp, s: CpSolver): bool =
    let a = p.vs[0]
    let b = p.vs[1]
    if not s.setMin(b, 0): return false
    let bLo = (if s.lo(a) > 0: s.lo(a) elif s.hi(a) < 0: -s.hi(a) else: 0)
    if not s.setMin(b, bLo) or not s.setMax(b, max(abs(s.lo(a)), abs(s.hi(a)))): return false
    if not s.setMin(a, -s.hi(b)) or not s.setMax(a, s.hi(b)): return false
    if s.lo(a) >= 0:
        if not s.setMin(a, s.lo(b)): return false
    elif s.hi(a) <= 0:
        if not s.setMax(a, -s.lo(b)): return false
    true

method check(p: AbsProp, s: CpSolver): bool = abs(s.value(p.vs[0])) == s.value(p.vs[1])

proc addAbs*(s: CpSolver, a, b: int) = s.addProp(AbsProp(vs: @[a, b]))

# x in S (optionally (half-)reified by r)

type SetInProp = ref object of Prop
    vals: seq[int]      # sorted, unique
    r: int
    imp: bool

proc inSet(p: SetInProp, v: int): bool = p.vals.binarySearch(v) >= 0

method propagate(p: SetInProp, s: CpSolver): bool =
    let x = p.vs[0]
    var mode = 1    # 1 enforce x in S, 0 enforce x notin S, -1 decide r
    if p.r >= 0:
        if s.isFixed(p.r): mode = (if s.value(p.r) == 1: 1 elif p.imp: 2 else: 0)
        else: mode = -1
    if mode == 2: return true
    if mode == -1:
        if s.size(x) > 65536: return true
        var anyIn, anyOut = false
        for v in s.values(x):
            if p.inSet(v): anyIn = true else: anyOut = true
            if anyIn and anyOut: return true
        if not anyIn: return s.assign(p.r, 0)
        if not anyOut and not p.imp: return s.assign(p.r, 1)
        return true
    if mode == 1:
        if p.vals.len == 0: return false
        if not s.setMin(x, p.vals[0]) or not s.setMax(x, p.vals[^1]): return false
        if s.vars[x].w0 < 0:
            if s.isFixed(x) and not p.inSet(s.value(x)): return false
        else:
            s.buf.setLen 0
            for v in s.values(x):
                if not p.inSet(v): s.buf.add v
            for v in s.buf:
                if not s.remove(x, v): return false
    else:
        for v in p.vals:
            if not s.remove(x, v): return false
    true

method check(p: SetInProp, s: CpSolver): bool =
    let holds = p.inSet(s.value(p.vs[0]))
    if p.r < 0: return holds
    let r = s.value(p.r)
    if p.imp: r == 0 or holds else: (r == 1) == holds

proc addSetIn*(s: CpSolver, x: int, vals: seq[int], r = -1, imp = false) =
    var vs = vals
    vs.sort()
    var u: seq[int]
    for v in vs:
        if u.len == 0 or u[^1] != v: u.add v
    var p = SetInProp(vals: u, r: r, imp: imp)
    p.vs = @[x]
    if r >= 0: p.vs.add r
    s.addProp(p)

# regular(x, Q, S, d, q0, F): the DFA with states 1..Q (0 = dead), inputs
# 1..S and transitions d[(q-1)*S + (v-1)] accepts x. Domain-consistent:
# forward reachability over the layered graph, then backward support.

type RegularProp = ref object of Prop
    q, sy: int
    d: seq[int]
    q0: int
    final: seq[bool]
    fwd, bwd: seq[bool]     # (n + 1) x (Q + 1)

method propagate(p: RegularProp, s: CpSolver): bool =
    let n = p.vs.len
    let w = p.q + 1
    for k in 0 ..< p.fwd.len:
        p.fwd[k] = false
        p.bwd[k] = false
    p.fwd[p.q0] = true
    for i in 0 ..< n:
        let x = p.vs[i]
        var any = false
        for q in 1 .. p.q:
            if not p.fwd[i * w + q]: continue
            for v in s.values(x):
                if v < 1 or v > p.sy: continue
                let q2 = p.d[(q - 1) * p.sy + (v - 1)]
                if q2 > 0:
                    p.fwd[(i + 1) * w + q2] = true
                    any = true
        if not any: return false
    var anyFinal = false
    for q in 1 .. p.q:
        if p.fwd[n * w + q] and p.final[q]:
            p.bwd[n * w + q] = true
            anyFinal = true
    if not anyFinal: return false
    for i in countdown(n - 1, 0):
        let x = p.vs[i]
        s.buf.setLen 0
        for v in s.values(x):
            var supported = false
            if v >= 1 and v <= p.sy:
                for q in 1 .. p.q:
                    if not p.fwd[i * w + q]: continue
                    let q2 = p.d[(q - 1) * p.sy + (v - 1)]
                    if q2 > 0 and p.bwd[(i + 1) * w + q2]:
                        supported = true
                        p.bwd[i * w + q] = true
            if not supported: s.buf.add v
        for v in s.buf:
            if not s.remove(x, v): return false
    true

method check(p: RegularProp, s: CpSolver): bool =
    var q = p.q0
    for x in p.vs:
        let v = s.value(x)
        if v < 1 or v > p.sy: return false
        q = p.d[(q - 1) * p.sy + (v - 1)]
        if q == 0: return false
    p.final[q]

proc addRegular*(s: CpSolver, xs: seq[int], q, sy: int, d: seq[int], q0: int, final: seq[int]) =
    var p = RegularProp(vs: xs, heavy: true, q: q, sy: sy, d: d, q0: q0)
    p.final = newSeq[bool](q + 1)
    for f in final:
        if f >= 1 and f <= q: p.final[f] = true
    p.fwd = newSeq[bool]((xs.len + 1) * (q + 1))
    p.bwd = newSeq[bool]((xs.len + 1) * (q + 1))
    s.addProp(p)

# table(xs, tuples): (xs) is one of the tuples (row-major, arity xs.len).
# Domain-consistent by a scan of the tuples still valid.

type TableProp = ref object of Prop
    tuples: seq[int]
    sup: seq[seq[int]]      # scratch: supported values per column

method propagate(p: TableProp, s: CpSolver): bool =
    let k = p.vs.len
    for i in 0 ..< k: p.sup[i].setLen 0
    var any = false
    var t = 0
    while t < p.tuples.len:
        var ok = true
        for i in 0 ..< k:
            if not s.contains(p.vs[i], p.tuples[t + i]): ok = false; break
        if ok:
            any = true
            for i in 0 ..< k: p.sup[i].add p.tuples[t + i]
        t += k
    if not any: return false
    for i in 0 ..< k:
        let x = p.vs[i]
        p.sup[i].sort()
        if not s.setMin(x, p.sup[i][0]) or not s.setMax(x, p.sup[i][^1]): return false
        if s.vars[x].w0 >= 0 and s.size(x) > 2:
            s.buf.setLen 0
            for v in s.values(x):
                if p.sup[i].binarySearch(v) < 0: s.buf.add v
            for v in s.buf:
                if not s.remove(x, v): return false
    true

method check(p: TableProp, s: CpSolver): bool =
    let k = p.vs.len
    var t = 0
    while t < p.tuples.len:
        var ok = true
        for i in 0 ..< k:
            if s.value(p.vs[i]) != p.tuples[t + i]: ok = false; break
        if ok: return true
        t += k
    false

proc addTable*(s: CpSolver, xs: seq[int], tuples: seq[int]) =
    ## tuples.len must be a multiple of xs.len (> 0)
    assert xs.len > 0 and tuples.len mod xs.len == 0
    var p = TableProp(vs: xs, tuples: tuples, heavy: tuples.len > 256)
    p.sup = newSeq[seq[int]](xs.len)
    s.addProp(p)

# c = a div b, truncating toward zero (b != 0). Bounds: c from the corners of
# the box on each sign side of b; a from c once b is fixed.

type DivProp = ref object of Prop

proc divPreimage(q, k: int): (int, int) =
    ## The values a with a div k == q (k != 0), an interval.
    let m = abs(k)
    let qq = (if k > 0: q else: -q)     # a div m == qq
    if qq > 0: (qq * m, qq * m + m - 1)
    elif qq < 0: (qq * m - m + 1, qq * m)
    else: (-(m - 1), m - 1)

method propagate(p: DivProp, s: CpSolver): bool =
    let a = p.vs[0]
    let b = p.vs[1]
    let c = p.vs[2]
    if not s.remove(b, 0): return false
    var lo = high(int)
    var hi = low(int)
    for (bl, bh) in [(s.lo(b), min(s.hi(b), -1)), (max(s.lo(b), 1), s.hi(b))]:
        if bl > bh: continue
        for av in [s.lo(a), s.hi(a)]:
            for bv in [bl, bh]:
                let q = av div bv
                lo = min(lo, q)
                hi = max(hi, q)
    if lo > hi: return false
    if not s.setMin(c, lo) or not s.setMax(c, hi): return false
    if s.isFixed(b):
        let k = s.value(b)
        let (l1, h1) = divPreimage(s.lo(c), k)
        let (l2, h2) = divPreimage(s.hi(c), k)
        if not s.setMin(a, min(l1, l2)) or not s.setMax(a, max(h1, h2)): return false
    true

method check(p: DivProp, s: CpSolver): bool =
    let bv = s.value(p.vs[1])
    bv != 0 and s.value(p.vs[0]) div bv == s.value(p.vs[2])

proc addDiv*(s: CpSolver, a, b, c: int) = s.addProp(DivProp(vs: @[a, b, c]))

# global_cardinality(xs, cover, ...): the number of xs equal to cover[j] is
# within [lb[j], ub[j]] (constant bounds) or equals the variable counts[j]
# (vs = xs..., counts...); closed: every x takes a cover value. Counting:
# values fixed vs still possible per cover value; at the upper bound the value
# leaves the other domains, at the lower bound every candidate takes it.

type GccProp = ref object of Prop
    n: int                  # number of xs (counts follow in vs)
    cover: seq[int]
    lb, ub: seq[int]        # constant bounds (empty with count variables)
    closed: bool
    coverSorted: seq[int]
    cnt, poss: seq[int]     # scratch

proc coverIndex(p: GccProp, v: int): int =
    ## Index of v in cover, -1 when absent.
    for j, c in p.cover:
        if c == v: return j
    -1

method propagate(p: GccProp, s: CpSolver): bool =
    let m = p.cover.len
    let hasCounts = p.lb.len == 0
    if m == 0: return not p.closed or p.n == 0
    if p.closed:
        for i in 0 ..< p.n:
            let x = p.vs[i]
            if not s.setMin(x, p.coverSorted[0]) or not s.setMax(x, p.coverSorted[^1]): return false
            if s.vars[x].w0 >= 0 and s.size(x) > 1:
                s.buf.setLen 0
                for v in s.values(x):
                    if p.coverSorted.binarySearch(v) < 0: s.buf.add v
                for v in s.buf:
                    if not s.remove(x, v): return false
    for j in 0 ..< m:
        p.cnt[j] = 0
        p.poss[j] = 0
    for i in 0 ..< p.n:
        let x = p.vs[i]
        if s.isFixed(x):
            let j = p.coverIndex(s.value(x))
            if j >= 0: (inc p.cnt[j]; inc p.poss[j])
        elif s.vars[x].w0 >= 0 and s.size(x) <= m:
            for v in s.values(x):
                let j = p.coverIndex(v)
                if j >= 0: inc p.poss[j]
        else:
            for j in 0 ..< m:
                if s.contains(x, p.cover[j]): inc p.poss[j]
    var sumLo, sumHi = 0
    for j in 0 ..< m:
        var lo, hi: int
        if hasCounts:
            let cv = p.vs[p.n + j]
            if not s.setMin(cv, p.cnt[j]) or not s.setMax(cv, p.poss[j]): return false
            lo = s.lo(cv)
            hi = s.hi(cv)
        else:
            lo = p.lb[j]
            hi = p.ub[j]
        if p.cnt[j] > hi or p.poss[j] < lo: return false
        sumLo += max(lo, p.cnt[j])
        sumHi += min(hi, p.poss[j])
        let v = p.cover[j]
        if p.cnt[j] == hi and p.poss[j] > hi:
            for i in 0 ..< p.n:
                let x = p.vs[i]
                if not s.isFixed(x) and not s.remove(x, v): return false
        elif p.poss[j] == lo and p.poss[j] > p.cnt[j]:
            for i in 0 ..< p.n:
                let x = p.vs[i]
                if not s.isFixed(x) and s.contains(x, v) and not s.assign(x, v): return false
    if sumLo > p.n or (p.closed and sumHi < p.n): return false
    true

method check(p: GccProp, s: CpSolver): bool =
    let m = p.cover.len
    for j in 0 ..< m: p.cnt[j] = 0
    for i in 0 ..< p.n:
        let j = p.coverIndex(s.value(p.vs[i]))
        if j >= 0: inc p.cnt[j]
        elif p.closed: return false
    for j in 0 ..< m:
        if p.lb.len == 0:
            if s.value(p.vs[p.n + j]) != p.cnt[j]: return false
        elif p.cnt[j] < p.lb[j] or p.cnt[j] > p.ub[j]: return false
    true

proc addGcc*(s: CpSolver, xs: seq[int], cover: seq[int], lb, ub: seq[int],
             counts: seq[int] = @[], closed = false) =
    ## Either constant bounds (lb, ub) or count variables (counts, with lb and
    ## ub empty); cover values must be distinct.
    assert (counts.len == cover.len and lb.len == 0) or (lb.len == cover.len and ub.len == cover.len)
    var p = GccProp(vs: xs & counts, n: xs.len, cover: cover, lb: lb, ub: ub, closed: closed,
                    heavy: xs.len * cover.len > 256)
    p.coverSorted = cover
    p.coverSorted.sort()
    p.cnt = newSeq[int](cover.len)
    p.poss = newSeq[int](cover.len)
    s.addProp(p)

# diffn(x, y, dx, dy): every pair of rectangles i < j satisfies one of
# x_i + dx_i <= x_j, y_i + dy_i <= y_j, x_j + dx_j <= x_i, y_j + dy_j <= y_i
# (MiniZinc's strict fzn_diffn: zero-size rectangles may not lie inside
# others either). Pairwise on bounds: no disjunct possible fails, a single
# possible one is enforced.

type DiffnProp = ref object of Prop
    n: int

proc leOk(s: CpSolver, a, da, b: int): bool {.inline.} =
    ## a + da <= b is still possible
    s.lo(a) + s.lo(da) <= s.hi(b)

proc leSet(s: CpSolver, a, da, b: int): bool {.inline.} =
    ## enforce a + da <= b on bounds
    s.setMin(b, s.lo(a) + s.lo(da)) and s.setMax(a, s.hi(b) - s.lo(da)) and
        s.setMax(da, s.hi(b) - s.lo(a))

method propagate(p: DiffnProp, s: CpSolver): bool =
    let n = p.n
    for i in 0 ..< n:
        let xi = p.vs[i]
        let yi = p.vs[n + i]
        let dxi = p.vs[2 * n + i]
        let dyi = p.vs[3 * n + i]
        for j in i + 1 ..< n:
            let xj = p.vs[j]
            let yj = p.vs[n + j]
            let dxj = p.vs[2 * n + j]
            let dyj = p.vs[3 * n + j]
            let c1 = s.leOk(xi, dxi, xj)
            let c2 = s.leOk(yi, dyi, yj)
            let c3 = s.leOk(xj, dxj, xi)
            let c4 = s.leOk(yj, dyj, yi)
            case ord(c1) + ord(c2) + ord(c3) + ord(c4)
            of 0: return false
            of 1:
                let ok = (if c1: s.leSet(xi, dxi, xj)
                          elif c2: s.leSet(yi, dyi, yj)
                          elif c3: s.leSet(xj, dxj, xi)
                          else: s.leSet(yj, dyj, yi))
                if not ok: return false
            else: discard
    true

method check(p: DiffnProp, s: CpSolver): bool =
    let n = p.n
    template v(k: int): int = s.value(p.vs[k])
    for i in 0 ..< n:
        for j in i + 1 ..< n:
            if not (v(i) + v(2 * n + i) <= v(j) or v(n + i) + v(3 * n + i) <= v(n + j) or
                    v(j) + v(2 * n + j) <= v(i) or v(n + j) + v(3 * n + j) <= v(n + i)):
                return false
    true

proc addDiffn*(s: CpSolver, x, y, dx, dy: seq[int]) =
    ## Non-overlapping rectangles (x, y) of size (dx, dy); equal lengths.
    assert x.len == y.len and x.len == dx.len and x.len == dy.len
    if x.len < 2: return
    s.addProp(DiffnProp(vs: x & y & dx & dy, n: x.len, heavy: x.len > 32))

# Difference logic: the constraints x_v - x_u >= k among the model's linear
# constraints (after substituting defined variables), hard, reified by a
# literal, or as the separation disjunctions of diffn, as one graph. D[i][j]
# is the longest path i -> j over those edges (a lower bound on x_j - x_i;
# node 0 is the constant 0, for one-variable constraints), kept closed
# incrementally and trailed. Unlike bounds propagation it fails on a positive
# cycle as soon as its last edge is added, moves bounds along whole paths in
# one step, and fixes the literals whose difference a path implies or
# excludes: rect-euler EU (2000 reified differences, 666 clauses, 17 diffn
# over 120 coordinates of range ~1500) thrashed for 9 s without a solution
# on bounds; with path consistency a DFS branching on clauses solves it in
# 265 nodes (a z3 QF_IDL export in 0.13 s).
# Bounds stay out of D: as edges from node 0 they would connect every pair of
# nodes, so each bound change (and each added edge) would update all n^2
# cells (kitchen tall_complex, 360 nodes: LNS 8x slower).

const DlNeg = low(int) div 4          # no path
const DlMaxNodes* = 400               # n^2 cells, O(n^2) per added edge

type
    DlDef* = object
        ## v = c + sum a_i x_i (a defined variable, substituted)
        v*: int
        a*, x*: seq[int]
        c*: int
    DlEdge = object
        a, b, k: int                  # x_b - x_a >= k (node indices)
    DlLit = object
        r: int                        # engine boolean
        e: DlEdge                     # r = 1 -> e
        full: bool                    # r = 0 -> not e (else r = 0 says nothing)
    DiffLogicProp = ref object of Prop
        n, base: int                  # nodes, first cell of D
        seen: int                     # first of 2n cells: bounds last pushed along D
        nodeVar: seq[int]             # engine variable per node (node 0: -1)
        lits: seq[DlLit]
        disj: seq[seq[DlEdge]]        # at least one edge holds

template dl(s: CpSolver, p: DiffLogicProp, i, j: int): int = s.cells[p.base + i * p.n + j]

proc nlo(s: CpSolver, p: DiffLogicProp, i: int): int {.inline.} =
    (if i == 0: 0 else: s.lo(p.nodeVar[i]))
proc nhi(s: CpSolver, p: DiffLogicProp, i: int): int {.inline.} =
    (if i == 0: 0 else: s.hi(p.nodeVar[i]))

proc dlEntailed(s: CpSolver, p: DiffLogicProp, e: DlEdge): bool {.inline.} =
    s.dl(p, e.a, e.b) >= e.k

proc dlExcluded(s: CpSolver, p: DiffLogicProp, e: DlEdge): bool {.inline.} =
    ## Adding e would close a positive cycle.
    let back = s.dl(p, e.b, e.a)
    back > DlNeg and back + e.k > 0

proc dlAdd(s: CpSolver, p: DiffLogicProp, e: DlEdge): bool =
    ## Adds x_b - x_a >= k and restores the closure (false: positive cycle).
    ## Row b and column a cannot change (that would need a positive cycle),
    ## so they are read while the rest is updated.
    if s.dlEntailed(p, e): return true
    if s.dlExcluded(p, e): return false
    let n = p.n
    s.buf.setLen 0
    for j in 0 ..< n:
        if s.dl(p, e.b, j) > DlNeg: s.buf.add j
    for i in 0 ..< n:
        let dia = s.dl(p, i, e.a)
        if dia <= DlNeg: continue
        let base = dia + e.k
        let row = p.base + i * n
        for j in s.buf:
            let cand = base + s.cells[p.base + e.b * n + j]
            if cand > s.cells[row + j]: s.setCell(row + j, cand)
    true

proc dlPush(s: CpSolver, p: DiffLogicProp, i: int): bool =
    ## Moves the bounds of node i along its paths: x_j >= lo_i + D[i][j],
    ## x_j <= hi_i - D[j][i].
    let li = s.nlo(p, i)
    let hi = s.nhi(p, i)
    if i > 0:
        if s.cells[p.seen + 2 * i] != li: s.setCell(p.seen + 2 * i, li)
        if s.cells[p.seen + 2 * i + 1] != hi: s.setCell(p.seen + 2 * i + 1, hi)
    for j in 0 ..< p.n:
        if j == i: continue
        let dij = s.dl(p, i, j)
        if dij > DlNeg:
            if j == 0:
                if li + dij > 0: return false
            elif not s.setMin(p.nodeVar[j], li + dij): return false
        let dji = s.dl(p, j, i)
        if dji > DlNeg:
            if j == 0:
                if hi - dji < 0: return false
            elif not s.setMax(p.nodeVar[j], hi - dji): return false
    true

method propagate(p: DiffLogicProp, s: CpSolver): bool =
    var added = false
    # fixed literals in
    for l in p.lits:
        if not s.isFixed(l.r): continue
        let e = (if s.value(l.r) == 1: l.e
                 elif l.full: DlEdge(a: l.e.b, b: l.e.a, k: 1 - l.e.k)
                 else: continue)
        if not s.dlEntailed(p, e):
            if not s.dlAdd(p, e): return false
            added = true
    # disjunctions: unit propagation to a fixpoint (paths and bounds)
    var again = true
    while again:
        again = false
        for d in p.disj:
            var free = -1
            var nFree = 0
            var sat = false
            for k, e in d:
                if s.dlEntailed(p, e) or s.nlo(p, e.b) - s.nhi(p, e.a) >= e.k: (sat = true; break)
                if not s.dlExcluded(p, e) and s.nhi(p, e.b) - s.nlo(p, e.a) >= e.k:
                    inc nFree
                    free = k
            if sat: continue
            if nFree == 0: return false
            if nFree == 1:
                if not s.dlAdd(p, d[free]): return false
                added = true
                again = true
    # bounds along paths: every node after a new edge, else the nodes whose
    # bounds changed since they were last pushed
    for i in 0 ..< p.n:
        if added or (i > 0 and (s.cells[p.seen + 2 * i] != s.nlo(p, i) or
                                s.cells[p.seen + 2 * i + 1] != s.nhi(p, i))):
            if not s.dlPush(p, i): return false
    # literals out
    for l in p.lits:
        if s.isFixed(l.r): continue
        if s.dlExcluded(p, l.e):
            if not s.assign(l.r, 0): return false
        elif l.full and s.dlEntailed(p, l.e):
            if not s.assign(l.r, 1): return false
    true

proc addDifferenceLogic*(s: CpSolver, defs: seq[DlDef] = @[], maxNodes = DlMaxNodes): int =
    ## Adds one DiffLogicProp over the difference constraints among the
    ## linear and diffn propagators added so far (call after the model, before
    ## prepare). defs: defined variables, substituted into every constraint
    ## (rect-euler: diffn sizes c_width + 5 with c_width = cx_max - cx_min, so
    ## x_i + dx_i <= x_j is cx_max_i + 5 <= cx_min_j). Redundant with the
    ## propagators it reads, so it only strengthens propagation. Returns the
    ## number of nodes, 0 when nothing was added (no literal or disjunction,
    ## or more than maxNodes variables).
    var defOf = newSeq[int](s.vars.len)
    for i in 0 ..< defOf.len: defOf[i] = -1
    for k, d in defs:
        if d.v >= 0 and d.v < defOf.len: defOf[d.v] = k
    # linear form over non-defined, non-fixed variables: (coef, var) pairs + constant
    proc expand(s: CpSolver, a, x: seq[int], c0: int): (seq[(int, int)], int) =
        var terms: seq[(int, int)]
        var c = c0
        var work: seq[(int, int, int)]          # (coef, var, depth)
        for k in 0 ..< x.len: work.add (a[k], x[k], 0)
        while work.len > 0:
            let (co, v, depth) = work.pop()
            if co == 0: continue
            if s.vars[v].size == 1:
                c += co * s.vars[v].lo
            elif defOf[v] >= 0 and depth < 16:
                let d = defs[defOf[v]]
                c += co * d.c
                for k in 0 ..< d.x.len: work.add (co * d.a[k], d.x[k], depth + 1)
            else:
                var found = false
                for t in terms.mitems:
                    if t[1] == v: (t[0] += co; found = true; break)
                if not found: terms.add (co, v)
        var kept: seq[(int, int)]
        for t in terms:
            if t[0] != 0: kept.add t
        (kept, c)
    var nodeOf = newSeq[int](s.vars.len)
    for i in 0 ..< nodeOf.len: nodeOf[i] = -1
    var nodeVar = @[-1]
    proc nodeFor(v: int): int =
        if v < 0: return 0
        if nodeOf[v] < 0:
            nodeOf[v] = nodeVar.len
            nodeVar.add v
        nodeOf[v]
    # sum a_i x_i + c <= 0 as an edge, or none
    proc edgeOf(s: CpSolver, a, x: seq[int], c: int, e: var DlEdge): bool =
        let (t, k) = s.expand(a, x, c)
        # u - v + k <= 0  <=>  x_u - x_v <= -k  <=>  x_v - x_u >= k
        var u = -1
        var v = -1
        if t.len == 1 and abs(t[0][0]) == 1:
            if t[0][0] == 1: u = t[0][1] else: v = t[0][1]
        elif t.len == 2 and t[0][0] + t[1][0] == 0 and abs(t[0][0]) == 1:
            if t[0][0] == 1: (u = t[0][1]; v = t[1][1]) else: (u = t[1][1]; v = t[0][1])
        else: return false
        e = DlEdge(a: nodeFor(u), b: nodeFor(v), k: k)
        true
    var hard: seq[DlEdge]
    var lits: seq[DlLit]
    var disj: seq[seq[DlEdge]]
    var hasTrivialFalse = false
    proc neg(a: seq[int]): seq[int] =
        for x in a: result.add -x
    for p in s.props:
        if p of LinProp:
            let q = LinProp(p)
            if q.rel == lrNe or (q.rel == lrEq and q.r >= 0): continue
            var e: DlEdge
            # sum a x <= c  <=>  sum a x - c <= 0
            if not s.edgeOf(q.a, q.x, -q.c, e): continue
            if q.rel == lrEq:
                var f: DlEdge
                discard s.edgeOf(neg(q.a), q.x, q.c, f)
                hard.add e
                hard.add f
            elif q.r < 0: hard.add e
            elif s.vars[q.r].size == 1:
                if s.vars[q.r].lo == 1: hard.add e
                elif not q.imp: hard.add DlEdge(a: e.b, b: e.a, k: 1 - e.k)
            else:
                lits.add DlLit(r: q.r, e: e, full: not q.imp)
        elif p of DiffnProp:
            let q = DiffnProp(p)
            let n = q.n
            for i in 0 ..< n:
                for j in i + 1 ..< n:
                    var d: seq[DlEdge]
                    var ok = true
                    # x_i + dx_i <= x_j, y_i + dy_i <= y_j, x_j + dx_j <= x_i, y_j + dy_j <= y_i
                    for (o, z) in [(0, 0), (n, 0), (0, 1), (n, 1)]:
                        let (f, g) = (if z == 0: (i, j) else: (j, i))
                        var e: DlEdge
                        if not s.edgeOf(@[1, 1, -1], @[q.vs[o + f], q.vs[2 * n + o + f], q.vs[o + g]], 0, e):
                            ok = false
                            break
                        d.add e
                    if ok: disj.add d
    if lits.len == 0 and disj.len == 0: return 0
    # defined variables' own bounds
    for d in defs:
        if d.v < 0 or d.v >= s.vars.len or s.vars[d.v].size == 1: continue
        var e: DlEdge
        # v <= hi: sum a x + c - hi <= 0;  v >= lo: -(sum a x) - c + lo <= 0
        if s.edgeOf(d.a, d.x, d.c - s.vars[d.v].hi, e): hard.add e
        if s.edgeOf(neg(d.a), d.x, -d.c + s.vars[d.v].lo, e): hard.add e
    if nodeVar.len > maxNodes: return 0
    let n = nodeVar.len
    let p = DiffLogicProp(n: n, nodeVar: nodeVar, lits: lits, disj: disj, heavy: true)
    p.base = s.newCells(n * n, DlNeg)
    for i in 0 ..< n: s.cells[p.base + i * n + i] = 0
    # bounds last pushed along D: none yet (the first call pushes every node)
    p.seen = s.newCells(2 * n, DlNeg)
    # root closure (Floyd-Warshall) over the hard edges
    template D(i, j: int): untyped = s.cells[p.base + (i) * n + (j)]
    for e in hard:
        if e.k > D(e.a, e.b): D(e.a, e.b) = e.k
    for k in 0 ..< n:
        for i in 0 ..< n:
            let dik = D(i, k)
            if dik <= DlNeg: continue
            for j in 0 ..< n:
                let dkj = D(k, j)
                if dkj <= DlNeg: continue
                if dik + dkj > D(i, j): D(i, j) = dik + dkj
    for i in 0 ..< n:
        if D(i, i) > 0:
            # infeasible at the root: an empty variable makes prepare fail
            hasTrivialFalse = true
    if hasTrivialFalse:
        discard s.newVar(1, 0)
        return n
    for i in 1 ..< n: p.vs.add nodeVar[i]
    for l in lits: p.vs.add l.r
    s.addProp(p)
    n

proc arithmeticSafe*(s: CpSolver): bool =
    ## No linear sum or product can leave int64 over the current domains
    ## (with a factor-2 margin); domains only shrink, so this holds for the
    ## whole search. Overflow raises (checks stay on in release builds), so
    ## an unsafe model fails loudly rather than unsoundly, but a proof
    ## should not crash.
    const lim = float(1 shl 62)
    proc mag(s: CpSolver, v: int): float = max(abs(float(s.vars[v].lo)), abs(float(s.vars[v].hi)))
    for p in s.props:
        if p of LinProp:
            let lp = LinProp(p)
            var tot = abs(float(lp.c))
            for i in 0 ..< lp.a.len: tot += abs(float(lp.a[i])) * s.mag(lp.x[i])
            if tot >= lim: return false
        elif p of TimesProp:
            if s.mag(p.vs[0]) * s.mag(p.vs[1]) >= lim or s.mag(p.vs[2]) >= lim: return false
    true

# --------------------------------------------------------------- shaving

const ShaveMaxStepsPerBound = 64   # removals per bound and round (wide domains)

proc shaveBounds*(s: CpSolver, deadline: float = 0.0, maxRounds = 4): int =
    ## Root-level singleton bound consistency: a variable's lowest (highest)
    ## value is removed while assigning it fails propagation; rounds repeat
    ## while a bound moved. Finds what bounds propagation sees only once a
    ## variable is fixed, e.g. zephyrus' unicity constraints `n = i ->
    ## bindings <= i * m` for i < 10 against `bindings = 10 * m`, m >= 1:
    ## n >= 10. The removals are permanent (call before solve). Returns the
    ## number of refuted bound values (propagation removes more), -1 when the
    ## root is infeasible.
    for p in 0 ..< s.props.len: s.enqueue(p)
    if not s.propagateAll(): return -1
    let fails0 = s.fails
    for round in 0 ..< maxRounds:
        var moved = false
        for v in 0 ..< s.vars.len:
            for side in 0 .. 1:
                var steps = 0
                while s.vars[v].size > 1 and steps < ShaveMaxStepsPerBound:
                    if deadline > 0 and epochTime() > deadline:
                        s.fails = fails0
                        return result
                    let val = if side == 0: s.vars[v].lo else: s.vars[v].hi
                    s.pushLevel()
                    let ok = s.assign(v, val) and s.propagateAll()
                    s.popLevel()
                    if ok: break
                    s.clearQueues()
                    let cut = if side == 0: s.setMin(v, val + 1) else: s.setMax(v, val - 1)
                    if not (cut and s.propagateAll()): return -1
                    inc result; inc steps
                    moved = true
        if not moved: break
    s.fails = fails0

# ------------------------------------------------------------------ search

proc addBranchGroup*(s: CpSolver, vars: seq[int], varSel: CpVarSel, valSel: CpValSel) =
    var vs: seq[int]
    for v in vars:
        if v >= 0 and not s.grouped[v]:
            s.grouped[v] = true
            vs.add v
    if vs.len > 0: s.groups.add BranchGroup(vars: vs, varSel: varSel, valSel: valSel)

proc selectDomWdeg(s: CpSolver, d: var Decision): bool =
    ## Smallest domain size / summed weight of the watching propagators
    ## (Boussemart et al.'s dom/wdeg, without the two-unfixed-variables test),
    ## minimum value first.
    var best = -1
    var bestScore = 0.0
    for v in 0 ..< s.vars.len:
        let x = s.vars[v]
        if x.size == 1: continue
        var w = 0
        for p in s.watch[v]: w += s.weight[p]
        let score = float(x.size) / float(max(1, w))
        if best < 0 or score < bestScore:
            best = v
            bestScore = score
    if best < 0: return false
    d = Decision(v: best, val: s.vars[best].lo, kind: dkEq)
    true

proc selectDecision(s: CpSolver, d: var Decision): bool =
    if s.wdegAll: return s.selectDomWdeg(d)
    for g in s.groups:
        var best = -1
        var bestKey = 0
        for v in g.vars:
            let x = s.vars[v]
            if x.size == 1: continue
            let key = case g.varSel
                of vsInputOrder: 0
                of vsFirstFail: x.size
                of vsAntiFirstFail: -x.size
                of vsSmallest: x.lo
                of vsLargest: -x.hi
            if best < 0 or key < bestKey:
                best = v; bestKey = key
                if g.varSel == vsInputOrder: break
        if best < 0: continue
        let x = s.vars[best]
        d.v = best
        case g.valSel
        of valMin: (d.kind = dkEq; d.val = x.lo)
        of valMax: (d.kind = dkEq; d.val = x.hi)
        of valSplit: (d.kind = dkLe; d.val = floorDiv(x.lo + x.hi, 2))
        of valReverseSplit: (d.kind = dkGe; d.val = floorDiv(x.lo + x.hi, 2) + 1)
        return true
    false

proc applyDecision(s: CpSolver, d: Decision, left: bool): bool =
    case d.kind
    of dkEq: (if left: s.assign(d.v, d.val) else: s.remove(d.v, d.val))
    of dkLe: (if left: s.setMax(d.v, d.val) else: s.setMin(d.v, d.val + 1))
    of dkGe: (if left: s.setMin(d.v, d.val) else: s.setMax(d.v, d.val - 1))

proc prepare*(s: CpSolver): bool =
    ## Adds the remaining variables as the last branch group (first fail) and
    ## propagates the root; false when the root is infeasible. Idempotent.
    var rest: seq[int]
    for v in 0 ..< s.vars.len:
        if not s.grouped[v]: rest.add v
    s.addBranchGroup(rest, vsFirstFail, valMin)
    for x in s.vars:
        if x.size <= 0: return false
    for p in 0 ..< s.props.len: s.enqueue(p)
    s.propagateAll()

proc groupVars*(s: CpSolver): seq[int] =
    ## Variables of the branch groups added so far, in group order.
    for g in s.groups:
        for v in g.vars: result.add v

proc level*(s: CpSolver): int = s.trailLim.len
    ## Current decision level (0 = root); see popTo.

proc popTo*(s: CpSolver, lvl: int) =
    ## Undoes every level above lvl (after a search, to read and then discard
    ## its solution, or after assumptions pushed with pushAssume).
    s.clearQueues()
    while s.trailLim.len > lvl: s.popLevel()

proc pushAssume*(s: CpSolver) = s.pushLevel()
    ## Opens a level for assumptions (assign / setMin / setMax + propagate),
    ## undone with popTo.

proc propagate*(s: CpSolver): bool = s.propagateAll()

proc search*(s: CpSolver, deadline: float = 0.0, stop: ptr bool = nil,
             stallMin: float = 0.0, maxNodes = 0): CpStatus =
    ## Depth-first search below the current level (call prepare first). On
    ## cpSat every variable is fixed (read with value) and the search levels
    ## stay on the trail (popTo to discard them); cpUnsat / cpLimit restore
    ## the level search started from. maxNodes > 0 limits the nodes of this
    ## call. See solve for stallMin.
    var stack: seq[Decision]
    let t0 = epochTime()
    let base = s.trailLim.len
    let nodes0 = s.nodes
    var depthT = 0.0
    s.stalled = false
    proc limitHit(): bool =
        if stop != nil and stop[]: return true
        if maxNodes > 0 and s.nodes - nodes0 >= maxNodes: return true
        if deadline <= 0 and stallMin <= 0: return false
        let now = epochTime()
        if deadline > 0 and now > deadline: return true
        if stallMin > 0 and now - t0 - depthT > max(stallMin, 2 * depthT):
            s.stalled = true
            return true
        false
    template giveUp(st: CpStatus) =
        s.popTo(base)
        return st
    while true:
        var d: Decision
        if not s.selectDecision(d):
            for p in s.props:
                if not p.check(s):
                    stderr.writeLine("[CP] solution violates constraint " & $p.id & ": propagator bug")
                    giveUp(cpLimit)
            return cpSat
        inc s.nodes
        if (s.nodes and 7) == 0 or maxNodes > 0:
            if limitHit(): giveUp(cpLimit)
        s.pushLevel()
        stack.add d
        if stack.len > s.maxDepth:
            s.maxDepth = stack.len
            if stallMin > 0: depthT = epochTime() - t0
        var ok = s.applyDecision(d, true) and s.propagateAll()
        while not ok:
            if stack.len == 0: giveUp(cpUnsat)
            let last = stack.pop()
            s.popLevel()
            ok = s.applyDecision(last, false) and s.propagateAll()
            if not ok and ((s.fails and 7) == 0 or maxNodes > 0) and limitHit(): giveUp(cpLimit)

proc luby(i: int): int =
    ## The i-th term (1-based) of the Luby sequence 1 1 2 1 1 2 4 ...
    var k = 1
    while (1 shl k) - 1 < i: inc k
    if i == (1 shl k) - 1: return 1 shl (k - 1)
    luby(i - (1 shl (k - 1)) + 1)

const RefuteRestartBase = 100   # nodes per Luby unit

proc refute*(s: CpSolver, deadline: float = 0.0): CpStatus =
    ## Complete search for a solution or a proof that none exists: dom/wdeg
    ## branching over every variable (failures raise the weight of the
    ## propagator that failed) with Luby restarts that keep the weights.
    ## Restart limits grow without bound, so the search stays complete:
    ## cpUnsat only when one run exhausts its tree; cpLimit on the deadline.
    if not s.prepare(): return cpUnsat
    s.wdegAll = true
    var i = 1
    while true:
        let st = s.search(deadline = deadline, maxNodes = RefuteRestartBase * luby(i))
        if st != cpLimit: return st
        if deadline > 0 and epochTime() > deadline: return cpLimit
        inc i

proc solve*(s: CpSolver, deadline: float = 0.0, stop: ptr bool = nil,
            stallMin: float = 0.0): CpStatus =
    ## Depth-first search for one solution; on cpSat every variable is fixed
    ## (read with value). Ungrouped variables are searched last (first fail).
    ## With stallMin > 0 the search also gives up (cpLimit, stalled = true)
    ## once the deepest decision level has not grown for max(stallMin,
    ## 2 * the time at which it was reached): searches that will not finish
    ## thrash at a fixed depth (zephyrus, hoist, hard nonograms), while the
    ## ones that do finish keep reaching new depths (nonogram medium_05's
    ## longest gap is 0.70 of this limit, kitchen b1's 0.44).
    if not s.prepare(): return cpUnsat
    s.search(deadline, stop, stallMin)
