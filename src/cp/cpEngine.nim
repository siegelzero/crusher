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

    TrailEntry = object
        isWord: bool
        i: int           # var id or word index
        a, b, c: int     # lo, hi, size, or the old word (a)

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
        s.trail.add TrailEntry(isWord: false, i: v, a: x.lo, b: x.hi, c: x.size)

proc saveWord(s: CpSolver, w: int) {.inline.} =
    if s.trailLim.len > 0 and s.wordStamp[w] != s.curLevel:
        s.wordStamp[w] = s.curLevel
        s.trail.add TrailEntry(isWord: true, i: w, a: cast[int](s.words[w]))

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
        if e.isWord: s.words[e.i] = cast[uint64](e.a)
        else:
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

# ------------------------------------------------------------------ search

proc addBranchGroup*(s: CpSolver, vars: seq[int], varSel: CpVarSel, valSel: CpValSel) =
    var vs: seq[int]
    for v in vars:
        if v >= 0 and not s.grouped[v]:
            s.grouped[v] = true
            vs.add v
    if vs.len > 0: s.groups.add BranchGroup(vars: vs, varSel: varSel, valSel: valSel)

proc selectDecision(s: CpSolver, d: var Decision): bool =
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
    var rest: seq[int]
    for v in 0 ..< s.vars.len:
        if not s.grouped[v]: rest.add v
    s.addBranchGroup(rest, vsFirstFail, valMin)
    for x in s.vars:
        if x.size <= 0: return cpUnsat
    for p in 0 ..< s.props.len: s.enqueue(p)
    if not s.propagateAll(): return cpUnsat
    var stack: seq[Decision]
    let t0 = epochTime()
    var depthT = 0.0
    s.stalled = false
    proc limitHit(): bool =
        if stop != nil and stop[]: return true
        if deadline <= 0 and stallMin <= 0: return false
        let now = epochTime()
        if deadline > 0 and now > deadline: return true
        if stallMin > 0 and now - t0 - depthT > max(stallMin, 2 * depthT):
            s.stalled = true
            return true
        false
    while true:
        var d: Decision
        if not s.selectDecision(d):
            for p in s.props:
                if not p.check(s):
                    stderr.writeLine("[CP] solution violates constraint " & $p.id & ": propagator bug")
                    return cpLimit
            return cpSat
        inc s.nodes
        if (s.nodes and 7) == 0:
            if limitHit(): return cpLimit
        s.pushLevel()
        stack.add d
        if stack.len > s.maxDepth:
            s.maxDepth = stack.len
            if stallMin > 0: depthT = epochTime() - t0
        var ok = s.applyDecision(d, true) and s.propagateAll()
        while not ok:
            if stack.len == 0: return cpUnsat
            let last = stack.pop()
            s.popLevel()
            ok = s.applyDecision(last, false) and s.propagateAll()
            if not ok and (s.fails and 7) == 0 and limitHit(): return cpLimit
