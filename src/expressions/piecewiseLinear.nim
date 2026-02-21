## Piecewise-linear function representation for fast batch evaluation.
## Compiles ExpressionNode trees into PL functions of a single variable,
## enabling O(1) evaluation per domain value instead of O(tree_depth).

import types

const MaxPLSegs* = 32

type
    PLSegment* = object
        coeff*: int   # f(v) = coeff * v + base
        base*: int

    PiecewiseLinear* = object
        n*: int  # number of segments (1..MaxPLSegs)
        breaks*: array[MaxPLSegs - 1, int]  # sorted breakpoints, first n-1 used
        segs*: array[MaxPLSegs, PLSegment]   # first n used
        # segs[0] for v < breaks[0]
        # segs[i] for breaks[i-1] <= v < breaks[i]  (1 <= i < n-1)
        # segs[n-1] for v >= breaks[n-2]

# Integer division helpers (Nim `div` truncates toward zero; we need floor/ceil)

func floorDivI(a, b: int): int {.inline.} =
    ## Floor division: largest k such that k*b <= a. Requires b > 0.
    assert b > 0
    if a >= 0: a div b
    else: -(((-a) + b - 1) div b)

func ceilDivI(a, b: int): int {.inline.} =
    ## Ceiling division: smallest k such that k*b >= a. Requires b > 0.
    assert b > 0
    if a >= 0: (a + b - 1) div b
    else: -((-a) div b)

# Constructors

func plConst*(c: int): PiecewiseLinear {.inline.} =
    result.n = 1
    result.segs[0] = PLSegment(coeff: 0, base: c)

func plIdent*(): PiecewiseLinear {.inline.} =
    result.n = 1
    result.segs[0] = PLSegment(coeff: 1, base: 0)

# Evaluate at a single point

func plEval*(f: PiecewiseLinear, v: int): int {.inline.} =
    var idx = 0
    for i in 0 ..< f.n - 1:
        if v >= f.breaks[i]: idx = i + 1
        else: break
    f.segs[idx].coeff * v + f.segs[idx].base

# Negate

func plNeg*(f: PiecewiseLinear): PiecewiseLinear =
    result.n = f.n
    for i in 0 ..< f.n - 1: result.breaks[i] = f.breaks[i]
    for i in 0 ..< f.n:
        result.segs[i] = PLSegment(coeff: -f.segs[i].coeff, base: -f.segs[i].base)

# Scale by constant

func plScale*(f: PiecewiseLinear, c: int): PiecewiseLinear =
    if c == 0: return plConst(0)
    result.n = f.n
    for i in 0 ..< f.n - 1: result.breaks[i] = f.breaks[i]
    for i in 0 ..< f.n:
        result.segs[i] = PLSegment(coeff: f.segs[i].coeff * c, base: f.segs[i].base * c)

# Absolute value — splits segments at zero crossings

func plAbs*(f: PiecewiseLinear): PiecewiseLinear =
    var si = 0  # output segment index
    for i in 0 ..< f.n:
        let seg = f.segs[i]
        let regionLo = if i == 0: int.low div 4 else: f.breaks[i - 1]
        let regionHi = if i == f.n - 1: int.high div 4 else: f.breaks[i]

        if seg.coeff == 0:
            if si >= MaxPLSegs: return f  # overflow fallback
            result.segs[si] = PLSegment(coeff: 0, base: abs(seg.base))
            si += 1
        else:
            # Find zero-crossing breakpoint
            var zb: int
            var negBelow: bool  # true if f < 0 for v below zb
            if seg.coeff > 0:
                zb = ceilDivI(-seg.base, seg.coeff)
                negBelow = true
            else:
                zb = floorDivI(seg.base, -seg.coeff) + 1
                negBelow = false

            let negSeg = PLSegment(coeff: -seg.coeff, base: -seg.base)
            let posSeg = seg

            if zb <= regionLo:
                # No crossing in region
                if si >= MaxPLSegs: return f
                result.segs[si] = if negBelow: posSeg else: negSeg
                si += 1
            elif zb >= regionHi:
                if si >= MaxPLSegs: return f
                result.segs[si] = if negBelow: negSeg else: posSeg
                si += 1
            else:
                # Split at zero crossing
                if si + 1 >= MaxPLSegs: return f
                if negBelow:
                    result.segs[si] = negSeg; si += 1
                    result.breaks[si - 1] = zb
                    result.segs[si] = posSeg; si += 1
                else:
                    result.segs[si] = posSeg; si += 1
                    result.breaks[si - 1] = zb
                    result.segs[si] = negSeg; si += 1

        # Add original breakpoint after this source segment (if not last)
        if i < f.n - 1:
            if si > 0 and si - 1 < MaxPLSegs - 1:
                result.breaks[si - 1] = f.breaks[i]
    result.n = si

# Add two PL functions

func plAdd*(f, g: PiecewiseLinear): PiecewiseLinear =
    var si = 0
    var fi = 0; var gi = 0
    var fbi = 0; var gbi = 0

    while true:
        if si >= MaxPLSegs: return f  # overflow
        result.segs[si] = PLSegment(
            coeff: f.segs[fi].coeff + g.segs[gi].coeff,
            base: f.segs[fi].base + g.segs[gi].base)
        si += 1

        let fHas = fbi < f.n - 1
        let gHas = gbi < g.n - 1
        if not fHas and not gHas: break

        let fb = if fHas: f.breaks[fbi] else: int.high
        let gb = if gHas: g.breaks[gbi] else: int.high

        if si - 1 >= MaxPLSegs - 1: break  # can't add more breaks
        if fb < gb:
            result.breaks[si - 1] = fb
            fi += 1; fbi += 1
        elif gb < fb:
            result.breaks[si - 1] = gb
            gi += 1; gbi += 1
        else:
            result.breaks[si - 1] = fb
            fi += 1; fbi += 1
            gi += 1; gbi += 1
    result.n = si

func plSub*(f, g: PiecewiseLinear): PiecewiseLinear {.inline.} =
    plAdd(f, plNeg(g))

# Max of two PL functions — merge breakpoints and detect crossings

func plMax*(f, g: PiecewiseLinear): PiecewiseLinear =
    var si = 0
    var fi = 0; var gi = 0
    var fbi = 0; var gbi = 0

    while true:
        if si >= MaxPLSegs: return f

        let fSeg = f.segs[fi]
        let gSeg = g.segs[gi]

        # Determine region boundaries
        let fHas = fbi < f.n - 1
        let gHas = gbi < g.n - 1
        let fb = if fHas: f.breaks[fbi] else: int.high div 2
        let gb = if gHas: g.breaks[gbi] else: int.high div 2
        let regionEnd = min(fb, gb)
        let regionStart = if si == 0: int.low div 4
                          elif si - 1 < MaxPLSegs - 1: result.breaks[si - 1]
                          else: int.low div 4

        # In this region, f = fSeg.coeff*v + fSeg.base, g = gSeg.coeff*v + gSeg.base
        # diff(v) = f(v) - g(v) = dc*v + db where:
        let dc = fSeg.coeff - gSeg.coeff
        let db = fSeg.base - gSeg.base

        if dc == 0:
            # Parallel — one is always >= the other
            if si >= MaxPLSegs: return f
            result.segs[si] = if db >= 0: fSeg else: gSeg
            si += 1
        else:
            # Find crossing point within region
            # diff(v) = dc*v + db = 0 at v = -db/dc
            # f >= g when dc*v + db >= 0
            var crossAt: int
            var fFirstBelow: bool  # f >= g for v < crossAt

            if dc > 0:
                # f - g is increasing → g >= f below cross, f >= g above cross
                crossAt = ceilDivI(-db, dc)
                fFirstBelow = false
            else:
                # f - g is decreasing → f >= g below cross, g >= f above cross
                let negDc = -dc
                crossAt = floorDivI(db, negDc) + 1
                fFirstBelow = true

            if crossAt <= regionStart:
                # Crossing before region
                if si >= MaxPLSegs: return f
                result.segs[si] = if fFirstBelow: gSeg else: fSeg
                si += 1
            elif crossAt >= regionEnd:
                # Crossing at or beyond region end
                if si >= MaxPLSegs: return f
                result.segs[si] = if fFirstBelow: fSeg else: gSeg
                si += 1
            else:
                # Crossing inside region — split
                if si + 1 >= MaxPLSegs: return f
                if fFirstBelow:
                    result.segs[si] = fSeg; si += 1
                    result.breaks[si - 1] = crossAt
                    result.segs[si] = gSeg; si += 1
                else:
                    result.segs[si] = gSeg; si += 1
                    result.breaks[si - 1] = crossAt
                    result.segs[si] = fSeg; si += 1

        if not fHas and not gHas: break
        if si - 1 >= MaxPLSegs - 1: break

        # Add region-end breakpoint and advance
        let nextBreak = regionEnd
        if fb <= gb:
            fi += 1; fbi += 1
        if gb <= fb:
            gi += 1; gbi += 1
        # Only add break if we haven't just added one at the same position
        if si > 0 and (si - 1 >= MaxPLSegs - 1 or result.breaks[si - 1] != nextBreak):
            result.breaks[si - 1] = nextBreak
    result.n = si

func plMin*(f, g: PiecewiseLinear): PiecewiseLinear {.inline.} =
    plNeg(plMax(plNeg(f), plNeg(g)))

# Compile an ExpressionNode into a PiecewiseLinear function of varyingPos.
# Returns (true, pl) on success, (false, default) if the tree can't be compiled.

proc compilePL*(node: ExpressionNode[int], varyingPos: int,
                assignment: seq[int]): (bool, PiecewiseLinear) =
    case node.kind:
    of LiteralNode:
        return (true, plConst(node.value))
    of RefNode:
        if node.position == varyingPos:
            return (true, plIdent())
        else:
            return (true, plConst(assignment[node.position]))
    of UnaryOpNode:
        let (ok, child) = compilePL(node.target, varyingPos, assignment)
        if not ok: return (false, PiecewiseLinear())
        case node.unaryOp:
        of AbsoluteValue:
            return (true, plAbs(child))
        of Negation:
            return (true, plNeg(child))
    of BinaryOpNode:
        let (lok, left) = compilePL(node.left, varyingPos, assignment)
        if not lok: return (false, PiecewiseLinear())
        let (rok, right) = compilePL(node.right, varyingPos, assignment)
        if not rok: return (false, PiecewiseLinear())
        case node.binaryOp:
        of Addition:
            return (true, plAdd(left, right))
        of Subtraction:
            return (true, plSub(left, right))
        of Multiplication:
            # One side must be constant for PL to work
            if left.n == 1 and left.segs[0].coeff == 0:
                return (true, plScale(right, left.segs[0].base))
            elif right.n == 1 and right.segs[0].coeff == 0:
                return (true, plScale(left, right.segs[0].base))
            else:
                return (false, PiecewiseLinear())  # non-linear multiplication
        of Maximum:
            return (true, plMax(left, right))
        of Minimum:
            return (true, plMin(left, right))
