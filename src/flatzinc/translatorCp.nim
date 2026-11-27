## Included from translator.nim -- not a standalone module.
##
## FlatZinc model -> propagation engine (cp/cpEngine), for a short
## depth-first search before local search starts. The engine works on the
## FlatZinc model itself (after translation: presolve-tightened domains,
## rewrites that keep it equivalent), not on the ConstraintSystem; a model
## with any constraint it has no propagator for is declined, since a DFS
## solution must satisfy the whole model. The search follows the solve
## annotation (int_search / bool_search / seq_search), then first-fail over
## the remaining variables.
##
## The solution seeds the first resolve (`cpSeedFirst` ->
## `ConstraintSystem.seedFirst`); local search then confirms it in its own
## model, so output never rests on the engine alone.

import ../cp/cpEngine

const CpSupported = ["int_lin_le", "int_lin_eq", "int_lin_ne", "bool_lin_le", "bool_lin_eq",
    "int_lin_le_reif", "int_lin_eq_reif", "int_lin_ne_reif",
    "int_lin_le_imp", "int_lin_eq_imp", "int_lin_ne_imp",
    "int_le", "int_lt", "int_eq", "int_ne", "bool_le", "bool_lt", "bool_eq", "bool_not",
    "int_le_reif", "int_lt_reif", "int_eq_reif", "int_ne_reif",
    "int_le_imp", "int_lt_imp", "int_eq_imp", "int_ne_imp",
    "bool_le_reif", "bool_lt_reif", "bool_eq_reif", "bool_eq_imp",
    "bool2int", "bool_clause", "bool_clause_reif", "array_bool_and", "array_bool_or",
    "bool_and", "bool_or", "bool_xor",
    "int_times", "int_abs", "int_max", "int_min", "array_int_maximum", "array_int_minimum",
    "array_int_element", "array_bool_element", "array_var_int_element", "array_var_bool_element",
    "set_in", "set_in_reif", "set_in_imp", "fzn_regular", "fzn_table_int", "int_div",
    "fzn_global_cardinality", "fzn_global_cardinality_closed",
    "fzn_global_cardinality_low_up", "fzn_global_cardinality_low_up_closed", "fzn_diffn"]

type CpPlan = object
    s: CpSolver
    varOf: Table[string, int]       # FZN scalar variable -> engine variable
    unsupported: string
    dlNodes: int                    # variables of the difference-logic propagator (0: none)

proc buildCpModel(tr: var FznTranslator, strict = false): CpPlan =
    ## strict: declared domains only (no presolve), and variables declared
    ## without bounds decline (otherwise capped at CpUnboundedLimit), for
    ## proofs (cpRefute).
    var plan = CpPlan(s: newCpSolver())
    template decline(why: string) =
        plan.unsupported = why
        return plan
    for con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin CpSupported: decline(name)
    let s = plan.s
    # Variables: presolve-tightened domains where known, else declared ones
    var varArrays: Table[string, seq[FznExpr]]
    var aliases: seq[(string, FznExpr)]
    for decl in tr.model.variables:
        if decl.isArray:
            if decl.value != nil and decl.value.kind == FznArrayLit:
                varArrays[decl.name] = decl.value.elems
            continue
        if not decl.isVar: continue
        if decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
            decline("set variable " & decl.name)
        var id: int
        if strict and decl.varType.kind notin {FznBool, FznIntRange, FznIntSet}:
            decline("unbounded variable " & decl.name)
        if not strict and decl.name in tr.presolveDomains:
            id = s.newVarValues(tr.presolveDomains[decl.name])
        else:
            case decl.varType.kind
            of FznBool: id = s.newVar(0, 1)
            of FznIntRange: id = s.newVar(decl.varType.lo, decl.varType.hi)
            of FznIntSet: id = s.newVarValues(decl.varType.values)
            else: id = s.newVar(-CpUnboundedLimit, CpUnboundedLimit)
        if id < 0: decline("wide domain with holes: " & decl.name)
        plan.varOf[decl.name] = id
        if decl.value != nil: aliases.add (decl.name, decl.value)

    var bad = ""
    proc argVar(tr: FznTranslator, plan: var CpPlan, e: FznExpr, bad: var string): int =
        case e.kind
        of FznIntLit: plan.s.constVar(e.intVal)
        of FznBoolLit: plan.s.constVar(if e.boolVal: 1 else: 0)
        of FznIdent:
            if e.ident in plan.varOf: plan.varOf[e.ident]
            elif e.ident in tr.paramValues: plan.s.constVar(tr.paramValues[e.ident])
            else: (bad = "unknown identifier " & e.ident; -1)
        else: (bad = "unexpected argument"; -1)
    proc argVars(tr: FznTranslator, plan: var CpPlan, varArrays: Table[string, seq[FznExpr]],
                 e: FznExpr, bad: var string): seq[int] =
        var elems: seq[FznExpr]
        if e.kind == FznArrayLit: elems = e.elems
        elif e.kind == FznIdent and e.ident in varArrays: elems = varArrays[e.ident]
        elif e.kind == FznIdent and e.ident in tr.arrayValues:
            for v in tr.arrayValues[e.ident]: result.add plan.s.constVar(v)
            return
        else:
            bad = "unresolved array"
            return
        for el in elems: result.add argVar(tr, plan, el, bad)
    proc intArray(tr: FznTranslator, e: FznExpr, bad: var string): seq[int] =
        try: tr.resolveIntArray(e)
        except CatchableError:
            bad = "non-constant coefficients"
            @[]
    proc intConst(tr: FznTranslator, e: FznExpr, bad: var string): int =
        if e.kind == FznIntLit: return e.intVal
        if e.kind == FznBoolLit: return (if e.boolVal: 1 else: 0)
        if e.kind == FznIdent and e.ident in tr.paramValues: return tr.paramValues[e.ident]
        bad = "non-constant argument"
        0
    proc setConst(tr: FznTranslator, e: FznExpr, bad: var string): seq[int] =
        case e.kind
        of FznSetLit, FznRange: extractSetValues(e)
        of FznIdent:
            if e.ident in tr.setParamValues: tr.setParamValues[e.ident]
            else: (bad = "unknown set " & e.ident; @[])
        else: (bad = "unexpected set argument"; @[])

    for (name, value) in aliases:
        let other = argVar(tr, plan, value, bad)
        if bad != "": decline(bad)
        s.addLinear(@[1, -1], @[plan.varOf[name], other], 0, lrEq)

    for con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        let args = con.args
        template V(i: int): int = argVar(tr, plan, args[i], bad)
        template VS(i: int): seq[int] = argVars(tr, plan, varArrays, args[i], bad)
        case name
        of "int_lin_le", "int_lin_eq", "int_lin_ne", "bool_lin_le", "bool_lin_eq",
           "int_lin_le_reif", "int_lin_eq_reif", "int_lin_ne_reif",
           "int_lin_le_imp", "int_lin_eq_imp", "int_lin_ne_imp":
            let a = intArray(tr, args[0], bad)
            let x = VS(1)
            let c = intConst(tr, args[2], bad)
            let rel = (if "_le" in name: lrLe elif "_eq" in name: lrEq else: lrNe)
            let r = (if args.len > 3: V(3) else: -1)
            if bad == "" and a.len != x.len: bad = name & ": length mismatch"
            if bad != "": decline(bad)
            s.addLinear(a, x, c, rel, r, name.endsWith("_imp"))
        of "int_le", "int_lt", "int_eq", "int_ne", "bool_le", "bool_lt", "bool_eq",
           "int_le_reif", "int_lt_reif", "int_eq_reif", "int_ne_reif",
           "int_le_imp", "int_lt_imp", "int_eq_imp", "int_ne_imp",
           "bool_le_reif", "bool_lt_reif", "bool_eq_reif", "bool_eq_imp":
            let a = V(0)
            let b = V(1)
            let r = (if args.len > 2: V(2) else: -1)
            if bad != "": decline(bad)
            let base = name.split('_')[1]
            let imp = name.endsWith("_imp")
            case base
            of "le": s.addLinear(@[1, -1], @[a, b], 0, lrLe, r, imp)
            of "lt": s.addLinear(@[1, -1], @[a, b], -1, lrLe, r, imp)
            of "eq": s.addLinear(@[1, -1], @[a, b], 0, lrEq, r, imp)
            else: s.addLinear(@[1, -1], @[a, b], 0, lrNe, r, imp)
        of "bool_not":
            let a = V(0)
            let b = V(1)
            if bad != "": decline(bad)
            s.addLinear(@[1, 1], @[a, b], 1, lrEq)
        of "bool2int":
            let a = V(0)
            let b = V(1)
            if bad != "": decline(bad)
            s.addLinear(@[1, -1], @[a, b], 0, lrEq)
        of "bool_clause", "bool_clause_reif":
            let pos = VS(0)
            let neg = VS(1)
            let r = (if args.len > 2: V(2) else: -1)
            if bad != "": decline(bad)
            var lv = pos & neg
            var lp: seq[bool]
            for _ in pos: lp.add true
            for _ in neg: lp.add false
            if r < 0: s.addOr(lv, lp) else: s.addOr(lv, lp, r, true)
        of "array_bool_or", "array_bool_and":
            let xs = VS(0)
            let r = V(1)
            if bad != "": decline(bad)
            var lp: seq[bool]
            for _ in xs: lp.add(name == "array_bool_or")
            # and(xs) = r  <=>  or(not xs) = not r
            s.addOr(xs, lp, r, name == "array_bool_or")
        of "bool_and", "bool_or":
            let a = V(0)
            let b = V(1)
            let r = V(2)
            if bad != "": decline(bad)
            let isOr = name == "bool_or"
            s.addOr(@[a, b], @[isOr, isOr], r, isOr)
        of "bool_xor":
            let a = V(0)
            let b = V(1)
            if bad != "": decline(bad)
            if args.len == 2:
                s.addLinear(@[1, -1], @[a, b], 0, lrNe)
            else:
                let r = V(2)
                if bad != "": decline(bad)
                var mask = 0'u32
                for t in 0 ..< 8:
                    if ((t and 1) xor ((t shr 1) and 1)) == ((t shr 2) and 1): mask = mask or (1'u32 shl t)
                s.addBoolTable(@[a, b, r], mask)
        of "int_times":
            let a = V(0)
            let b = V(1)
            let c = V(2)
            if bad != "": decline(bad)
            s.addTimes(a, b, c)
        of "int_abs":
            let a = V(0)
            let b = V(1)
            if bad != "": decline(bad)
            s.addAbs(a, b)
        of "int_max", "int_min":
            let a = V(0)
            let b = V(1)
            let c = V(2)
            if bad != "": decline(bad)
            s.addMax(c, @[a, b], name == "int_min")
        of "array_int_maximum", "array_int_minimum":
            let m = V(0)
            let xs = VS(1)
            if bad != "": decline(bad)
            if xs.len == 0: decline(name & " over an empty array")
            s.addMax(m, xs, name == "array_int_minimum")
        of "array_int_element", "array_bool_element":
            let idx = V(0)
            let arr = intArray(tr, args[1], bad)
            let r = V(2)
            if bad != "": decline(bad)
            s.addElement(idx, arr, r)
        of "array_var_int_element", "array_var_bool_element":
            let idx = V(0)
            let xs = VS(1)
            let r = V(2)
            if bad != "": decline(bad)
            s.addVarElement(idx, xs, r)
        of "set_in", "set_in_reif", "set_in_imp":
            let x = V(0)
            let vals = setConst(tr, args[1], bad)
            let r = (if args.len > 2: V(2) else: -1)
            if bad != "": decline(bad)
            s.addSetIn(x, vals, r, name == "set_in_imp")
        of "fzn_regular":
            let xs = VS(0)
            let q = intConst(tr, args[1], bad)
            let sy = intConst(tr, args[2], bad)
            let d = intArray(tr, args[3], bad)
            let q0 = intConst(tr, args[4], bad)
            let f = setConst(tr, args[5], bad)
            if bad == "" and d.len != q * sy: bad = "regular: transition table size"
            if bad != "": decline(bad)
            s.addRegular(xs, q, sy, d, q0, f)
        of "fzn_table_int":
            let xs = VS(0)
            let t = intArray(tr, args[1], bad)
            if bad == "" and (xs.len == 0 or t.len mod xs.len != 0): bad = "table: tuple size"
            if bad != "": decline(bad)
            s.addTable(xs, t)
        of "int_div":
            let a = V(0)
            let b = V(1)
            let c = V(2)
            if bad != "": decline(bad)
            s.addDiv(a, b, c)
        of "fzn_global_cardinality", "fzn_global_cardinality_closed",
           "fzn_global_cardinality_low_up", "fzn_global_cardinality_low_up_closed":
            let xs = VS(0)
            let cover = intArray(tr, args[1], bad)
            let closed = name.endsWith("_closed")
            var lb, ub, counts: seq[int]
            if "_low_up" in name:
                lb = intArray(tr, args[2], bad)
                ub = intArray(tr, args[3], bad)
                if bad == "" and (lb.len != cover.len or ub.len != cover.len): bad = name & ": length mismatch"
            else:
                counts = VS(2)
                if bad == "" and counts.len != cover.len: bad = name & ": length mismatch"
            if bad == "" and cover.deduplicate.len != cover.len: bad = name & ": repeated cover value"
            if bad != "": decline(bad)
            s.addGcc(xs, cover, lb, ub, counts, closed)
            # Implied: the counts add up to the xs taking a cover value
            if counts.len > 0:
                var ones: seq[int]
                for _ in counts: ones.add 1
                if closed: s.addLinear(ones, counts, xs.len, lrEq)
                else: s.addLinear(ones, counts, xs.len, lrLe)
        of "fzn_diffn":
            let x = VS(0)
            let y = VS(1)
            let dx = VS(2)
            let dy = VS(3)
            if bad == "" and (y.len != x.len or dx.len != x.len or dy.len != x.len):
                bad = name & ": length mismatch"
            if bad != "": decline(bad)
            s.addDiffn(x, y, dx, dy)
        else:
            decline(name)

    # Difference logic over the linear and diffn constraints, with the
    # variables that int_lin_eq defines (coefficient +-1) substituted
    var defs: seq[DlDef]
    for con in tr.model.constraints:
        if stripSolverPrefix(con.name) != "int_lin_eq" or not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident notin plan.varOf: continue
        var b = ""
        let a = intArray(tr, con.args[0], b)
        let x = argVars(tr, plan, varArrays, con.args[1], b)
        let c = intConst(tr, con.args[2], b)
        if b != "" or a.len != x.len: continue
        let v = plan.varOf[ann.args[0].ident]
        var k = -1
        for i in 0 ..< x.len:
            if x[i] == v: (k = i; break)
        if k < 0 or abs(a[k]) != 1: continue
        var d = DlDef(v: v, c: a[k] * c)
        for i in 0 ..< x.len:
            if i != k:
                d.a.add -a[k] * a[i]
                d.x.add x[i]
        defs.add d
    plan.dlNodes = s.addDifferenceLogic(defs)

    # Branching: the solve annotation's search lists, in order
    proc annName(e: FznExpr): string =
        if e.kind == FznIdent: e.ident
        elif e.kind == FznAnnotationExpr: e.annName
        else: ""
    proc addSearch(tr: FznTranslator, plan: var CpPlan, varArrays: Table[string, seq[FznExpr]],
                   name: string, args: seq[FznExpr]) =
        case name
        of "seq_search", "warm_start_array":
            if name == "seq_search" and args.len > 0 and args[0].kind == FznArrayLit:
                for sub in args[0].elems:
                    if sub.kind == FznAnnotationExpr:
                        addSearch(tr, plan, varArrays, sub.annName, sub.annArgs)
        of "int_search", "bool_search":
            if args.len < 3: return
            var bad = ""
            let vs = argVars(tr, plan, varArrays, args[0], bad)
            if bad != "": return
            let vsel = case annName(args[1])
                of "input_order": vsInputOrder
                of "anti_first_fail": vsAntiFirstFail
                of "smallest": vsSmallest
                of "largest": vsLargest
                else: vsFirstFail
            let valsel = case annName(args[2])
                of "indomain_max": valMax
                of "indomain_split", "indomain_interval": valSplit
                of "indomain_reverse_split": valReverseSplit
                else: valMin
            plan.s.addBranchGroup(vs, vsel, valsel)
        else: discard
    for ann in tr.model.solve.annotations:
        addSearch(tr, plan, varArrays, ann.name, ann.args)
    plan

const CpStallMinSecs = 2.0   # see CpSolver.solve: depth-stall cutoff floor
const CpShaveShare = 0.25    # share of the seed budget for root shaving

type CpPositionMap = object
    defaults: seq[int]            # value per position (first domain value)
    posVar: seq[(int, int)]       # (position, engine variable)
    posDom: seq[seq[int]]         # position domains, parallel to posVar

proc cpPositionMap(tr: FznTranslator, plan: CpPlan): CpPositionMap =
    result.defaults = newSeq[int](tr.sys.baseArray.len)
    for p in 0 ..< result.defaults.len:
        let d {.cursor.} = tr.sys.baseArray.domain[p]
        result.defaults[p] = if d.len > 0: d[0] else: 0
    for name, v in plan.varOf:
        if name notin tr.varPositions: continue
        let p = tr.varPositions[name]
        if p < 0 or p >= result.defaults.len or tr.sys.baseArray.domain[p].len == 0: continue
        result.posVar.add (p, v)
    for (p, v) in result.posVar: result.posDom.add tr.sys.baseArray.domain[p]

proc toAssignment(m: CpPositionMap, value: proc(v: int): int): seq[int] =
    ## Engine values -> a position assignment (nearest domain value)
    result = m.defaults
    for k, (p, v) in m.posVar:
        let x = value(v)
        let d {.cursor.} = m.posDom[k]
        var bestV = d[0]
        for y in d:
            if abs(y - x) < abs(bestV - x): bestV = y
        result[p] = bestV

proc cpSeedFirst*(tr: var FznTranslator, verbose: bool,
                  known: Table[string, int] = initTable[string, int]()):
                  proc(budget: float): tuple[seed: seq[int], later: bool] {.closure.} =
    ## The DFS as a seed source for the first resolve (nil when the engine
    ## has no propagator for some constraint of the model). known: a
    ## solution of the FlatZinc model by variable name (cpRefute's). With a
    ## DFS solution, the seed is the one of the better objective
    ## (community-detection mexican: the DFS's 466964 leads LNS to the
    ## optimum, the refutation's 85314 does not; rect-euler british_isles:
    ## the refutation's 2742 leads to the optimum 2702, the DFS's 3029 to
    ## 2707-2736). Without one, known is a later seed on optimization
    ## problems: used only when local search finds nothing of its own
    ## (rect-euler EU).
    let t0 = epochTime()
    let sol = tr.model.solve
    let objName = if sol.kind != Satisfy and sol.objective != nil and sol.objective.kind == FznIdent:
                      sol.objective.ident else: ""
    var plan = tr.buildCpModel()
    if plan.unsupported != "":
        if verbose: stderr.writeLine(&"[CP] skipped: {plan.unsupported}")
        return nil
    # Position mapping, so the search needs nothing from the translator
    let m = tr.cpPositionMap(plan)
    if verbose:
        let dl = if plan.dlNodes > 0: &", difference logic over {plan.dlNodes - 1}" else: ""
        stderr.writeLine(&"[CP] ready: {plan.s.numVars} variables{dl} ({epochTime() - t0:.2f}s)")
    let deferKnown = sol.kind != Satisfy   # a satisfaction problem's is an answer
    result = proc(budget: float): tuple[seed: seq[int], later: bool] =
        proc fromKnown(later = deferKnown): seq[int] =
            if known.len == 0: return @[]
            var val = newSeq[int](plan.s.numVars)
            for v in 0 ..< val.len: val[v] = plan.s.lo(v)
            for name, v in plan.varOf:
                if name in known: val[v] = known[name]
            if verbose:
                let what = if later: "later seed" else: "seed"
                stderr.writeLine(&"[CP] {what}: the refutation's solution ({known.len} variables)")
            m.toAssignment(proc(v: int): int = val[v])
        let t1 = epochTime()
        let shaved = plan.s.shaveBounds(deadline = t1 + budget * CpShaveShare)
        if verbose:
            stderr.writeLine(&"[CP] root shaving: {shaved} values removed ({epochTime() - t1:.2f}s)")
        if shaved < 0: return (fromKnown(), deferKnown)
        let st = plan.s.solve(deadline = t1 + budget, stallMin = CpStallMinSecs)
        if verbose or st == cpSat:
            let why = if plan.s.stalled: " (depth stalled)" else: ""
            stderr.writeLine(&"[CP] DFS {st}{why}: {plan.s.nodes} nodes, {plan.s.fails} fails, " &
                             &"depth {plan.s.maxDepth}, {epochTime() - t1:.2f}s")
        if st != cpSat: return (fromKnown(), deferKnown)
        let s = plan.s
        if objName in known and objName in plan.varOf:
            let mine = s.value(plan.varOf[objName])
            let theirs = known[objName]
            if (if sol.kind == Minimize: theirs < mine else: theirs > mine):
                if verbose: stderr.writeLine(&"[CP] refutation's objective {theirs} beats the DFS's {mine}")
                return (fromKnown(later = false), false)
        (m.toAssignment(proc(v: int): int = s.value(v)), false)

import std/random

const
    CpLnsMaxNodes = 2000        # nodes per neighbourhood search
    CpLnsStallMin = 3.0         # a phase ends after max(this, half its improving time) without a gain
    CpLnsFracStart = 0.2        # share of the decision variables freed per neighbourhood
    # A gain counts as progress (resets the stall clock) only when it moves the
    # objective by this share of its magnitude since the last such gain, and a
    # phase's result is returned only when it beats the incumbent by as much:
    # spot5 1504 crept 285544 -> 285493 in 40 s, and adopting that state turned
    # on the ladder's objective annealing (worse there: 175361 vs 165999 mean
    # over 3 runs at 300 s), where local search alone reaches 191375 in one probe.
    CpLnsMinGain = 0.001
    CpLnsDlNodes = 200          # LP nodes per orientation neighbourhood
    CpLnsDlFracStart = 0.15     # share of the disjunctions an orientation neighbourhood re-decides
    CpLnsDlStallIts = 100       # orientation neighbourhoods: a stall also needs this many without a gain

proc cpImproveLns*(tr: var FznTranslator, verbose: bool): proc(incumbent: seq[int], budget: float): seq[int] {.closure.} =
    ## Large neighbourhood search with the propagation engine, for the
    ## optimizer (nil when the model is unsupported or has no objective
    ## variable). Each neighbourhood keeps a random share of the decision
    ## variables (the solve annotation's search lists) at the incumbent's
    ## values, requires a strictly better objective and runs a node-limited
    ## DFS over the rest; the share freed grows when neighbourhoods are proved
    ## empty and shrinks when the search runs out of nodes. kitchen at 300 s
    ## -p 4: tall_complex 409 (optimal), larger 465 of 470, linear 501 of
    ## 516, real_b1 802 of 852, b1 9351 of 9942, where local search alone
    ## reached 255 / 422 / 277 / 431 / 5200. A phase ends on its
    ## budget or once it stops improving; the incumbent comes from the caller
    ## (imported when it propagates), else from a DFS of the engine's own.
    let sol = tr.model.solve
    if sol.kind == Satisfy or sol.objective == nil or sol.objective.kind != FznIdent: return nil
    var plan = tr.buildCpModel()
    if plan.unsupported != "" or sol.objective.ident notin plan.varOf: return nil
    let s = plan.s
    let obj = plan.varOf[sol.objective.ident]
    let maximize = sol.kind == Maximize
    let dvars = s.groupVars()
    if dvars.len == 0: return nil
    let m = tr.cpPositionMap(plan)
    var isDvar = newSeq[bool](s.numVars)
    for v in dvars: isDvar[v] = true
    var ready = false
    var rootOk = true
    var cur: seq[int]          # engine incumbent (all variables), empty until known
    var rng = initRand(0x5eed)
    var frac = CpLnsFracStart
    var orient: DlOrient        # orientation neighbourhoods (difference-logic models)
    var disjOfNode: seq[seq[int]]
    var oFrac = CpLnsDlFracStart
    proc better(a, b: int): bool = (if maximize: a > b else: a < b)
    proc significant(a, b: int): bool =
        ## a improves on b by at least CpLnsMinGain of b's magnitude (and by 1)
        float(abs(a - b)) >= max(1.0, CpLnsMinGain * abs(float(b)))
    proc record() =
        cur.setLen s.numVars
        for v in 0 ..< s.numVars: cur[v] = s.value(v)
    result = proc(incumbent: seq[int], budget: float): seq[int] =
        let t0 = epochTime()
        let deadline = t0 + budget
        if not ready:
            ready = true
            # Orientation neighbourhoods need no shaving: their LP moves every
            # variable at once (rect-euler EU: 10 s of a 120 s run's LNS
            # budget, 8418 vs 8541 without it)
            rootOk = s.prepare()
            if rootOk:
                orient = s.dlOrientation(obj, maximize)
                if orient == nil:
                    rootOk = s.shaveBounds(deadline = t0 + budget * CpShaveShare) >= 0 and s.prepare()
            if orient != nil:
                for k, ns in orient.disjNodes:
                    for nd in ns:
                        if nd >= disjOfNode.len: disjOfNode.setLen nd + 1
                        disjOfNode[nd].add k
            if verbose and not rootOk: stderr.writeLine("[CP] LNS: root infeasible")
        if not rootOk: return @[]
        # Import the caller's incumbent: its decision values, completed by a DFS
        var startObj = 0
        var haveStart = false
        if incumbent.len == m.defaults.len:
            s.pushAssume()
            var ok = true
            for (p, v) in m.posVar:
                if isDvar[v] and not s.assign(v, incumbent[p]):
                    ok = false
                    break
            var stage = (if ok: "propagate" else: "assign")
            if ok and s.propagate():
                stage = "search"
                if s.search(deadline = deadline, maxNodes = CpLnsMaxNodes) == cpSat:
                    stage = ""
                    startObj = s.value(obj)
                    haveStart = true
                    if cur.len == 0 or not better(cur[obj], startObj): record()
            if verbose and stage != "":
                stderr.writeLine(&"[CP] LNS: incumbent import failed at {stage}")
            s.popTo(0)
        if cur.len == 0:
            if s.search(deadline = deadline, stallMin = CpStallMinSecs) != cpSat:
                if verbose: stderr.writeLine("[CP] LNS: no start (import and DFS failed)")
                return @[]
            record()
            s.popTo(0)
        let from0 = cur[obj]
        # The stall clock starts after shaving and the import, which can take
        # longer than the stall limit on large models
        let tLoop = epochTime()
        var lastGain = tLoop
        var lastSig = cur[obj]      # objective at the last gain that counted as progress
        var its, gains = 0
        var lastGainIt = 0          # neighbourhood of the last gain that counted as progress
        while true:
            let now = epochTime()
            if now > deadline or (now - lastGain > max(CpLnsStallMin, 0.5 * (lastGain - tLoop)) and
                                  (orient == nil or its - lastGainIt >= CpLnsDlStallIts)): break
            inc its
            if orient != nil:
                # Re-decide the disjunctions around a few random ones, every
                # variable free (the first neighbourhood re-decides none: the
                # LP placement of the incumbent's own orientation)
                var free = newSeq[bool](orient.disj.len)
                if its > 1:
                    let target = max(1, int(oFrac * float(free.len)))
                    var cnt = 0
                    while cnt < target:
                        for nd in orient.disjNodes[rng.rand(free.len - 1)]:
                            for k in disjOfNode[nd]:
                                if not free[k]:
                                    free[k] = true
                                    inc cnt
                var used = 0
                let vals = s.dlImprove(orient, cur, free, CpLnsDlNodes, deadline, used)
                if vals.len > 0:
                    cur = vals
                    inc gains
                    if significant(cur[obj], lastSig):
                        lastSig = cur[obj]
                        lastGain = epochTime()
                        lastGainIt = its
                elif used < CpLnsDlNodes: oFrac = min(0.9, oFrac * 1.1)
                else: oFrac = max(0.005, oFrac / 1.1)
                continue
            s.pushAssume()
            var ok = (if maximize: s.setMin(obj, cur[obj] + 1) else: s.setMax(obj, cur[obj] - 1))
            if ok:
                for v in dvars:
                    if rng.rand(1.0) >= frac and not s.assign(v, cur[v]):
                        ok = false
                        break
            let st = if ok and s.propagate(): s.search(deadline = deadline, maxNodes = CpLnsMaxNodes)
                     else: cpUnsat
            case st
            of cpSat:
                record()
                inc gains
                if significant(cur[obj], lastSig):
                    lastSig = cur[obj]
                    lastGain = epochTime()
            of cpUnsat: frac = min(0.9, frac * 1.05)
            of cpLimit: frac = max(0.02, frac / 1.05)
            s.popTo(0)
        if verbose:
            let start = if haveStart: $startObj else: "not imported"
            stderr.writeLine(&"[CP] LNS: {from0} -> {cur[obj]} (incumbent {start}), {gains} gains in {its} " &
                             &"neighbourhoods, free share {frac:.2f}, {epochTime() - t0:.2f}s " &
                             &"({tLoop - t0:.2f}s setup)")
            if orient != nil:
                stderr.writeLine(&"[CP] LNS orientations: {orient.disj.len} disjunctions, share {oFrac:.3f}, " &
                                 &"{orient.bbNodes} nodes, {orient.lps} LPs, {orient.leaves} leaves " &
                                 &"({orient.leafFails} failed)")
        if haveStart and not (better(cur[obj], startObj) and significant(cur[obj], startObj)): return @[]
        let snapshot = cur
        m.toAssignment(proc(v: int): int = snapshot[v])

proc cpRefutable*(model: FznModel): bool =
    ## Every constraint of the (untranslated) model has a propagator and no
    ## variable is a set: worth calling cpRefute (which checks the rest).
    for con in model.constraints:
        if stripSolverPrefix(con.name) notin CpSupported: return false
    for decl in model.variables:
        if decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}: return false
    true

proc cpRefute*(filename: string, deadline: float, verbose: bool,
               found: var Table[string, int]): bool =
    ## True when the propagation engine proves the FlatZinc model in filename
    ## unsatisfiable (false: a solution exists, the model is unsupported or
    ## time ran out; when the search found a solution, found holds its value
    ## per FlatZinc variable name). Sound by construction, so the caller may print
    ## UNSATISFIABLE: the file is parsed afresh
    ## (translation rewrites the parsed model and presolve tightens domains,
    ## neither of which a proof may rest on), parameters are its literal
    ## values, variables keep their declared domains (declined when one has
    ## no bounds), arithmetic must fit int64 over those domains, and the
    ## search (after root shaving) is complete: dom/wdeg on bounds with
    ## growing Luby restarts (CpSolver.refute). Proves gcc-benchmark l35_1 at
    ## the root; l42_3 (triangle-free conflicts, every day matchable) needs
    ## clause learning, not found in 300 s.
    let t0 = epochTime()
    var pt: FznTranslator
    try:
        pt.model = parseFznFile(filename)
        pt.translateParameters()
    except CatchableError:
        return false
    var plan = pt.buildCpModel(strict = true)
    if plan.unsupported != "":
        if verbose: stderr.writeLine(&"[CP] refutation skipped: {plan.unsupported}")
        return false
    if not plan.s.arithmeticSafe():
        if verbose: stderr.writeLine("[CP] refutation skipped: arithmetic may overflow")
        return false
    let shaved = plan.s.shaveBounds(deadline = t0 + CpShaveShare * (deadline - t0))
    let st = if shaved < 0: cpUnsat else: plan.s.refute(deadline = deadline)
    if verbose:
        stderr.writeLine(&"[CP] refutation: {st} ({plan.s.numVars} variables, dl {plan.dlNodes}, {plan.s.nodes} nodes, " &
                         &"{plan.s.fails} fails, {epochTime() - t0:.2f}s)")
    if st == cpSat:
        found.clear()
        for name, v in plan.varOf: found[name] = plan.s.value(v)
    st == cpUnsat
