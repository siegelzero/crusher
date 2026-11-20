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
    "set_in", "set_in_reif", "set_in_imp", "fzn_regular"]

type CpPlan = object
    s: CpSolver
    varOf: Table[string, int]       # FZN scalar variable -> engine variable
    unsupported: string

proc buildCpModel(tr: var FznTranslator): CpPlan =
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
        if decl.name in tr.presolveDomains:
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
        else:
            decline(name)

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

proc cpSeedFirst*(tr: var FznTranslator, verbose: bool): proc(budget: float): seq[int] {.closure.} =
    ## The DFS as a seed source for the first resolve (nil when the engine
    ## has no propagator for some constraint of the model).
    let t0 = epochTime()
    var plan = tr.buildCpModel()
    if plan.unsupported != "":
        if verbose: stderr.writeLine(&"[CP] skipped: {plan.unsupported}")
        return nil
    # Position mapping, so the search needs nothing from the translator
    var defaults = newSeq[int](tr.sys.baseArray.len)
    for p in 0 ..< defaults.len:
        let d {.cursor.} = tr.sys.baseArray.domain[p]
        defaults[p] = if d.len > 0: d[0] else: 0
    var posVar: seq[(int, int)]     # (position, engine variable)
    for name, v in plan.varOf:
        if name notin tr.varPositions: continue
        let p = tr.varPositions[name]
        if p < 0 or p >= defaults.len or tr.sys.baseArray.domain[p].len == 0: continue
        posVar.add (p, v)
    var posDom: seq[seq[int]]
    for (p, v) in posVar: posDom.add tr.sys.baseArray.domain[p]
    if verbose:
        stderr.writeLine(&"[CP] ready: {plan.s.numVars} variables ({epochTime() - t0:.2f}s)")
    result = proc(budget: float): seq[int] =
        let t1 = epochTime()
        let st = plan.s.solve(deadline = t1 + budget, stallMin = CpStallMinSecs)
        if verbose or st == cpSat:
            let why = if plan.s.stalled: " (depth stalled)" else: ""
            stderr.writeLine(&"[CP] DFS {st}{why}: {plan.s.nodes} nodes, {plan.s.fails} fails, " &
                             &"depth {plan.s.maxDepth}, {epochTime() - t1:.2f}s")
        if st != cpSat: return @[]
        result = defaults
        for k, (p, v) in posVar:
            let x = plan.s.value(v)
            let d {.cursor.} = posDom[k]
            var bestV = d[0]
            for y in d:
                if abs(y - x) < abs(bestV - x): bestV = y
            result[p] = bestV
