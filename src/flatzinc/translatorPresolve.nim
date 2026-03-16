## Included from translator.nim -- not a standalone module.
## Translation-time propagation loop (presolve): fixes singletons, simplifies
## constraints, propagates domains, resolves reifications, and eliminates dead
## constraints before the main translation pipeline runs.

func psFloorDiv(a, b: int): int {.inline.} =
    ## floor(a / b) for b > 0
    assert b > 0, "psFloorDiv requires b > 0"
    if a >= 0: a div b
    else: -((-a + b - 1) div b)

func psCeilDiv(a, b: int): int {.inline.} =
    ## ceil(a / b) for b > 0
    assert b > 0, "psCeilDiv requires b > 0"
    if a >= 0: (a + b - 1) div b
    else: -((-a) div b)

proc initPresolveDomains(tr: FznTranslator): Table[string, seq[int]] =
    ## Build domain table from model variable declarations + already-fixed params.
    result = initTable[string, seq[int]]()
    for decl in tr.model.variables:
        if decl.isArray: continue
        # Variables with assigned literal values are already fixed
        if decl.value != nil:
            case decl.value.kind
            of FznIntLit:
                result[decl.name] = @[decl.value.intVal]
                continue
            of FznBoolLit:
                result[decl.name] = @[if decl.value.boolVal: 1 else: 0]
                continue
            else: discard
        case decl.varType.kind
        of FznIntRange:
            result[decl.name] = toSeq(decl.varType.lo..decl.varType.hi)
        of FznIntSet:
            result[decl.name] = decl.varType.values.sorted()
        of FznBool:
            result[decl.name] = @[0, 1]
        of FznInt:
            # Unbounded int -- skip, can't propagate
            discard
        else:
            # Set types handled elsewhere
            discard

proc presolveIsFixed(tr: FznTranslator, arg: FznExpr,
                     fixedVars: Table[string, int]): bool =
    case arg.kind
    of FznIntLit, FznBoolLit: return true
    of FznIdent:
        return arg.ident in tr.paramValues or arg.ident in fixedVars
    else: return false

proc presolveResolve(tr: FznTranslator, arg: FznExpr,
                     fixedVars: Table[string, int]): int =
    case arg.kind
    of FznIntLit: return arg.intVal
    of FznBoolLit: return if arg.boolVal: 1 else: 0
    of FznIdent:
        if arg.ident in fixedVars: return fixedVars[arg.ident]
        if arg.ident in tr.paramValues: return tr.paramValues[arg.ident]
        raise newException(KeyError, "presolveResolve: not fixed: " & arg.ident)
    else:
        raise newException(ValueError, "presolveResolve: unexpected kind")

proc presolveVarName(arg: FznExpr): string =
    ## Extract variable name from an FznExpr, or "" if not an ident.
    if arg.kind == FznIdent: arg.ident else: ""

proc presolveTightenDomain(domains: var Table[string, seq[int]],
                           varName: string, allowed: seq[int],
                           infeasible: var bool): bool =
    ## Intersect a variable's domain with `allowed`. Returns true if domain changed.
    ## Sets infeasible=true if the domain becomes empty.
    if varName notin domains: return false
    let oldDom = domains[varName]
    let allowedSet = allowed.toPackedSet()
    var newDom: seq[int]
    for v in oldDom:
        if v in allowedSet:
            newDom.add(v)
    if newDom.len < oldDom.len:
        domains[varName] = newDom
        if newDom.len == 0:
            infeasible = true
        return true
    return false

proc presolveRemoveValue(domains: var Table[string, seq[int]],
                         varName: string, value: int,
                         infeasible: var bool): bool =
    ## Remove a single value from a variable's domain. Returns true if domain changed.
    ## Sets infeasible=true if the domain becomes empty.
    if varName notin domains: return false
    let oldDom = domains[varName]
    var newDom: seq[int]
    for v in oldDom:
        if v != value:
            newDom.add(v)
    if newDom.len < oldDom.len:
        domains[varName] = newDom
        if newDom.len == 0:
            infeasible = true
        return true
    return false

proc presolveRestrictBounds(domains: var Table[string, seq[int]],
                            varName: string, lo, hi: int,
                            infeasible: var bool): bool =
    ## Remove values outside [lo, hi] from domain. Returns true if domain changed.
    ## Sets infeasible=true if the domain becomes empty.
    if varName notin domains: return false
    let oldDom = domains[varName]
    var newDom: seq[int]
    for v in oldDom:
        if v >= lo and v <= hi:
            newDom.add(v)
    if newDom.len < oldDom.len:
        domains[varName] = newDom
        if newDom.len == 0:
            infeasible = true
        return true
    return false

proc canEliminate(con: FznConstraint): bool {.inline.} =
    ## Returns true if a constraint can be eliminated by presolve.
    ## Only eliminate constraints where ALL arguments are constants/params —
    ## constraints with any variable argument may be needed by the pattern
    ## detection pipeline for channel building, even if trivially satisfied.
    ## Also never eliminate defines_var constraints.
    if con.hasAnnotation("defines_var"): return false
    for arg in con.args:
        if arg.kind == FznIdent: return false
        if arg.kind == FznArrayLit:
            for e in arg.elems:
                if e.kind == FznIdent: return false
    return true

proc fixSingletons(domains: Table[string, seq[int]],
                   fixedVars: var Table[string, int]): bool =
    ## Scan domains for singletons and add them to fixedVars.
    result = false
    for name, dom in domains:
        if dom.len == 1 and name notin fixedVars:
            fixedVars[name] = dom[0]
            result = true

proc simplifyConstraints(tr: FznTranslator,
                         domains: var Table[string, seq[int]],
                         fixedVars: var Table[string, int],
                         eliminated: var PackedSet[int],
                         infeasible: var bool): bool =
    ## Substitute fixed values into constraints and simplify.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)

        # --- int_eq(a, b) ---
        if name == "int_eq" and con.args.len >= 2:
            let aFixed = tr.presolveIsFixed(con.args[0], fixedVars)
            let bFixed = tr.presolveIsFixed(con.args[1], fixedVars)
            if aFixed and bFixed:
                # Both fixed: verify and eliminate
                if con.canEliminate:
                    eliminated.incl(ci)
                    result = true
            elif aFixed:
                let val = tr.presolveResolve(con.args[0], fixedVars)
                let vn = presolveVarName(con.args[1])
                if vn != "":
                    if presolveTightenDomain(domains, vn, @[val], infeasible):
                        result = true
            elif bFixed:
                let val = tr.presolveResolve(con.args[1], fixedVars)
                let vn = presolveVarName(con.args[0])
                if vn != "":
                    if presolveTightenDomain(domains, vn, @[val], infeasible):
                        result = true

        # --- int_ne(a, b) ---
        elif name == "int_ne" and con.args.len >= 2:
            let aFixed = tr.presolveIsFixed(con.args[0], fixedVars)
            let bFixed = tr.presolveIsFixed(con.args[1], fixedVars)
            if aFixed and bFixed:
                if con.canEliminate:
                    eliminated.incl(ci)
                    result = true
            elif aFixed:
                let val = tr.presolveResolve(con.args[0], fixedVars)
                let vn = presolveVarName(con.args[1])
                if vn != "":
                    if presolveRemoveValue(domains, vn, val, infeasible):
                        result = true
            elif bFixed:
                let val = tr.presolveResolve(con.args[1], fixedVars)
                let vn = presolveVarName(con.args[0])
                if vn != "":
                    if presolveRemoveValue(domains, vn, val, infeasible):
                        result = true

        # --- int_le(a, b): a <= b ---
        elif name == "int_le" and con.args.len >= 2:
            let aFixed = tr.presolveIsFixed(con.args[0], fixedVars)
            let bFixed = tr.presolveIsFixed(con.args[1], fixedVars)
            if aFixed and bFixed:
                if con.canEliminate:
                    eliminated.incl(ci)
                    result = true
            elif aFixed:
                let val = tr.presolveResolve(con.args[0], fixedVars)
                let vn = presolveVarName(con.args[1])
                if vn != "":
                    if presolveRestrictBounds(domains, vn, val, high(int), infeasible):
                        result = true
            elif bFixed:
                let val = tr.presolveResolve(con.args[1], fixedVars)
                let vn = presolveVarName(con.args[0])
                if vn != "":
                    if presolveRestrictBounds(domains, vn, low(int), val, infeasible):
                        result = true

        # --- int_lt(a, b): a < b ---
        elif name == "int_lt" and con.args.len >= 2:
            let aFixed = tr.presolveIsFixed(con.args[0], fixedVars)
            let bFixed = tr.presolveIsFixed(con.args[1], fixedVars)
            if aFixed and bFixed:
                if con.canEliminate:
                    eliminated.incl(ci)
                    result = true
            elif aFixed:
                let val = tr.presolveResolve(con.args[0], fixedVars)
                let vn = presolveVarName(con.args[1])
                if vn != "":
                    if presolveRestrictBounds(domains, vn, val + 1, high(int), infeasible):
                        result = true
            elif bFixed:
                let val = tr.presolveResolve(con.args[1], fixedVars)
                let vn = presolveVarName(con.args[0])
                if vn != "":
                    if presolveRestrictBounds(domains, vn, low(int), val - 1, infeasible):
                        result = true

        # --- set_in(x, S) where S is constant ---
        elif name == "set_in" and con.args.len >= 2:
            let xn = presolveVarName(con.args[0])
            if xn != "" and con.args[1].kind in {FznSetLit, FznRange}:
                let setVals = extractSetValues(con.args[1])
                if presolveTightenDomain(domains, xn, setVals, infeasible):
                    result = true
                # If x is now fixed, we can eliminate
                if xn in domains and domains[xn].len <= 1:
                    if con.canEliminate:
                        eliminated.incl(ci)
                        result = true

        # --- int_lin_eq(coeffs, vars, rhs) ---
        elif name == "int_lin_eq" and con.args.len >= 3:
            if con.args[0].kind == FznArrayLit and con.args[1].kind == FznArrayLit:
                let nArgs = con.args[0].elems.len
                if nArgs == con.args[1].elems.len and
                        tr.presolveIsFixed(con.args[2], fixedVars):
                    var rhs = tr.presolveResolve(con.args[2], fixedVars)
                    var unfixedIdx = -1
                    var unfixedCoeff = 0
                    var unfixedName = ""
                    var nUnfixed = 0
                    var allFixed = true
                    for i in 0..<nArgs:
                        let cExpr = con.args[0].elems[i]
                        let vExpr = con.args[1].elems[i]
                        if cExpr.kind != FznIntLit: allFixed = false; break
                        let c = cExpr.intVal
                        if tr.presolveIsFixed(vExpr, fixedVars):
                            rhs -= c * tr.presolveResolve(vExpr, fixedVars)
                        else:
                            inc nUnfixed
                            unfixedIdx = i
                            unfixedCoeff = c
                            unfixedName = presolveVarName(vExpr)
                    if allFixed and nUnfixed == 0:
                        # All fixed: verify and eliminate
                        if con.canEliminate:
                            eliminated.incl(ci)
                            result = true
                    elif allFixed and nUnfixed == 1 and unfixedCoeff != 0 and unfixedName != "":
                        # One unfixed variable: c*x = rhs => x = rhs/c
                        if rhs mod unfixedCoeff == 0:
                            let val = rhs div unfixedCoeff
                            if presolveTightenDomain(domains, unfixedName, @[val], infeasible):
                                result = true

        # --- int_lin_le(coeffs, vars, rhs): sum(c_i * x_i) <= rhs ---
        elif name == "int_lin_le" and con.args.len >= 3:
            if con.args[0].kind == FznArrayLit and con.args[1].kind == FznArrayLit:
                let nArgs = con.args[0].elems.len
                if nArgs == con.args[1].elems.len and
                        tr.presolveIsFixed(con.args[2], fixedVars):
                    var rhs = tr.presolveResolve(con.args[2], fixedVars)
                    var allFixed = true
                    var nUnfixed = 0
                    # First check all coeffs are literals
                    for i in 0..<nArgs:
                        if con.args[0].elems[i].kind != FznIntLit:
                            allFixed = false; break
                        if not tr.presolveIsFixed(con.args[1].elems[i], fixedVars):
                            inc nUnfixed
                    if allFixed and nUnfixed == 0:
                        if con.canEliminate:
                            eliminated.incl(ci)
                            result = true

proc boundsPropagate(tr: FznTranslator,
                     domains: var Table[string, seq[int]],
                     fixedVars: Table[string, int],
                     eliminated: PackedSet[int],
                     infeasible: var bool): bool =
    ## Linear bounds propagation: for int_lin_le and int_lin_eq, compute
    ## tightest bounds on each unfixed variable from other variables' domain bounds.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        let isEq = name == "int_lin_eq"
        let isLe = name == "int_lin_le"
        if not isEq and not isLe: continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznArrayLit or con.args[1].kind != FznArrayLit: continue
        let nArgs = con.args[0].elems.len
        if nArgs != con.args[1].elems.len: continue
        if not tr.presolveIsFixed(con.args[2], fixedVars): continue

        let rhs = tr.presolveResolve(con.args[2], fixedVars)

        # Collect coefficients and domain bounds
        type VarInfo = object
            coeff: int
            varName: string
            fixed: bool
            fixedVal: int
            lo, hi: int
        var vars = newSeq[VarInfo](nArgs)
        var valid = true
        for i in 0..<nArgs:
            if con.args[0].elems[i].kind != FznIntLit:
                valid = false; break
            vars[i].coeff = con.args[0].elems[i].intVal
            let vExpr = con.args[1].elems[i]
            vars[i].varName = presolveVarName(vExpr)
            if tr.presolveIsFixed(vExpr, fixedVars):
                vars[i].fixed = true
                vars[i].fixedVal = tr.presolveResolve(vExpr, fixedVars)
                vars[i].lo = vars[i].fixedVal
                vars[i].hi = vars[i].fixedVal
            else:
                vars[i].fixed = false
                if vars[i].varName in domains:
                    let dom = domains[vars[i].varName]
                    if dom.len == 0:
                        valid = false; break
                    vars[i].lo = dom[0]   # sorted, so min
                    vars[i].hi = dom[^1]  # sorted, so max
                else:
                    valid = false; break
        if not valid: continue

        # For sum(c_i * x_i) <= rhs (or == rhs):
        # For each variable j, compute: c_j * x_j <= rhs - sum_{i!=j} min(c_i * x_i)
        # min(c_i * x_i) = c_i * lo_i if c_i > 0, c_i * hi_i if c_i < 0
        var totalMinContrib = 0
        var totalMaxContrib = 0
        for i in 0..<nArgs:
            let c = vars[i].coeff
            if c > 0:
                totalMinContrib += c * vars[i].lo
                totalMaxContrib += c * vars[i].hi
            elif c < 0:
                totalMinContrib += c * vars[i].hi
                totalMaxContrib += c * vars[i].lo
            # c == 0 contributes nothing

        for j in 0..<nArgs:
            if vars[j].fixed: continue
            if vars[j].varName == "": continue
            let c = vars[j].coeff
            if c == 0: continue

            # min contribution of others = totalMinContrib - min contribution of j
            var jMinContrib, jMaxContrib: int
            if c > 0:
                jMinContrib = c * vars[j].lo
                jMaxContrib = c * vars[j].hi
            else:
                jMinContrib = c * vars[j].hi
                jMaxContrib = c * vars[j].lo
            let othersMin = totalMinContrib - jMinContrib
            let othersMax = totalMaxContrib - jMaxContrib

            # From sum <= rhs: c_j * x_j <= rhs - othersMin
            # If c_j > 0: x_j <= (rhs - othersMin) / c_j  (floor)
            # If c_j < 0: x_j >= (rhs - othersMin) / c_j  (ceil)
            if isLe or isEq:
                let slack = rhs - othersMin
                if c > 0:
                    # x_j <= floor(slack / c)
                    let upperBound = psFloorDiv(slack, c)
                    if presolveRestrictBounds(domains, vars[j].varName,
                                              low(int), upperBound, infeasible):
                        result = true
                        # Update local bounds for subsequent iterations within this constraint
                        vars[j].hi = min(vars[j].hi, upperBound)
                elif c < 0:
                    # c_j * x_j <= slack, c_j < 0 => x_j >= ceil(slack / c_j)
                    # ceil(a/b) for b < 0 = -floor(a / |b|)
                    let lowerBound = -psFloorDiv(slack, -c)
                    if presolveRestrictBounds(domains, vars[j].varName,
                                              lowerBound, high(int), infeasible):
                        result = true
                        vars[j].lo = max(vars[j].lo, lowerBound)

            # For equality: also sum >= rhs, i.e. -sum <= -rhs
            # c_j * x_j >= rhs - othersMax
            if isEq:
                let slack2 = rhs - othersMax
                if c > 0:
                    # x_j >= ceil(slack2 / c)
                    let lowerBound = psCeilDiv(slack2, c)
                    if presolveRestrictBounds(domains, vars[j].varName,
                                              lowerBound, high(int), infeasible):
                        result = true
                        vars[j].lo = max(vars[j].lo, lowerBound)
                elif c < 0:
                    # x_j <= floor(slack2 / c_j) for c_j < 0 = -ceil(slack2 / |c_j|)
                    let upperBound = -psCeilDiv(slack2, -c)
                    if presolveRestrictBounds(domains, vars[j].varName,
                                              low(int), upperBound, infeasible):
                        result = true
                        vars[j].hi = min(vars[j].hi, upperBound)

proc allDiffPropagate(tr: FznTranslator,
                      domains: var Table[string, seq[int]],
                      fixedVars: Table[string, int],
                      eliminated: PackedSet[int],
                      infeasible: var bool): bool =
    ## For allDifferent constraints, remove fixed values from other variables' domains.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_all_different_int": continue
        if con.args.len < 1: continue
        let elems = if con.args[0].kind == FznArrayLit: con.args[0].elems
                    else: @[]
        if elems.len == 0: continue

        # Collect fixed values
        var fixedValues: seq[int]
        for e in elems:
            if tr.presolveIsFixed(e, fixedVars):
                fixedValues.add(tr.presolveResolve(e, fixedVars))
            elif e.kind == FznIdent and e.ident in domains and domains[e.ident].len == 1:
                fixedValues.add(domains[e.ident][0])

        # Remove each fixed value from unfixed variables' domains
        for fv in fixedValues:
            for e in elems:
                let vn = presolveVarName(e)
                if vn != "" and vn notin fixedVars:
                    if vn in domains and domains[vn].len > 1:
                        if presolveRemoveValue(domains, vn, fv, infeasible):
                            result = true

proc resolveReifications(tr: FznTranslator,
                         domains: var Table[string, seq[int]],
                         fixedVars: var Table[string, int],
                         eliminated: var PackedSet[int],
                         infeasible: var bool): bool =
    ## Check reified constraints and fix boolean result when domains determine truth value.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)

        # --- int_eq_reif(x, val_or_y, b) ---
        if name == "int_eq_reif" and con.args.len >= 3:
            let bName = presolveVarName(con.args[2])
            let bFixed = tr.presolveIsFixed(con.args[2], fixedVars) or
                         (bName != "" and bName in domains and domains[bName].len == 1)
            let bVal = if tr.presolveIsFixed(con.args[2], fixedVars):
                           tr.presolveResolve(con.args[2], fixedVars)
                       elif bName != "" and bName in domains and domains[bName].len == 1:
                           domains[bName][0]
                       else: -1

            let xName = presolveVarName(con.args[0])
            let yFixed = tr.presolveIsFixed(con.args[1], fixedVars)

            if yFixed:
                let val = tr.presolveResolve(con.args[1], fixedVars)
                let xDom = if xName != "" and xName in domains: domains[xName] else: @[]

                if xDom.len > 0:
                    let valInDom = val in xDom
                    if not valInDom and bName != "":
                        # val not in domain(x) => b = 0
                        if presolveTightenDomain(domains, bName, @[0], infeasible):
                            result = true
                    elif xDom.len == 1 and xDom[0] == val and bName != "":
                        # domain(x) == {val} => b = 1
                        if presolveTightenDomain(domains, bName, @[1], infeasible):
                            result = true

                if bFixed:
                    if bVal == 1 and xName != "":
                        # b = true => x = val
                        if presolveTightenDomain(domains, xName, @[val], infeasible):
                            result = true
                    elif bVal == 0 and xName != "":
                        # b = false => x != val
                        if presolveRemoveValue(domains, xName, val, infeasible):
                            result = true

            # Two-variable case: int_eq_reif(x, y, b) where neither is fixed
            elif not yFixed and not bFixed:
                let yName = presolveVarName(con.args[1])
                let xDom = if xName != "" and xName in domains: domains[xName] else: @[]
                let yDom = if yName != "" and yName in domains: domains[yName] else: @[]
                if xDom.len > 0 and yDom.len > 0:
                    # Check if domains are disjoint
                    let xSet = xDom.toPackedSet()
                    var disjoint = true
                    for v in yDom:
                        if v in xSet:
                            disjoint = false; break
                    if disjoint and bName != "":
                        if presolveTightenDomain(domains, bName, @[0], infeasible):
                            result = true

        # --- int_ne_reif(x, val, b) ---
        elif name == "int_ne_reif" and con.args.len >= 3:
            let bName = presolveVarName(con.args[2])
            let bFixed = tr.presolveIsFixed(con.args[2], fixedVars) or
                         (bName != "" and bName in domains and domains[bName].len == 1)
            let bVal = if tr.presolveIsFixed(con.args[2], fixedVars):
                           tr.presolveResolve(con.args[2], fixedVars)
                       elif bName != "" and bName in domains and domains[bName].len == 1:
                           domains[bName][0]
                       else: -1

            if tr.presolveIsFixed(con.args[1], fixedVars):
                let val = tr.presolveResolve(con.args[1], fixedVars)
                let xName = presolveVarName(con.args[0])
                let xDom = if xName != "" and xName in domains: domains[xName] else: @[]
                if xDom.len > 0:
                    if val notin xDom and bName != "":
                        # val not in domain => ne is always true => b = 1
                        if presolveTightenDomain(domains, bName, @[1], infeasible):
                            result = true
                    elif xDom.len == 1 and xDom[0] == val and bName != "":
                        # domain = {val} => ne is always false => b = 0
                        if presolveTightenDomain(domains, bName, @[0], infeasible):
                            result = true
                if bFixed:
                    if bVal == 1 and xName != "":
                        if presolveRemoveValue(domains, xName, val, infeasible):
                            result = true
                    elif bVal == 0 and xName != "":
                        if presolveTightenDomain(domains, xName, @[val], infeasible):
                            result = true

        # --- int_le_reif(x, y, b): b <=> (x <= y) ---
        elif name == "int_le_reif" and con.args.len >= 3:
            let bName = presolveVarName(con.args[2])
            let xName = presolveVarName(con.args[0])
            let yName = presolveVarName(con.args[1])

            # Get bounds
            var xLo, xHi, yLo, yHi: int
            var xHasDom, yHasDom: bool
            if tr.presolveIsFixed(con.args[0], fixedVars):
                let v = tr.presolveResolve(con.args[0], fixedVars)
                xLo = v; xHi = v; xHasDom = true
            elif xName != "" and xName in domains and domains[xName].len > 0:
                xLo = domains[xName][0]; xHi = domains[xName][^1]; xHasDom = true
            if tr.presolveIsFixed(con.args[1], fixedVars):
                let v = tr.presolveResolve(con.args[1], fixedVars)
                yLo = v; yHi = v; yHasDom = true
            elif yName != "" and yName in domains and domains[yName].len > 0:
                yLo = domains[yName][0]; yHi = domains[yName][^1]; yHasDom = true

            if xHasDom and yHasDom and bName != "":
                if xHi <= yLo:
                    # x <= y always true
                    if presolveTightenDomain(domains, bName, @[1], infeasible):
                        result = true
                elif xLo > yHi:
                    # x <= y always false
                    if presolveTightenDomain(domains, bName, @[0], infeasible):
                        result = true

            # If b is fixed, propagate to x and y
            let bFixedNow = tr.presolveIsFixed(con.args[2], fixedVars) or
                            (bName != "" and bName in domains and domains[bName].len == 1)
            if bFixedNow and xHasDom and yHasDom:
                let bv = if tr.presolveIsFixed(con.args[2], fixedVars):
                             tr.presolveResolve(con.args[2], fixedVars)
                         else: domains[bName][0]
                if bv == 1:
                    # x <= y: restrict x <= yHi, y >= xLo
                    if xName != "":
                        if presolveRestrictBounds(domains, xName, low(int), yHi, infeasible):
                            result = true
                    if yName != "":
                        if presolveRestrictBounds(domains, yName, xLo, high(int), infeasible):
                            result = true
                else:
                    # NOT(x <= y) => x > y: x >= yLo + 1, y <= xHi - 1
                    if xName != "":
                        if presolveRestrictBounds(domains, xName, yLo + 1, high(int), infeasible):
                            result = true
                    if yName != "":
                        if presolveRestrictBounds(domains, yName, low(int), xHi - 1, infeasible):
                            result = true

        # --- int_lt_reif(x, y, b): b <=> (x < y) ---
        elif name == "int_lt_reif" and con.args.len >= 3:
            let bName = presolveVarName(con.args[2])
            let xName = presolveVarName(con.args[0])
            let yName = presolveVarName(con.args[1])

            var xLo, xHi, yLo, yHi: int
            var xHasDom, yHasDom: bool
            if tr.presolveIsFixed(con.args[0], fixedVars):
                let v = tr.presolveResolve(con.args[0], fixedVars)
                xLo = v; xHi = v; xHasDom = true
            elif xName != "" and xName in domains and domains[xName].len > 0:
                xLo = domains[xName][0]; xHi = domains[xName][^1]; xHasDom = true
            if tr.presolveIsFixed(con.args[1], fixedVars):
                let v = tr.presolveResolve(con.args[1], fixedVars)
                yLo = v; yHi = v; yHasDom = true
            elif yName != "" and yName in domains and domains[yName].len > 0:
                yLo = domains[yName][0]; yHi = domains[yName][^1]; yHasDom = true

            if xHasDom and yHasDom and bName != "":
                if xHi < yLo:
                    # x < y always true
                    if presolveTightenDomain(domains, bName, @[1], infeasible):
                        result = true
                elif xLo >= yHi:
                    # x < y always false
                    if presolveTightenDomain(domains, bName, @[0], infeasible):
                        result = true

            let bFixedNow = tr.presolveIsFixed(con.args[2], fixedVars) or
                            (bName != "" and bName in domains and domains[bName].len == 1)
            if bFixedNow and xHasDom and yHasDom:
                let bv = if tr.presolveIsFixed(con.args[2], fixedVars):
                             tr.presolveResolve(con.args[2], fixedVars)
                         else: domains[bName][0]
                if bv == 1:
                    # x < y: x <= yHi - 1, y >= xLo + 1
                    if xName != "":
                        if presolveRestrictBounds(domains, xName, low(int), yHi - 1, infeasible):
                            result = true
                    if yName != "":
                        if presolveRestrictBounds(domains, yName, xLo + 1, high(int), infeasible):
                            result = true
                else:
                    # NOT(x < y) => x >= y: x >= yLo, y <= xHi
                    if xName != "":
                        if presolveRestrictBounds(domains, xName, yLo, high(int), infeasible):
                            result = true
                    if yName != "":
                        if presolveRestrictBounds(domains, yName, low(int), xHi, infeasible):
                            result = true

        # --- set_in_reif(x, S, b) ---
        elif name == "set_in_reif" and con.args.len >= 3:
            let xName = presolveVarName(con.args[0])
            let bName = presolveVarName(con.args[2])
            # Only handle constant set argument
            if con.args[1].kind in {FznSetLit, FznRange}:
                let setVals = extractSetValues(con.args[1])
                let xDom = if xName != "" and xName in domains: domains[xName] else: @[]
                if xDom.len > 0 and bName != "":
                    let setPS = setVals.toPackedSet()
                    # Check if domain(x) is a subset of S
                    var isSubset = true
                    var isDisjoint = true
                    for v in xDom:
                        if v notin setPS: isSubset = false
                        if v in setPS: isDisjoint = false
                    if isSubset:
                        if presolveTightenDomain(domains, bName, @[1], infeasible):
                            result = true
                    elif isDisjoint:
                        if presolveTightenDomain(domains, bName, @[0], infeasible):
                            result = true

                # If b is fixed, propagate
                let bFixed = tr.presolveIsFixed(con.args[2], fixedVars) or
                             (bName != "" and bName in domains and domains[bName].len == 1)
                if bFixed and xName != "":
                    let bv = if tr.presolveIsFixed(con.args[2], fixedVars):
                                 tr.presolveResolve(con.args[2], fixedVars)
                             else: domains[bName][0]
                    if bv == 1:
                        # x in S
                        if presolveTightenDomain(domains, xName, setVals, infeasible):
                            result = true
                    else:
                        # x not in S
                        let setPS = setVals.toPackedSet()
                        if xName in domains:
                            let oldDom = domains[xName]
                            var newDom: seq[int]
                            for v in oldDom:
                                if v notin setPS:
                                    newDom.add(v)
                            if newDom.len < oldDom.len:
                                domains[xName] = newDom
                                if newDom.len == 0:
                                    infeasible = true
                                result = true
            # Also handle when x is fixed (regardless of whether S is constant)
            elif tr.presolveIsFixed(con.args[0], fixedVars):
                let xVal = tr.presolveResolve(con.args[0], fixedVars)
                if con.args[1].kind in {FznSetLit, FznRange}:
                    let setVals = extractSetValues(con.args[1])
                    let inSet = xVal in setVals
                    if bName != "":
                        if presolveTightenDomain(domains, bName,
                                                 @[if inSet: 1 else: 0], infeasible):
                            result = true

        # --- bool2int(b, x): x = b (both 0/1) ---
        elif name == "bool2int" and con.args.len >= 2:
            let bName = presolveVarName(con.args[0])
            let xName = presolveVarName(con.args[1])
            # Propagate domain intersection in both directions
            let bDom = if bName != "" and bName in domains: domains[bName] else: @[]
            let xDom = if xName != "" and xName in domains: domains[xName] else: @[]
            if bDom.len > 0 and xName != "":
                if presolveTightenDomain(domains, xName, bDom, infeasible):
                    result = true
            if xDom.len > 0 and bName != "":
                if presolveTightenDomain(domains, bName, xDom, infeasible):
                    result = true

        # --- array_bool_and(array, r) ---
        elif name == "array_bool_and" and con.args.len >= 2:
            let rName = presolveVarName(con.args[1])
            let rFixed = tr.presolveIsFixed(con.args[1], fixedVars) or
                         (rName != "" and rName in domains and domains[rName].len == 1)
            if rFixed:
                let rVal = if tr.presolveIsFixed(con.args[1], fixedVars):
                               tr.presolveResolve(con.args[1], fixedVars)
                           else: domains[rName][0]
                if con.args[0].kind == FznArrayLit:
                    if rVal == 1:
                        # AND = true => all elements are true
                        for e in con.args[0].elems:
                            let vn = presolveVarName(e)
                            if vn != "":
                                if presolveTightenDomain(domains, vn, @[1], infeasible):
                                    result = true
            # If any element is fixed to 0 => r = 0
            if con.args[0].kind == FznArrayLit and rName != "":
                for e in con.args[0].elems:
                    if tr.presolveIsFixed(e, fixedVars):
                        if tr.presolveResolve(e, fixedVars) == 0:
                            if presolveTightenDomain(domains, rName, @[0], infeasible):
                                result = true
                            break
                    elif presolveVarName(e) != "":
                        let vn = presolveVarName(e)
                        if vn in domains and domains[vn] == @[0]:
                            if presolveTightenDomain(domains, rName, @[0], infeasible):
                                result = true
                            break

        # --- array_bool_or(array, r) ---
        elif name == "array_bool_or" and con.args.len >= 2:
            let rName = presolveVarName(con.args[1])
            let rFixed = tr.presolveIsFixed(con.args[1], fixedVars) or
                         (rName != "" and rName in domains and domains[rName].len == 1)
            if rFixed:
                let rVal = if tr.presolveIsFixed(con.args[1], fixedVars):
                               tr.presolveResolve(con.args[1], fixedVars)
                           else: domains[rName][0]
                if con.args[0].kind == FznArrayLit:
                    if rVal == 0:
                        # OR = false => all elements are false
                        for e in con.args[0].elems:
                            let vn = presolveVarName(e)
                            if vn != "":
                                if presolveTightenDomain(domains, vn, @[0], infeasible):
                                    result = true
            # If any element is fixed to 1 => r = 1
            if con.args[0].kind == FznArrayLit and rName != "":
                for e in con.args[0].elems:
                    if tr.presolveIsFixed(e, fixedVars):
                        if tr.presolveResolve(e, fixedVars) == 1:
                            if presolveTightenDomain(domains, rName, @[1], infeasible):
                                result = true
                            break
                    elif presolveVarName(e) != "":
                        let vn = presolveVarName(e)
                        if vn in domains and domains[vn] == @[1]:
                            if presolveTightenDomain(domains, rName, @[1], infeasible):
                                result = true
                            break

        # --- bool_clause(pos, neg): OR(pos) v OR(NOT neg) ---
        elif name == "bool_clause" and con.args.len >= 2:
            if con.args[0].kind == FznArrayLit and con.args[1].kind == FznArrayLit:
                let posElems = con.args[0].elems
                let negElems = con.args[1].elems
                # Check if satisfied by any fixed literal
                var satisfied = false
                var unfixedPos: seq[string]
                var unfixedNeg: seq[string]
                for e in posElems:
                    if tr.presolveIsFixed(e, fixedVars):
                        if tr.presolveResolve(e, fixedVars) == 1:
                            satisfied = true; break
                    else:
                        let vn = presolveVarName(e)
                        if vn != "" and vn in domains:
                            if domains[vn] == @[1]:
                                satisfied = true; break
                            elif domains[vn] == @[0]:
                                discard  # this literal is false, skip
                            else:
                                unfixedPos.add(vn)
                if not satisfied:
                    for e in negElems:
                        if tr.presolveIsFixed(e, fixedVars):
                            if tr.presolveResolve(e, fixedVars) == 0:
                                satisfied = true; break
                        else:
                            let vn = presolveVarName(e)
                            if vn != "" and vn in domains:
                                if domains[vn] == @[0]:
                                    satisfied = true; break
                                elif domains[vn] == @[1]:
                                    discard  # NOT(1) = false, skip
                                else:
                                    unfixedNeg.add(vn)
                if satisfied:
                    if con.canEliminate:
                        eliminated.incl(ci)
                        result = true
                elif unfixedPos.len + unfixedNeg.len == 1:
                    # Unit propagation: force the one remaining literal
                    if unfixedPos.len == 1:
                        if presolveTightenDomain(domains, unfixedPos[0], @[1], infeasible):
                            result = true
                    else:
                        if presolveTightenDomain(domains, unfixedNeg[0], @[0], infeasible):
                            result = true
                elif unfixedPos.len + unfixedNeg.len == 0:
                    # All literals false — infeasible
                    infeasible = true

proc applyPresolveResults(tr: var FznTranslator,
                          domains: Table[string, seq[int]],
                          fixedVars: Table[string, int],
                          eliminated: PackedSet[int]) =
    ## Store tightened domains for use during translateVariables. Do NOT mutate
    ## the FznModel — pattern detection needs to see the original model structure.

    # Build varDomainIndex if not already built (O(V) once instead of O(V^2) per lookup)
    if tr.varDomainIndex.len == 0:
        for i, decl in tr.model.variables:
            if decl.isArray: continue
            tr.varDomainIndex[decl.name] = i

    # Store tightened domains in the translator (applied during translateVariables)
    for name, dom in domains:
        if dom.len == 0: continue
        # Check if domain was actually tightened using O(1) index lookup
        var originalLen = 0
        if name in tr.varDomainIndex:
            let decl = tr.model.variables[tr.varDomainIndex[name]]
            case decl.varType.kind
            of FznIntRange:
                originalLen = decl.varType.hi - decl.varType.lo + 1
            of FznIntSet:
                originalLen = decl.varType.values.len
            of FznBool:
                originalLen = 2
            else: discard
        if dom.len < originalLen:
            tr.presolveDomains[name] = dom

    # Mark eliminated constraints as defining (to be skipped during translation).
    for ci in eliminated:
        tr.definingConstraints.incl(ci)

proc presolve*(tr: var FznTranslator) =
    ## Main entry point: fixpoint propagation loop.
    var domains = tr.initPresolveDomains()
    var fixedVars = initTable[string, int]()
    var eliminated = initPackedSet[int]()
    var infeasible = false

    # Seed fixedVars from existing paramValues and singleton domains
    for name, val in tr.paramValues:
        fixedVars[name] = val
    for name, dom in domains:
        if dom.len == 1:
            fixedVars[name] = dom[0]

    var totalIterations = 0

    for iteration in 0..<30:
        var changed = false

        # Step 1: Fix singleton-domain variables
        if fixSingletons(domains, fixedVars):
            changed = true

        # Step 2: Substitute constants into constraints, simplify/eliminate
        if simplifyConstraints(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 3: Resolve reifications (highest impact for FZN models)
        if resolveReifications(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 4: Linear bounds propagation
        if boundsPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 5: AllDifferent propagation
        if allDiffPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6: Fix any newly-created singletons
        if fixSingletons(domains, fixedVars):
            changed = true

        inc totalIterations
        if not changed:
            break

    if infeasible:
        stderr.writeLine(&"[FZN] Presolve: infeasibility detected at iteration {totalIterations}")
        tr.applyPresolveResults(domains, fixedVars, eliminated)
        return

    # Count newly fixed variables (not counting pre-existing params)
    var nFixed = 0
    for name, val in fixedVars:
        if name notin tr.paramValues:
            inc nFixed

    if nFixed > 0 or eliminated.len > 0:
        stderr.writeLine(&"[FZN] Presolve: {totalIterations} iterations, {nFixed} vars fixed, {eliminated.len} constraints eliminated")

    tr.applyPresolveResults(domains, fixedVars, eliminated)
