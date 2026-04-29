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
            let rangeSize = decl.varType.hi - decl.varType.lo + 1
            if rangeSize > 1_000_000:
                # Skip very large domains — too expensive to enumerate.
                # These will be handled as unbounded during propagation.
                discard
            else:
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
                    elif allFixed and nUnfixed > 1 and rhs == nUnfixed:
                        # All-ones cardinality forcing: int_lin_eq([1,...,1], vars, k)
                        # where k == nUnfixed means all unfixed variables must be 1.
                        # (rhs already has fixed-variable contributions subtracted)
                        var allCoeffsOne = true
                        for i in 0..<nArgs:
                            let c = con.args[0].elems[i].intVal
                            if c != 1: allCoeffsOne = false; break
                        if allCoeffsOne:
                            for i in 0..<nArgs:
                                let vExpr = con.args[1].elems[i]
                                if not tr.presolveIsFixed(vExpr, fixedVars):
                                    let vn = presolveVarName(vExpr)
                                    if vn != "":
                                        if presolveTightenDomain(domains, vn, @[1], infeasible):
                                            result = true

            # Handle parameter-referenced coefficient array for cardinality forcing
            elif con.args[0].kind == FznIdent and
                 (con.args[1].kind == FznArrayLit or con.args[1].kind == FznIdent) and
                 con.args[0].ident in tr.arrayValues:
                let coeffs = tr.arrayValues[con.args[0].ident]
                # Resolve variable names
                var varExprs: seq[FznExpr]
                if con.args[1].kind == FznArrayLit:
                    varExprs = con.args[1].elems
                elif con.args[1].kind == FznIdent:
                    # Variable array reference - need to look up elements
                    # Skip for now; inline arrays are the common case
                    discard
                if varExprs.len > 0 and varExprs.len == coeffs.len and
                   tr.presolveIsFixed(con.args[2], fixedVars):
                    var rhs = tr.presolveResolve(con.args[2], fixedVars)
                    var nUnfixed = 0
                    var allCoeffsOne = true
                    for i in 0..<coeffs.len:
                        if coeffs[i] != 1: allCoeffsOne = false
                        if tr.presolveIsFixed(varExprs[i], fixedVars):
                            rhs -= coeffs[i] * tr.presolveResolve(varExprs[i], fixedVars)
                        else:
                            inc nUnfixed
                    # All-ones cardinality forcing
                    if allCoeffsOne and nUnfixed > 0 and rhs == nUnfixed:
                        for i in 0..<varExprs.len:
                            if not tr.presolveIsFixed(varExprs[i], fixedVars):
                                let vn = presolveVarName(varExprs[i])
                                if vn != "":
                                    if presolveTightenDomain(domains, vn, @[1], infeasible):
                                        result = true
                    elif nUnfixed == 1:
                        # One unfixed variable
                        for i in 0..<varExprs.len:
                            if not tr.presolveIsFixed(varExprs[i], fixedVars):
                                let c = coeffs[i]
                                if c != 0 and rhs mod c == 0:
                                    let vn = presolveVarName(varExprs[i])
                                    if vn != "":
                                        let val = rhs div c
                                        if presolveTightenDomain(domains, vn, @[val], infeasible):
                                            result = true
                                break
                    elif nUnfixed == 0:
                        if con.canEliminate:
                            eliminated.incl(ci)
                            result = true

        # --- int_lin_le(coeffs, vars, rhs): sum(c_i * x_i) <= rhs ---
        elif name == "int_lin_le" and con.args.len >= 3:
            if con.args[0].kind == FznArrayLit and con.args[1].kind == FznArrayLit:
                let nArgs = con.args[0].elems.len
                if nArgs == con.args[1].elems.len and
                        tr.presolveIsFixed(con.args[2], fixedVars):
                    var rhs = tr.presolveResolve(con.args[2], fixedVars)
                    var allCoeffsLit = true
                    var nUnfixed = 0
                    var allCoeffsOne = true
                    var allUnfixedBinary = true
                    var nFixedContribution = 0
                    # First check all coeffs are literals; track unit-coefficient case
                    # and accumulate fixed-variable contribution to LHS.
                    for i in 0..<nArgs:
                        if con.args[0].elems[i].kind != FznIntLit:
                            allCoeffsLit = false; break
                        let c = con.args[0].elems[i].intVal
                        if c != 1: allCoeffsOne = false
                        let vExpr = con.args[1].elems[i]
                        if tr.presolveIsFixed(vExpr, fixedVars):
                            nFixedContribution += c * tr.presolveResolve(vExpr, fixedVars)
                        else:
                            inc nUnfixed
                            # For NAND-style propagation we also need every
                            # unfixed var to be binary {0,1}.
                            let vn = presolveVarName(vExpr)
                            if vn == "" or vn notin domains:
                                allUnfixedBinary = false
                            else:
                                let dom = domains[vn]
                                if dom != @[0, 1]:
                                    allUnfixedBinary = false
                    if allCoeffsLit and nUnfixed == 0:
                        # Verify the now-fully-evaluated constraint and eliminate.
                        if nFixedContribution > rhs:
                            infeasible = true
                        elif con.canEliminate:
                            eliminated.incl(ci)
                            result = true
                    elif allCoeffsLit and allCoeffsOne and allUnfixedBinary:
                        # Unit-coefficient atMost on (still-)binary unfixed vars.
                        # Generalised NAND unit propagation:
                        #   sum_unfixed x_i  <=  rhs - nFixedContribution
                        # i.e. atMost(unfixed, 1, slack).
                        let slack = rhs - nFixedContribution
                        if slack < 0:
                            infeasible = true
                        elif slack == 0:
                            # Every remaining unfixed variable must be 0.
                            for i in 0..<nArgs:
                                let vExpr = con.args[1].elems[i]
                                if tr.presolveIsFixed(vExpr, fixedVars): continue
                                let vn = presolveVarName(vExpr)
                                if vn != "":
                                    if presolveTightenDomain(domains, vn, @[0], infeasible):
                                        result = true
                            if con.canEliminate:
                                eliminated.incl(ci)
                                result = true
                        elif slack >= nUnfixed:
                            # Even setting every unfixed variable to 1 satisfies it
                            # → constraint is tautological in the current state.
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
        # Resolve coefficients array: handle both inline FznArrayLit and named parameter/variable arrays
        var coeffsArg = con.args[0]
        if coeffsArg.kind == FznIdent:
            let arrName = coeffsArg.ident
            if arrName in tr.paramValues:
                continue  # scalar param, not an array
            var found = false
            for decl in tr.model.parameters:
                if decl.isArray and decl.name == arrName:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        coeffsArg = decl.value
                        found = true
                    break
            if not found:
                for decl in tr.model.variables:
                    if decl.isArray and decl.name == arrName:
                        if decl.value != nil and decl.value.kind == FznArrayLit:
                            coeffsArg = decl.value
                            found = true
                        break
            if not found: continue
        if coeffsArg.kind != FznArrayLit: continue
        var varsArg = con.args[1]
        if varsArg.kind == FznIdent:
            var found = false
            for decl in tr.model.variables:
                if decl.isArray and decl.name == varsArg.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        varsArg = decl.value
                        found = true
                    break
            if not found:
                for decl in tr.model.parameters:
                    if decl.isArray and decl.name == varsArg.ident:
                        if decl.value != nil and decl.value.kind == FznArrayLit:
                            varsArg = decl.value
                            found = true
                        break
            if not found: continue
        if varsArg.kind != FznArrayLit: continue
        let nArgs = coeffsArg.elems.len
        if nArgs != varsArg.elems.len: continue
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
            if coeffsArg.elems[i].kind != FznIntLit:
                valid = false; break
            vars[i].coeff = coeffsArg.elems[i].intVal
            let vExpr = varsArg.elems[i]
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

        # GCD-based feasibility pruning for equalities.
        # For sum(c_i * x_i) = rhs, for each unfixed variable x_j, the sum of
        # other terms must equal (rhs - c_j * x_j). That sum is a multiple of
        # gcd(other coefficients), so (rhs - c_j * x_j) must also be.
        if isEq and nArgs >= 2:
            for j in 0..<nArgs:
                if vars[j].fixed: continue
                if vars[j].varName == "": continue
                let c = vars[j].coeff
                if c == 0: continue
                # Compute gcd of OTHER unfixed coefficients
                var gRest = 0
                for i in 0..<nArgs:
                    if i == j or vars[i].fixed: continue
                    gRest = gcd(gRest, abs(vars[i].coeff))
                if gRest <= 1: continue
                # Need: (adjRhs - c * v) mod gRest == 0
                # where adjRhs = rhs - sum(c_i * fixedVal_i) for fixed i
                # i.e. c * v ≡ adjRhs (mod gRest)
                var adjRhs = rhs
                for i in 0..<nArgs:
                    if i != j and vars[i].fixed:
                        adjRhs -= vars[i].coeff * vars[i].fixedVal
                let target = ((adjRhs mod gRest) + gRest) mod gRest
                if vars[j].varName in domains:
                    let dom = domains[vars[j].varName]
                    var allowed: seq[int]
                    for v in dom:
                        let residue = ((c * v) mod gRest + gRest) mod gRest
                        if residue == target:
                            allowed.add(v)
                    if allowed.len < dom.len:
                        if presolveTightenDomain(domains, vars[j].varName, allowed, infeasible):
                            result = true
                            if allowed.len > 0:
                                vars[j].lo = allowed[0]
                                vars[j].hi = allowed[^1]

proc reachableValuesPropagate(tr: var FznTranslator,
                              domains: var Table[string, seq[int]],
                              fixedVars: Table[string, int],
                              eliminated: PackedSet[int],
                              infeasible: var bool): bool =
    ## Discrete-domain (reachable-values) propagation for int_lin_eq.
    ##
    ## For a constraint Σᵢ cᵢ·xᵢ = rhs with each xᵢ having a small enumerable
    ## domain, tighten each xⱼ to those values v for which some assignment of
    ## the other xᵢ over their discrete domains can complete the sum. This is
    ## strictly stronger than the interval-only reasoning in `boundsPropagate`:
    ## it removes values in *gaps* of the achievable value set (e.g. y ∈ {0,70,140}
    ## when y = 70·b₁ + 70·b₂ and the bᵢ are binary, where interval arithmetic
    ## would only give y ∈ [0, 140]).
    ##
    ## Budgeted: aborts the constraint if the Cartesian product of domain sizes
    ## exceeds `enumerationLimit` so we don't blow up on long sums.
    const enumerationLimit = 4096
    result = false
    var nTightened = 0
    var nValuesRemoved = 0
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if con.args.len < 3: continue

        # Resolve coefficients array (same logic as boundsPropagate)
        var coeffsArg = con.args[0]
        if coeffsArg.kind == FznIdent:
            let arrName = coeffsArg.ident
            if arrName in tr.paramValues: continue
            var found = false
            for decl in tr.model.parameters:
                if decl.isArray and decl.name == arrName:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        coeffsArg = decl.value
                        found = true
                    break
            if not found:
                for decl in tr.model.variables:
                    if decl.isArray and decl.name == arrName:
                        if decl.value != nil and decl.value.kind == FznArrayLit:
                            coeffsArg = decl.value
                            found = true
                        break
            if not found: continue
        if coeffsArg.kind != FznArrayLit: continue

        var varsArg = con.args[1]
        if varsArg.kind == FznIdent:
            var found = false
            for decl in tr.model.variables:
                if decl.isArray and decl.name == varsArg.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        varsArg = decl.value
                        found = true
                    break
            if not found:
                for decl in tr.model.parameters:
                    if decl.isArray and decl.name == varsArg.ident:
                        if decl.value != nil and decl.value.kind == FznArrayLit:
                            varsArg = decl.value
                            found = true
                        break
            if not found: continue
        if varsArg.kind != FznArrayLit: continue

        let nArgs = coeffsArg.elems.len
        if nArgs != varsArg.elems.len: continue
        if nArgs < 2: continue
        if not tr.presolveIsFixed(con.args[2], fixedVars): continue
        let rhs = tr.presolveResolve(con.args[2], fixedVars)

        # Collect per-term info and check budget.
        type Term = object
            coeff: int
            varName: string
            fixed: bool
            fixedVal: int
            dom: seq[int]
        var terms = newSeq[Term](nArgs)
        var fixedSum = 0
        var cartProduct = 1
        var nUnfixed = 0
        var valid = true
        var overBudget = false
        for i in 0..<nArgs:
            if coeffsArg.elems[i].kind != FznIntLit:
                valid = false; break
            terms[i].coeff = coeffsArg.elems[i].intVal
            let vExpr = varsArg.elems[i]
            terms[i].varName = presolveVarName(vExpr)
            if tr.presolveIsFixed(vExpr, fixedVars):
                terms[i].fixed = true
                terms[i].fixedVal = tr.presolveResolve(vExpr, fixedVars)
                fixedSum += terms[i].coeff * terms[i].fixedVal
            elif terms[i].varName in domains:
                terms[i].dom = domains[terms[i].varName]
                if terms[i].dom.len == 0:
                    valid = false; break
                if terms[i].coeff != 0:
                    inc nUnfixed
                    # Guard against overflow and keep the budget check cheap.
                    if cartProduct > enumerationLimit or
                       terms[i].dom.len > enumerationLimit:
                        overBudget = true
                    else:
                        cartProduct *= terms[i].dom.len
                        if cartProduct > enumerationLimit:
                            overBudget = true
            else:
                valid = false; break
        if not valid or overBudget or nUnfixed < 2: continue

        let adjRhs = rhs - fixedSum

        # For each unfixed term j: enumerate the achievable values of the sum
        # of the remaining unfixed terms and tighten dom(xⱼ) accordingly.
        for j in 0..<nArgs:
            if terms[j].fixed: continue
            if terms[j].varName == "": continue
            let cj = terms[j].coeff
            if cj == 0: continue
            if terms[j].dom.len <= 1: continue

            # Build coeff-scaled domains of the other unfixed terms.
            var otherDomains: seq[seq[int]]
            for i in 0..<nArgs:
                if i == j or terms[i].fixed or terms[i].coeff == 0: continue
                if terms[i].dom.len == 0: continue
                var scaled = newSeq[int](terms[i].dom.len)
                for k, v in terms[i].dom:
                    scaled[k] = terms[i].coeff * v
                otherDomains.add(scaled)

            let reachable = computeReachableSums(otherDomains, enumerationLimit)
            if reachable.len == 0: continue  # budget exceeded, skip

            var newDom: seq[int]
            for v in terms[j].dom:
                let needed = adjRhs - cj * v
                if needed in reachable:
                    newDom.add(v)
            if newDom.len == 0:
                infeasible = true
                return
            if newDom.len < terms[j].dom.len:
                let removed = terms[j].dom.len - newDom.len
                if presolveTightenDomain(domains, terms[j].varName, newDom, infeasible):
                    result = true
                    inc nTightened
                    nValuesRemoved += removed
                    terms[j].dom = newDom  # tighter for remaining j iterations

    if nTightened > 0:
        tr.reachableValuesTightened += nTightened
        tr.reachableValuesRemoved += nValuesRemoved

proc bigMDomainPruning(tr: FznTranslator,
                       domains: var Table[string, seq[int]],
                       fixedVars: Table[string, int],
                       eliminated: PackedSet[int],
                       infeasible: var bool): bool =
    ## Detect big-M indicator linking patterns and prune infeasible gaps.
    ##
    ## Pattern: two int_lin_le constraints on the same (x, indicator) pair where
    ## indicator is a binary {0,1} variable (often from bool2int):
    ##   int_lin_le([1, -U], [x, ind], 0)   →  x ≤ U * ind
    ##   int_lin_le([-1, L], [x, ind], 0)   →  x ≥ L * ind
    ##
    ## When ind=0: x ≤ 0 AND x ≥ 0 → x = 0
    ## When ind=1: x ∈ [L, U]
    ## Domain should be {0} ∪ [L, U], not [0, U].
    ##
    ## More generally, detects any 2-variable int_lin_le([a, b], [x, y], c) where
    ## one variable has domain {0,1} and creates the disjoint domain.
    result = false

    # Build index: for each pair of variable names, collect the constraints
    type LinLePair = tuple[coeffX, coeffY: int, rhs: int, ci: int]
    var pairConstraints: Table[(string, string), seq[LinLePair]]

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue

        # Resolve coefficients and variables arrays (may be named parameters)
        var coeffArr = con.args[0]
        if coeffArr.kind == FznIdent:
            var found = false
            for decl in tr.model.parameters:
                if decl.isArray and decl.name == coeffArr.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        coeffArr = decl.value
                        found = true
                    break
            if not found: continue
        if coeffArr.kind != FznArrayLit: continue
        if coeffArr.elems.len != 2: continue  # Only 2-variable constraints

        var varArr = con.args[1]
        if varArr.kind == FznIdent:
            var found = false
            for decl in tr.model.variables:
                if decl.isArray and decl.name == varArr.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        varArr = decl.value
                        found = true
                    break
            if not found: continue
        if varArr.kind != FznArrayLit: continue
        if varArr.elems.len != 2: continue

        let rhsArg = con.args[2]
        if not tr.presolveIsFixed(rhsArg, fixedVars): continue
        let rhs = tr.presolveResolve(rhsArg, fixedVars)

        # Resolve variable names (may be param aliases)
        var varNames: array[2, string]
        var coeffs: array[2, int]
        var allOk = true
        for k in 0..1:
            if coeffArr.elems[k].kind != FznIntLit:
                allOk = false; break
            coeffs[k] = coeffArr.elems[k].intVal
            let varg = varArr.elems[k]
            if varg.kind == FznIdent:
                varNames[k] = varg.ident
            elif varg.kind == FznIntLit:
                allOk = false; break  # constant, not interesting
            else:
                allOk = false; break
        if not allOk: continue

        # Skip if either variable is already fixed
        if varNames[0] in fixedVars or varNames[1] in fixedVars: continue

        let key = if varNames[0] < varNames[1]: (varNames[0], varNames[1])
                  else: (varNames[1], varNames[0])
        let entry: LinLePair = if varNames[0] < varNames[1]:
            (coeffX: coeffs[0], coeffY: coeffs[1], rhs: rhs, ci: ci)
        else:
            (coeffX: coeffs[1], coeffY: coeffs[0], rhs: rhs, ci: ci)
        pairConstraints.mgetOrPut(key, @[]).add(entry)

    # For each pair with 2+ constraints, check for big-M pattern
    for key, entries in pairConstraints:
        if entries.len < 2: continue
        let varX = key[0]
        let varY = key[1]

        # Check which variable is binary {0,1}
        let domX = if varX in domains: domains[varX]
                   elif varX in fixedVars: @[fixedVars[varX]]
                   else: continue
        let domY = if varY in domains: domains[varY]
                   elif varY in fixedVars: @[fixedVars[varY]]
                   else: continue

        # Identify the binary indicator and the continuous variable
        var indVar, contVar: string
        var contDom: seq[int]
        var indIsX: bool  # true if indicator is varX

        let xIsBin = domX.len == 2 and domX[0] == 0 and domX[1] == 1
        let yIsBin = domY.len == 2 and domY[0] == 0 and domY[1] == 1
        if xIsBin:
            indVar = varX; contVar = varY; contDom = domY; indIsX = true
        elif yIsBin:
            indVar = varY; contVar = varX; contDom = domX; indIsX = false
        else:
            continue

        # For each constraint, compute bounds on contVar when ind=0 and ind=1
        # Constraint: coeffX * x + coeffY * y <= rhs
        # If ind is x: coeffX * ind + coeffY * cont <= rhs
        #   ind=0: coeffY * cont <= rhs
        #   ind=1: coeffY * cont <= rhs - coeffX
        # If ind is y: coeffX * cont + coeffY * ind <= rhs
        #   ind=0: coeffX * cont <= rhs
        #   ind=1: coeffX * cont <= rhs - coeffY

        var lo0 = low(int) div 2  # lower bound when ind=0
        var hi0 = high(int) div 2 # upper bound when ind=0
        var lo1 = low(int) div 2  # lower bound when ind=1
        var hi1 = high(int) div 2 # upper bound when ind=1

        for e in entries:
            let contCoeff = if indIsX: e.coeffY else: e.coeffX
            let indCoeff = if indIsX: e.coeffX else: e.coeffY

            if contCoeff == 0: continue

            # a * x <= b:
            #   a > 0 → x <= floor(b / a)
            #   a < 0 → x >= ceil(b / a)
            # ceil(b/a) for a < 0: rewrite as ceil(-b / |a|) where |a| = -a > 0
            proc psCeilDiv(n, d: int): int =
                ## ceil(n / d) for d > 0
                if n >= 0: (n + d - 1) div d
                else: -((-n) div d)

            for indVal in [0, 1]:
                let r = e.rhs - indCoeff * indVal
                if contCoeff > 0:
                    let ub = psFloorDiv(r, contCoeff)
                    if indVal == 0: hi0 = min(hi0, ub)
                    else: hi1 = min(hi1, ub)
                else:
                    let lb = psCeilDiv(-r, -contCoeff)
                    if indVal == 0: lo0 = max(lo0, lb)
                    else: lo1 = max(lo1, lb)

        # Check if we found a useful gap:
        # When ind=0, cont must be in [lo0, hi0]
        # When ind=1, cont must be in [lo1, hi1]
        # If [lo0, hi0] ∩ [lo1, hi1] doesn't cover the full domain, we can prune
        if hi0 < lo0 or hi1 < lo1: continue  # infeasible case, leave for other propagation

        # Build the disjoint domain: values in [lo0, hi0] ∪ [lo1, hi1]
        if contVar notin domains: continue
        let origDom = domains[contVar]
        if origDom.len <= 2: continue  # already small enough

        var newDom: seq[int]
        for v in origDom:
            if (v >= lo0 and v <= hi0) or (v >= lo1 and v <= hi1):
                newDom.add(v)

        if newDom.len < origDom.len and newDom.len > 0:
            domains[contVar] = newDom
            result = true

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

proc tryResolveReifBoolFromDomains(tr: FznTranslator,
                                   boolVarName: string,
                                   domains: Table[string, seq[int]],
                                   fixedVars: Table[string, int],
                                   eliminated: PackedSet[int],
                                   reifDefMap: Table[string, int]): int =
    ## Try to determine a boolean reification output's value from domain bounds.
    ## Returns 0 (always false), 1 (always true), or -1 (undetermined).
    ## Does NOT modify domains; caller should apply the result.
    if boolVarName notin reifDefMap: return -1
    let ci = reifDefMap[boolVarName]
    if ci in eliminated: return -1
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)

    if name == "int_ne_reif" and con.args.len >= 3:
        let xName = presolveVarName(con.args[0])
        if tr.presolveIsFixed(con.args[1], fixedVars):
            let val = tr.presolveResolve(con.args[1], fixedVars)
            let xDom = if xName != "" and xName in domains: domains[xName] else: @[]
            if xDom.len > 0:
                if val notin xDom: return 1   # always not-equal
                if xDom.len == 1 and xDom[0] == val: return 0  # always equal
    elif name == "int_eq_reif" and con.args.len >= 3:
        let xName = presolveVarName(con.args[0])
        if tr.presolveIsFixed(con.args[1], fixedVars):
            let val = tr.presolveResolve(con.args[1], fixedVars)
            let xDom = if xName != "" and xName in domains: domains[xName] else: @[]
            if xDom.len > 0:
                if val notin xDom: return 0
                if xDom.len == 1 and xDom[0] == val: return 1
    elif name == "int_le_reif" and con.args.len >= 3:
        var xLo, xHi, yLo, yHi: int
        var xOk, yOk: bool
        let xName = presolveVarName(con.args[0])
        let yName = presolveVarName(con.args[1])
        if tr.presolveIsFixed(con.args[0], fixedVars):
            let v = tr.presolveResolve(con.args[0], fixedVars); xLo = v; xHi = v; xOk = true
        elif xName != "" and xName in domains and domains[xName].len > 0:
            xLo = domains[xName][0]; xHi = domains[xName][^1]; xOk = true
        if tr.presolveIsFixed(con.args[1], fixedVars):
            let v = tr.presolveResolve(con.args[1], fixedVars); yLo = v; yHi = v; yOk = true
        elif yName != "" and yName in domains and domains[yName].len > 0:
            yLo = domains[yName][0]; yHi = domains[yName][^1]; yOk = true
        if xOk and yOk:
            if xHi <= yLo: return 1   # always true
            if xLo > yHi: return 0    # always false
    elif name == "int_lt_reif" and con.args.len >= 3:
        var xLo, xHi, yLo, yHi: int
        var xOk, yOk: bool
        let xName = presolveVarName(con.args[0])
        let yName = presolveVarName(con.args[1])
        if tr.presolveIsFixed(con.args[0], fixedVars):
            let v = tr.presolveResolve(con.args[0], fixedVars); xLo = v; xHi = v; xOk = true
        elif xName != "" and xName in domains and domains[xName].len > 0:
            xLo = domains[xName][0]; xHi = domains[xName][^1]; xOk = true
        if tr.presolveIsFixed(con.args[1], fixedVars):
            let v = tr.presolveResolve(con.args[1], fixedVars); yLo = v; yHi = v; yOk = true
        elif yName != "" and yName in domains and domains[yName].len > 0:
            yLo = domains[yName][0]; yHi = domains[yName][^1]; yOk = true
        if xOk and yOk:
            if xHi < yLo: return 1
            if xLo >= yHi: return 0
    elif name == "int_lin_le_reif" and con.args.len >= 4:
        var coeffsArg = con.args[0]
        if coeffsArg.kind == FznIdent:
            for decl in tr.model.parameters:
                if decl.isArray and decl.name == coeffsArg.ident and
                   decl.value != nil and decl.value.kind == FznArrayLit:
                    coeffsArg = decl.value; break
        var varsArg = con.args[1]
        if varsArg.kind == FznIdent:
            for decl in tr.model.variables:
                if decl.isArray and decl.name == varsArg.ident and
                   decl.value != nil and decl.value.kind == FznArrayLit:
                    varsArg = decl.value; break
        if coeffsArg.kind == FznArrayLit and varsArg.kind == FznArrayLit and
           coeffsArg.elems.len == varsArg.elems.len and
           tr.presolveIsFixed(con.args[2], fixedVars):
            let rhs = tr.presolveResolve(con.args[2], fixedVars)
            var totalMin, totalMax: int
            var valid = true
            for i in 0..<coeffsArg.elems.len:
                if coeffsArg.elems[i].kind != FznIntLit: valid = false; break
                let c = coeffsArg.elems[i].intVal
                let vExpr = varsArg.elems[i]
                var lo, hi: int
                if tr.presolveIsFixed(vExpr, fixedVars):
                    let v = tr.presolveResolve(vExpr, fixedVars); lo = v; hi = v
                else:
                    let vn = presolveVarName(vExpr)
                    if vn != "" and vn in domains and domains[vn].len > 0:
                        lo = domains[vn][0]; hi = domains[vn][^1]
                    else: valid = false; break
                if c > 0: totalMin += c * lo; totalMax += c * hi
                elif c < 0: totalMin += c * hi; totalMax += c * lo
            if valid:
                if totalMax <= rhs: return 1
                if totalMin > rhs: return 0
    return -1

proc resolveReifications(tr: FznTranslator,
                         domains: var Table[string, seq[int]],
                         fixedVars: var Table[string, int],
                         eliminated: var PackedSet[int],
                         infeasible: var bool): bool =
    ## Check reified constraints and fix boolean result when domains determine truth value.
    result = false

    # Build a map from reification output boolean name → defining constraint index.
    # Used by bool_clause handler for chain propagation through reification.
    var reifDefMap: Table[string, int]
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name in ["int_eq_reif", "int_ne_reif", "int_le_reif", "int_lt_reif"] and
           con.args.len >= 3 and con.args[2].kind == FznIdent:
            reifDefMap[con.args[2].ident] = ci
        elif name in ["int_lin_le_reif", "int_lin_eq_reif", "int_lin_ne_reif"] and
             con.args.len >= 4 and con.args[3].kind == FznIdent:
            reifDefMap[con.args[3].ident] = ci

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

        # --- int_div(x, y, z): z = x div y ---
        elif name == "int_div" and con.args.len >= 3:
            let xArg = con.args[0]
            let yArg = con.args[1]
            let zArg = con.args[2]

            if yArg.kind == FznIntLit and yArg.intVal > 0:
                let cVal = yArg.intVal
                # Forward propagation: tighten Z's domain from X's domain bounds
                let xName = presolveVarName(xArg)
                let zName = presolveVarName(zArg)
                if xName != "" and xName in domains and zName != "" and zName in domains:
                    let xDom = domains[xName]
                    if xDom.len > 0:
                        let zLo = xDom[0] div cVal
                        let zHi = xDom[^1] div cVal
                        let zMin = min(zLo, zHi)
                        let zMax = max(zLo, zHi)
                        var newZDom: seq[int]
                        for v in domains[zName]:
                            if v >= zMin and v <= zMax:
                                newZDom.add(v)
                        if newZDom.len < domains[zName].len:
                            if newZDom.len == 0:
                                infeasible = true
                            else:
                                domains[zName] = newZDom
                                result = true
                # Reverse propagation: tighten X's domain from Z's domain
                if not infeasible and xName != "" and xName in domains and zName != "" and zName in domains:
                    let zDom = domains[zName]
                    if zDom.len > 0:
                        # X must be in [z*C, z*C + C-1] for some z in zDom
                        let xMin = zDom[0] * cVal
                        let xMax = zDom[^1] * cVal + cVal - 1
                        var newXDom: seq[int]
                        for v in domains[xName]:
                            if v >= xMin and v <= xMax:
                                newXDom.add(v)
                        if newXDom.len < domains[xName].len:
                            if newXDom.len == 0:
                                infeasible = true
                            else:
                                domains[xName] = newXDom
                                result = true
                # Elimination: if both fully fixed
                if not infeasible:
                    let xFixed = tr.presolveIsFixed(xArg, fixedVars)
                    let zFixed = zName != "" and zName in domains and domains[zName].len == 1
                    if xFixed and zFixed and con.canEliminate:
                        eliminated.incl(ci)
                        result = true
            elif tr.presolveIsFixed(xArg, fixedVars) and tr.presolveIsFixed(yArg, fixedVars):
                let xVal = tr.presolveResolve(xArg, fixedVars)
                let yVal = tr.presolveResolve(yArg, fixedVars)
                if yVal != 0:
                    let zVal = xVal div yVal
                    let zName = presolveVarName(zArg)
                    if zName != "" and zName in domains:
                        if presolveTightenDomain(domains, zName, @[zVal], infeasible):
                            result = true
                    if not infeasible and con.canEliminate:
                        eliminated.incl(ci)
                        result = true

        # --- int_lin_le_reif(coeffs, vars, rhs, b): b <=> (sum(c_i * x_i) <= rhs) ---
        # --- int_lin_eq_reif(coeffs, vars, rhs, b): b <=> (sum(c_i * x_i) == rhs) ---
        elif (name == "int_lin_le_reif" or name == "int_lin_eq_reif" or
              name == "int_lin_ne_reif") and con.args.len >= 4:
            let isLeReif = name == "int_lin_le_reif"
            let isEqReif = name == "int_lin_eq_reif"
            # let isNeReif = name == "int_lin_ne_reif"
            let bName = presolveVarName(con.args[3])
            let bFixed = tr.presolveIsFixed(con.args[3], fixedVars) or
                         (bName != "" and bName in domains and domains[bName].len == 1)
            # Resolve coefficient and variable arrays
            var coeffsArg = con.args[0]
            if coeffsArg.kind == FznIdent:
                let arrName = coeffsArg.ident
                if arrName notin tr.paramValues:
                    var found = false
                    for decl in tr.model.parameters:
                        if decl.isArray and decl.name == arrName:
                            if decl.value != nil and decl.value.kind == FznArrayLit:
                                coeffsArg = decl.value; found = true
                            break
                    if not found:
                        for decl in tr.model.variables:
                            if decl.isArray and decl.name == arrName:
                                if decl.value != nil and decl.value.kind == FznArrayLit:
                                    coeffsArg = decl.value; found = true
                                break
            if coeffsArg.kind == FznArrayLit:
                var varsArg = con.args[1]
                if varsArg.kind == FznIdent:
                    var found = false
                    for decl in tr.model.variables:
                        if decl.isArray and decl.name == varsArg.ident:
                            if decl.value != nil and decl.value.kind == FznArrayLit:
                                varsArg = decl.value; found = true
                            break
                    if not found:
                        for decl in tr.model.parameters:
                            if decl.isArray and decl.name == varsArg.ident:
                                if decl.value != nil and decl.value.kind == FznArrayLit:
                                    varsArg = decl.value; found = true
                                break
                if varsArg.kind == FznArrayLit and
                   coeffsArg.elems.len == varsArg.elems.len and
                   tr.presolveIsFixed(con.args[2], fixedVars):
                    let rhs = tr.presolveResolve(con.args[2], fixedVars)
                    let nArgs = coeffsArg.elems.len

                    # Collect per-variable info
                    type LinReifVarInfo = object
                        coeff: int
                        varName: string
                        fixed: bool
                        fixedVal: int
                        lo, hi: int
                    var lvars = newSeq[LinReifVarInfo](nArgs)
                    var valid = true
                    for i in 0..<nArgs:
                        if coeffsArg.elems[i].kind != FznIntLit:
                            valid = false; break
                        lvars[i].coeff = coeffsArg.elems[i].intVal
                        let vExpr = varsArg.elems[i]
                        lvars[i].varName = presolveVarName(vExpr)
                        if tr.presolveIsFixed(vExpr, fixedVars):
                            lvars[i].fixed = true
                            lvars[i].fixedVal = tr.presolveResolve(vExpr, fixedVars)
                            lvars[i].lo = lvars[i].fixedVal
                            lvars[i].hi = lvars[i].fixedVal
                        else:
                            lvars[i].fixed = false
                            if lvars[i].varName in domains:
                                let dom = domains[lvars[i].varName]
                                if dom.len == 0: valid = false; break
                                lvars[i].lo = dom[0]
                                lvars[i].hi = dom[^1]
                            else:
                                valid = false; break
                    if valid:
                        # Compute bounds on sum(c_i * x_i)
                        var totalMin, totalMax: int
                        for i in 0..<nArgs:
                            let c = lvars[i].coeff
                            if c > 0:
                                totalMin += c * lvars[i].lo
                                totalMax += c * lvars[i].hi
                            elif c < 0:
                                totalMin += c * lvars[i].hi
                                totalMax += c * lvars[i].lo

                        # Determine b from bounds
                        if not bFixed and bName != "":
                            if isLeReif:
                                if totalMax <= rhs:
                                    # sum always <= rhs → b = 1
                                    if presolveTightenDomain(domains, bName, @[1], infeasible):
                                        result = true
                                elif totalMin > rhs:
                                    # sum always > rhs → b = 0
                                    if presolveTightenDomain(domains, bName, @[0], infeasible):
                                        result = true
                            elif isEqReif:
                                if totalMin == rhs and totalMax == rhs:
                                    # sum always == rhs → b = 1
                                    if presolveTightenDomain(domains, bName, @[1], infeasible):
                                        result = true
                                elif totalMin > rhs or totalMax < rhs:
                                    # sum never == rhs → b = 0
                                    if presolveTightenDomain(domains, bName, @[0], infeasible):
                                        result = true
                            else:  # int_lin_ne_reif
                                if totalMin == rhs and totalMax == rhs:
                                    # sum always == rhs → ne is always false → b = 0
                                    if presolveTightenDomain(domains, bName, @[0], infeasible):
                                        result = true
                                elif totalMin > rhs or totalMax < rhs:
                                    # sum never == rhs → ne is always true → b = 1
                                    if presolveTightenDomain(domains, bName, @[1], infeasible):
                                        result = true

                        # If b is fixed, propagate bounds to variables
                        let bFixedNow = tr.presolveIsFixed(con.args[3], fixedVars) or
                                        (bName != "" and bName in domains and domains[bName].len == 1)
                        if bFixedNow:
                            let bv = if tr.presolveIsFixed(con.args[3], fixedVars):
                                         tr.presolveResolve(con.args[3], fixedVars)
                                     else: domains[bName][0]
                            if (isLeReif and bv == 1) or (isEqReif and bv == 1):
                                # sum <= rhs (for LE) or sum == rhs (for EQ): tighten each variable
                                for j in 0..<nArgs:
                                    if lvars[j].fixed or lvars[j].varName == "": continue
                                    let c = lvars[j].coeff
                                    if c == 0: continue
                                    var jMinC, jMaxC: int
                                    if c > 0: jMinC = c * lvars[j].lo; jMaxC = c * lvars[j].hi
                                    else: jMinC = c * lvars[j].hi; jMaxC = c * lvars[j].lo
                                    let othersMin = totalMin - jMinC
                                    # sum <= rhs: c*x <= rhs - othersMin
                                    let slack = rhs - othersMin
                                    if c > 0:
                                        let ub = psFloorDiv(slack, c)
                                        if presolveRestrictBounds(domains, lvars[j].varName,
                                                                  low(int), ub, infeasible):
                                            result = true
                                            lvars[j].hi = min(lvars[j].hi, ub)
                                    elif c < 0:
                                        let lb = -psFloorDiv(slack, -c)
                                        if presolveRestrictBounds(domains, lvars[j].varName,
                                                                  lb, high(int), infeasible):
                                            result = true
                                            lvars[j].lo = max(lvars[j].lo, lb)
                                    if isEqReif:
                                        let othersMax = totalMax - jMaxC
                                        let slack2 = rhs - othersMax
                                        if c > 0:
                                            let lb = psCeilDiv(slack2, c)
                                            if presolveRestrictBounds(domains, lvars[j].varName,
                                                                      lb, high(int), infeasible):
                                                result = true
                                                lvars[j].lo = max(lvars[j].lo, lb)
                                        elif c < 0:
                                            let ub = -psCeilDiv(slack2, -c)
                                            if presolveRestrictBounds(domains, lvars[j].varName,
                                                                      low(int), ub, infeasible):
                                                result = true
                                                lvars[j].hi = min(lvars[j].hi, ub)
                                    # Update total bounds for subsequent variables
                                    var newJMinC, newJMaxC: int
                                    if c > 0: newJMinC = c * lvars[j].lo; newJMaxC = c * lvars[j].hi
                                    else: newJMinC = c * lvars[j].hi; newJMaxC = c * lvars[j].lo
                                    totalMin += newJMinC - jMinC
                                    totalMax += newJMaxC - jMaxC
                            elif isLeReif and bv == 0:
                                # NOT(sum <= rhs) → sum > rhs → sum >= rhs + 1
                                let newRhs = -(rhs + 1)  # -sum <= -(rhs+1)
                                for j in 0..<nArgs:
                                    if lvars[j].fixed or lvars[j].varName == "": continue
                                    let c = -lvars[j].coeff  # negate coeffs for -sum <= newRhs
                                    if c == 0: continue
                                    var jMinC, jMaxC: int
                                    if c > 0: jMinC = c * lvars[j].lo; jMaxC = c * lvars[j].hi
                                    else: jMinC = c * lvars[j].hi; jMaxC = c * lvars[j].lo
                                    var negTotalMin = 0
                                    for i in 0..<nArgs:
                                        let nc = -lvars[i].coeff
                                        if nc > 0: negTotalMin += nc * lvars[i].lo
                                        elif nc < 0: negTotalMin += nc * lvars[i].hi
                                    let othersMin = negTotalMin - jMinC
                                    let slack = newRhs - othersMin
                                    if c > 0:
                                        let ub = psFloorDiv(slack, c)
                                        if presolveRestrictBounds(domains, lvars[j].varName,
                                                                  low(int), ub, infeasible):
                                            result = true
                                    elif c < 0:
                                        let lb = -psFloorDiv(slack, -c)
                                        if presolveRestrictBounds(domains, lvars[j].varName,
                                                                  lb, high(int), infeasible):
                                            result = true

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
                                # Try to resolve through reification definition
                                let reifVal = tr.tryResolveReifBoolFromDomains(
                                    vn, domains, fixedVars, eliminated, reifDefMap)
                                if reifVal == 1:
                                    satisfied = true; break
                                elif reifVal == 0:
                                    discard  # effectively false, skip
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
                                    # Try to resolve through reification
                                    let reifVal = tr.tryResolveReifBoolFromDomains(
                                        vn, domains, fixedVars, eliminated, reifDefMap)
                                    if reifVal == 0:
                                        satisfied = true; break  # NOT(false) = true
                                    elif reifVal == 1:
                                        discard  # NOT(true) = false, skip
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

proc implicationPropagate(tr: FznTranslator,
                          domains: var Table[string, seq[int]],
                          fixedVars: var Table[string, int],
                          eliminated: var PackedSet[int],
                          infeasible: var bool): bool =
    ## Builds an implication graph from bool_clause constraints and performs
    ## BFS propagation from fixed boolean variables.
    ##
    ## Pattern: bool_clause([b], [a]) means a → b (if a=1 then b=1).
    ## When a is fixed to 1, we can immediately fix b to 1, and transitively
    ## propagate through all downstream implications in a single BFS pass.
    ##
    ## This is much more effective than iterative unit propagation for long
    ## implication chains (common in dominance, reification decompositions).
    result = false

    # Phase 1: Build implication graph from simple implications (pos=1, neg=1)
    # bool_clause([b], [a]) = a → b (positive implication: a=1 forces b=1)
    # bool_clause([a], [b]) with a fixed false and b unfixed is handled by unit prop
    type ImplEdge = object
        target: string
        ci: int  # constraint index for potential elimination
    var posImplGraph: Table[string, seq[ImplEdge]]  # a=1 → b=1
    var negImplGraph: Table[string, seq[ImplEdge]]  # a=0 → b=0 (from bool_clause([], [a, b]))

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        if con.args[0].kind != FznArrayLit or con.args[1].kind != FznArrayLit: continue

        let posElems = con.args[0].elems
        let negElems = con.args[1].elems

        if posElems.len == 1 and negElems.len == 1:
            # bool_clause([b], [a]) → a=1 implies b=1
            let aName = presolveVarName(negElems[0])
            let bName = presolveVarName(posElems[0])
            if aName != "" and bName != "" and aName != bName:
                if aName notin posImplGraph:
                    posImplGraph[aName] = @[]
                posImplGraph[aName].add(ImplEdge(target: bName, ci: ci))

        elif posElems.len == 0 and negElems.len == 2:
            # bool_clause([], [a, b]) → NOT(a) OR NOT(b) → a=1 implies b=0
            let aName = presolveVarName(negElems[0])
            let bName = presolveVarName(negElems[1])
            if aName != "" and bName != "" and aName != bName:
                if aName notin negImplGraph:
                    negImplGraph[aName] = @[]
                negImplGraph[aName].add(ImplEdge(target: bName, ci: ci))
                if bName notin negImplGraph:
                    negImplGraph[bName] = @[]
                negImplGraph[bName].add(ImplEdge(target: aName, ci: ci))

    if posImplGraph.len == 0 and negImplGraph.len == 0:
        return false

    # Phase 2: BFS propagation from variables fixed to 1 (positive implications)
    var queue: seq[string]
    var visited: HashSet[string]

    # Seed with all boolean variables currently fixed to 1
    for name, val in fixedVars:
        if val == 1 and name in posImplGraph:
            queue.add(name)
            visited.incl(name)
    for name, dom in domains:
        if dom == @[1] and name notin visited and name in posImplGraph:
            queue.add(name)
            visited.incl(name)

    var qi = 0
    while qi < queue.len:
        let src = queue[qi]
        inc qi
        if src in posImplGraph:
            for edge in posImplGraph[src]:
                let tgt = edge.target
                if tgt in domains:
                    if domains[tgt] != @[1]:
                        if domains[tgt] == @[0]:
                            # a=1 but b must be 0 — contradiction
                            infeasible = true
                            return true
                        domains[tgt] = @[1]
                        fixedVars[tgt] = 1
                        result = true
                    # Continue propagation from newly fixed target
                    if tgt notin visited:
                        visited.incl(tgt)
                        queue.add(tgt)

    if infeasible: return

    # Phase 3: BFS propagation from variables fixed to 1 (negative implications)
    # a=1 → b=0 (from NAND clauses)
    visited.clear()
    queue.setLen(0)
    qi = 0

    for name, val in fixedVars:
        if val == 1 and name in negImplGraph:
            queue.add(name)
            visited.incl(name)
    for name, dom in domains:
        if dom == @[1] and name notin visited and name in negImplGraph:
            queue.add(name)
            visited.incl(name)

    while qi < queue.len:
        let src = queue[qi]
        inc qi
        if src in negImplGraph:
            for edge in negImplGraph[src]:
                let tgt = edge.target
                if tgt in domains:
                    if domains[tgt] != @[0]:
                        if domains[tgt] == @[1]:
                            # a=1 but a→NOT(b), b already 1 — contradiction
                            infeasible = true
                            return true
                        domains[tgt] = @[0]
                        fixedVars[tgt] = 0
                        result = true
                    # A var fixed to 0 can trigger positive implications via bool_clause([a],[b])
                    # where b is now 0 — but that's handled by unit propagation, not here

    if infeasible: return

    # Phase 4: Propagation from variables fixed to 0.
    # For positive implications, if b is fixed to 0 and we have a → b,
    # this means a must be 0 (contrapositive). Build reverse graph for this.
    visited.clear()
    queue.setLen(0)
    qi = 0

    # Build reverse positive implication graph: b → a (contrapositive: b=0 → a=0)
    var revPosGraph: Table[string, seq[string]]
    for src, edges in posImplGraph:
        for edge in edges:
            if edge.target notin revPosGraph:
                revPosGraph[edge.target] = @[]
            revPosGraph[edge.target].add(src)

    for name, val in fixedVars:
        if val == 0 and name in revPosGraph:
            queue.add(name)
            visited.incl(name)
    for name, dom in domains:
        if dom == @[0] and name notin visited and name in revPosGraph:
            queue.add(name)
            visited.incl(name)

    while qi < queue.len:
        let src = queue[qi]
        inc qi
        if src in revPosGraph:
            for tgt in revPosGraph[src]:
                if tgt in domains:
                    if domains[tgt] != @[0]:
                        if domains[tgt] == @[1]:
                            infeasible = true
                            return true
                        domains[tgt] = @[0]
                        fixedVars[tgt] = 0
                        result = true
                    if tgt notin visited:
                        visited.incl(tgt)
                        queue.add(tgt)

proc disjunctionEqualitiesPropagate(tr: FznTranslator,
                                    domains: var Table[string, seq[int]],
                                    fixedVars: Table[string, int],
                                    eliminated: PackedSet[int],
                                    infeasible: var bool): bool =
    ## Recover the membership relation `b ↔ x ∈ S` from MiniZinc's flattened
    ## "exists(j where C(j))(x = j)" patterns: one int_eq_reif per candidate
    ## with the booleans ORed together. By the time the disjunction reaches
    ## FZN it's lost the "x must be one of these values" semantics — we
    ## recover it here as bidirectional domain ↔ result-flag propagation.
    ##
    ## Three carrier forms are handled:
    ##   bool_clause([b_1,...], [])         → implicit OR-result = 1
    ##   array_bool_or([b_1,...], b)        → reified OR
    ##   bool_clause_reif([b_1,...], [], b) → reified OR (rare in FZN)
    ##
    ## Where every b_i is `int_eq_reif(x, c_i, b_i)` on a shared x:
    ##   - OR-result fixed to 1 (or implicit)        ⇒ dom(x) ⊆ {c_i}
    ##   - OR-result fixed to 0                      ⇒ dom(x) ∩ {c_i} = ∅
    ##   - dom(x) ⊆ {c_i for known i}                ⇒ OR-result = 1
    ##   - dom(x) disjoint from {c_i for known i}    ⇒ OR-result = 0
    ##
    ## We don't eliminate the carrier constraints: case-analysis and other
    ## downstream detectors may still want them, and once domains are
    ## tightened they're trivially satisfied so leaving them costs nothing.
    result = false

    # Phase 1: build map b_name -> (x_name, c) for int_eq_reif with constant
    # RHS. A boolean produced by multiple defining int_eq_reifs (shouldn't
    # happen in well-formed FZN, but we don't audit that) is dropped.
    var eqMap: Table[string, (string, int)]
    var conflict: HashSet[string]
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        if stripSolverPrefix(con.name) != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[1].kind != FznIntLit: continue
        let xName = presolveVarName(con.args[0])
        let bName = presolveVarName(con.args[2])
        if xName == "" or bName == "": continue
        if bName in conflict: continue
        if bName in eqMap:
            # Different defining constraint for the same b — drop both.
            eqMap.del(bName)
            conflict.incl(bName)
        else:
            eqMap[bName] = (xName, con.args[1].intVal)

    if eqMap.len == 0: return

    # Helper: for a literal-array, check that all elements are eq-reif outputs
    # over the same source variable and collect their constants.
    proc collectMembership(elems: seq[FznExpr],
                           eqMap: Table[string, (string, int)]):
                          tuple[ok: bool, x: string, vals: HashSet[int]] =
        var x = ""
        var vals = initHashSet[int]()
        for e in elems:
            let bName = presolveVarName(e)
            if bName == "" or bName notin eqMap:
                return (false, "", initHashSet[int]())
            let (xName, c) = eqMap[bName]
            if x == "":
                x = xName
            elif x != xName:
                return (false, "", initHashSet[int]())
            vals.incl(c)
        return (true, x, vals)

    # Apply bidirectional propagation between x and the OR-result `bArg` given
    # membership set S = {c_i}. `bArg` may be missing (= implicit-true case).
    proc applyMembership(tr: FznTranslator,
                         domains: var Table[string, seq[int]],
                         fixedVars: Table[string, int],
                         x: string, vals: HashSet[int],
                         bArg: FznExpr, bImplicitTrue: bool,
                         infeasible: var bool): bool =
        var changed = false
        if x notin domains: return false
        # Snapshot result-flag value if known.
        var bVal = -1
        if bImplicitTrue:
            bVal = 1
        elif bArg.kind == FznIntLit or bArg.kind == FznBoolLit:
            bVal = tr.presolveResolve(bArg, fixedVars)
        elif bArg.kind == FznIdent:
            if bArg.ident in fixedVars:
                bVal = fixedVars[bArg.ident]
            elif bArg.ident in tr.paramValues:
                bVal = tr.paramValues[bArg.ident]
            elif bArg.ident in domains and domains[bArg.ident].len == 1:
                bVal = domains[bArg.ident][0]

        # Forward direction: result-flag drives domain.
        if bVal == 1:
            var allowed: seq[int]
            for v in vals: allowed.add(v)
            if presolveTightenDomain(domains, x, allowed, infeasible):
                changed = true
        elif bVal == 0:
            for v in vals:
                if presolveRemoveValue(domains, x, v, infeasible):
                    changed = true
                if infeasible: return changed

        # Reverse direction: domain drives result-flag (only if there's a flag).
        if not bImplicitTrue and bArg.kind == FznIdent and
           bArg.ident in domains and domains[bArg.ident].len > 1:
            let bName = bArg.ident
            let xDom = domains[x]
            if xDom.len > 0:
                var allInS = true
                var anyInS = false
                for v in xDom:
                    if v in vals:
                        anyInS = true
                    else:
                        allInS = false
                if allInS:
                    if presolveTightenDomain(domains, bName, @[1], infeasible):
                        changed = true
                elif not anyInS:
                    if presolveTightenDomain(domains, bName, @[0], infeasible):
                        changed = true
        return changed

    # Phase 2a: bool_clause([pos], []) — the implicit-true OR.
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        if con.args[0].kind != FznArrayLit: continue
        if con.args[1].kind != FznArrayLit: continue
        if con.args[1].elems.len > 0: continue
        let posElems = con.args[0].elems
        if posElems.len < 2: continue
        let m = collectMembership(posElems, eqMap)
        if not m.ok or m.x == "": continue
        if applyMembership(tr, domains, fixedVars, m.x, m.vals,
                           FznExpr(kind: FznIdent, ident: ""), true, infeasible):
            result = true

    # Phase 2b: array_bool_or([pos], b) — reified OR, both directions.
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        if stripSolverPrefix(con.name) != "array_bool_or": continue
        if con.args.len < 2: continue
        if con.args[0].kind != FznArrayLit: continue
        let posElems = con.args[0].elems
        if posElems.len < 2: continue
        let m = collectMembership(posElems, eqMap)
        if not m.ok or m.x == "": continue
        if applyMembership(tr, domains, fixedVars, m.x, m.vals,
                           con.args[1], false, infeasible):
            result = true

    # Phase 2c: bool_clause_reif([pos], [], b) — reified OR with empty negs.
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        if stripSolverPrefix(con.name) != "bool_clause_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznArrayLit: continue
        if con.args[1].kind != FznArrayLit: continue
        if con.args[1].elems.len > 0: continue
        let posElems = con.args[0].elems
        if posElems.len < 2: continue
        let m = collectMembership(posElems, eqMap)
        if not m.ok or m.x == "": continue
        if applyMembership(tr, domains, fixedVars, m.x, m.vals,
                           con.args[2], false, infeasible):
            result = true

proc nonMembershipPropagate(tr: FznTranslator,
                            domains: var Table[string, seq[int]],
                            fixedVars: Table[string, int],
                            eliminated: PackedSet[int],
                            infeasible: var bool): bool =
    ## Dual of disjunctionEqualitiesPropagate: recover `r ↔ x ∉ S` from
    ## MiniZinc's flattened "forall(j where C(j))(x != j)" pattern, where each
    ## inequality is an int_ne_reif and they're conjoined by an array_bool_and.
    ##
    ## Also catches the inconsistent shape `r ↔ AND of (x = c_i)` with
    ## distinct c_i — that AND can never hold, so r is forced to 0.
    ##
    ## Forms handled (the carrier is array_bool_and([b_1,...], r)):
    ##   each b_i = int_ne_reif(x, c_i, b_i)  ⇒
    ##     r=1            ⇒ dom(x) ∩ {c_i} = ∅
    ##     r=0            ⇒ dom(x) ⊆ {c_i}
    ##     dom(x) ⊆ Sᶜ    ⇒ r=1
    ##     dom(x) ⊆ S     ⇒ r=0     (where S = {c_i})
    ##
    ##   each b_i = int_eq_reif(x, c_i, b_i) with ≥2 distinct c_i ⇒
    ##     r is forced to 0 (mutually exclusive equalities).
    ##
    ## Like the OR-side propagator, we don't eliminate the carrier — downstream
    ## detectors may still want it and it's trivially satisfied once the
    ## domains are tightened.
    result = false

    # Build maps from b_name → (x_name, c_value) for both reif kinds.
    var eqMap: Table[string, (string, int)]
    var neMap: Table[string, (string, int)]
    var eqConflict, neConflict: HashSet[string]
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if con.args.len < 3: continue
        if con.args[1].kind != FznIntLit: continue
        let xName = presolveVarName(con.args[0])
        let bName = presolveVarName(con.args[2])
        if xName == "" or bName == "": continue
        if name == "int_eq_reif":
            if bName in eqConflict: continue
            if bName in eqMap:
                eqMap.del(bName); eqConflict.incl(bName)
            else:
                eqMap[bName] = (xName, con.args[1].intVal)
        elif name == "int_ne_reif":
            if bName in neConflict: continue
            if bName in neMap:
                neMap.del(bName); neConflict.incl(bName)
            else:
                neMap[bName] = (xName, con.args[1].intVal)

    if eqMap.len == 0 and neMap.len == 0: return

    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        if stripSolverPrefix(con.name) != "array_bool_and": continue
        if con.args.len < 2: continue
        if con.args[0].kind != FznArrayLit: continue
        let elems = con.args[0].elems
        if elems.len < 2: continue

        # Classify: are all elements ne_reif on a shared x, or eq_reif on
        # a shared x? Mixed shapes → skip.
        var commonX = ""
        var values = initHashSet[int]()
        var allNe = true
        var allEq = true
        for e in elems:
            let bName = presolveVarName(e)
            if bName == "":
                allNe = false; allEq = false; break
            if bName notin neMap: allNe = false
            if bName notin eqMap: allEq = false
            if not allNe and not allEq: break

        if allNe:
            for e in elems:
                let (xName, c) = neMap[presolveVarName(e)]
                if commonX == "":
                    commonX = xName
                elif commonX != xName:
                    commonX = ""; break
                values.incl(c)
            if commonX == "" or commonX notin domains: continue

            # rArg known?
            let rArg = con.args[1]
            var rVal = -1
            if rArg.kind == FznBoolLit or rArg.kind == FznIntLit:
                rVal = tr.presolveResolve(rArg, fixedVars)
            elif rArg.kind == FznIdent:
                if rArg.ident in fixedVars: rVal = fixedVars[rArg.ident]
                elif rArg.ident in tr.paramValues: rVal = tr.paramValues[rArg.ident]
                elif rArg.ident in domains and domains[rArg.ident].len == 1:
                    rVal = domains[rArg.ident][0]

            if rVal == 1:
                # x ∉ S
                for v in values:
                    if presolveRemoveValue(domains, commonX, v, infeasible):
                        result = true
                    if infeasible: return
            elif rVal == 0:
                # x ∈ S
                var allowed: seq[int]
                for v in values: allowed.add(v)
                if presolveTightenDomain(domains, commonX, allowed, infeasible):
                    result = true

            # Reverse: domain → r.
            if rArg.kind == FznIdent and rArg.ident in domains and
               domains[rArg.ident].len > 1:
                let xDom = domains[commonX]
                if xDom.len > 0:
                    var anyInS = false
                    var allInS = true
                    for v in xDom:
                        if v in values: anyInS = true
                        else: allInS = false
                    if not anyInS:
                        if presolveTightenDomain(domains, rArg.ident, @[1], infeasible):
                            result = true
                    elif allInS:
                        if presolveTightenDomain(domains, rArg.ident, @[0], infeasible):
                            result = true

        elif allEq:
            # AND of int_eq_reif on the same var with ≥2 distinct constants is
            # unsatisfiable — force r=0.
            for e in elems:
                let (xName, c) = eqMap[presolveVarName(e)]
                if commonX == "":
                    commonX = xName
                elif commonX != xName:
                    commonX = ""; break
                values.incl(c)
            if commonX == "": continue
            if values.len < 2: continue
            let rArg = con.args[1]
            if rArg.kind == FznIdent:
                if presolveTightenDomain(domains, rArg.ident, @[0], infeasible):
                    result = true

proc cpmBoundsPropagate(tr: FznTranslator,
                        domains: var Table[string, seq[int]],
                        fixedVars: Table[string, int],
                        eliminated: PackedSet[int],
                        infeasible: var bool): bool =
    ## Critical Path Method: single O(V+E) forward/backward pass for precedence
    ## constraints. Tightens start variable domains from [0..UB] to [ES(i)..LS(i)].
    ## Much more effective than iterative boundsPropagate for deep precedence chains.
    result = false

    # Phase 1: Collect candidate edges from int_lin_le constraints.
    # Pattern A: coeffs=[1,1,-1], vars=[v0, v1, v2], rhs=0 → v0 + v1 <= v2
    # Pattern B: coeffs=[c,-c], vars=[a, b], rhs=R → a - b <= R/c → edge a→b weight -R/c
    type CpmCandidate = object
        fromVar, toVar, durVar: string  # durVar="" for constant-weight edges
        constWeight: int                # used when durVar=""
    var candidates: seq[CpmCandidate]
    var destVars: HashSet[string]  # vars appearing with coeff=-1

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue

        var coeffs: seq[int]
        try:
            coeffs = tr.resolveIntArray(con.args[0])
        except CatchableError:
            continue

        if not tr.presolveIsFixed(con.args[2], fixedVars): continue
        let rhs = tr.presolveResolve(con.args[2], fixedVars)

        if con.args[1].kind != FznArrayLit: continue
        var varNames: seq[string]
        var allIdent = true
        for e in con.args[1].elems:
            if e.kind != FznIdent:
                allIdent = false
                break
            varNames.add(e.ident)
        if not allIdent or varNames.len != coeffs.len: continue

        if coeffs.len == 3 and coeffs == @[1, 1, -1] and rhs == 0:
            # Pattern A: v0 + v1 - v2 <= 0 → v2 >= v0 + v1
            destVars.incl(varNames[2])
            candidates.add(CpmCandidate(
                fromVar: varNames[0], toVar: varNames[2],
                durVar: varNames[1], constWeight: 0))
        elif coeffs.len == 2:
            # Pattern B: c*a - c*b <= R → edge a→b weight -R/c
            if coeffs[0] > 0 and coeffs[1] < 0 and coeffs[0] == -coeffs[1]:
                let c = coeffs[0]
                if c > 1 and rhs mod c != 0: continue
                destVars.incl(varNames[1])
                candidates.add(CpmCandidate(
                    fromVar: varNames[0], toVar: varNames[1],
                    durVar: "", constWeight: -(rhs div c)))
            elif coeffs[0] < 0 and coeffs[1] > 0 and -coeffs[0] == coeffs[1]:
                let c = coeffs[1]
                if c > 1 and rhs mod c != 0: continue
                destVars.incl(varNames[0])
                candidates.add(CpmCandidate(
                    fromVar: varNames[1], toVar: varNames[0],
                    durVar: "", constWeight: -(rhs div c)))

    if candidates.len == 0 and tr.model.constraints.len == 0: return false

    # Phase 1b: Generate implied precedence edges through int_max/int_min.
    # If M = max(A, B) (from int_max :: defines_var) and there's a candidate edge
    # M → D with weight w (meaning D >= M + w), then D >= A + w AND D >= B + w.
    # Similarly for int_min: if M = min(A, B) and there's a candidate edge D → M
    # with weight w (meaning M >= D + w), then A >= D + w AND B >= D + w.
    block:
        # Build mapping: max/min output var → (input1, input2, isMax)
        var maxMinDefs: Table[string, tuple[input1, input2: string, isMax: bool]]
        for ci, con in tr.model.constraints:
            if ci in eliminated: continue
            let name = stripSolverPrefix(con.name)
            let isMax = name == "int_max"
            let isMin = name == "int_min"
            if not isMax and not isMin: continue
            if con.args.len < 3: continue
            if not con.hasAnnotation("defines_var"): continue
            let a0 = con.args[0]
            let a1 = con.args[1]
            let a2 = con.args[2]
            if a0.kind != FznIdent or a1.kind != FznIdent or a2.kind != FznIdent: continue
            maxMinDefs[a2.ident] = (input1: a0.ident, input2: a1.ident, isMax: isMax)

        if maxMinDefs.len > 0:
            var nImplied = 0
            # For int_max(A, B, M): edge M→D becomes edges A→D and B→D (same weight)
            # For int_min(A, B, M): edge D→M becomes edges D→A and D→B (same weight)
            var extraCandidates: seq[CpmCandidate]
            for cand in candidates:
                if cand.durVar != "":
                    # 3-var candidate: check if fromVar or toVar is a max/min output
                    # fromVar is one of the two +1 vars, toVar is the -1 var
                    # These are more complex — skip for now
                    discard
                else:
                    # Constant-weight edge fromVar → toVar
                    if cand.fromVar in maxMinDefs:
                        let def = maxMinDefs[cand.fromVar]
                        if def.isMax:
                            # M = max(A,B), edge M→toVar: since A <= M, edge A→toVar is also valid
                            extraCandidates.add(CpmCandidate(
                                fromVar: def.input1, toVar: cand.toVar,
                                durVar: "", constWeight: cand.constWeight))
                            extraCandidates.add(CpmCandidate(
                                fromVar: def.input2, toVar: cand.toVar,
                                durVar: "", constWeight: cand.constWeight))
                            nImplied += 2
                    if cand.toVar in maxMinDefs:
                        let def = maxMinDefs[cand.toVar]
                        if not def.isMax:
                            # M = min(A,B), edge fromVar→M: since M <= A, edge fromVar→A is also valid
                            extraCandidates.add(CpmCandidate(
                                fromVar: cand.fromVar, toVar: def.input1,
                                durVar: "", constWeight: cand.constWeight))
                            extraCandidates.add(CpmCandidate(
                                fromVar: cand.fromVar, toVar: def.input2,
                                durVar: "", constWeight: cand.constWeight))
                            nImplied += 2
            if nImplied > 0:
                candidates.add(extraCandidates)
                for c in extraCandidates:
                    destVars.incl(c.toVar)

    if candidates.len == 0: return false

    # Phase 2: Resolve 3-var candidates into edges.
    # For pattern A, determine which +1 var is start (source) vs duration (weight).
    # destVars contains all vars that appear with coeff=-1 somewhere — these are start vars.
    # Among the two +1 vars, if one is in destVars it's the source; otherwise use domain range.
    type CpmEdge = object
        toId: int
        minW, maxW: int
    var nameToId: Table[string, int]
    var idToName: seq[string]
    var nextId = 0

    proc getId(name: string): int =
        if name in nameToId:
            return nameToId[name]
        result = nextId
        nameToId[name] = nextId
        idToName.add(name)
        inc nextId

    var adjFwd: seq[seq[CpmEdge]]  # forward adjacency: succ edges
    var nEdges = 0

    proc addEdge(fromId, toId, minW, maxW: int) =
        while adjFwd.len <= max(fromId, toId):
            adjFwd.add(@[])
        # Merge parallel edges: keep tightest (max weight)
        for e in adjFwd[fromId].mitems:
            if e.toId == toId:
                e.minW = max(e.minW, minW)
                e.maxW = max(e.maxW, maxW)
                return
        adjFwd[fromId].add(CpmEdge(toId: toId, minW: minW, maxW: maxW))
        inc nEdges

    for cand in candidates:
        if cand.durVar == "":
            # Constant weight edge
            let fId = getId(cand.fromVar)
            let tId = getId(cand.toVar)
            addEdge(fId, tId, cand.constWeight, cand.constWeight)
        else:
            # 3-var: determine source vs duration
            var sourceVar, durVar: string
            let fromIsDest = cand.fromVar in destVars
            let durIsDest = cand.durVar in destVars
            if fromIsDest and not durIsDest:
                sourceVar = cand.fromVar
                durVar = cand.durVar
            elif durIsDest and not fromIsDest:
                sourceVar = cand.durVar
                durVar = cand.fromVar
            else:
                # Both or neither in destVars — use domain range as tiebreaker.
                # Start vars have large ranges (0..UB), duration vars have small ranges.
                let fromDom = domains.getOrDefault(cand.fromVar)
                let durDom = domains.getOrDefault(cand.durVar)
                let fromRange = if fromDom.len > 0: fromDom[^1] - fromDom[0] else: 0
                let durRange = if durDom.len > 0: durDom[^1] - durDom[0] else: 0
                if fromRange >= durRange:
                    sourceVar = cand.fromVar
                    durVar = cand.durVar
                else:
                    sourceVar = cand.durVar
                    durVar = cand.fromVar

            # Get duration domain bounds
            var minDur, maxDur: int
            if durVar in fixedVars:
                minDur = fixedVars[durVar]
                maxDur = fixedVars[durVar]
            elif durVar in domains:
                let dom = domains[durVar]
                if dom.len == 0: continue
                minDur = dom[0]
                maxDur = dom[^1]
            else:
                continue

            let fId = getId(sourceVar)
            let tId = getId(cand.toVar)
            addEdge(fId, tId, minDur, maxDur)

    let n = nextId
    if n == 0 or nEdges == 0: return false
    while adjFwd.len < n:
        adjFwd.add(@[])

    # Phase 3: Topological sort (Kahn's algorithm)
    var inDeg = newSeq[int](n)
    for u in 0..<n:
        for e in adjFwd[u]:
            inDeg[e.toId] += 1

    var queue: seq[int]
    for i in 0..<n:
        if inDeg[i] == 0:
            queue.add(i)

    var topoOrder: seq[int]
    var qi = 0
    while qi < queue.len:
        let u = queue[qi]
        inc qi
        topoOrder.add(u)
        for e in adjFwd[u]:
            inDeg[e.toId] -= 1
            if inDeg[e.toId] == 0:
                queue.add(e.toId)

    if topoOrder.len != n:
        # Cycle detected — skip CPM
        return false

    # Phase 4: Forward pass — compute earliest start times
    var es = newSeq[int](n)
    for i in 0..<n:
        let nm = idToName[i]
        if nm in fixedVars:
            es[i] = fixedVars[nm]
        elif nm in domains and domains[nm].len > 0:
            es[i] = domains[nm][0]  # domain min
        else:
            es[i] = 0

    for u in topoOrder:
        for e in adjFwd[u]:
            let newES = es[u] + e.minW
            if newES > es[e.toId]:
                es[e.toId] = newES

    # Phase 5: Backward pass — compute latest start times
    var ls = newSeq[int](n)
    for i in 0..<n:
        let nm = idToName[i]
        if nm in fixedVars:
            ls[i] = fixedVars[nm]
        elif nm in domains and domains[nm].len > 0:
            ls[i] = domains[nm][^1]  # domain max
        else:
            ls[i] = high(int) div 2

    for i in countdown(topoOrder.len - 1, 0):
        let u = topoOrder[i]
        for e in adjFwd[u]:
            let newLS = ls[e.toId] - e.maxW
            if newLS < ls[u]:
                ls[u] = newLS

    # Phase 6: Tighten domains
    var nTightened = 0
    for i in 0..<n:
        let nm = idToName[i]
        if nm in fixedVars: continue
        if presolveRestrictBounds(domains, nm, es[i], ls[i], infeasible):
            result = true
            inc nTightened

    if nTightened > 0:
        stderr.writeLine(&"[FZN] CPM: tightened {nTightened} start variable domains across {nEdges} precedence edges")

proc permutationCountingPropagate(tr: FznTranslator,
                                   domains: var Table[string, seq[int]],
                                   fixedVars: Table[string, int],
                                   eliminated: PackedSet[int],
                                   infeasible: var bool): bool =
    ## For all_different (permutation) constraints with precedence edges,
    ## tighten domains by counting predecessors/successors in the transitive closure.
    ##
    ## CPM only uses the longest chain length, but for permutations, every
    ## predecessor needs a distinct value below the variable, so:
    ##   lb(x) = |ancestors(x)| + domain_min
    ##   ub(x) = domain_max - |descendants(x)|
    ##
    ## This can be MUCH tighter than CPM when many predecessors are independent
    ## (not in a single chain). Example: 12 independent predecessors give lb=13,
    ## but CPM only gives lb=2.
    result = false

    # Step 1: Collect all_different groups as sets of variable names.
    # Handle both array literal and array name arguments.
    var allDiffGroups: seq[HashSet[string]]
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_all_different_int": continue
        if con.args.len < 1: continue
        var varNames: seq[string]
        if con.args[0].kind == FznArrayLit:
            for e in con.args[0].elems:
                if e.kind == FznIdent:
                    varNames.add(e.ident)
        elif con.args[0].kind == FznIdent:
            # Array name — resolve from model declarations
            for decl in tr.model.variables:
                if decl.isArray and decl.name == con.args[0].ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        for e in decl.value.elems:
                            if e.kind == FznIdent:
                                varNames.add(e.ident)
                    break
        if varNames.len >= 3:
            allDiffGroups.add(toHashSet(varNames))

    if allDiffGroups.len == 0: return

    # Step 2: Collect precedence edges from int_lin_le constraints.
    # Pattern: coeffs=[1,-1], vars=[from, to], rhs=-w → from + w <= to (edge from→to weight w)
    # Pattern: coeffs=[-1,1], vars=[to, from], rhs=-w → same
    type Edge = tuple[fromVar, toVar: string, weight: int]
    var edges: seq[Edge]
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue
        var coeffs: seq[int]
        try:
            coeffs = tr.resolveIntArray(con.args[0])
        except CatchableError:
            continue
        if coeffs.len != 2: continue
        if not tr.presolveIsFixed(con.args[2], fixedVars): continue
        let rhs = tr.presolveResolve(con.args[2], fixedVars)
        if con.args[1].kind != FznArrayLit: continue
        let elems = con.args[1].elems
        if elems.len != 2 or elems[0].kind != FznIdent or elems[1].kind != FznIdent: continue
        let v0 = elems[0].ident
        let v1 = elems[1].ident
        # [1,-1],[v0,v1],rhs → v0 - v1 <= rhs → v1 >= v0 + (-rhs) → edge v0→v1 weight -rhs
        if coeffs[0] == 1 and coeffs[1] == -1 and rhs < 0:
            edges.add((fromVar: v0, toVar: v1, weight: -rhs))
        elif coeffs[0] == -1 and coeffs[1] == 1 and rhs < 0:
            edges.add((fromVar: v1, toVar: v0, weight: -rhs))

    if edges.len == 0: return

    # Step 3: For each all_different group, compute transitive closure and tighten.
    var totalTightened = 0
    var totalEdges = 0
    for group in allDiffGroups:
        # Filter edges to those with both endpoints in the group
        var adj: Table[string, seq[string]]
        var rev: Table[string, seq[string]]
        var groupEdgeCount = 0
        for e in edges:
            if e.fromVar in group and e.toVar in group:
                adj.mgetOrPut(e.fromVar, @[]).add(e.toVar)
                rev.mgetOrPut(e.toVar, @[]).add(e.fromVar)
                inc groupEdgeCount
        if groupEdgeCount == 0: continue
        totalEdges += groupEdgeCount

        # Compute domain min/max for the group
        var globalMin = high(int)
        var globalMax = low(int)
        for vn in group:
            if vn in fixedVars:
                globalMin = min(globalMin, fixedVars[vn])
                globalMax = max(globalMax, fixedVars[vn])
            elif vn in domains and domains[vn].len > 0:
                globalMin = min(globalMin, domains[vn][0])
                globalMax = max(globalMax, domains[vn][^1])

        # BFS from each node to compute ancestor/descendant counts
        # Only count group members (not external variables in precedence chains)
        for vn in group:
            if vn in fixedVars: continue
            if vn notin domains or domains[vn].len <= 1: continue

            # Count ancestors (predecessors): BFS backward
            var ancestors = 0
            var visited: HashSet[string]
            var queue: seq[string]
            if vn in rev:
                for pred in rev[vn]:
                    if pred notin visited:
                        visited.incl(pred)
                        queue.add(pred)
            var qi = 0
            while qi < queue.len:
                let cur = queue[qi]
                inc qi
                inc ancestors
                if cur in rev:
                    for pred in rev[cur]:
                        if pred notin visited:
                            visited.incl(pred)
                            queue.add(pred)

            # Count descendants (successors): BFS forward
            var descendants = 0
            visited.clear()
            queue.setLen(0)
            qi = 0
            if vn in adj:
                for succ in adj[vn]:
                    if succ notin visited:
                        visited.incl(succ)
                        queue.add(succ)
            while qi < queue.len:
                let cur = queue[qi]
                inc qi
                inc descendants
                if cur in adj:
                    for succ in adj[cur]:
                        if succ notin visited:
                            visited.incl(succ)
                            queue.add(succ)

            # Tighten bounds: need `ancestors` distinct values below, `descendants` above
            let newLo = globalMin + ancestors
            let newHi = globalMax - descendants
            if presolveRestrictBounds(domains, vn, newLo, newHi, infeasible):
                result = true
                inc totalTightened

    if totalTightened > 0:
        stderr.writeLine(&"[FZN] Permutation counting: tightened {totalTightened} domains " &
                         &"across {totalEdges} precedence edges in {allDiffGroups.len} groups")

proc nonRenewableResourcePruning(tr: FznTranslator,
                                  domains: var Table[string, seq[int]],
                                  fixedVars: Table[string, int],
                                  eliminated: PackedSet[int],
                                  infeasible: var bool): bool =
    ## Prune infeasible domain values from resource demand variables based on
    ## global capacity limits. For int_lin_le where all coefficients are 1 and
    ## rhs is fixed (non-renewable resource pattern: sum of demands <= capacity),
    ## each variable's max feasible value is capacity minus the sum of other mins.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue
        if not tr.presolveIsFixed(con.args[2], fixedVars): continue

        var coeffs: seq[int]
        try:
            coeffs = tr.resolveIntArray(con.args[0])
        except CatchableError:
            continue

        # Check all coefficients are 1
        var allOnes = true
        for c in coeffs:
            if c != 1:
                allOnes = false
                break
        if not allOnes: continue
        if coeffs.len < 2: continue

        if con.args[1].kind != FznArrayLit: continue
        if con.args[1].elems.len != coeffs.len: continue

        # Collect variable info: need all non-fixed with domain in domains table
        let cap = tr.presolveResolve(con.args[2], fixedVars)
        type VInfo = object
            varName: string
            fixed: bool
            fixedVal: int
            lo: int
        var vars: seq[VInfo]
        var valid = true
        var totalMin = 0
        var nUnfixed = 0
        for i in 0..<coeffs.len:
            let e = con.args[1].elems[i]
            var vi: VInfo
            vi.varName = presolveVarName(e)
            if tr.presolveIsFixed(e, fixedVars):
                vi.fixed = true
                vi.fixedVal = tr.presolveResolve(e, fixedVars)
                vi.lo = vi.fixedVal
                totalMin += vi.fixedVal
            elif vi.varName != "" and vi.varName in domains:
                let dom = domains[vi.varName]
                if dom.len == 0:
                    valid = false; break
                vi.fixed = false
                vi.lo = dom[0]
                totalMin += dom[0]
                inc nUnfixed
            else:
                valid = false; break
            vars.add(vi)
        if not valid or nUnfixed < 2: continue

        # Prune each unfixed variable
        for i in 0..<vars.len:
            if vars[i].fixed: continue
            let othersMin = totalMin - vars[i].lo
            let slack = cap - othersMin
            if presolveRestrictBounds(domains, vars[i].varName, low(int), slack, infeasible):
                result = true
                # Update local min for subsequent iterations within this constraint
                let newDom = domains[vars[i].varName]
                if newDom.len > 0:
                    let oldMin = vars[i].lo
                    vars[i].lo = newDom[0]
                    totalMin += (newDom[0] - oldMin)

proc tablePropagate(tr: FznTranslator,
                    domains: var Table[string, seq[int]],
                    fixedVars: Table[string, int],
                    eliminated: PackedSet[int],
                    infeasible: var bool): bool =
    ## Generalized arc consistency propagation on table_int constraints.
    ## For each variable in each table constraint, remove domain values
    ## that have no support in any tuple (given current domains of all other variables).
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_table_int" and name != "table_int": continue
        if con.args.len < 2: continue
        let varsArg = con.args[0]
        let tableArg = con.args[1]
        if varsArg.kind != FznArrayLit or tableArg.kind != FznArrayLit: continue
        let arity = varsArg.elems.len
        if arity < 2: continue

        # Resolve variable names for all columns
        var varNames = newSeq[string](arity)
        var allValid = true
        for col in 0..<arity:
            varNames[col] = presolveVarName(varsArg.elems[col])
            if varNames[col] == "":
                allValid = false
                break
        if not allValid: continue

        # Parse flat table into tuples
        let flatElems = tableArg.elems
        if flatElems.len mod arity != 0: continue
        let nTuples = flatElems.len div arity
        var tuples = newSeq[seq[int]](nTuples)
        var parseOk = true
        for i in 0..<nTuples:
            tuples[i] = newSeq[int](arity)
            for col in 0..<arity:
                let elem = flatElems[i * arity + col]
                if elem.kind != FznIntLit:
                    parseOk = false
                    break
                tuples[i][col] = elem.intVal
            if not parseOk: break
        if not parseOk: continue

        # Resolve fixed values and build domain sets for each column
        var fixedCol = newSeq[bool](arity)
        var fixedVal = newSeq[int](arity)
        var domSets = newSeq[PackedSet[int]](arity)
        for col in 0..<arity:
            if tr.presolveIsFixed(varsArg.elems[col], fixedVars):
                fixedCol[col] = true
                fixedVal[col] = tr.presolveResolve(varsArg.elems[col], fixedVars)
            elif varNames[col] in domains:
                domSets[col] = domains[varNames[col]].toPackedSet()

        # Filter tuples to those compatible with all current domains/fixed values
        var supported = newSeq[PackedSet[int]](arity)
        for col in 0..<arity:
            supported[col] = initPackedSet[int]()

        for t in tuples:
            var valid = true
            for col in 0..<arity:
                if fixedCol[col]:
                    if t[col] != fixedVal[col]:
                        valid = false
                        break
                elif varNames[col] in domains:
                    if t[col] notin domSets[col]:
                        valid = false
                        break
            if valid:
                for col in 0..<arity:
                    supported[col].incl(t[col])

        # Tighten domains for non-fixed variables
        for col in 0..<arity:
            if fixedCol[col]: continue
            if varNames[col] notin domains: continue
            var allowed: seq[int]
            for v in domains[varNames[col]]:
                if v in supported[col]:
                    allowed.add(v)
            if allowed.len < domains[varNames[col]].len and allowed.len > 0:
                if presolveTightenDomain(domains, varNames[col], allowed, infeasible):
                    result = true
            elif allowed.len == 0:
                infeasible = true
                return

proc presolveResolveVarElems(tr: FznTranslator, arg: FznExpr): seq[FznExpr] =
    ## Resolve a constraint arg (FznArrayLit or named var array FznIdent) to its elements.
    case arg.kind
    of FznArrayLit: return arg.elems
    of FznIdent:
        # Look up the named variable array declaration in the model
        for decl in tr.model.variables:
            if decl.isArray and decl.name == arg.ident:
                if decl.value != nil and decl.value.kind == FznArrayLit:
                    return decl.value.elems
                break
        return @[]
    else: return @[]


proc arrayMinMaxPropagate(tr: FznTranslator,
                          domains: var Table[string, seq[int]],
                          fixedVars: Table[string, int],
                          eliminated: PackedSet[int],
                          infeasible: var bool): bool =
    ## Bounds propagation for `array_int_maximum(m, [x_1,...,x_n])` and
    ## `array_int_minimum(m, [x_1,...,x_n])`.
    ##
    ## For max:
    ##   Forward:  m ∈ [max_i lo(x_i), max_i hi(x_i)]
    ##   Backward: each x_i ≤ hi(m)
    ##   Strong:   if exactly one x_i has hi(x_i) ≥ lo(m), then that x_i ≥ lo(m)
    ## For min: symmetric (swap bounds and directions).
    ##
    ## Critical for objective tightening in max-of-sums models: the FZN
    ## flattener often emits `array_int_maximum(obj, [f_1,...,f_k])` with
    ## `obj ∈ [0..big]`, even though the tightest coarse bound is
    ## `max_i hi(f_i)`. Running to fixed-point couples tightening in both
    ## directions as the component f_i bounds shrink.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        let isMax = name == "array_int_maximum"
        let isMin = name == "array_int_minimum"
        if not isMax and not isMin: continue
        if con.args.len < 2: continue

        let mArg = con.args[0]
        if mArg.kind != FznIdent: continue
        let mName = mArg.ident
        let arrVars = presolveResolveVarElems(tr, con.args[1])
        if arrVars.len == 0: continue

        # Collect element (lo, hi, varName, fixed) quadruples.
        type ElemInfo = tuple[lo, hi: int, varName: string, fixed: bool]
        var elems = newSeq[ElemInfo](arrVars.len)
        var valid = true
        for i, e in arrVars:
            if tr.presolveIsFixed(e, fixedVars):
                let v = tr.presolveResolve(e, fixedVars)
                elems[i] = (lo: v, hi: v, varName: presolveVarName(e), fixed: true)
            else:
                let vn = presolveVarName(e)
                if vn == "" or vn notin domains:
                    valid = false; break
                let d = domains[vn]
                if d.len == 0:
                    valid = false; break
                elems[i] = (lo: d[0], hi: d[^1], varName: vn, fixed: false)
        if not valid: continue

        # m's current bounds
        var mLo, mHi: int
        var mFixed = false
        if mName in fixedVars:
            mLo = fixedVars[mName]; mHi = mLo; mFixed = true
        elif mName in domains:
            let d = domains[mName]
            if d.len == 0: continue
            mLo = d[0]; mHi = d[^1]
        else:
            continue

        var aggLo = elems[0].lo
        var aggHi = elems[0].hi
        for i in 1..<elems.len:
            if isMax:
                aggLo = max(aggLo, elems[i].lo)
                aggHi = max(aggHi, elems[i].hi)
            else:
                aggLo = min(aggLo, elems[i].lo)
                aggHi = min(aggHi, elems[i].hi)

        # Forward: tighten m to the aggregated bounds.
        if not mFixed:
            if presolveRestrictBounds(domains, mName, aggLo, aggHi, infeasible):
                result = true
                let d = domains[mName]
                if d.len == 0: return
                mLo = d[0]; mHi = d[^1]
        if infeasible: return

        # Backward: each element is bounded by m.
        if isMax:
            for i in 0..<elems.len:
                if elems[i].fixed or elems[i].varName == "": continue
                if presolveRestrictBounds(domains, elems[i].varName,
                                          low(int), mHi, infeasible):
                    result = true
                    let d = domains[elems[i].varName]
                    if d.len == 0: return
                    elems[i].lo = d[0]; elems[i].hi = d[^1]
                if infeasible: return
        else:
            for i in 0..<elems.len:
                if elems[i].fixed or elems[i].varName == "": continue
                if presolveRestrictBounds(domains, elems[i].varName,
                                          mLo, high(int), infeasible):
                    result = true
                    let d = domains[elems[i].varName]
                    if d.len == 0: return
                    elems[i].lo = d[0]; elems[i].hi = d[^1]
                if infeasible: return

        # Strong backward: if the max requires lo(m), at most one element can
        # still reach it — if that element is unique, it must be ≥ lo(m).
        if isMax and mLo > low(int):
            var candidate = -1
            var unique = true
            for i in 0..<elems.len:
                if elems[i].hi >= mLo:
                    if candidate < 0:
                        candidate = i
                    else:
                        unique = false; break
            if unique and candidate >= 0 and not elems[candidate].fixed and
                    elems[candidate].varName != "":
                if presolveRestrictBounds(domains, elems[candidate].varName,
                                          mLo, high(int), infeasible):
                    result = true
            if infeasible: return
        elif isMin and mHi < high(int):
            var candidate = -1
            var unique = true
            for i in 0..<elems.len:
                if elems[i].lo <= mHi:
                    if candidate < 0:
                        candidate = i
                    else:
                        unique = false; break
            if unique and candidate >= 0 and not elems[candidate].fixed and
                    elems[candidate].varName != "":
                if presolveRestrictBounds(domains, elems[candidate].varName,
                                          low(int), mHi, infeasible):
                    result = true
            if infeasible: return

proc intMaxMinPropagate(tr: FznTranslator,
                        domains: var Table[string, seq[int]],
                        fixedVars: Table[string, int],
                        eliminated: PackedSet[int],
                        infeasible: var bool): bool =
    ## Bounds propagation for int_max(a, b, c) and int_min(a, b, c).
    ## int_max: c = max(a, b)
    ##   Forward:  c ∈ [max(lo_a, lo_b), max(hi_a, hi_b)]
    ##   Backward: a <= c  (hi_a <= hi_c),  b <= c  (hi_b <= hi_c)
    ##   Strong:   if hi_b < lo_c then a = c  (lo_a >= lo_c)
    ## int_min: c = min(a, b)
    ##   Forward:  c ∈ [min(lo_a, lo_b), min(hi_a, hi_b)]
    ##   Backward: a >= c  (lo_a >= lo_c),  b >= c  (lo_b >= lo_c)
    ##   Strong:   if lo_b > hi_c then a = c  (hi_a <= hi_c)
    result = false

    type ArgInfo = tuple[lo, hi: int, name: string, isFixed: bool]
    proc getArgBounds(tr: FznTranslator, arg: FznExpr,
                      domains: Table[string, seq[int]],
                      fixedVars: Table[string, int]): ArgInfo =
        let vn = presolveVarName(arg)
        if tr.presolveIsFixed(arg, fixedVars):
            let v = tr.presolveResolve(arg, fixedVars)
            return (lo: v, hi: v, name: vn, isFixed: true)
        if vn != "" and vn in domains:
            let dom = domains[vn]
            if dom.len > 0:
                return (lo: dom[0], hi: dom[^1], name: vn, isFixed: false)
        # Unknown bounds — can't propagate
        return (lo: low(int) div 2, hi: high(int) div 2, name: vn, isFixed: true)

    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        let isMax = name == "int_max"
        let isMin = name == "int_min"
        if not isMax and not isMin: continue
        if con.args.len < 3: continue

        let a = getArgBounds(tr, con.args[0], domains, fixedVars)
        let b = getArgBounds(tr, con.args[1], domains, fixedVars)
        var c = getArgBounds(tr, con.args[2], domains, fixedVars)

        if isMax:
            # Forward: c = max(a, b)
            let fwdLo = max(a.lo, b.lo)
            let fwdHi = max(a.hi, b.hi)
            if not c.isFixed and c.name != "":
                if presolveRestrictBounds(domains, c.name, fwdLo, fwdHi, infeasible):
                    result = true
                    # Update local c bounds for subsequent backward propagation
                    c = getArgBounds(tr, con.args[2], domains, fixedVars)
            if infeasible: return

            # Backward: a <= max(a,b) = c, so a <= hi(c)
            if not a.isFixed and a.name != "":
                if presolveRestrictBounds(domains, a.name, low(int), c.hi, infeasible):
                    result = true
            if infeasible: return
            if not b.isFixed and b.name != "":
                if presolveRestrictBounds(domains, b.name, low(int), c.hi, infeasible):
                    result = true
            if infeasible: return

            # Strong backward: if hi(b) < lo(c), then max(a,b) = a = c
            if b.hi < c.lo and not a.isFixed and a.name != "":
                if presolveRestrictBounds(domains, a.name, c.lo, c.hi, infeasible):
                    result = true
            if infeasible: return
            if a.hi < c.lo and not b.isFixed and b.name != "":
                if presolveRestrictBounds(domains, b.name, c.lo, c.hi, infeasible):
                    result = true
            if infeasible: return

        elif isMin:
            # Forward: c = min(a, b)
            let fwdLo = min(a.lo, b.lo)
            let fwdHi = min(a.hi, b.hi)
            if not c.isFixed and c.name != "":
                if presolveRestrictBounds(domains, c.name, fwdLo, fwdHi, infeasible):
                    result = true
                    c = getArgBounds(tr, con.args[2], domains, fixedVars)
            if infeasible: return

            # Backward: a >= min(a,b) = c, so a >= lo(c)
            if not a.isFixed and a.name != "":
                if presolveRestrictBounds(domains, a.name, c.lo, high(int), infeasible):
                    result = true
            if infeasible: return
            if not b.isFixed and b.name != "":
                if presolveRestrictBounds(domains, b.name, c.lo, high(int), infeasible):
                    result = true
            if infeasible: return

            # Strong backward: if lo(b) > hi(c), then min(a,b) = a = c
            if b.lo > c.hi and not a.isFixed and a.name != "":
                if presolveRestrictBounds(domains, a.name, c.lo, c.hi, infeasible):
                    result = true
            if infeasible: return
            if a.lo > c.hi and not b.isFixed and b.name != "":
                if presolveRestrictBounds(domains, b.name, c.lo, c.hi, infeasible):
                    result = true
            if infeasible: return


proc intTimesPropagate(tr: FznTranslator,
                       domains: var Table[string, seq[int]],
                       fixedVars: Table[string, int],
                       eliminated: var PackedSet[int],
                       infeasible: var bool): bool =
    ## Bounds propagation for int_times(a, b, c): c = a * b.
    ## Forward:  c ∈ [min(corners), max(corners)] where corners = {a_lo*b_lo, a_lo*b_hi, a_hi*b_lo, a_hi*b_hi}
    ## Backward: when b bounds are strictly positive or negative, derive a bounds from c/b and vice versa
    result = false

    type ArgInfo = tuple[lo, hi: int, name: string, isFixed: bool]
    proc getArgBounds(tr: FznTranslator, arg: FznExpr,
                      domains: Table[string, seq[int]],
                      fixedVars: Table[string, int]): ArgInfo =
        let vn = presolveVarName(arg)
        if tr.presolveIsFixed(arg, fixedVars):
            let v = tr.presolveResolve(arg, fixedVars)
            return (lo: v, hi: v, name: vn, isFixed: true)
        if vn != "" and vn in domains:
            let dom = domains[vn]
            if dom.len > 0:
                return (lo: dom[0], hi: dom[^1], name: vn, isFixed: false)
        return (lo: low(int) div 2, hi: high(int) div 2, name: vn, isFixed: true)

    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_times": continue
        if con.args.len < 3: continue

        var a = getArgBounds(tr, con.args[0], domains, fixedVars)
        var b = getArgBounds(tr, con.args[1], domains, fixedVars)
        var c = getArgBounds(tr, con.args[2], domains, fixedVars)

        # Forward: c = a * b — compute bounds from four corner products
        let p1 = a.lo * b.lo
        let p2 = a.lo * b.hi
        let p3 = a.hi * b.lo
        let p4 = a.hi * b.hi
        let fwdLo = min(min(p1, p2), min(p3, p4))
        let fwdHi = max(max(p1, p2), max(p3, p4))
        if not c.isFixed and c.name != "":
            if presolveRestrictBounds(domains, c.name, fwdLo, fwdHi, infeasible):
                result = true
                c = getArgBounds(tr, con.args[2], domains, fixedVars)
        if infeasible: return

        # Backward: restrict a from c and b bounds
        # c = a * b → a = c / b (when b is strictly positive or strictly negative)
        if not a.isFixed and a.name != "":
            if b.lo > 0:
                # b > 0: a ∈ [ceil(c_lo / b_hi), floor(c_hi / b_lo)]
                let aLo = psCeilDiv(c.lo, b.hi)
                let aHi = psFloorDiv(c.hi, b.lo)
                if presolveRestrictBounds(domains, a.name, aLo, aHi, infeasible):
                    result = true
                    a = getArgBounds(tr, con.args[0], domains, fixedVars)
            elif b.hi < 0:
                # b < 0: division flips sign
                let aLo = psCeilDiv(-c.hi, -b.lo)
                let aHi = psFloorDiv(-c.lo, -b.hi)
                if presolveRestrictBounds(domains, a.name, aLo, aHi, infeasible):
                    result = true
                    a = getArgBounds(tr, con.args[0], domains, fixedVars)
            # b spans 0: can't tighten a from division alone
        if infeasible: return

        # Backward: restrict b from c and a bounds (symmetric)
        if not b.isFixed and b.name != "":
            if a.lo > 0:
                let bLo = psCeilDiv(c.lo, a.hi)
                let bHi = psFloorDiv(c.hi, a.lo)
                if presolveRestrictBounds(domains, b.name, bLo, bHi, infeasible):
                    result = true
            elif a.hi < 0:
                let bLo = psCeilDiv(-c.hi, -a.lo)
                let bHi = psFloorDiv(-c.lo, -a.hi)
                if presolveRestrictBounds(domains, b.name, bLo, bHi, infeasible):
                    result = true
        if infeasible: return

        # Elimination: if all three are fixed
        if a.isFixed and b.isFixed and c.isFixed:
            if a.lo * b.lo == c.lo and con.canEliminate:
                eliminated.incl(ci)
                result = true


proc productChainBoundPropagate(tr: FznTranslator,
                                domains: var Table[string, seq[int]],
                                fixedVars: Table[string, int],
                                eliminated: PackedSet[int],
                                infeasible: var bool): bool =
    ## Tighten bounds on common factors in int_times by detecting telescoping chains.
    ##
    ## Pattern: int_times(X, Y_i, P_i) + chain of int_lin_le constraints where
    ## intermediate variables cancel when summed + sum(Y_i) <= K.
    ## Derives: X >= (chain_constant + closing_offset) / (1 + K).
    ##
    ## Applies to cyclic scheduling, lot sizing, and models with multiplicative delays.
    result = false

    # Helper: resolve coefficient and variable arrays from an int_lin_le constraint
    proc resolveLinLeArgs(tr: FznTranslator, con: FznConstraint):
                          tuple[ok: bool, coeffs: seq[int], varNames: seq[string], rhs: int] =
        result.ok = false
        if con.args.len < 3: return
        var coeffsArg = con.args[0]
        if coeffsArg.kind == FznIdent:
            let arrName = coeffsArg.ident
            if arrName in tr.paramValues: return
            var found = false
            for decl in tr.model.parameters:
                if decl.isArray and decl.name == arrName:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        coeffsArg = decl.value; found = true
                    break
            if not found:
                for decl in tr.model.variables:
                    if decl.isArray and decl.name == arrName:
                        if decl.value != nil and decl.value.kind == FznArrayLit:
                            coeffsArg = decl.value; found = true
                        break
            if not found: return
        if coeffsArg.kind != FznArrayLit: return
        var varsArg = con.args[1]
        if varsArg.kind == FznIdent:
            var found = false
            for decl in tr.model.variables:
                if decl.isArray and decl.name == varsArg.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        varsArg = decl.value; found = true
                    break
            if not found:
                for decl in tr.model.parameters:
                    if decl.isArray and decl.name == varsArg.ident:
                        if decl.value != nil and decl.value.kind == FznArrayLit:
                            varsArg = decl.value; found = true
                        break
            if not found: return
        if varsArg.kind != FznArrayLit: return
        if coeffsArg.elems.len != varsArg.elems.len: return
        for i in 0..<coeffsArg.elems.len:
            if coeffsArg.elems[i].kind != FznIntLit: return
            result.coeffs.add(coeffsArg.elems[i].intVal)
            result.varNames.add(presolveVarName(varsArg.elems[i]))
            if result.varNames[^1] == "": return
        if con.args[2].kind == FznIntLit:
            result.rhs = con.args[2].intVal
        elif con.args[2].kind == FznIdent and con.args[2].ident in tr.paramValues:
            result.rhs = tr.paramValues[con.args[2].ident]
        else:
            return
        result.ok = true

    # Step 1: Group int_times by common factor (larger-domain variable)
    type ProductDef = object
        factorName, smallName, prodName: string
    var productsByFactor: Table[string, seq[ProductDef]]
    var prodToSmall: Table[string, string]

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        if stripSolverPrefix(con.name) != "int_times": continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue
        let aName = presolveVarName(con.args[0])
        let bName = presolveVarName(con.args[1])
        let pName = presolveVarName(con.args[2])
        if aName == "" or bName == "" or pName == "": continue
        let aDom = domains.getOrDefault(aName, @[])
        let bDom = domains.getOrDefault(bName, @[])
        let factorName = if aDom.len >= bDom.len: aName else: bName
        let smallName = if factorName == aName: bName else: aName
        productsByFactor.mgetOrPut(factorName, @[]).add(
            ProductDef(factorName: factorName, smallName: smallName, prodName: pName))
        prodToSmall[pName] = smallName

    if productsByFactor.len == 0: return

    # Step 2: For each factor group, detect chains
    for factorName, products in productsByFactor:
        if products.len < 3: continue

        var prodNames: HashSet[string]
        for p in products: prodNames.incl(p.prodName)

        # Find int_lin_le containing exactly one product variable,
        # where other chain variables have opposite-sign coefficients (for telescoping).
        # Handles both interior links (2 chain vars) and boundary links (1 chain var + 1 fixed).
        type ChainLink = object
            prodName: string
            prodCoeff: int
            upVar: string       # "" for boundary start (fixed value absorbed into rhs)
            downVar: string     # "" for boundary end
            chainCoeffAbs: int  # |coefficient| of chain variables
            rhs: int

        var chainLinks: seq[ChainLink]

        for ci, con in tr.model.constraints:
            if ci in eliminated: continue
            if stripSolverPrefix(con.name) != "int_lin_le": continue
            let parsed = tr.resolveLinLeArgs(con)
            if not parsed.ok: continue

            # Find exactly one product variable
            var prodIdx = -1
            var prodCount = 0
            for i, vn in parsed.varNames:
                if vn in prodNames:
                    prodIdx = i; inc prodCount
            if prodCount != 1: continue

            # Collect non-product, non-fixed variables
            var chainVars: seq[tuple[name: string, coeff: int]]
            var fixedContrib = 0
            var valid = true
            for i, vn in parsed.varNames:
                if i == prodIdx: continue
                if vn in fixedVars:
                    fixedContrib += parsed.coeffs[i] * fixedVars[vn]
                elif vn in domains:
                    chainVars.add((name: vn, coeff: parsed.coeffs[i]))
                else:
                    valid = false; break
            if not valid: continue
            if chainVars.len < 1 or chainVars.len > 2: continue

            let pc = parsed.coeffs[prodIdx]
            let adjustedRhs = parsed.rhs - fixedContrib

            if chainVars.len == 2:
                # Interior link: two chain variables with opposite-sign equal-magnitude coefficients
                if chainVars[0].coeff + chainVars[1].coeff != 0: continue
                var link = ChainLink(
                    prodName: parsed.varNames[prodIdx],
                    prodCoeff: pc,
                    chainCoeffAbs: abs(chainVars[0].coeff),
                    rhs: adjustedRhs)
                if (chainVars[0].coeff > 0) == (pc > 0):
                    link.downVar = chainVars[0].name
                    link.upVar = chainVars[1].name
                else:
                    link.downVar = chainVars[1].name
                    link.upVar = chainVars[0].name
                chainLinks.add(link)
            else:
                # Boundary link: one chain variable (the other was fixed)
                # The chain variable becomes either upVar or downVar
                let cv = chainVars[0]
                var link = ChainLink(
                    prodName: parsed.varNames[prodIdx],
                    prodCoeff: pc,
                    chainCoeffAbs: abs(cv.coeff),
                    rhs: adjustedRhs)
                # If chain var has same sign as product: it's the "down" end (boundary start)
                if (cv.coeff > 0) == (pc > 0):
                    link.downVar = cv.name
                    link.upVar = ""  # boundary start
                else:
                    link.upVar = cv.name
                    link.downVar = ""  # boundary end
                chainLinks.add(link)

        if chainLinks.len < 3: continue

        # Group chain links by (prodCoeff, chainCoeffAbs) — lower/upper bound constraints
        # may have opposite prodCoeff signs and must be processed separately.
        var linkGroups: Table[tuple[pc, cc: int], seq[int]]
        for i, link in chainLinks:
            let key = (pc: link.prodCoeff, cc: link.chainCoeffAbs)
            linkGroups.mgetOrPut(key, @[]).add(i)

        for groupKey, groupIndices in linkGroups:
            if groupIndices.len < 3: continue
            let refPC = groupKey.pc
            let refCC = groupKey.cc

            # Build chain graph from this group's links.
            const boundaryKey = "\x00__BOUNDARY__"
            var edgesFrom: Table[string, seq[int]]
            var asDown: HashSet[string]
            for li in groupIndices:
                let link = chainLinks[li]
                let up = if link.upVar == "": boundaryKey else: link.upVar
                let down = if link.downVar == "": boundaryKey else: link.downVar
                edgesFrom.mgetOrPut(up, @[]).add(li)
                asDown.incl(down)

            # Chain start: prefer boundary start (sentinel) if available
            var chainStart = ""
            var foundStart = false
            if boundaryKey in edgesFrom and boundaryKey notin asDown:
                chainStart = boundaryKey
                foundStart = true
            else:
                for v in edgesFrom.keys:
                    if v != boundaryKey and v notin asDown:
                        chainStart = v
                        foundStart = true
                        break
            if not foundStart: continue

            # Follow chain greedily
            var chain: seq[int]
            var current = chainStart
            var visited: HashSet[string]
            visited.incl(current)
            while current in edgesFrom:
                var nextLink = -1
                for li in edgesFrom[current]:
                    let dv = if chainLinks[li].downVar == "": boundaryKey else: chainLinks[li].downVar
                    if dv notin visited:
                        nextLink = li; break
                if nextLink < 0: break
                chain.add(nextLink)
                let dv = if chainLinks[nextLink].downVar == "": boundaryKey else: chainLinks[nextLink].downVar
                current = dv
                visited.incl(current)

            if chain.len < 3: continue
            let chainEnd = current

            # Sum the chain: intermediate chain variables cancel.
            var totalRhs = 0
            for li in chain: totalRhs += chainLinks[li].rhs

            let realChainEnd = if chainEnd == boundaryKey: "" else: chainEnd
            let startIsBoundary = (chainStart == boundaryKey)

            # Step 3: Find closing constraint linking chain endpoint to factor variable.
            var closingOffset = 0
            var foundClosing = false

            if realChainEnd != "":
                for ci, con in tr.model.constraints:
                    if ci in eliminated: continue
                    if stripSolverPrefix(con.name) != "int_lin_le": continue
                    let parsed = tr.resolveLinLeArgs(con)
                    if not parsed.ok: continue
                    var endCoeff, factCoeff, fixContrib: int
                    var endFound, factFound: bool
                    for i, vn in parsed.varNames:
                        if vn == realChainEnd: endCoeff = parsed.coeffs[i]; endFound = true
                        elif vn == factorName: factCoeff = parsed.coeffs[i]; factFound = true
                        elif vn in fixedVars: fixContrib += parsed.coeffs[i] * fixedVars[vn]
                        else: endFound = false; break
                    if not endFound or not factFound: continue
                    let adjRhs = parsed.rhs - fixContrib
                    if endCoeff > 0 and factCoeff < 0 and endCoeff == -factCoeff:
                        closingOffset = -(adjRhs div endCoeff)
                        foundClosing = true
                        break

            if not foundClosing: continue

            # Step 4: Find sum constraint on small variables
            var smallNameSet: HashSet[string]
            for li in chain:
                let sn = prodToSmall.getOrDefault(chainLinks[li].prodName, "")
                if sn != "": smallNameSet.incl(sn)

            var sumBound = int.high
            for ci, con in tr.model.constraints:
                if ci in eliminated: continue
                if stripSolverPrefix(con.name) != "int_lin_le": continue
                let parsed = tr.resolveLinLeArgs(con)
                if not parsed.ok: continue
                var allSmall = true
                var allSameCoeff = true
                var fixedSum = 0
                var varCount = 0
                let firstCoeff = if parsed.coeffs.len > 0: parsed.coeffs[0] else: 0
                if firstCoeff <= 0: continue
                for i, vn in parsed.varNames:
                    if parsed.coeffs[i] != firstCoeff:
                        allSameCoeff = false; break
                    if vn in fixedVars:
                        fixedSum += fixedVars[vn] * parsed.coeffs[i]
                    elif vn in smallNameSet:
                        inc varCount
                    else:
                        allSmall = false; break
                if allSmall and allSameCoeff and varCount >= smallNameSet.len div 2:
                    let bound = (parsed.rhs - fixedSum) div firstCoeff
                    if bound < sumBound:
                        sumBound = bound

            if sumBound >= int.high: continue

            # Step 5: Derive bound on factorName
            let startContrib = if startIsBoundary: 0
                               elif chainStart in fixedVars: refCC * fixedVars[chainStart]
                               elif chainStart in domains and domains[chainStart].len > 0:
                                   refCC * domains[chainStart][0]
                               else: continue

            let lhsCoeff = refPC * sumBound - refCC
            let rhsVal = totalRhs - startContrib - refCC * closingOffset

            if lhsCoeff < 0:
                # factor >= ceil(rhsVal / lhsCoeff) [division of negative by negative = positive]
                let newLo = psCeilDiv(-rhsVal, -lhsCoeff)
                if factorName in domains:
                    let oldDom = domains[factorName]
                    if oldDom.len > 0 and newLo > oldDom[0]:
                        if presolveRestrictBounds(domains, factorName, newLo, oldDom[^1], infeasible):
                            stderr.writeLine(&"[FZN] Product chain bound: {factorName} >= {newLo} " &
                                             &"(chain length {chain.len}, sum bound {sumBound})")
                            result = true
                        if infeasible: return
            elif lhsCoeff > 0:
                # factor <= floor(rhsVal / lhsCoeff)
                # This branch requires factor >= 0: the substitution sum(B) <= sumBound
                # into X * refPC * sumB is only valid when X is non-negative (refPC > 0 here).
                if factorName in domains:
                    let oldDom = domains[factorName]
                    if oldDom.len > 0 and oldDom[0] >= 0:
                        let newHi = rhsVal div lhsCoeff
                        if newHi < oldDom[^1]:
                            if presolveRestrictBounds(domains, factorName, oldDom[0], newHi, infeasible):
                                stderr.writeLine(&"[FZN] Product chain bound: {factorName} <= {newHi} " &
                                                 &"(chain length {chain.len}, sum bound {sumBound})")
                                result = true
                            if infeasible: return


proc varElementPropagate(tr: FznTranslator,
                         domains: var Table[string, seq[int]],
                         fixedVars: Table[string, int],
                         eliminated: PackedSet[int],
                         infeasible: var bool): bool =
    ## Bounds propagation for array_var_int_element(idx, varArr, val).
    ## Forward:  val ∈ ∪{arr[i].domain : i ∈ domain(idx)}
    ## Backward: prune idx values where arr[i].domain ∩ val.domain = ∅
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        if con.args.len < 3: continue

        # Resolve array elements (mix of constants and variables)
        let arrElems = tr.presolveResolveVarElems(con.args[1])
        if arrElems.len == 0: continue

        let idxName = presolveVarName(con.args[0])
        let valName = presolveVarName(con.args[2])

        # Get index domain
        var idxDom: seq[int]
        if idxName != "" and idxName in domains:
            idxDom = domains[idxName]
        elif tr.presolveIsFixed(con.args[0], fixedVars):
            idxDom = @[tr.presolveResolve(con.args[0], fixedVars)]
        else:
            continue

        # Get val domain bounds
        var valLo, valHi: int
        if valName != "" and valName in domains:
            let vd = domains[valName]
            if vd.len == 0: continue
            valLo = vd[0]
            valHi = vd[^1]
        elif tr.presolveIsFixed(con.args[2], fixedVars):
            let v = tr.presolveResolve(con.args[2], fixedVars)
            valLo = v
            valHi = v
        else:
            continue

        # Get element bounds for each array position
        proc elemBounds(tr: FznTranslator, elem: FznExpr,
                        domains: Table[string, seq[int]],
                        fixedVars: Table[string, int]): tuple[lo, hi: int, valid: bool] =
            if elem.kind == FznIntLit:
                return (lo: elem.intVal, hi: elem.intVal, valid: true)
            if elem.kind == FznBoolLit:
                let v = if elem.boolVal: 1 else: 0
                return (lo: v, hi: v, valid: true)
            let vn = presolveVarName(elem)
            if tr.presolveIsFixed(elem, fixedVars):
                let v = tr.presolveResolve(elem, fixedVars)
                return (lo: v, hi: v, valid: true)
            if vn != "" and vn in domains:
                let dom = domains[vn]
                if dom.len > 0:
                    return (lo: dom[0], hi: dom[^1], valid: true)
            return (lo: 0, hi: 0, valid: false)

        let isShifted = name == "array_var_int_element"  # 1-based indexing
        let idxOffset = if isShifted: 1 else: 0

        # Forward: compute reachable value bounds from idx domain
        var fwdLo = high(int)
        var fwdHi = low(int)
        var validIdxValues: seq[int]

        for i in idxDom:
            let arrIdx = i - idxOffset
            if arrIdx < 0 or arrIdx >= arrElems.len: continue
            let eb = elemBounds(tr, arrElems[arrIdx], domains, fixedVars)
            if not eb.valid:
                # Unknown element bounds — can't prune this index value
                validIdxValues.add(i)
                fwdLo = low(int)
                fwdHi = high(int)
                continue
            # Backward: check if element domain intersects val domain
            if eb.hi < valLo or eb.lo > valHi:
                # No overlap — this index value is infeasible
                discard
            else:
                validIdxValues.add(i)
                fwdLo = min(fwdLo, eb.lo)
                fwdHi = max(fwdHi, eb.hi)

        # Backward: prune idx domain to valid values
        if idxName != "" and idxName notin fixedVars:
            if validIdxValues.len < idxDom.len:
                if presolveTightenDomain(domains, idxName, validIdxValues, infeasible):
                    result = true
                if infeasible: return

        # Forward: tighten val domain bounds
        if valName != "" and valName notin fixedVars:
            if fwdLo != low(int) and fwdHi != high(int) and fwdLo <= fwdHi:
                if presolveRestrictBounds(domains, valName, fwdLo, fwdHi, infeasible):
                    result = true
                if infeasible: return

        # Forward (sparse): compute the set-union of element domains over the
        # valid index values. When elements have sparse domains (gaps), this is
        # strictly tighter than the [lo, hi] interval and can drop many values
        # from `val`'s domain. Budgeted by ValueUnionLimit so this stays cheap
        # on long arrays. Generalises the set-based propagation that the
        # constant-array variant `elementPropagate` already does.
        const ValueUnionLimit = 256
        if valName != "" and valName notin fixedVars and valName in domains:
            let curValDom = domains[valName]
            if curValDom.len > 1:
                var unionVals: PackedSet[int]
                var unionOk = true
                for i in validIdxValues:
                    let arrIdx = i - idxOffset
                    if arrIdx < 0 or arrIdx >= arrElems.len: continue
                    let elem = arrElems[arrIdx]
                    case elem.kind
                    of FznIntLit:
                        unionVals.incl(elem.intVal)
                    of FznBoolLit:
                        unionVals.incl(if elem.boolVal: 1 else: 0)
                    of FznIdent:
                        if tr.presolveIsFixed(elem, fixedVars):
                            unionVals.incl(tr.presolveResolve(elem, fixedVars))
                        else:
                            let vn = elem.ident
                            if vn != "" and vn in domains:
                                let dom = domains[vn]
                                if dom.len == 0:
                                    unionOk = false
                                    break
                                for v in dom: unionVals.incl(v)
                            else:
                                unionOk = false
                                break
                    else:
                        unionOk = false
                        break
                    if unionVals.len > ValueUnionLimit:
                        unionOk = false
                        break
                if unionOk and unionVals.len > 0 and unionVals.len < curValDom.len:
                    var newDom = newSeq[int](0)
                    for v in curValDom:
                        if v in unionVals: newDom.add(v)
                    if newDom.len < curValDom.len:
                        if presolveTightenDomain(domains, valName, newDom, infeasible):
                            result = true
                        if infeasible: return


proc varElementArrayBackwardPropagate(tr: FznTranslator,
                                      domains: var Table[string, seq[int]],
                                      fixedVars: Table[string, int],
                                      eliminated: PackedSet[int],
                                      infeasible: var bool): bool =
    ## Backward propagation from element result domains to array element domains.
    ## For array_var_int_element(idx, varArr, val) where idx is fixed (singleton):
    ##   varArr[idx] = val is forced, so domain(varArr[idx]) ⊆ domain(val).
    ## When multiple element constraints have fixed indices pointing to the same
    ## position, the intersection of all result domains applies (all are forced).
    ## Non-singleton indices are skipped: the position may not be accessed, so the
    ## element constraint alone cannot restrict the array variable's domain.
    result = false

    # Map: (arrayArgIdent, arrayIndex) → intersected result bounds from forced accesses
    type BoundsInfo = object
        reqLo: int
        reqHi: int

    var arrayAccessors: Table[string, Table[int, BoundsInfo]]

    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        if con.args.len < 3: continue

        let isShifted = name == "array_var_int_element"
        let idxOffset = if isShifted: 1 else: 0

        # Get array argument identifier
        let arrArg = con.args[1]
        var arrIdent = ""
        if arrArg.kind == FznIdent:
            arrIdent = arrArg.ident
        else:
            continue  # array literal, not a named variable array

        # Only propagate for fixed (singleton) indices — non-singleton means the
        # position may not be accessed, so the element constraint can't restrict it.
        let idxName = presolveVarName(con.args[0])
        var idxVal: int
        if idxName != "" and idxName in fixedVars:
            idxVal = fixedVars[idxName]
        elif idxName != "" and idxName in domains and domains[idxName].len == 1:
            idxVal = domains[idxName][0]
        elif tr.presolveIsFixed(con.args[0], fixedVars):
            idxVal = tr.presolveResolve(con.args[0], fixedVars)
        else:
            continue  # non-singleton index: can't prune array element

        # Get result domain bounds
        let valName = presolveVarName(con.args[2])
        var valLo, valHi: int
        if valName != "" and valName in domains:
            let vd = domains[valName]
            if vd.len == 0: continue
            valLo = vd[0]
            valHi = vd[^1]
        elif tr.presolveIsFixed(con.args[2], fixedVars):
            let v = tr.presolveResolve(con.args[2], fixedVars)
            valLo = v
            valHi = v
        else:
            continue

        let arrIdx = idxVal - idxOffset
        if arrIdx < 0: continue

        # Record/intersect bounds for this forced access
        if arrIdent notin arrayAccessors:
            arrayAccessors[arrIdent] = initTable[int, BoundsInfo]()

        if arrIdx in arrayAccessors[arrIdent]:
            # Multiple forced accesses: intersect bounds
            arrayAccessors[arrIdent][arrIdx].reqLo = max(arrayAccessors[arrIdent][arrIdx].reqLo, valLo)
            arrayAccessors[arrIdent][arrIdx].reqHi = min(arrayAccessors[arrIdent][arrIdx].reqHi, valHi)
        else:
            arrayAccessors[arrIdent][arrIdx] = BoundsInfo(reqLo: valLo, reqHi: valHi)

    if arrayAccessors.len == 0: return

    # Step 2: Resolve array element names and apply domain restrictions
    var totalRemoved = 0
    for arrIdent, posAccessors in arrayAccessors:
        # Resolve the array to get element variable names from model declarations
        let arrElems = tr.presolveResolveVarElems(FznExpr(kind: FznIdent, ident: arrIdent))
        if arrElems.len == 0: continue
        var elemNames: seq[string]
        for e in arrElems:
            if e.kind == FznIdent:
                elemNames.add(e.ident)
            else:
                elemNames.add("")  # constant element, not a variable

        for arrIdx, bounds in posAccessors:
            if arrIdx >= elemNames.len: continue
            let elemName = elemNames[arrIdx]
            if elemName == "" or elemName notin domains or elemName in fixedVars: continue

            if bounds.reqLo > bounds.reqHi:
                # Conflicting forced requirements — provably infeasible
                infeasible = true
                return

            # Standard intersection: keep only values in [reqLo, reqHi]
            let elemDom = domains[elemName]
            if elemDom.len == 0: continue

            var newDom: seq[int]
            for v in elemDom:
                if v >= bounds.reqLo and v <= bounds.reqHi:
                    newDom.add(v)
            if newDom.len < elemDom.len:
                totalRemoved += elemDom.len - newDom.len
                domains[elemName] = newDom
                result = true
                if newDom.len == 0:
                    infeasible = true
                    return

    if totalRemoved > 0:
        stderr.writeLine(&"[Presolve] Element array backward: {totalRemoved} domain values removed")


proc elementPropagate(tr: FznTranslator,
                      domains: var Table[string, seq[int]],
                      fixedVars: Table[string, int],
                      eliminated: PackedSet[int],
                      infeasible: var bool): bool =
    ## Bidirectional arc consistency for array_int_element(idx, constArr, val)
    ## and array_bool_element(idx, constArr, val) constraints.
    ## Forward:  val domain ⊆ {constArr[i-1] : i ∈ domain(idx)}
    ## Backward: idx domain ⊆ {i : constArr[i-1] ∈ domain(val)}
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_int_element", "array_int_element_nonshifted",
                        "array_bool_element"]: continue
        if con.args.len < 3: continue

        # Resolve constant array
        let constArray = try: tr.resolveIntArray(con.args[1])
                         except ValueError, KeyError: continue

        if constArray.len == 0: continue

        let idxName = presolveVarName(con.args[0])
        let valName = presolveVarName(con.args[2])

        # Get current domains
        var idxDom: seq[int]
        if idxName != "" and idxName in domains:
            idxDom = domains[idxName]
        elif tr.presolveIsFixed(con.args[0], fixedVars):
            idxDom = @[tr.presolveResolve(con.args[0], fixedVars)]
        else:
            continue

        var valDom: seq[int]
        if valName != "" and valName in domains:
            valDom = domains[valName]
        elif tr.presolveIsFixed(con.args[2], fixedVars):
            valDom = @[tr.presolveResolve(con.args[2], fixedVars)]
        else:
            continue

        let valSet = valDom.toPackedSet()

        # Forward: restrict val domain to reachable values from idx domain
        var reachableValSet: PackedSet[int]
        var reachableVals: seq[int]
        var validIdxValues: seq[int]
        for i in idxDom:
            let arrIdx = i - 1  # FZN 1-based to 0-based
            if arrIdx >= 0 and arrIdx < constArray.len:
                let v = constArray[arrIdx]
                if v in valSet:
                    if v notin reachableValSet:
                        reachableValSet.incl(v)
                        reachableVals.add(v)
                    validIdxValues.add(i)

        # Backward: restrict idx domain to indices with valid values
        if idxName != "" and idxName notin fixedVars:
            if presolveTightenDomain(domains, idxName, validIdxValues, infeasible):
                result = true
            if infeasible: return

        # Forward: restrict val domain to reachable values
        if valName != "" and valName notin fixedVars:
            if reachableVals.len > 0:
                reachableVals.sort()
                if presolveTightenDomain(domains, valName, reachableVals, infeasible):
                    result = true
                if infeasible: return


# ---------------------------------------------------------------------------
# Helpers + Pareto dominance pruning of element index domains
# ---------------------------------------------------------------------------

proc ppResolveConstIntSeq(tr: FznTranslator, arg: FznExpr): tuple[vals: seq[int], ok: bool] =
    ## Resolve an int_lin_* coefficient argument (or any constant int array arg)
    ## to a concrete seq[int]. Handles inline FznArrayLit and FznIdent references
    ## to parameter arrays in tr.arrayValues or decl.value.
    var a = arg
    if a.kind == FznIdent:
        if a.ident in tr.arrayValues:
            return (tr.arrayValues[a.ident], true)
        for decl in tr.model.parameters:
            if decl.isArray and decl.name == a.ident and decl.value != nil and
                    decl.value.kind == FznArrayLit:
                a = decl.value
                break
    if a.kind == FznArrayLit:
        var s = newSeq[int](a.elems.len)
        for i, e in a.elems:
            if e.kind != FznIntLit: return (@[], false)
            s[i] = e.intVal
        return (s, true)
    return (@[], false)

proc ppResolveVarExprSeq(tr: FznTranslator, arg: FznExpr): tuple[items: seq[FznExpr], ok: bool] =
    ## Resolve an int_lin_* vars argument to a flat seq[FznExpr]. Handles both
    ## inline FznArrayLit and FznIdent references to array declarations.
    var a = arg
    if a.kind == FznIdent:
        var found = false
        for decl in tr.model.variables:
            if decl.isArray and decl.name == a.ident and decl.value != nil and
                    decl.value.kind == FznArrayLit:
                a = decl.value
                found = true
                break
        if not found:
            for decl in tr.model.parameters:
                if decl.isArray and decl.name == a.ident and decl.value != nil and
                        decl.value.kind == FznArrayLit:
                    a = decl.value
                    break
    if a.kind == FznArrayLit:
        return (a.elems, true)
    return (@[], false)

proc computeVarDirections(tr: FznTranslator,
                          domains: Table[string, seq[int]],
                          fixedVars: Table[string, int],
                          eliminated: PackedSet[int]): Table[string, int] =
    ## Compute a per-variable "preferred direction":
    ##   +1 — weakly bigger value is better (reduces objective / relaxes constraints)
    ##   -1 — weakly smaller value is better
    ##    0 — mixed / unknown (do not rely on it)
    ##
    ## Three phases, run in order into a single `result` table:
    ##   A. Seed the objective variable (minimize → −1, maximize → +1). No-op for Satisfy.
    ##   B. Seed feasibility votes from int_lin_le / int_lin_lt. Each coefficient implies
    ##      a preferred sign for its variable; conflicting votes downgrade to 0 (sticky).
    ##   C. Iterated backward propagation through `defines_var` annotations on
    ##      int_lin_eq, int_times, int_plus, int_max, int_min, int_abs, bool2int,
    ##      array_int_maximum, array_int_minimum. Each rule propagates only when the
    ##      partial-derivative sign is knowable (see per-rule comments).
    ##
    ## Phase B runs before C so that satisfy-problem feasibility seeds can drive
    ## defines_var propagation. For min/max problems the semantics match the older
    ## order: setDir's sticky-zero conflict handling still downgrades contradictions.
    result = initTable[string, int]()

    proc setDir(t: var Table[string, int], name: string, d: int): bool =
        ## Returns true if the table entry was updated.
        if name == "" or d == 0: return false
        if name in t:
            if t[name] == 0: return false  # already marked mixed
            if t[name] != d:
                t[name] = 0
                return true
            return false
        else:
            t[name] = d
            return true

    proc argBounds(tr: FznTranslator, a: FznExpr,
                   doms: Table[string, seq[int]],
                   fx: Table[string, int]): tuple[lo, hi: int, ok: bool] =
        if a.kind == FznIntLit: return (a.intVal, a.intVal, true)
        if a.kind == FznBoolLit:
            let v = if a.boolVal: 1 else: 0
            return (v, v, true)
        if a.kind == FznIdent:
            if a.ident in fx: return (fx[a.ident], fx[a.ident], true)
            if a.ident in tr.paramValues:
                return (tr.paramValues[a.ident], tr.paramValues[a.ident], true)
            if a.ident in doms:
                let d = doms[a.ident]
                if d.len > 0: return (d[0], d[^1], true)
        return (0, 0, false)

    # Phase A: seed objective direction
    if tr.model.solve.objective != nil and tr.model.solve.objective.kind == FznIdent:
        case tr.model.solve.kind
        of Minimize: result[tr.model.solve.objective.ident] = -1
        of Maximize: result[tr.model.solve.objective.ident] = 1
        else: discard

    # Phase B: seed feasibility votes from int_lin_le/int_lin_lt.
    # For sum(c_i * x_i) ≤ rhs: bigger c_i * x_i is worse for feasibility, so
    # positive c → dir[x] = −1, negative c → dir[x] = +1. Multiple votes for the
    # same variable aggregate via setDir, with conflict collapsing to 0.
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let cname = stripSolverPrefix(con.name)
        if cname != "int_lin_le" and cname != "int_lin_lt": continue
        if con.args.len < 3: continue
        let (coeffs, okC) = ppResolveConstIntSeq(tr, con.args[0])
        if not okC: continue
        let (vars, okV) = ppResolveVarExprSeq(tr, con.args[1])
        if not okV: continue
        if coeffs.len != vars.len: continue
        for i in 0..<vars.len:
            if vars[i].kind != FznIdent: continue
            let c = coeffs[i]
            if c == 0: continue
            let newDir = if c > 0: -1 else: 1
            discard setDir(result, vars[i].ident, newDir)

    # Phase C: iterated backward propagation through defines_var chains.
    for iter in 0..<32:
        var changed = false
        for ci, con in tr.model.constraints:
            if ci in eliminated: continue
            if not con.hasAnnotation("defines_var"): continue
            let defAnn = con.getAnnotation("defines_var")
            if defAnn.args.len < 1 or defAnn.args[0].kind != FznIdent: continue
            let defName = defAnn.args[0].ident
            if defName notin result: continue
            let dirDef = result[defName]
            if dirDef == 0: continue
            let cname = stripSolverPrefix(con.name)

            # int_lin_eq with defines_var(y): y is linear combo of other vars.
            # From sum(c_i * x_i) = rhs we get y = (rhs − sum_{i≠y} c_i*x_i) / c_y,
            # so ∂y/∂x_i = −c_i / c_y. direction[x_i] = sign(∂y/∂x_i) * dirY.
            if cname == "int_lin_eq" and con.args.len >= 3:
                let (coeffs, okC) = ppResolveConstIntSeq(tr, con.args[0])
                if not okC: continue
                let (vars, okV) = ppResolveVarExprSeq(tr, con.args[1])
                if not okV: continue
                if coeffs.len != vars.len: continue

                var cy = 0
                for i in 0..<vars.len:
                    if vars[i].kind == FznIdent and vars[i].ident == defName:
                        cy = coeffs[i]
                        break
                if cy == 0: continue

                for i in 0..<vars.len:
                    if vars[i].kind != FznIdent: continue
                    if vars[i].ident == defName: continue
                    let ci = coeffs[i]
                    if ci == 0: continue
                    let sameSign = (ci > 0) == (cy > 0)
                    let newDir = if sameSign: -dirDef else: dirDef
                    if setDir(result, vars[i].ident, newDir):
                        changed = true

            # int_times(a, b, c) with defines_var(c): c = a * b.
            # ∂c/∂a = b, ∂c/∂b = a. Propagate only when the partner is sign-stable.
            elif cname == "int_times" and con.args.len == 3:
                let argA = con.args[0]
                let argB = con.args[1]
                let argC = con.args[2]
                if argC.kind != FznIdent or argC.ident != defName: continue

                let bB = argBounds(tr, argB, domains, fixedVars)
                if argA.kind == FznIdent and bB.ok:
                    var bSign = 0
                    if bB.lo >= 0: bSign = 1
                    elif bB.hi <= 0: bSign = -1
                    if bSign != 0:
                        if setDir(result, argA.ident, bSign * dirDef):
                            changed = true
                let aB = argBounds(tr, argA, domains, fixedVars)
                if argB.kind == FznIdent and aB.ok:
                    var aSign = 0
                    if aB.lo >= 0: aSign = 1
                    elif aB.hi <= 0: aSign = -1
                    if aSign != 0:
                        if setDir(result, argB.ident, aSign * dirDef):
                            changed = true

            # int_plus(a, b, c) with defines_var on any of a/b/c: a + b = c.
            # If c defined: ∂c/∂a = ∂c/∂b = +1 → dir[a] = dir[b] = dirC.
            # If a defined: a = c − b, so dir[c] = dirA, dir[b] = −dirA.
            # If b defined: b = c − a, so dir[c] = dirB, dir[a] = −dirB.
            elif cname == "int_plus" and con.args.len == 3:
                let argA = con.args[0]
                let argB = con.args[1]
                let argC = con.args[2]
                if argC.kind == FznIdent and argC.ident == defName:
                    if argA.kind == FznIdent and setDir(result, argA.ident, dirDef):
                        changed = true
                    if argB.kind == FznIdent and setDir(result, argB.ident, dirDef):
                        changed = true
                elif argA.kind == FznIdent and argA.ident == defName:
                    if argC.kind == FznIdent and setDir(result, argC.ident, dirDef):
                        changed = true
                    if argB.kind == FznIdent and setDir(result, argB.ident, -dirDef):
                        changed = true
                elif argB.kind == FznIdent and argB.ident == defName:
                    if argC.kind == FznIdent and setDir(result, argC.ident, dirDef):
                        changed = true
                    if argA.kind == FznIdent and setDir(result, argA.ident, -dirDef):
                        changed = true

            # int_max(a, b, c) / int_min(a, b, c) with defines_var(c): max/min are
            # weakly monotone in each operand (∂c/∂a ∈ [0,1]), so dir[a] = dir[b] = dirC.
            # Inverse direction (a or b defined) is skipped — not monotone.
            elif (cname == "int_max" or cname == "int_min") and con.args.len == 3:
                let argC = con.args[2]
                if argC.kind != FznIdent or argC.ident != defName: continue
                let argA = con.args[0]
                let argB = con.args[1]
                if argA.kind == FznIdent and setDir(result, argA.ident, dirDef):
                    changed = true
                if argB.kind == FznIdent and setDir(result, argB.ident, dirDef):
                    changed = true

            # int_abs(a, b) with defines_var(b): b = |a|. ∂b/∂a = sign(a), so we can
            # only propagate when dom(a) is sign-stable (strictly non-negative or
            # strictly non-positive). Inverse direction (a defined) is skipped.
            elif cname == "int_abs" and con.args.len == 2:
                let argA = con.args[0]
                let argB = con.args[1]
                if argB.kind != FznIdent or argB.ident != defName: continue
                if argA.kind != FznIdent: continue
                let aB = argBounds(tr, argA, domains, fixedVars)
                if not aB.ok: continue
                var aSign = 0
                if aB.lo >= 0: aSign = 1
                elif aB.hi <= 0: aSign = -1
                if aSign != 0:
                    if setDir(result, argA.ident, aSign * dirDef):
                        changed = true

            # bool2int(b, i): i = b (order isomorphism 0↔false, 1↔true).
            # Either defines_var orientation propagates 1:1.
            elif cname == "bool2int" and con.args.len == 2:
                let argB = con.args[0]
                let argI = con.args[1]
                if argI.kind == FznIdent and argI.ident == defName:
                    if argB.kind == FznIdent and setDir(result, argB.ident, dirDef):
                        changed = true
                elif argB.kind == FznIdent and argB.ident == defName:
                    if argI.kind == FznIdent and setDir(result, argI.ident, dirDef):
                        changed = true

            # array_int_maximum(m, arr) / array_int_minimum(m, arr) with
            # defines_var(m): m = max(arr) / min(arr). Weakly monotone in every
            # element of arr, so dir[x] = dirM for each x in arr.
            elif (cname == "array_int_maximum" or cname == "array_int_minimum") and
                    con.args.len == 2:
                let argM = con.args[0]
                if argM.kind != FznIdent or argM.ident != defName: continue
                let (arrVars, okV) = ppResolveVarExprSeq(tr, con.args[1])
                if not okV: continue
                for x in arrVars:
                    if x.kind == FznIdent and setDir(result, x.ident, dirDef):
                        changed = true

        if not changed: break


proc paretoElementIndexPrune(tr: FznTranslator,
                             domains: var Table[string, seq[int]],
                             fixedVars: Table[string, int],
                             eliminated: PackedSet[int],
                             infeasible: var bool): bool =
    ## For each variable x that is used *only* as the first argument (index)
    ## of array_int_element constraints and where the direction of every
    ## element result is known, prune Pareto-dominated values from dom(x).
    ##
    ## A value v dominates w iff for every element constraint with this index,
    ##   direction_i * arr_i[v-1]  ≥  direction_i * arr_i[w-1]
    ## with strict > in at least one i. Safe because all downstream effects of
    ## changing x are captured by the element results, and every such result
    ## has a consistent directional preference.
    ##
    ## Applications: VM/offer selection (capacity + cost), menu selection, any
    ## catalog-index variable feeding resource checks and a cost objective.
    result = false

    var totalRemoved = 0
    var prunedVars = 0

    type IndexUse = object
        arr: seq[int]
        valName: string
        idxOffset: int  # 1 for _element (1-based), 0 for _nonshifted

    var elementUses = initTable[string, seq[IndexUse]]()

    # Pass 1: collect candidate index variables and their element constraints.
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let cname = stripSolverPrefix(con.name)
        if cname notin ["array_int_element", "array_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent: continue
        let idxName = con.args[0].ident
        if idxName in fixedVars: continue
        if idxName notin domains: continue
        if domains[idxName].len <= 1: continue

        var constArr: seq[int]
        try:
            constArr = tr.resolveIntArray(con.args[1])
        except ValueError, KeyError:
            continue
        if constArr.len == 0: continue

        let valName = if con.args[2].kind == FznIdent: con.args[2].ident else: ""
        if valName == "": continue

        let idxOffset = if cname == "array_int_element": 1 else: 0

        if idxName notin elementUses:
            elementUses[idxName] = @[]
        elementUses[idxName].add(IndexUse(arr: constArr, valName: valName, idxOffset: idxOffset))

    if elementUses.len == 0: return

    # Pass 2: invalidate any index variable that has a non-index use
    # (appears anywhere except as args[0] of an array_int_element constraint).
    # Scans each argument three ways: as a direct scalar ident, as an inline
    # FznArrayLit, and (crucially) as an FznIdent referring to a variable array
    # declaration — e.g. `xs = [x1, x2, ...]` passed to `all_different(xs)`.
    var invalidated = initHashSet[string]()

    proc scanArg(tr: FznTranslator, arg: FznExpr,
                 elementUses: Table[string, seq[IndexUse]],
                 invalidated: var HashSet[string]) =
        case arg.kind
        of FznIdent:
            if arg.ident in elementUses:
                invalidated.incl(arg.ident)
                return
            # Might be a named variable array; resolve and scan its elements.
            let (items, ok) = ppResolveVarExprSeq(tr, arg)
            if ok:
                for e in items:
                    if e.kind == FznIdent and e.ident in elementUses:
                        invalidated.incl(e.ident)
        of FznArrayLit:
            for e in arg.elems:
                if e.kind == FznIdent and e.ident in elementUses:
                    invalidated.incl(e.ident)
        else: discard

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let cname = stripSolverPrefix(con.name)
        let isElement =
            cname in ["array_int_element", "array_int_element_nonshifted"] and
            con.args.len >= 3
        for i in 0..<con.args.len:
            # For element constraints, args[0] is the (valid) idx use — skip it;
            # still scan args[1] (constant array) and args[2] (result) to catch
            # candidates that show up there.
            if isElement and i == 0: continue
            scanArg(tr, con.args[i], elementUses, invalidated)

    # Directions only need to be computed if at least one candidate survived.
    var anyCandidate = false
    for nm in elementUses.keys:
        if nm notin invalidated:
            anyCandidate = true
            break
    if not anyCandidate: return

    let directions = computeVarDirections(tr, domains, fixedVars, eliminated)

    # Pass 3: for each surviving candidate, attach a direction to every element
    # result and run pairwise Pareto dominance elimination on the index domain.
    for idxName, usesRaw in elementUses:
        if idxName in invalidated: continue
        if idxName in fixedVars: continue
        if idxName notin domains: continue
        let dom = domains[idxName]
        if dom.len <= 1: continue

        # Resolve direction per element use; bail if any unknown.
        type Dir = object
            arr: seq[int]
            dir: int  # +1 or -1
            idxOffset: int
            valName: string
        var uses = newSeq[Dir](usesRaw.len)
        var allKnown = true
        for i, u in usesRaw:
            let d = directions.getOrDefault(u.valName, 0)
            if d == 0:
                allKnown = false
                break
            uses[i] = Dir(arr: u.arr, dir: d, idxOffset: u.idxOffset, valName: u.valName)
        if not allKnown: continue

        # Bounds check: every value in dom(idx) must map to a valid index into
        # every array, respecting each use's offset. If any use is out of range
        # for some dom value, skip — elementPropagate will eliminate that value
        # on a later iteration.
        var allInRange = true
        for v in dom:
            for u in uses:
                let arrIdx = v - u.idxOffset
                if arrIdx < 0 or arrIdx >= u.arr.len:
                    allInRange = false
                    break
            if not allInRange: break
        if not allInRange: continue

        # Guard against excessively large domains (O(n^2 * k) pairwise check).
        # 5000^2 * 5 ≈ 125M ops per presolve iteration — cap at 5000.
        if dom.len > 5000: continue

        # Pairwise Pareto elimination. Equal values are broken by keeping the
        # smaller index, so duplicate offers collapse to a single survivor.
        let n = dom.len
        var keep = newSeq[bool](n)
        for i in 0..<n: keep[i] = true

        for i in 0..<n:
            if not keep[i]: continue
            let vi = dom[i]
            for j in 0..<n:
                if i == j or not keep[j]: continue
                let vj = dom[j]
                # Does vi weakly dominate vj with strict > somewhere, OR are
                # they equal and vi has the smaller domain index?
                var allGeq = true
                var anyStrict = false
                for u in uses:
                    let a = u.dir * u.arr[vi - u.idxOffset]
                    let b = u.dir * u.arr[vj - u.idxOffset]
                    if a < b:
                        allGeq = false
                        break
                    if a > b:
                        anyStrict = true
                if allGeq and (anyStrict or i < j):
                    keep[j] = false

        var newDom: seq[int]
        for i in 0..<n:
            if keep[i]: newDom.add(dom[i])

        if newDom.len < dom.len:
            totalRemoved += dom.len - newDom.len
            inc prunedVars
            domains[idxName] = newDom
            result = true
            if newDom.len == 0:
                infeasible = true
                return

            # Forward-propagate the pruned idx domain to each element result:
            # val_i ⊆ {arr_i[v − offset] : v ∈ newDom}. Doing this inline cuts
            # fixpoint iterations and tightens downstream domains (price
            # contribution → Price[k] → objective) without waiting for
            # elementPropagate to re-run.
            for u in uses:
                if u.valName in fixedVars: continue
                if u.valName notin domains: continue
                var reachable: seq[int]
                var seen: PackedSet[int]
                for v in newDom:
                    let w = u.arr[v - u.idxOffset]
                    if w notin seen:
                        seen.incl(w)
                        reachable.add(w)
                reachable.sort()
                if presolveTightenDomain(domains, u.valName, reachable, infeasible):
                    result = true
                if infeasible: return

    if totalRemoved > 0:
        stderr.writeLine(&"[Presolve] Pareto element index prune: {totalRemoved} values removed across {prunedVars} vars")


proc regularPropagate(tr: FznTranslator,
                      domains: var Table[string, seq[int]],
                      fixedVars: Table[string, int],
                      eliminated: PackedSet[int],
                      infeasible: var bool): bool =
    ## Arc consistency propagation for fzn_regular constraints.
    ## Uses forward/backward DFA reachability to eliminate values unsupported by the DFA.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_regular": continue
        if con.args.len < 6: continue

        # Args: vars (array), Q, S, d (transition array), q0, F (set or array)
        let varElems = tr.presolveResolveVarElems(con.args[0])
        let n = varElems.len
        if n == 0: continue

        if con.args[1].kind != FznIntLit or con.args[2].kind != FznIntLit: continue
        if con.args[4].kind != FznIntLit: continue
        let Q = con.args[1].intVal
        let S = con.args[2].intVal
        let q0 = con.args[4].intVal

        # Guard against slow cases
        if Q * n > 100_000: continue

        # Extract transition table (flat int array: inline literal or named constant array)
        var trans: seq[int]  # trans[(q-1)*S + (s-1)] = next state (1-indexed)
        case con.args[3].kind
        of FznArrayLit:
            let transElems = con.args[3].elems
            if transElems.len != Q * S: continue
            var ok = true
            for e in transElems:
                if e.kind != FznIntLit: ok = false; break
                trans.add(e.intVal)
            if not ok: continue
        of FznIdent:
            try: trans = tr.resolveIntArray(con.args[3])
            except CatchableError: continue
            if trans.len != Q * S: continue
        else: continue

        # Extract accepting states F (set literal or array literal)
        var acceptSet: PackedSet[int]
        let fArg = con.args[5]
        case fArg.kind
        of FznArrayLit:
            for e in fArg.elems:
                if e.kind == FznIntLit: acceptSet.incl(e.intVal)
        of FznSetLit:
            for v in fArg.setElems: acceptSet.incl(v)
        of FznRange:
            for v in fArg.lo..fArg.hi: acceptSet.incl(v)
        else: continue

        # Build var names and check which are fixed
        var varNames: seq[string]
        var fixedInput: seq[int]  # -1 means free, else the symbol value
        for e in varElems:
            if tr.presolveIsFixed(e, fixedVars):
                varNames.add("")
                fixedInput.add(tr.presolveResolve(e, fixedVars))
                continue
            let vn = presolveVarName(e)
            varNames.add(vn)
            if vn != "" and vn in domains and domains[vn].len == 1:
                fixedInput.add(domains[vn][0])
            else:
                fixedInput.add(-1)

        # Forward pass: fwdReach[i] = set of states reachable before consuming vars[i]
        var fwdReach = newSeq[PackedSet[int]](n + 1)
        fwdReach[0].incl(q0)
        for i in 0..<n:
            if fwdReach[i].len == 0: break
            let sym = fixedInput[i]
            for q in fwdReach[i]:
                if sym >= 0:
                    let si = sym - 1
                    if si >= 0 and si < S:
                        let nq = trans[(q-1)*S + si]
                        if nq != 0: fwdReach[i+1].incl(nq)
                else:
                    for s in 0..<S:
                        let nq = trans[(q-1)*S + s]
                        if nq != 0: fwdReach[i+1].incl(nq)

        # Backward pass: bwdReach[i] = states at position i that can reach acceptance
        var bwdReach = newSeq[PackedSet[int]](n + 1)
        for q in acceptSet: bwdReach[n].incl(q)
        for i in countdown(n-1, 0):
            let sym = fixedInput[i]
            for q in 1..Q:
                if sym >= 0:
                    let si = sym - 1
                    if si >= 0 and si < S:
                        let nq = trans[(q-1)*S + si]
                        if nq in bwdReach[i+1]: bwdReach[i].incl(q)
                else:
                    for s in 0..<S:
                        let nq = trans[(q-1)*S + s]
                        if nq in bwdReach[i+1]:
                            bwdReach[i].incl(q)
                            break

        # Arc consistency: remove unsupported values from free variables
        for i in 0..<n:
            if fixedInput[i] >= 0: continue  # already fixed
            let vn = varNames[i]
            if vn == "" or vn notin domains: continue
            var allowed: seq[int]
            for v in domains[vn]:
                let si = v - 1  # 1-indexed symbol → 0-indexed
                if si < 0 or si >= S: continue
                for q in fwdReach[i]:
                    let nq = trans[(q-1)*S + si]
                    if nq in bwdReach[i+1]:
                        allowed.add(v)
                        break
            if allowed.len < domains[vn].len:
                if presolveTightenDomain(domains, vn, allowed, infeasible):
                    result = true
                    if infeasible: return


proc gccPropagate(tr: FznTranslator,
                  domains: var Table[string, seq[int]],
                  fixedVars: Table[string, int],
                  eliminated: PackedSet[int],
                  infeasible: var bool): bool =
    ## Arc consistency propagation for fzn_global_cardinality_closed constraints.
    ## Enforces count bounds: if a value's canCount == requiredCount, all remaining vars
    ## that can take it must take it; if mustCount == requiredCount, remove from others.
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_global_cardinality_closed" and name != "fzn_global_cardinality": continue
        if con.args.len < 3: continue

        # Args: vars (array), cover values (array), count values (array)
        let varElems = tr.presolveResolveVarElems(con.args[0])
        let coverElems = tr.presolveResolveVarElems(con.args[1])
        let countElems = tr.presolveResolveVarElems(con.args[2])
        if coverElems.len != countElems.len: continue
        if varElems.len == 0: continue

        var varNames: seq[string]
        for e in varElems:
            varNames.add(presolveVarName(e))

        # Process each cover value
        for k in 0..<coverElems.len:
            if infeasible: return
            if coverElems[k].kind != FznIntLit or countElems[k].kind != FznIntLit: continue
            let v = coverElems[k].intVal
            let required = countElems[k].intVal

            var mustCount = 0  # vars with domain == {v}
            var canCount = 0   # vars whose domain contains v
            var canIdxs: seq[int]  # indices of vars that can take v but aren't fixed to it

            for i, vn in varNames:
                if vn == "" or vn notin domains: continue
                let dom = domains[vn]
                if dom == @[v]:
                    inc mustCount
                    inc canCount
                elif v in dom:
                    inc canCount
                    canIdxs.add(i)

            if mustCount > required or canCount < required:
                infeasible = true
                return

            if canCount == required:
                # All vars that can take v must take v
                for i in canIdxs:
                    let vn = varNames[i]
                    if presolveTightenDomain(domains, vn, @[v], infeasible):
                        result = true
                    if infeasible: return

            if mustCount == required:
                # No other var can take v
                for i in canIdxs:
                    let vn = varNames[i]
                    if presolveRemoveValue(domains, vn, v, infeasible):
                        result = true
                    if infeasible: return


proc partitionPropagate(tr: FznTranslator,
                        domains: var Table[string, seq[int]],
                        fixedVars: Table[string, int],
                        eliminated: PackedSet[int],
                        infeasible: var bool): bool =
    ## Propagation for partition constraints (sum-of-indicators == 1).
    ## Detects int_lin_eq([1,...,1], [sel_1,...,sel_n], 1) where each sel_i
    ## chains through bool2int → int_ne_reif to a place variable.
    ## Rules:
    ## - If a place var's domain excludes nullValue → forced active → all others = {nullValue}
    ## - If all but one place var have domain = {nullValue} → remove nullValue from remaining
    result = false

    # Build reverse maps for tracing: sel_var → bool2int source, bool_var → ne_reif source + null value
    type Bool2IntInfo = object
        boolVar: string
    type NeReifInfo = object
        placeVar: string
        nullVal: int

    var bool2intMap = initTable[string, Bool2IntInfo]()  # sel_var → bool source
    var neReifMap = initTable[string, NeReifInfo]()  # bool_var → place source + null value

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name == "bool2int" and con.args.len >= 2:
            let bArg = con.args[0]
            let iArg = con.args[1]
            if bArg.kind == FznIdent and iArg.kind == FznIdent:
                bool2intMap[iArg.ident] = Bool2IntInfo(boolVar: bArg.ident)
        elif name == "int_ne_reif" and con.args.len >= 3:
            let xArg = con.args[0]
            let valArg = con.args[1]
            let bArg = con.args[2]
            if xArg.kind == FznIdent and bArg.kind == FznIdent:
                let nullVal = if valArg.kind == FznIntLit: valArg.intVal
                              elif valArg.kind == FznIdent and valArg.ident in fixedVars: fixedVars[valArg.ident]
                              elif valArg.kind == FznIdent and valArg.ident in tr.paramValues: tr.paramValues[valArg.ident]
                              else: continue
                neReifMap[bArg.ident] = NeReifInfo(placeVar: xArg.ident, nullVal: nullVal)

    # Find partition groups: int_lin_eq([1,...,1], [sel_1,...,sel_n], 1)
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznArrayLit or con.args[1].kind != FznArrayLit: continue

        # Check RHS = 1
        if not tr.presolveIsFixed(con.args[2], fixedVars): continue
        let rhs = tr.presolveResolve(con.args[2], fixedVars)
        if rhs != 1: continue

        let coeffs = con.args[0].elems
        let vars = con.args[1].elems
        if coeffs.len != vars.len or coeffs.len < 2: continue

        # Check all coefficients are 1
        var allOnes = true
        for c in coeffs:
            if c.kind != FznIntLit or c.intVal != 1:
                allOnes = false
                break
        if not allOnes: continue

        # Trace each sel variable back to place variable
        type PartMember = object
            selVar: string
            placeVar: string
            nullVal: int
        var members: seq[PartMember]
        var valid = true
        var nullVal = 0
        var nullValSet = false

        for vExpr in vars:
            if vExpr.kind != FznIdent:
                valid = false; break
            let selVar = vExpr.ident
            if selVar notin bool2intMap:
                valid = false; break
            let boolVar = bool2intMap[selVar].boolVar
            if boolVar notin neReifMap:
                valid = false; break
            let info = neReifMap[boolVar]
            if nullValSet:
                if info.nullVal != nullVal:
                    valid = false; break
            else:
                nullVal = info.nullVal
                nullValSet = true
            members.add(PartMember(selVar: selVar, placeVar: info.placeVar, nullVal: info.nullVal))

        if not valid or members.len < 2 or not nullValSet: continue

        # Propagation rule 1: forced member (domain excludes nullValue)
        var forcedIdx = -1
        var nForceable = 0
        for i, m in members:
            if m.placeVar in domains:
                let dom = domains[m.placeVar]
                var hasNull = false
                for v in dom:
                    if v == nullVal:
                        hasNull = true; break
                if not hasNull:
                    forcedIdx = i
                    inc nForceable
        if nForceable == 1:
            # Force all others to {nullValue}
            for i, m in members:
                if i == forcedIdx: continue
                if m.placeVar in domains and domains[m.placeVar] != @[nullVal]:
                    if presolveTightenDomain(domains, m.placeVar, @[nullVal], infeasible):
                        result = true
        elif nForceable > 1:
            # Multiple forced — infeasible
            infeasible = true
            return

        # Propagation rule 2: singleton remainder
        var nNull = 0
        var remainIdx = -1
        for i, m in members:
            if m.placeVar in domains and domains[m.placeVar] == @[nullVal]:
                inc nNull
            elif m.placeVar in fixedVars and fixedVars[m.placeVar] == nullVal:
                inc nNull
            else:
                remainIdx = i
        if nNull == members.len - 1 and remainIdx >= 0:
            # Remove nullValue from the remaining member
            let m = members[remainIdx]
            if m.placeVar in domains:
                if presolveRemoveValue(domains, m.placeVar, nullVal, infeasible):
                    result = true

proc binPackingLoadPropagate(tr: FznTranslator,
                             domains: var Table[string, seq[int]],
                             fixedVars: Table[string, int],
                             eliminated: PackedSet[int],
                             infeasible: var bool): bool =
    ## Subset-sum domain tightening for `fzn_bin_packing_load(load, bin, w)`.
    ##
    ## Each `load[b]` equals the sum of `w[i]` over items whose bin var takes
    ## value `b`. The achievable values of `load[b]` are therefore
    ##
    ##     { constOffset[b] + s : s ∈ subset-sums of { w[i] : domain(bin[i]) ∋ b } }
    ##
    ## where `constOffset[b]` is the contribution of items whose bin is a fixed
    ## literal equal to `b`. We intersect each load var's current domain with
    ## this reachable set. Running inside the presolve fixpoint lets the tight
    ## loads feed downstream bound propagation (e.g. objective ≥ max load).
    const subsetSumLimit = 8192
    result = false
    for ci, con in tr.model.constraints:
        if infeasible: return
        if ci in eliminated: continue
        let cname = stripSolverPrefix(con.name)
        if cname != "fzn_bin_packing_load": continue
        if con.args.len < 3: continue

        let loadElems = presolveResolveVarElems(tr, con.args[0])
        let binElems = presolveResolveVarElems(tr, con.args[1])
        if loadElems.len == 0 or binElems.len == 0: continue

        let weights = try: tr.resolveIntArray(con.args[2])
                      except CatchableError: continue
        if weights.len != binElems.len: continue

        # Partition items into variable-bin and fixed-bin, and resolve each
        # variable bin's current domain.
        type BinItem = tuple[weight: int, binDomain: seq[int]]
        var varItems: seq[BinItem]
        var constPerBin = initTable[int, int]()
        for i, e in binElems:
            if tr.presolveIsFixed(e, fixedVars):
                let b = tr.presolveResolve(e, fixedVars)
                constPerBin[b] = constPerBin.getOrDefault(b, 0) + weights[i]
            else:
                let vn = presolveVarName(e)
                if vn == "" or vn notin domains:
                    # Unknown bin domain — can't prune, skip the whole constraint.
                    varItems.setLen(0); break
                let dom = domains[vn]
                if dom.len == 0:
                    infeasible = true; return
                varItems.add((weight: weights[i], binDomain: dom))

        if varItems.len == 0 and constPerBin.len == 0: continue

        # Resolve load variable names and their current domains.
        var loadVarNames: seq[string]
        var loadBase = high(int)
        for _, item in varItems:
            for v in item.binDomain:
                loadBase = min(loadBase, v)
        for b, _ in constPerBin:
            loadBase = min(loadBase, b)
        if loadBase == high(int):
            loadBase = 1

        for e in loadElems:
            let vn = presolveVarName(e)
            loadVarNames.add(vn)

        # Cache subset-sum sets: key is the sorted active-weight string so bins
        # with the same support share the enumeration.
        var cache = initTable[string, HashSet[int]]()

        for bIdx, loadVarName in loadVarNames:
            if loadVarName == "": continue
            if loadVarName notin domains: continue
            let binValue = bIdx + loadBase
            let constOffset = constPerBin.getOrDefault(binValue, 0)

            var activeWeights = newSeqOfCap[int](varItems.len)
            for item in varItems:
                if binValue in item.binDomain:
                    activeWeights.add(item.weight)
            let key = activeWeights.sorted.join(",")

            var reachable: HashSet[int]
            if key in cache:
                reachable = cache[key]
            else:
                reachable = reachableWeightedSums(activeWeights, subsetSumLimit)
                cache[key] = reachable
            if reachable.len == 0: continue  # budget exceeded

            let currentDom = domains[loadVarName]
            var newDom = newSeqOfCap[int](currentDom.len)
            for v in currentDom:
                if (v - constOffset) in reachable:
                    newDom.add(v)
            if newDom.len == 0:
                infeasible = true
                return
            if newDom.len < currentDom.len:
                if presolveTightenDomain(domains, loadVarName, newDom, infeasible):
                    result = true

proc inferUnboundedDomains(tr: FznTranslator,
                           domains: var Table[string, seq[int]],
                           fixedVars: var Table[string, int],
                           eliminated: PackedSet[int],
                           infeasible: var bool): bool =
    ## Infer domains for "var int" (unbounded) variables that were skipped
    ## during initPresolveDomains. Uses two strategies:
    ##
    ## 1. Element results: array_int_element(idx, const_table, result)
    ##    → result domain = set of reachable table values
    ##
    ## 2. If-then-else reification: when X appears in exactly 2 int_eq_reif
    ##    constraints connected by complementary bool_clause (cond → b1, ¬cond → b2),
    ##    X's domain = union of the two reif target values/domains.
    result = false

    # --- Strategy 1: Element result inference ---
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let cname = stripSolverPrefix(con.name)
        if cname notin ["array_int_element", "array_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        let valName = presolveVarName(con.args[2])
        if valName == "" or valName in domains or valName in fixedVars: continue

        let constArray = try: tr.resolveIntArray(con.args[1])
                         except CatchableError: continue
        if constArray.len == 0: continue

        # Get reachable values via index domain
        var idxDom: seq[int]
        let idxName = presolveVarName(con.args[0])
        if idxName != "" and idxName in domains:
            idxDom = domains[idxName]
        elif tr.presolveIsFixed(con.args[0], fixedVars):
            idxDom = @[tr.presolveResolve(con.args[0], fixedVars)]
        else:
            idxDom = toSeq(1..constArray.len)  # Full range as fallback

        var seen = initHashSet[int]()
        var vals: seq[int]
        for i in idxDom:
            let arrIdx = i - 1  # FZN 1-based
            if arrIdx >= 0 and arrIdx < constArray.len:
                let v = constArray[arrIdx]
                if v notin seen:
                    seen.incl(v)
                    vals.add(v)
        if vals.len > 0:
            vals.sort()
            domains[valName] = vals
            result = true

    # --- Strategy 2: If-then-else reification inference ---
    # Collect int_eq_reif constraints grouped by first argument (unbounded vars only)
    var reifsByVar: Table[string, seq[tuple[boolVar: string, valArg: FznExpr]]]
    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        let cname = stripSolverPrefix(con.name)
        if cname != "int_eq_reif": continue
        if con.args.len < 3: continue
        let xName = presolveVarName(con.args[0])
        if xName == "" or xName in fixedVars or xName in domains: continue
        let bName = presolveVarName(con.args[2])
        if bName == "": continue
        if xName notin reifsByVar:
            reifsByVar[xName] = @[]
        reifsByVar[xName].add((boolVar: bName, valArg: con.args[1]))

    if reifsByVar.len == 0: return

    # Index bool_clause for implication patterns
    # Pattern A: bool_clause([b], [cond]) → cond → b
    # Pattern B: bool_clause([A, B], []) → ¬A → B, ¬B → A
    var impliedByPos: Table[string, seq[string]]  # b → conds where cond → b
    var impliedByNeg: Table[string, seq[string]]  # b → conds where ¬cond → b

    for ci, con in tr.model.constraints:
        if ci in eliminated: continue
        if con.name != "bool_clause": continue
        if con.args.len < 2: continue
        var posLits, negLits: seq[string]
        if con.args[0].kind == FznArrayLit:
            for e in con.args[0].elems:
                if e.kind == FznIdent: posLits.add(e.ident)
        if con.args[1].kind == FznArrayLit:
            for e in con.args[1].elems:
                if e.kind == FznIdent: negLits.add(e.ident)

        if posLits.len == 1 and negLits.len == 1:
            # cond → b
            let b = posLits[0]
            let cond = negLits[0]
            if b notin impliedByPos: impliedByPos[b] = @[]
            impliedByPos[b].add(cond)
        elif posLits.len == 2 and negLits.len == 0:
            # A ∨ B → ¬A → B and ¬B → A
            if posLits[0] notin impliedByNeg: impliedByNeg[posLits[0]] = @[]
            impliedByNeg[posLits[0]].add(posLits[1])
            if posLits[1] notin impliedByNeg: impliedByNeg[posLits[1]] = @[]
            impliedByNeg[posLits[1]].add(posLits[0])

    # For each unbounded variable with 2+ reifs, check complementarity
    for xName, reifs in reifsByVar:
        if reifs.len < 2: continue

        # Try all pairs of reifs
        var foundComplement = false
        var validReifIndices: seq[int]

        for i in 0..<reifs.len:
            for j in (i+1)..<reifs.len:
                let b1 = reifs[i].boolVar
                let b2 = reifs[j].boolVar
                # Check: ∃ cond such that (cond → b1) and (¬cond → b2)
                var complementary = false
                if b1 in impliedByPos:
                    for cond in impliedByPos[b1]:
                        if b2 in impliedByNeg and cond in impliedByNeg[b2]:
                            complementary = true
                            break
                if not complementary and b2 in impliedByPos:
                    for cond in impliedByPos[b2]:
                        if b1 in impliedByNeg and cond in impliedByNeg[b1]:
                            complementary = true
                            break
                if complementary:
                    foundComplement = true
                    validReifIndices = @[i, j]
                    break
            if foundComplement: break

        if not foundComplement: continue

        # Collect possible values from the complementary reifs
        var possibleValues = initHashSet[int]()
        var incomplete = false
        for idx in validReifIndices:
            let valArg = reifs[idx].valArg
            if valArg.kind == FznIntLit:
                possibleValues.incl(valArg.intVal)
            elif valArg.kind == FznIdent:
                let valName = valArg.ident
                if valName in fixedVars:
                    possibleValues.incl(fixedVars[valName])
                elif valName in domains:
                    for v in domains[valName]:
                        possibleValues.incl(v)
                else:
                    incomplete = true
                    break
            else:
                incomplete = true
                break

        if incomplete or possibleValues.len == 0: continue
        if possibleValues.len > 100_000: continue  # Safety

        var newDom: seq[int]
        for v in possibleValues: newDom.add(v)
        newDom.sort()
        domains[xName] = newDom
        result = true

    if result:
        # Re-run singleton detection for newly inferred domains
        discard fixSingletons(domains, fixedVars)


proc applyPresolveResults(tr: var FznTranslator,
                          domains: Table[string, seq[int]],
                          fixedVars: Table[string, int],
                          eliminated: PackedSet[int]) =
    ## Store tightened domains for use during translateVariables. Do NOT mutate
    ## the FznModel — pattern detection needs to see the original model structure.

    # Build varDomainIndex if not already built (O(1) lookups instead of O(V) scan)
    if tr.varDomainIndex.len == 0:
        for i, decl in tr.model.variables:
            if decl.isArray: continue
            tr.varDomainIndex[decl.name] = i

    # Store tightened domains in the translator (applied during translateVariables)
    for name, dom in domains:
        if dom.len == 0: continue
        # Check if domain was actually tightened
        if name notin tr.varDomainIndex: continue
        let decl = tr.model.variables[tr.varDomainIndex[name]]
        var originalLen: int
        case decl.varType.kind
        of FznIntRange:
            originalLen = decl.varType.hi - decl.varType.lo + 1
        of FznIntSet:
            originalLen = decl.varType.values.len
        of FznBool:
            originalLen = 2
        of FznInt:
            # Unbounded var: any inferred domain is a tightening
            tr.presolveDomains[name] = dom
            continue
        else:
            continue
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

    # CPM: single-pass forward/backward propagation for precedence chains.
    # Run once before the fixpoint loop — O(V+E) vs O(D) iterations needed by boundsPropagate.
    if cpmBoundsPropagate(tr, domains, fixedVars, eliminated, infeasible):
        discard fixSingletons(domains, fixedVars)

    # Permutation counting: for all_different groups with precedences, count ancestors/descendants
    # in the transitive closure and tighten bounds. Strictly stronger than CPM for permutations
    # when predecessors are independent (not in a single chain).
    if permutationCountingPropagate(tr, domains, fixedVars, eliminated, infeasible):
        discard fixSingletons(domains, fixedVars)

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

        # Step 3b: Implication transitive propagation (BFS through bool_clause chains)
        if implicationPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 3c: Disjunction-of-equalities domain reduction.
        # bool_clause([b_1,...,b_n],[]) where every b_i is int_eq_reif(x, c_i, b_i)
        # on a shared x ⇒ dom(x) ⊆ {c_i}. Recovers MZN's flattened "exists" pattern.
        if disjunctionEqualitiesPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 3d: Conjunction-of-inequalities (dual of step 3c).
        # array_bool_and([b_1,...,b_n], r) where every b_i is int_ne_reif(x, c_i, b_i)
        # on a shared x ⇒ r ↔ x ∉ {c_i}. Also catches AND-of-eq_reif inconsistency.
        if nonMembershipPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 4: Linear bounds propagation
        if boundsPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 4b: Big-M indicator linking domain pruning
        if bigMDomainPruning(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 4c: Discrete-domain reachable-values propagation for int_lin_eq.
        # Stronger than interval bounds: removes values in gaps of the achievable
        # value set when all terms have small enumerable domains. Budget-capped.
        if reachableValuesPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 5: AllDifferent propagation
        if allDiffPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6: Non-renewable resource pruning
        if nonRenewableResourcePruning(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6b: Element constraint propagation (bidirectional arc consistency)
        if elementPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6c: Variable element constraint propagation (bounds + index pruning)
        if varElementPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6c2: Variable element backward array propagation
        # Tighten array element domains using result domain intersection
        if varElementArrayBackwardPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6c3: Pareto dominance pruning for element index variables
        # When a var indexes constant arrays whose element results all have a
        # known directional preference (from the objective or capacity-style
        # constraints), dominated values in the index domain are removed.
        if paretoElementIndexPrune(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6d: int_max/int_min bounds propagation
        if intMaxMinPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6d2: array_int_maximum/minimum bounds propagation. Essential for
        # max-of-sums objectives (e.g. `obj = max(f_1,...,f_k)`) where the
        # default domain of the objective far exceeds the tightest aggregate
        # bound over the component fᵢ.
        if arrayMinMaxPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6d3: bin_packing_load subset-sum propagation. Tightens each
        # load variable's domain to the set of achievable subset sums of the
        # item weights. Runs inside the fixpoint so tightened loads feed into
        # boundsPropagate / arrayMinMaxPropagate (e.g. objective upper bound).
        if binPackingLoadPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6e: int_times bounds propagation
        if intTimesPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 6f: Product-chain telescoping bound propagation
        if productChainBoundPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 7: Table constraint propagation (arc consistency)
        if tablePropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 7b: Regular (DFA) arc consistency propagation
        if regularPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 7c: GCC arc consistency propagation
        if gccPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 7d: Infer domains for unbounded "var int" variables
        if inferUnboundedDomains(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 8: Partition propagation (forced member / singleton remainder)
        if partitionPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break

        # Step 9: Fix any newly-created singletons
        if fixSingletons(domains, fixedVars):
            changed = true

        inc totalIterations
        if not changed:
            break

    if infeasible:
        stderr.writeLine(&"[FZN] Presolve: infeasibility detected at iteration {totalIterations}")
        # Still apply what we can — the solver will discover infeasibility
        tr.applyPresolveResults(domains, fixedVars, eliminated)
        return

    # Count newly fixed variables (not counting pre-existing params)
    var nFixed = 0
    for name, val in fixedVars:
        if name notin tr.paramValues:
            inc nFixed

    tr.applyPresolveResults(domains, fixedVars, eliminated)

    if nFixed > 0 or eliminated.len > 0 or tr.presolveDomains.len > 0:
        stderr.writeLine(&"[FZN] Presolve: {totalIterations} iterations, {nFixed} vars fixed, {eliminated.len} constraints eliminated, {tr.presolveDomains.len} domains tightened")
    if tr.reachableValuesTightened > 0:
        stderr.writeLine(&"[FZN] Presolve: reachable-values propagation tightened {tr.reachableValuesTightened} domains ({tr.reachableValuesRemoved} values removed)")

proc repropagateBounds*(tr: var FznTranslator) =
    ## Run linear bounds propagation + big-M indicator pruning AFTER detection
    ## passes have potentially tightened `tr.presolveDomains`. The initial
    ## `presolve()` runs before detection, so any domain tightenings produced
    ## by detection passes (e.g., guard fixings from `detectBigMImplicationLinLe`)
    ## don't get a chance to cascade through the rest of the model.
    ##
    ## This pass picks up the current state and runs a small fix-point loop on
    ## the cheap, broadly-applicable propagators only (no AC, no element/table,
    ## no reif resolution — those are best-effort, and the search will find
    ## what's left).
    var domains = tr.initPresolveDomains()
    # Overlay detection-time tightenings.
    for name, dom in tr.presolveDomains:
        domains[name] = dom

    var fixedVars = initTable[string, int]()
    for name, val in tr.paramValues:
        fixedVars[name] = val
    for name, dom in domains:
        if dom.len == 1:
            fixedVars[name] = dom[0]

    var eliminated = initPackedSet[int]()
    # Seed eliminated from detection consumption so we don't redo work on
    # already-discharged constraints.
    for ci in tr.definingConstraints:
        eliminated.incl(ci)

    var infeasible = false
    var nIterations = 0
    let nFixedBefore = fixedVars.len
    let nTightenedBefore = tr.presolveDomains.len

    for iteration in 0..<5:
        var changed = false
        if fixSingletons(domains, fixedVars):
            changed = true
        if boundsPropagate(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break
        if bigMDomainPruning(tr, domains, fixedVars, eliminated, infeasible):
            changed = true
        if infeasible: break
        inc nIterations
        if not changed: break

    # Write back the tightened state.
    tr.applyPresolveResults(domains, fixedVars, eliminated)

    let nFixedAfter = fixedVars.len
    let nTightenedAfter = tr.presolveDomains.len
    let nNewFixed = nFixedAfter - nFixedBefore
    let nNewTightened = nTightenedAfter - nTightenedBefore
    if nNewFixed > 0 or nNewTightened > 0:
        stderr.writeLine(&"[FZN] Repropagate: {nIterations} iterations, " &
                          &"+{nNewFixed} vars fixed, +{nNewTightened} domains tightened")
