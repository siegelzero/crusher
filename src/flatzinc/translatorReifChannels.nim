## Included from translator.nim -- not a standalone module.
## Reification channel detection: int_eq_reif, bool2int, bool_not, le_reif, lin_le_reif, lin_eq_reif.

proc detectReifChannels(tr: var FznTranslator) =
    ## Detects int_eq_reif(x, val, b) :: defines_var(b) and bool2int(b, i) :: defines_var(i)
    ## patterns and marks the defined variables as channel variables.
    ## Channel variables get positions but are not searched; their values are computed
    ## from decision variables via element-style lookups.
    ##
    ## Handles two int_eq_reif variants:
    ##   - Constant val: b = (x == val) ? 1 : 0 → element lookup on x's domain
    ##   - Variable val: b = (x == y) ? 1 : 0 → 2D element lookup on (x,y) domains

    # First pass: find int_eq_reif with defines_var, not already consumed
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if (name != "int_eq_reif" and name != "int_ne_reif") or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 3 or con.args[2].kind != FznIdent:
            continue

        let bName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
            continue

        # Don't channel if already handled by another optimization
        if bName in tr.definedVarNames or bName in tr.channelVarNames:
            continue

        # Verify args[0] is a variable (not a constant) — we need a position for the index
        let xArg = con.args[0]
        if xArg.kind != FznIdent:
            continue
        # x must resolve to a position (not a defined variable with no position)
        # Exception: element channel aliases and bool2int identity aliases resolve to positions
        if xArg.ident in tr.definedVarNames and xArg.ident notin tr.elementChannelAliases and
             xArg.ident notin tr.bool2intIdentityAliases:
            continue

        # For var-to-var case, verify args[1] is also a positioned variable
        let valArg = con.args[1]
        if valArg.kind == FznIdent and valArg.ident in tr.definedVarNames and
             valArg.ident notin tr.elementChannelAliases and
             valArg.ident notin tr.bool2intIdentityAliases:
            continue

        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        tr.reifChannelDefs.add(ci)

    # Second pass: find bool2int with defines_var, not already consumed
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "bool2int" or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 2 or con.args[1].kind != FznIdent:
            continue

        let iName = con.args[1].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != iName:
            continue

        if iName in tr.definedVarNames or iName in tr.channelVarNames:
            continue

        # b must be a variable with a position (either search or channel)
        let bArg = con.args[0]
        if bArg.kind != FznIdent:
            continue
        if bArg.ident in tr.definedVarNames:
            continue

        tr.channelVarNames.incl(iName)
        tr.definingConstraints.incl(ci)
        tr.bool2intChannelDefs.add(ci)

    # Pass 2b: find bool_not with defines_var (b = 1 - a)
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_not" or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 2 or con.args[1].kind != FznIdent:
            continue

        let bName = con.args[1].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
            continue

        if bName in tr.definedVarNames or bName in tr.channelVarNames:
            continue

        # a must be a variable with a position (either search or channel)
        let aArg = con.args[0]
        if aArg.kind != FznIdent:
            continue
        if aArg.ident in tr.definedVarNames:
            continue

        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        tr.boolNotChannelDefs.add(ci)

    # Third pass: find bool_clause_reif with defines_var
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause_reif" or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 3 or con.args[2].kind != FznIdent:
            continue
        let rName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != rName:
            continue
        if rName in tr.definedVarNames or rName in tr.channelVarNames:
            continue
        # Verify all inputs in pos/neg arrays are positioned variables (not defined vars)
        let posElems = tr.resolveVarArrayElems(con.args[0])
        let negElems = tr.resolveVarArrayElems(con.args[1])
        if posElems.len == 0 and negElems.len == 0:
            continue  # No inputs — can't build a meaningful channel binding
        var allValid = true
        for elem in posElems:
            if elem.kind != FznIdent or elem.ident in tr.definedVarNames:
                allValid = false
                break
        if allValid:
            for elem in negElems:
                if elem.kind != FznIdent or elem.ident in tr.definedVarNames:
                    allValid = false
                    break
        if not allValid:
            continue
        tr.channelVarNames.incl(rName)
        tr.definingConstraints.incl(ci)
        tr.boolClauseReifChannelDefs.add(ci)

    # Fourth pass: find set_in_reif with defines_var
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "set_in_reif" or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 3 or con.args[2].kind != FznIdent:
            continue

        let bName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
            continue

        if bName in tr.definedVarNames or bName in tr.channelVarNames:
            continue

        let xArg = con.args[0]
        let setArg = con.args[1]

        if xArg.kind == FznIdent and xArg.ident notin tr.definedVarNames:
            # set_in_reif(var, constSet, b): x is variable, S is constant set
            if setArg.kind == FznSetLit or setArg.kind == FznRange:
                tr.channelVarNames.incl(bName)
                tr.definingConstraints.incl(ci)
                tr.setInReifChannelDefs.add(ci)
                continue
        if (xArg.kind == FznIntLit or
            (xArg.kind == FznIdent and xArg.ident in tr.paramValues)):
            # set_in_reif(const, varSet, b): x is constant, S is set variable
            # b = S.bools[x - lo] (identity channel)
            # Note: setVarBoolPositions not yet populated; check it's a var by excluding params
            if setArg.kind == FznIdent and
               setArg.ident notin tr.paramValues and
               setArg.ident notin tr.setParamValues:
                tr.channelVarNames.incl(bName)
                tr.definingConstraints.incl(ci)
                tr.setInReifChannelDefs.add(ci)
                continue

    # Fifth pass: find array_bool_and/array_bool_or with defines_var
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_and" and name != "array_bool_or":
            continue
        if not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 2 or con.args[1].kind != FznIdent:
            continue
        let rName = con.args[1].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != rName:
            continue
        if rName in tr.definedVarNames or rName in tr.channelVarNames:
            continue
        # Verify all inputs are positioned variables (not defined vars)
        let inputElems = tr.resolveVarArrayElems(con.args[0])
        if inputElems.len == 0:
            continue
        var allValid = true
        for elem in inputElems:
            if elem.kind != FznIdent or elem.ident in tr.definedVarNames:
                allValid = false
                break
        if not allValid:
            continue
        tr.channelVarNames.incl(rName)
        tr.definingConstraints.incl(ci)
        tr.boolAndOrChannelDefs.add(ci)

    # Sixth pass: find int_le_reif/int_lt_reif with defines_var
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if (name != "int_le_reif" and name != "int_lt_reif") or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 3 or con.args[2].kind != FznIdent:
            continue

        let bName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
            continue

        if bName in tr.definedVarNames or bName in tr.channelVarNames:
            continue

        # Check args[0] and args[1] — at least one must be a positioned variable
        # (not a defined variable), the other can be a constant or positioned variable
        let arg0 = con.args[0]
        let arg1 = con.args[1]

        # Check arg0: must be constant, channel var, or positioned variable (not defined var)
        # Exception: element channel aliases resolve to a channel position
        if arg0.kind == FznIdent and arg0.ident in tr.definedVarNames and
             arg0.ident notin tr.elementChannelAliases:
            continue
        # Check arg1: must be constant, channel var, or positioned variable (not defined var)
        if arg1.kind == FznIdent and arg1.ident in tr.definedVarNames and
             arg1.ident notin tr.elementChannelAliases:
            continue

        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        tr.leReifChannelDefs.add(ci)

    # Seventh pass: find int_lin_le_reif with defines_var
    # These define boolean variables as channels: b <-> sum(coeffs*vars) <= rhs
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le_reif" or not con.hasAnnotation("defines_var"):
            continue
        # int_lin_le_reif(coeffs, vars, rhs, b) — b is args[3]
        if con.args.len < 4 or con.args[3].kind != FznIdent:
            continue

        let bName = con.args[3].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
            continue

        if bName in tr.channelVarNames:
            continue

        # All variables in args[1] are resolvable: they'll either get a position
        # (non-defined vars), have a defining expression (definedVarNames from
        # int_lin_eq etc.), or be a channel variable. No resolvability check needed.

        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        tr.linLeReifChannelDefs.add(ci)

    # Eighth pass: find bool_eq_reif/bool_ne_reif with defines_var
    # bool_eq_reif(a, b, r): r = (a == b) where a, b are boolean
    # bool_ne_reif(a, b, r): r = (a != b) where a, b are boolean
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if (name != "bool_eq_reif" and name != "bool_ne_reif") or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 3 or con.args[2].kind != FznIdent:
            continue

        let rName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != rName:
            continue

        if rName in tr.definedVarNames or rName in tr.channelVarNames:
            continue

        # Both a and b must be positioned variables (not defined vars)
        let aArg = con.args[0]
        let bArg = con.args[1]
        if aArg.kind != FznIdent or aArg.ident in tr.definedVarNames:
            continue
        if bArg.kind != FznIdent or bArg.ident in tr.definedVarNames:
            continue

        tr.channelVarNames.incl(rName)
        tr.definingConstraints.incl(ci)
        tr.boolEqReifChannelDefs.add(ci)

    if tr.reifChannelDefs.len > 0 or tr.bool2intChannelDefs.len > 0 or
         tr.boolNotChannelDefs.len > 0 or
         tr.boolClauseReifChannelDefs.len > 0 or tr.setInReifChannelDefs.len > 0 or
         tr.boolAndOrChannelDefs.len > 0 or tr.leReifChannelDefs.len > 0 or
         tr.linLeReifChannelDefs.len > 0 or tr.linEqReifChannelDefs.len > 0 or
         tr.boolEqReifChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected reification channels: {tr.reifChannelDefs.len} int_eq/ne_reif, {tr.bool2intChannelDefs.len} bool2int, {tr.boolNotChannelDefs.len} bool_not, {tr.boolClauseReifChannelDefs.len} bool_clause_reif, {tr.setInReifChannelDefs.len} set_in_reif, {tr.boolAndOrChannelDefs.len} array_bool_and/or, {tr.leReifChannelDefs.len} int_le/lt_reif, {tr.linLeReifChannelDefs.len} int_lin_le_reif, {tr.boolEqReifChannelDefs.len} bool_eq/ne_reif")


proc detectConditionalBinaryChannels*(tr: var FznTranslator) =
    ## Detects binary variables X (domain {0,1}) that are functionally determined as:
    ##   X = condBool AND b2
    ## where condBool and b2 are both channel variables.
    ##
    ## Pattern (from gametes problem):
    ##   int_eq_reif(X, 1, b1) :: defines_var(b1)   → b1 ≡ X (binary)
    ##   bool_eq_reif(b1, b2, b3) :: defines_var(b3) → b3 = (b1 == b2)
    ##   bool_clause([b3], [condBool])                → condBool => b3
    ##   int_eq_reif(X, 0, b4) :: defines_var(b4)    → b4 = (X==0) ≡ ¬X
    ##   array_bool_and([..., b4, ...], conj)         → conj includes X=0
    ##   bool_clause([conj, condBool], [])             → ¬condBool => conj (=> X=0)
    ##
    ## Together: X = condBool ? b2 : 0 = condBool AND b2
    ## Channel binding: X = element(condBool*2 + b2, [0, 0, 0, 1])

    # Build maps for int_eq_reif(X, const, b) :: defines_var(b) where X is binary.
    # These are ALREADY consumed by detectReifChannels (in reifChannelDefs), so we
    # scan that list rather than looking for unclaimed constraints.
    var eqReif1Map: Table[string, tuple[bName: string, ci: int]]  # X → (b1, ci) for val=1

    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        let val = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
        if val != 1: continue
        let xName = con.args[0].ident
        let bName = con.args[2].ident
        # X must be binary (domain {0,1}) and NOT already a channel
        if xName in tr.channelVarNames or xName in tr.definedVarNames: continue
        let dom = tr.lookupVarDomain(xName)
        if dom != @[0, 1]: continue
        eqReif1Map[xName] = (bName, ci)

    if eqReif1Map.len == 0: return

    # Build reverse map: b1Name → xName for quick lookup
    var b1ToX: Table[string, string]
    for xName, entry in eqReif1Map.pairs:
        b1ToX[entry.bName] = xName

    # Build map: b1 → (X, bool_eq_reif b3 name, b2 name, bool_eq_reif ci)
    # from bool_eq_reif(b1, b2, b3) :: defines_var(b3) where b1 is from eqReif1Map
    var boolEqReifFromB1: Table[string, tuple[xName, b3Name, b2Name: string, boolEqCi: int]]
    for ci in tr.boolEqReifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "bool_eq_reif": continue
        if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent or con.args[2].kind != FznIdent: continue
        let a = con.args[0].ident
        let b = con.args[1].ident
        let r = con.args[2].ident
        # Check if either side is a b1 from eqReif1Map (the other side is b2, the neq indicator)
        # Don't require b2 to be channelized yet — int_lin_ne_reif channels may not be
        # detected until later (detectLinEqReifChannels), but b2 will get a position either way.
        if a in b1ToX:
            boolEqReifFromB1[a] = (b1ToX[a], r, b, ci)
        elif b in b1ToX:
            boolEqReifFromB1[b] = (b1ToX[b], r, a, ci)

    if boolEqReifFromB1.len == 0: return

    # Build map: positive literal var name → seq of bool_clause indices
    # for bool_clause([b3], [condBool]) patterns
    var posLiteralBoolClauses: Table[string, seq[tuple[condVar: string, ci: int]]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posElems = tr.extractVarElems(con.args[0])
        let negElems = tr.extractVarElems(con.args[1])
        if posElems.len == 1 and negElems.len == 1:
            if posElems[0].kind == FznIdent and negElems[0].kind == FznIdent:
                let posVar = posElems[0].ident
                let negVar = negElems[0].ident
                if negVar in tr.channelVarNames:
                    posLiteralBoolClauses.mgetOrPut(posVar, @[]).add((negVar, ci))

    # Match the complete pattern: X has eqReif1, bool_eq_reif(b1, b2, b3),
    # bool_clause([b3], [condBool]).
    # We only verify the forward half (cond => X=b2). The backward half
    # (¬cond => X=0) must also exist for the model to be satisfiable with
    # X binary, so MiniZinc always emits both directions together.
    var nDetected = 0
    for b1Name, info in boolEqReifFromB1.pairs:
        let xName = info.xName
        let b3Name = info.b3Name
        let b2Name = info.b2Name

        # Check bool_clause([b3], [condBool])
        if b3Name notin posLiteralBoolClauses: continue

        for clauseEntry in posLiteralBoolClauses[b3Name]:
            let condVar = clauseEntry.condVar

            # All conditions met: X = condVar AND b2
            tr.channelVarNames.incl(xName)
            tr.conditionalBinaryChannelDefs.add((targetVar: xName, condVar: condVar, neqVar: b2Name))
            inc nDetected
            break  # Only need one match

    if nDetected > 0:
        stderr.writeLine(&"[FZN] Detected {nDetected} conditional binary channels (X = cond AND b2)")


proc detectLinEqReifChannels*(tr: var FznTranslator) =
    ## Detect int_lin_eq_reif/int_lin_ne_reif(coeffs, vars, rhs, b) :: defines_var(b) patterns.
    ## b becomes a channel: b = (sum(coeffs*vars) == rhs) ? 1 : 0  (or != for ne)
    ## Must run AFTER detectCaseAnalysisChannels (which uses int_lin_eq_reif via linEqReifMap).
    var nEq, nNe = 0
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif" and name != "int_lin_ne_reif": continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 4 or con.args[3].kind != FznIdent: continue
        let bName = con.args[3].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName: continue
        if bName in tr.channelVarNames: continue
        # Always mark output as channel (even if constraint already consumed by
        # case-analysis) to prevent orphan search positions with no constraints
        tr.channelVarNames.incl(bName)
        if ci notin tr.definingConstraints:
            tr.definingConstraints.incl(ci)
            tr.linEqReifChannelDefs.add(ci)
        if name == "int_lin_eq_reif": inc nEq
        else: inc nNe
    if tr.linEqReifChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.linEqReifChannelDefs.len} int_lin_eq/ne_reif channels (eq={nEq} ne={nNe})")

