## Included from translator.nim -- not a standalone module.

proc detectCountPatterns(tr: var FznTranslator) =
    ## Detects int_lin_eq → bool2int → int_eq_reif chains that implement count_eq.
    ## Pattern: for each value v, n constraints of form:
    ##   int_eq_reif(x_j, v, b_j) :: defines_var(b_j)
    ##   bool2int(b_j, ind_j) :: defines_var(ind_j)
    ##   int_lin_eq([1, -1, ..., -1], [target, ind_1, ..., ind_n], 0)
    ## This replaces O(n²) decomposed constraints with a single count_eq.

    # Build maps: variable name → defining constraint index
    # bool2int(boolVar, intVar) :: defines_var(intVar) → intVar maps to constraint index
    var bool2intDefs: Table[string, int]  # indicator var name → constraint index
    # int_eq_reif(x, val, boolVar) :: defines_var(boolVar) → boolVar maps to constraint index
    var intEqReifDefs: Table[string, int]  # bool var name → constraint index

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue  # Already consumed by defined-var elimination
        let name = stripSolverPrefix(con.name)
        if name == "bool2int" and con.hasAnnotation("defines_var"):
            # bool2int(boolVar, intVar) :: defines_var(intVar)
            if con.args.len >= 2 and con.args[1].kind == FznIdent:
                bool2intDefs[con.args[1].ident] = ci
        elif name == "int_eq_reif" and con.hasAnnotation("defines_var"):
            # int_eq_reif(x, val, boolVar) :: defines_var(boolVar)
            if con.args.len >= 3 and con.args[2].kind == FznIdent:
                intEqReifDefs[con.args[2].ident] = ci

    # Now scan for int_lin_eq constraints that match the pattern
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq":
            continue

        # int_lin_eq(coeffs, vars, rhs)
        # Pattern: coeffs = [1, -1, -1, ..., -1], rhs = 0
        # vars = [target, ind_1, ind_2, ..., ind_n]
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if rhs != 0:
            continue

        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len < 2:
            continue

        # Check coefficient pattern: first is 1, rest are -1
        if coeffs[0] != 1:
            continue
        var allNegOne = true
        for i in 1..<coeffs.len:
            if coeffs[i] != -1:
                allNegOne = false
                break
        if not allNegOne:
            continue

        # Extract variable names - handle both inline arrays and named array references
        let vars = con.args[1]
        var varElems: seq[FznExpr]
        if vars.kind == FznArrayLit:
            varElems = vars.elems
        elif vars.kind == FznIdent:
            # Named array reference - find the array declaration
            var found = false
            for decl in tr.model.variables:
                if decl.isArray and decl.name == vars.ident and decl.value != nil and decl.value.kind == FznArrayLit:
                    varElems = decl.value.elems
                    found = true
                    break
            if not found:
                continue
        else:
            continue

        if varElems.len < 2:
            continue

        let targetArg = varElems[0]
        if targetArg.kind != FznIdent:
            continue
        let targetName = targetArg.ident

        # Check all indicator variables trace back through bool2int → int_eq_reif
        var countValue: int
        var countValueSet = false
        var arrayVarNames: seq[string]
        var consumedConstraints: seq[int]
        var consumedVarNames: seq[string]
        var valid = true

        for i in 1..<varElems.len:
            let indArg = varElems[i]
            if indArg.kind != FznIdent:
                valid = false
                break

            let indName = indArg.ident
            if indName notin bool2intDefs:
                valid = false
                break

            let b2iIdx = bool2intDefs[indName]
            let b2iCon = tr.model.constraints[b2iIdx]
            # bool2int(boolVar, intVar) — extract boolVar
            if b2iCon.args[0].kind != FznIdent:
                valid = false
                break
            let boolVarName = b2iCon.args[0].ident

            if boolVarName notin intEqReifDefs:
                valid = false
                break

            let eqReifIdx = intEqReifDefs[boolVarName]
            let eqReifCon = tr.model.constraints[eqReifIdx]
            # int_eq_reif(x, val, boolVar) — extract x and val
            if eqReifCon.args[0].kind != FznIdent:
                valid = false
                break
            let v = try: tr.resolveIntArg(eqReifCon.args[1]) except ValueError, KeyError: (valid = false; 0)
            if not valid:
                break
            if not countValueSet:
                countValue = v
                countValueSet = true
            elif v != countValue:
                valid = false
                break

            arrayVarNames.add(eqReifCon.args[0].ident)
            consumedConstraints.add(b2iIdx)
            consumedConstraints.add(eqReifIdx)
            consumedVarNames.add(indName)
            consumedVarNames.add(boolVarName)

        if not valid or not countValueSet:
            continue

        # Pattern detected! Record it.
        tr.countEqPatterns[ci] = CountEqPattern(
            linEqIdx: ci,
            countValue: countValue,
            targetVarName: targetName,
            arrayVarNames: arrayVarNames
        )

        # Mark consumed constraints (skip during translation)
        # Note: the int_lin_eq itself (ci) is NOT added to definingConstraints —
        # it's handled by the countEqPatterns check in the main loop
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)  # the bool2int and int_eq_reif

        # Mark intermediate variable names as defined (skip position creation)
        for vn in consumedVarNames:
            tr.definedVarNames.incl(vn)

        stderr.writeLine(&"[FZN] Detected count_eq pattern: count({arrayVarNames.len} vars, {countValue}) == {targetName}")

proc detectWeightedSameValuePattern(tr: var FznTranslator) =
    ## Detects weighted same-value objective pattern:
    ##   int_eq_reif(x_i, x_j, b_ij) :: defines_var(b_ij)  -- variable-variable equality
    ##   bool2int(b_ij, ind_ij) :: defines_var(ind_ij)
    ##   int_lin_eq(coeffs, [objective, ind_1, ...], rhs) :: defines_var(objective)
    ## Produces: objective = rhs + Σ(-coeff_k * δ(x_i == x_j))

    # Build maps: variable name → defining constraint index
    var bool2intDefs: Table[string, int]  # indicator var → constraint index
    var intEqReifDefs: Table[string, int]  # bool var → constraint index

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "bool2int" and con.hasAnnotation("defines_var"):
            if con.args.len >= 2 and con.args[1].kind == FznIdent:
                bool2intDefs[con.args[1].ident] = ci
        elif name == "int_eq_reif" and con.hasAnnotation("defines_var"):
            if con.args.len >= 3 and con.args[2].kind == FznIdent:
                intEqReifDefs[con.args[2].ident] = ci

    # Only scan if this is a minimize/maximize problem
    if tr.model.solve.kind notin {Minimize, Maximize}:
        return
    if tr.model.solve.objective == nil or tr.model.solve.objective.kind != FznIdent:
        return
    let objectiveName = tr.model.solve.objective.ident

    # Find the int_lin_eq that defines the objective
    # Note: don't skip definingConstraints — collectDefinedVars may have already claimed this
    for ci, con in tr.model.constraints:
        if ci in tr.countEqPatterns:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq" or not con.hasAnnotation("defines_var"):
            continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent:
            continue
        if ann.args[0].ident != objectiveName:
            continue

        # Found the defining constraint for the objective
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue

        # Extract variable names
        let vars = con.args[1]
        var varElems: seq[FznExpr]
        if vars.kind == FznArrayLit:
            varElems = vars.elems
        elif vars.kind == FznIdent:
            var found = false
            for decl in tr.model.variables:
                if decl.isArray and decl.name == vars.ident and decl.value != nil and decl.value.kind == FznArrayLit:
                    varElems = decl.value.elems
                    found = true
                    break
            if not found:
                continue
        else:
            continue

        if coeffs.len != varElems.len or varElems.len < 2:
            continue

        # First variable must be the objective (coefficient for objective itself)
        if varElems[0].kind != FznIdent or varElems[0].ident != objectiveName:
            continue
        let objCoeff = coeffs[0]  # usually 1

        # Try to trace all other variables through bool2int → int_eq_reif(varA, varB, bool)
        var pairs: seq[tuple[varNameA, varNameB: string, coeff: int]]
        var consumedConstraints: seq[int]
        var consumedVarNames: seq[string]
        var valid = true

        for i in 1..<varElems.len:
            let indArg = varElems[i]
            if indArg.kind != FznIdent:
                valid = false
                break

            let indName = indArg.ident
            if indName notin bool2intDefs:
                valid = false
                break

            let b2iIdx = bool2intDefs[indName]
            let b2iCon = tr.model.constraints[b2iIdx]
            if b2iCon.args[0].kind != FznIdent:
                valid = false
                break
            let boolVarName = b2iCon.args[0].ident

            if boolVarName notin intEqReifDefs:
                valid = false
                break

            let eqReifIdx = intEqReifDefs[boolVarName]
            let eqReifCon = tr.model.constraints[eqReifIdx]
            # int_eq_reif(argA, argB, boolVar) — both must be variable idents
            if eqReifCon.args[0].kind != FznIdent or eqReifCon.args[1].kind != FznIdent:
                valid = false
                break

            let varNameA = eqReifCon.args[0].ident
            let varNameB = eqReifCon.args[1].ident
            # Both must be real variables (not defined/consumed)
            if varNameA in tr.definedVarNames or varNameB in tr.definedVarNames:
                valid = false
                break

            # Pair coefficient: from objCoeff * objective + coeff_k * ind_k = rhs
            # => objective = (rhs - coeff_k * ind_k) / objCoeff
            # => pairCoeff = -coeff_k / objCoeff
            if (-coeffs[i] mod objCoeff) != 0:
                valid = false
                break
            let pairCoeff = -coeffs[i] div objCoeff
            pairs.add((varNameA: varNameA, varNameB: varNameB, coeff: pairCoeff))
            consumedConstraints.add(b2iIdx)
            consumedConstraints.add(eqReifIdx)
            consumedVarNames.add(indName)
            consumedVarNames.add(boolVarName)

        if not valid or pairs.len == 0:
            continue
        if (rhs mod objCoeff) != 0:
            continue

        # Pattern detected!
        tr.weightedSameValuePairs = pairs
        tr.weightedSameValueConstant = rhs div objCoeff
        tr.weightedSameValueObjName = objectiveName

        # Mark consumed constraints
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)
        # The int_lin_eq itself is a defining constraint (we handle the objective directly)
        tr.definingConstraints.incl(ci)

        # Mark intermediate variable names as defined (skip position creation)
        for vn in consumedVarNames:
            tr.definedVarNames.incl(vn)
        # Also mark the objective as defined
        tr.definedVarNames.incl(objectiveName)

        stderr.writeLine(&"[FZN] Detected weighted same-value pattern: {pairs.len} pairs, constant={tr.weightedSameValueConstant}, objective={objectiveName}")
        break  # Only one objective

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
        # Exception: element channel aliases resolve to a single channel position
        if xArg.ident in tr.definedVarNames and xArg.ident notin tr.elementChannelAliases:
            continue

        # For var-to-var case, verify args[1] is also a positioned variable
        let valArg = con.args[1]
        if valArg.kind == FznIdent and valArg.ident in tr.definedVarNames and
             valArg.ident notin tr.elementChannelAliases:
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

        # args[0] must be a positioned variable
        let xArg = con.args[0]
        if xArg.kind != FznIdent:
            continue
        if xArg.ident in tr.definedVarNames:
            continue

        # args[1] must be a set literal or range
        let setArg = con.args[1]
        if setArg.kind != FznSetLit and setArg.kind != FznRange:
            continue

        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        tr.setInReifChannelDefs.add(ci)

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

    if tr.reifChannelDefs.len > 0 or tr.bool2intChannelDefs.len > 0 or
         tr.boolNotChannelDefs.len > 0 or
         tr.boolClauseReifChannelDefs.len > 0 or tr.setInReifChannelDefs.len > 0 or
         tr.boolAndOrChannelDefs.len > 0 or tr.leReifChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected reification channels: {tr.reifChannelDefs.len} int_eq/ne_reif, {tr.bool2intChannelDefs.len} bool2int, {tr.boolNotChannelDefs.len} bool_not, {tr.boolClauseReifChannelDefs.len} bool_clause_reif, {tr.setInReifChannelDefs.len} set_in_reif, {tr.boolAndOrChannelDefs.len} array_bool_and/or, {tr.leReifChannelDefs.len} int_le/lt_reif")


proc detectSetUnionChannels(tr: var FznTranslator) =
    ## Detects set_union(A, B, C) :: defines_var(C) patterns, identifies linear chains,
    ## and traces set comprehension patterns (singleton→product→source sets).
    ## Chain intermediates and singletons are marked for skipping in translateVariables.
    ## Must be called before translateVariables.

    # Build set of known set variable names from the model
    var setVarNames: HashSet[string]
    for decl in tr.model.variables:
        if not decl.isArray and decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
            setVarNames.incl(decl.name)

    # Collect all set_union with defines_var
    type UnionRec = object
        ci: int
        aName, leafName, cName: string
    var unions: seq[UnionRec]
    var producedBy: Table[string, int]  # cName -> index into unions

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "set_union" or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 3 or con.args[2].kind != FznIdent:
            continue
        let cName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != cName:
            continue
        if cName notin setVarNames:
            continue
        let aName = if con.args[0].kind == FznIdent: con.args[0].ident else: ""
        let leafName = if con.args[1].kind == FznIdent: con.args[1].ident else: ""
        let idx = unions.len
        unions.add(UnionRec(ci: ci, aName: aName, leafName: leafName, cName: cName))
        producedBy[cName] = idx

    if unions.len == 0:
        return

    # Build forward adjacency: aName -> list of union indices where it's the accumulated input
    var fromA: Table[string, seq[int]]
    for i, u in unions:
        if u.aName.len > 0:
            fromA.mgetOrPut(u.aName, @[]).add(i)

    # Find chain starts: unions whose aName is NOT produced by another union (or is constant)
    var chainStartIndices: seq[int]
    for i, u in unions:
        if u.aName.len == 0 or u.aName notin producedBy:
            chainStartIndices.add(i)

    # Trace chains from each start
    var inChain: PackedSet[int]  # union indices that are part of a chain
    for startIdx in chainStartIndices:
        var chain: seq[int]  # indices into unions
        var current = startIdx
        while true:
            chain.add(current)
            inChain.incl(current)
            let cName = unions[current].cName
            if cName in fromA and fromA[cName].len == 1:
                current = fromA[cName][0]
            else:
                break

        if chain.len < 2:
            # Single union: handle as individual (no benefit from chain-collapsing)
            for idx in chain:
                inChain.excl(idx)
            continue

        # Build chain info
        var info = SetUnionChainInfo(
            resultName: unions[chain[^1]].cName,
            baseName: unions[chain[0]].aName,
            constraintIndices: newSeq[int](chain.len))

        # Check if base is a constant set
        if info.baseName.len == 0:
            info.baseIsConst = true
            info.baseConstVals = initHashSet[int]()
        elif info.baseName in tr.setParamValues:
            info.baseIsConst = true
            info.baseConstVals = toHashSet(tr.setParamValues[info.baseName])
        else:
            info.baseIsConst = false

        for j, idx in chain:
            info.constraintIndices[j] = unions[idx].ci
            info.leafNames.add(unions[idx].leafName)
            if j < chain.len - 1:
                info.intermediateNames.add(unions[idx].cName)

        # Mark all chain results as channel variables + mark constraints as consumed
        for idx in chain:
            let u = unions[idx]
            tr.channelVarNames.incl(u.cName)
            tr.definingConstraints.incl(u.ci)

        # Mark intermediates to skip boolean creation
        for iname in info.intermediateNames:
            tr.skipSetVarNames.incl(iname)

        tr.setUnionChains.add(info)

    # Handle non-chain unions as individual channels (existing behavior)
    for i, u in unions:
        if i in inChain:
            continue
        if u.cName in tr.channelVarNames:
            continue
        tr.channelVarNames.incl(u.cName)
        tr.definingConstraints.incl(u.ci)
        tr.setUnionChannelDefs.add((ci: u.ci, resultName: u.cName))

    # --- Set comprehension pattern detection ---
    # For each chain, try to trace singletons to their int_times products.
    # Pattern: set_card(S,1) + set_in(val_expr, S) where val_expr = k * product
    # from int_lin_eq([k,-1],[product,val_expr],0) :: defines_var(val_expr)

    # Build reverse map: variable name -> constraint that defines it (via defines_var)
    var definedByCI: Table[string, int]
    for ci, con in tr.model.constraints:
        if not con.hasAnnotation("defines_var"):
            continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len > 0 and ann.args[0].kind == FznIdent:
            definedByCI[ann.args[0].ident] = ci

    # Build singleton map: set_card(S, 1) → S name + ci
    var singletonCardCI: Table[string, int]  # S name -> set_card ci
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "set_card" and con.args.len >= 2:
            if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit and con.args[1].intVal == 1:
                singletonCardCI[con.args[0].ident] = ci

    # Build set_in map: set_in(val_expr, S) → (ci, val_expr)
    var singletonInCI: Table[string, tuple[ci: int, valArg: FznExpr]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "set_in" and con.args.len >= 2 and con.args[1].kind == FznIdent:
            let sName = con.args[1].ident
            if sName in singletonCardCI:
                singletonInCI[sName] = (ci: ci, valArg: con.args[0])

    for chainIdx in 0..<tr.setUnionChains.len:
        let chain = tr.setUnionChains[chainIdx]

        # Check if all leaves are singletons with traceable products
        var compInfo = SetComprehensionInfo(chainIdx: chainIdx)
        var allTraced = true

        for leafName in chain.leafNames:
            if leafName notin singletonCardCI or leafName notin singletonInCI:
                allTraced = false
                break

            let inInfo = singletonInCI[leafName]
            let valArg = inInfo.valArg

            if valArg.kind == FznIntLit:
                # Literal value (e.g., set_in(0, seed)) — contributes a fixed value
                # Not a product-traced pair; skip as a comprehension pair
                # but still consume the constraints
                compInfo.consumedConstraints.incl(inInfo.ci)
                compInfo.consumedConstraints.incl(singletonCardCI[leafName])
                tr.skipSetVarNames.incl(leafName)
                continue

            if valArg.kind != FznIdent:
                allTraced = false
                break

            let valName = valArg.ident

            # Trace val_expr to find sumVal and product variable.
            # Two patterns:
            #   1. val_expr defined by int_lin_eq([k,-1],[product,val_expr],0) → sumVal=k
            #   2. val_expr defined by int_times(a,b,val_expr) → sumVal=1 (product IS val_expr)
            if valName notin definedByCI:
                allTraced = false
                break

            let defCI = definedByCI[valName]
            let defCon = tr.model.constraints[defCI]
            let defName = stripSolverPrefix(defCon.name)

            var sumVal: int
            var productVarName: string

            if defName == "int_lin_eq" and defCon.args.len >= 3 and
                 defCon.args[0].kind == FznArrayLit and defCon.args[1].kind == FznArrayLit:
                # Pattern 1: int_lin_eq([k,-1],[product,val_expr],0) → val_expr = k * product
                let coeffs = defCon.args[0].elems
                let vars = defCon.args[1].elems
                if coeffs.len == 2 and vars.len == 2 and
                     coeffs[0].kind == FznIntLit and coeffs[1].kind == FznIntLit and
                     coeffs[1].intVal == -1 and vars[0].kind == FznIdent:
                    sumVal = coeffs[0].intVal
                    productVarName = vars[0].ident
                else:
                    allTraced = false
                    break
            elif defName == "int_times" and defCon.args.len >= 3:
                # Pattern 2: int_times(a,b,val_expr) → val_expr = a*b, sumVal depends on max domain
                # For boolean inputs, val_expr is 0 or 1, so this contributes value 1 when active
                # Find the actual sum value from the singleton's universe
                # The singleton set S has universe lo..hi. The set_in(val_expr, S) means
                # S = {val_expr}. Since val_expr domain is 0..1 and S has set_card=1,
                # the singleton either contains {0} or {1}. So sumVal = 1.
                sumVal = 1
                productVarName = valName  # the product IS the val_expr
            else:
                allTraced = false
                break

            compInfo.pairs.add(SetComprehensionPair(sumVal: sumVal, productVarName: productVarName))
            compInfo.consumedConstraints.incl(inInfo.ci)
            compInfo.consumedConstraints.incl(singletonCardCI[leafName])
            tr.skipSetVarNames.incl(leafName)

        if allTraced and compInfo.pairs.len > 0:
            # Mark consumed constraints
            for ci in compInfo.consumedConstraints.items:
                tr.definingConstraints.incl(ci)
            tr.setComprehensions.add(compInfo)

    # Log results
    var nChainUnions = 0
    for chain in tr.setUnionChains:
        nChainUnions += chain.constraintIndices.len
    if tr.setUnionChains.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.setUnionChains.len} set_union chains ({nChainUnions} unions, {tr.skipSetVarNames.len} set vars skipped)")
    if tr.setComprehensions.len > 0:
        var nPairs = 0
        for comp in tr.setComprehensions:
            nPairs += comp.pairs.len
        stderr.writeLine(&"[FZN] Detected {tr.setComprehensions.len} set comprehension patterns ({nPairs} product pairs)")
    if tr.setUnionChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.setUnionChannelDefs.len} individual set_union channel variables")

proc detectEqualityCopyVars(tr: var FznTranslator) =
    ## Detects "equality copy" variables: vars that are copies of another variable
    ## linked via int_eq_reif(copy, original, indicator) :: defines_var(indicator),
    ## where the copy only appears in defines_var constraints.
    ## These copies are eliminated by aliasing them to the original variable.

    # Phase 1: Build set of variable names referenced by "real" (non-defines_var) constraints
    var nonDefinesVarRefs: HashSet[string]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        if con.hasAnnotation("defines_var"):
            continue
        # Collect all FznIdent names from arguments
        for arg in con.args:
            if arg.kind == FznIdent:
                nonDefinesVarRefs.incl(arg.ident)
            elif arg.kind == FznArrayLit:
                for elem in arg.elems:
                    if elem.kind == FznIdent:
                        nonDefinesVarRefs.incl(elem.ident)

    # Build set of variables that are elements of any array referenced by constraints.
    # Variables used indirectly through array names (e.g., job_end in array_var_int_element)
    # must not be treated as equality copies, even if the referencing constraint has defines_var.
    var arrayElementVars: HashSet[string]
    block:
        # Map array names to their element variable names
        var arrElems: Table[string, seq[string]]
        for decl in tr.model.variables:
            if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
                var elems: seq[string]
                for e in decl.value.elems:
                    if e.kind == FznIdent:
                        elems.add(e.ident)
                if elems.len > 0:
                    arrElems[decl.name] = elems
        # Find arrays referenced in any constraint
        for ci, con in tr.model.constraints:
            for arg in con.args:
                if arg.kind == FznIdent and arg.ident in arrElems:
                    for elemName in arrElems[arg.ident]:
                        arrayElementVars.incl(elemName)

    # Phase 2: Scan reifChannelDefs for int_eq_reif(A, B, indicator) where A is a copy of B
    # First pass: count how many DISTINCT comparison partners each variable has.
    # A variable compared with multiple different partners is being equality-tested,
    # not copied (e.g., community-detection: x[i] compared with many other x[j]).
    var comparisonPartners: Table[string, HashSet[string]]  # var → set of distinct partners
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif":
            continue
        let arg0 = con.args[0]
        let arg1 = con.args[1]
        if arg0.kind != FznIdent or arg1.kind != FznIdent:
            continue
        let aName = arg0.ident
        let bName = arg1.ident
        if aName notin comparisonPartners:
            comparisonPartners[aName] = initHashSet[string]()
        comparisonPartners[aName].incl(bName)
        if bName notin comparisonPartners:
            comparisonPartners[bName] = initHashSet[string]()
        comparisonPartners[bName].incl(aName)

    # Second pass: identify candidates
    var candidates: Table[string, string]  # copy → original
    var candidateCIs: Table[string, int]   # copy → constraint index
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif":
            continue
        let arg0 = con.args[0]
        let arg1 = con.args[1]
        # Both must be identifiers (variables, not constants)
        if arg0.kind != FznIdent or arg1.kind != FznIdent:
            continue
        let aName = arg0.ident
        let bName = arg1.ident
        # A (the copy) must not be in any real constraint, and not already defined/channel/param
        if aName in nonDefinesVarRefs:
            continue
        if aName in tr.definedVarNames or aName in tr.channelVarNames or aName in tr.paramValues:
            continue
        # A must not be an element of an array used in constraints (indirect reference)
        if aName in arrayElementVars:
            continue
        # B (the original) must not be a parameter
        if bName in tr.paramValues:
            continue
        # A must only be compared with ONE partner (B) — if compared with multiple
        # different variables, it's an independent decision variable being equality-tested
        if aName in comparisonPartners and comparisonPartners[aName].len > 1:
            continue
        # B must also only be compared with one partner — otherwise it's a hub variable
        # that multiple variables are tested against, not a simple copy source
        if bName in comparisonPartners and comparisonPartners[bName].len > 1:
            continue
        # First match per A wins
        if aName notin candidates:
            candidates[aName] = bName
            candidateCIs[aName] = ci

    if candidates.len == 0:
        return

    # Phase 3: Resolve chains (A→B→C becomes A→C), drop self-cycles
    var toRemove: seq[string]
    for copyName in candidates.keys:
        var target = candidates[copyName]
        var visited: HashSet[string]
        visited.incl(copyName)
        while target in candidates and target notin visited:
            visited.incl(target)
            target = candidates[target]
        if target == copyName:
            # Self-cycle (A→B→...→A) — can't resolve, skip
            toRemove.add(copyName)
        else:
            candidates[copyName] = target
    for name in toRemove:
        candidates.del(name)
        candidateCIs.del(name)

    if candidates.len == 0:
        return

    # Commit: mark copies as defined variables and store aliases + reif constraint indices
    for copyName, originalName in candidates:
        tr.definedVarNames.incl(copyName)
        tr.equalityCopyAliases[copyName] = originalName
        tr.equalityCopyReifCIs.incl(candidateCIs[copyName])

    stderr.writeLine(&"[FZN] Detected {candidates.len} equality copy variables")


proc buildValueMapping(tr: FznTranslator, sourceValues: Table[string, int]): Table[string, int] =
    ## Given values for source (search) variables, evaluates all channel and reification
    ## variables to constants via fixed-point iteration. Used to resolve test values in
    ## case-analysis channel detection.
    result = initTable[string, int]()
    for name, val in sourceValues:
        result[name] = val
    for name, val in tr.paramValues:
        result[name] = val
    var changed = true
    while changed:
        changed = false
        # Evaluate element channel constraints
        for ci, definedName in tr.channelConstraints:
            if definedName in result: continue
            let con = tr.model.constraints[ci]
            let idxArg = con.args[0]
            var idx: int
            case idxArg.kind
            of FznIntLit: idx = idxArg.intVal
            of FznIdent:
                if idxArg.ident in result: idx = result[idxArg.ident]
                else: continue
            else: continue
            let arr = try: tr.resolveIntArray(con.args[1])
                             except ValueError, KeyError: continue
            let i = idx - 1  # FZN 1-based to 0-based
            if i < 0 or i >= arr.len: continue
            result[definedName] = arr[i]
            changed = true
        # Evaluate reification channels (int_eq_reif / int_ne_reif)
        for ci in tr.reifChannelDefs:
            let con = tr.model.constraints[ci]
            let name = stripSolverPrefix(con.name)
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            let resultVar = con.args[2].ident
            if resultVar in result: continue
            var xVal: int
            case con.args[0].kind
            of FznIdent:
                if con.args[0].ident in result: xVal = result[con.args[0].ident]
                else: continue
            of FznIntLit: xVal = con.args[0].intVal
            else: continue
            var testVal: int
            case con.args[1].kind
            of FznIntLit: testVal = con.args[1].intVal
            of FznBoolLit: testVal = if con.args[1].boolVal: 1 else: 0
            of FznIdent:
                if con.args[1].ident in result: testVal = result[con.args[1].ident]
                else: continue
            else: continue
            if name == "int_eq_reif":
                result[resultVar] = if xVal == testVal: 1 else: 0
            elif name == "int_ne_reif":
                result[resultVar] = if xVal != testVal: 1 else: 0
            changed = true
        # Evaluate bool2int channels
        for ci in tr.bool2intChannelDefs:
            let con = tr.model.constraints[ci]
            if con.args.len < 2: continue
            if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent: continue
            let iName = con.args[1].ident
            if iName in result: continue
            let bName = con.args[0].ident
            if bName notin result: continue
            result[iName] = result[bName]
            changed = true
        # Evaluate bool_not channels
        for ci in tr.boolNotChannelDefs:
            let con = tr.model.constraints[ci]
            if con.args.len < 2: continue
            if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent: continue
            let bName = con.args[1].ident
            if bName in result: continue
            let aName = con.args[0].ident
            if aName notin result: continue
            result[bName] = 1 - result[aName]
            changed = true
        # Evaluate bool_clause_reif channels
        for ci in tr.boolClauseReifChannelDefs:
            let con = tr.model.constraints[ci]
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            let resultVar = con.args[2].ident
            if resultVar in result: continue
            let posElems = tr.resolveVarArrayElems(con.args[0])
            let negElems = tr.resolveVarArrayElems(con.args[1])
            var allResolved = true
            var clauseTrue = false
            for elem in posElems:
                if elem.kind == FznIdent:
                    if elem.ident in result:
                        if result[elem.ident] >= 1:
                            clauseTrue = true
                            break
                    else:
                        allResolved = false
                        break
                elif elem.kind == FznIntLit:
                    if elem.intVal >= 1:
                        clauseTrue = true
                        break
                elif elem.kind == FznBoolLit:
                    if elem.boolVal:
                        clauseTrue = true
                        break
            if not clauseTrue and allResolved:
                for elem in negElems:
                    if elem.kind == FznIdent:
                        if elem.ident in result:
                            if result[elem.ident] == 0:
                                clauseTrue = true
                                break
                        else:
                            allResolved = false
                            break
                    elif elem.kind == FznIntLit:
                        if elem.intVal == 0:
                            clauseTrue = true
                            break
                    elif elem.kind == FznBoolLit:
                        if not elem.boolVal:
                            clauseTrue = true
                            break
            if not clauseTrue and not allResolved: continue
            result[resultVar] = if clauseTrue: 1 else: 0
            changed = true
        # Evaluate set_in_reif channels
        for ci in tr.setInReifChannelDefs:
            let con = tr.model.constraints[ci]
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            let resultVar = con.args[2].ident
            if resultVar in result: continue
            var xVal: int
            case con.args[0].kind
            of FznIdent:
                if con.args[0].ident in result: xVal = result[con.args[0].ident]
                else: continue
            of FznIntLit: xVal = con.args[0].intVal
            else: continue
            let setArg = con.args[1]
            var inSet = false
            case setArg.kind
            of FznRange:
                inSet = xVal >= setArg.lo and xVal <= setArg.hi
            of FznSetLit:
                inSet = xVal in setArg.setElems
            else: continue
            result[resultVar] = if inSet: 1 else: 0
            changed = true
        # Evaluate int_lin_eq with defines_var (for compound index expressions)
        for ci, con in tr.model.constraints:
            let cname = stripSolverPrefix(con.name)
            if cname != "int_lin_eq" or not con.hasAnnotation("defines_var"): continue
            var ann: FznAnnotation
            for a in con.annotations:
                if a.name == "defines_var":
                    ann = a
                    break
            if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
            let definedName = ann.args[0].ident
            if definedName in result: continue
            let coeffs = try: tr.resolveIntArray(con.args[0])
                                     except ValueError, KeyError: continue
            let varElems = tr.resolveVarArrayElems(con.args[1])
            let rhs = try: tr.resolveIntArg(con.args[2])
                                except ValueError, KeyError: continue
            # Find the defined variable's index and check all others are resolved
            var defIdx = -1
            var allOthersResolved = true
            for vi, v in varElems:
                if v.kind == FznIdent and v.ident == definedName:
                    if coeffs[vi] == 1 or coeffs[vi] == -1:
                        defIdx = vi
                elif v.kind == FznIdent:
                    if v.ident notin result:
                        allOthersResolved = false
                        break
            if defIdx < 0 or not allOthersResolved: continue
            # Solve: coeffs[defIdx] * defVal + sum(coeffs[j] * vals[j]) = rhs
            var sumOthers = 0
            for vi, v in varElems:
                if vi == defIdx: continue
                let val = case v.kind
                    of FznIntLit: v.intVal
                    of FznBoolLit: (if v.boolVal: 1 else: 0)
                    of FznIdent: result[v.ident]
                    else: 0
                sumOthers += coeffs[vi] * val
            let defVal = (rhs - sumOthers) div coeffs[defIdx]
            result[definedName] = defVal
            changed = true
        # Evaluate all array_int_element constraints (including non-defines_var)
        for ci, con in tr.model.constraints:
            let cname = stripSolverPrefix(con.name)
            if cname != "array_int_element": continue
            if con.args.len < 3: continue
            let resultArg = con.args[2]
            if resultArg.kind != FznIdent: continue
            if resultArg.ident in result: continue
            let idxArg = con.args[0]
            var idx: int
            case idxArg.kind
            of FznIntLit: idx = idxArg.intVal
            of FznIdent:
                if idxArg.ident in result: idx = result[idxArg.ident]
                else: continue
            else: continue
            let arr = try: tr.resolveIntArray(con.args[1])
                             except ValueError, KeyError: continue
            let i = idx - 1  # FZN 1-based to 0-based
            if i < 0 or i >= arr.len: continue
            result[resultArg.ident] = arr[i]
            changed = true
        # Evaluate int_lin_eq_reif / int_lin_ne_reif with defines_var
        for ci, con in tr.model.constraints:
            let cname = stripSolverPrefix(con.name)
            if cname != "int_lin_eq_reif" and cname != "int_lin_ne_reif": continue
            if not con.hasAnnotation("defines_var"): continue
            if con.args.len < 4 or con.args[3].kind != FznIdent: continue
            let resultVar = con.args[3].ident
            if resultVar in result: continue
            let coeffs = try: tr.resolveIntArray(con.args[0])
                                     except ValueError, KeyError: continue
            let varElems = tr.resolveVarArrayElems(con.args[1])
            let rhs = try: tr.resolveIntArg(con.args[2])
                                except ValueError, KeyError: continue
            if coeffs.len != varElems.len: continue
            var allVarsResolved = true
            var linSum = 0
            for vi, v in varElems:
                case v.kind
                of FznIntLit: linSum += coeffs[vi] * v.intVal
                of FznBoolLit: linSum += coeffs[vi] * (if v.boolVal: 1 else: 0)
                of FznIdent:
                    if v.ident in result: linSum += coeffs[vi] * result[v.ident]
                    else: allVarsResolved = false; break
                else: allVarsResolved = false; break
            if not allVarsResolved: continue
            if cname == "int_lin_eq_reif":
                result[resultVar] = if linSum == rhs: 1 else: 0
            else:
                result[resultVar] = if linSum != rhs: 1 else: 0
            changed = true
        # Evaluate case analysis channel defs
        for def in tr.caseAnalysisDefs:
            if def.targetVarName in result: continue
            # Compute flat index from source variable values
            var allSourcesKnown = true
            var flatIdx = 0
            for i, srcName in def.sourceVarNames:
                if srcName notin result:
                    allSourcesKnown = false
                    break
                let srcVal = result[srcName]
                let localIdx = srcVal - def.domainOffsets[i]
                if localIdx < 0 or localIdx >= def.domainSizes[i]:
                    allSourcesKnown = false
                    break
                flatIdx = flatIdx * def.domainSizes[i] + localIdx
            if not allSourcesKnown: continue
            if flatIdx < 0 or flatIdx >= def.lookupTable.len: continue
            result[def.targetVarName] = def.lookupTable[flatIdx]
            changed = true


proc detectCaseAnalysisChannels(tr: var FznTranslator) =
    ## Detects case-analysis patterns in bool_clause constraints where a target variable's
    ## value is fully determined by condition variables through exhaustive case analysis.
    ## Converts target variables to channel variables with constant lookup tables.
    ##
    ## Pattern (2-literal, first/last round):
    ##   int_eq_reif(target, val, B) :: defines_var(B)
    ##   int_ne_reif(condVar, condVal, C) :: defines_var(C)
    ##   bool_clause([B, C], [])  — condVar==condVal → target==val
    ##
    ## Pattern (3-literal, middle rounds):
    ##   bool_clause([B, C1, C2], [])  — condVar1==v1 AND condVar2==v2 → target==val
    ##
    ## Extended patterns:
    ##   int_lin_eq_reif(coeffs, vars, rhs, B) :: defines_var(B)
    ##   — condVar==condVal → target = f(otherVars)  (linear equation)
    ##
    ##   int_le_reif(condVar, threshold, C) :: defines_var(C) as condition
    ##   — condVar > threshold → target == val  (covers multiple condition values)
    ##
    ## When all condition value combinations are covered (or uncovered cases can be
    ## defaulted), the target becomes a channel with a precomputed constant lookup
    ## table indexed by source variable values.

    # Step 1: Build reverse index from reifChannelDefs
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
    var neReifMap: Table[string, tuple[condVar: string, condVal: int]]

    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if name == "int_eq_reif":
            if con.args[0].kind != FznIdent: continue
            eqReifMap[resultVar] = (sourceVar: con.args[0].ident, testVal: con.args[1])
        elif name == "int_ne_reif":
            if con.args[0].kind != FznIdent: continue
            let condVal = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
            neReifMap[resultVar] = (condVar: con.args[0].ident, condVal: condVal)

    # Step 1b: Build linEqReifMap from int_lin_eq_reif :: defines_var constraints.
    # These encode: sum(coeffs[i]*vars[i]) == rhs <-> bool, allowing us to solve for
    # the target variable: target = (rhs - sum of other terms) / targetCoeff.
    type LinEqReifEntry = object
        targetVar: string
        otherVars: seq[string]
        otherCoeffs: seq[int]
        rhs: int
        targetCoeff: int
        constraintIdx: int

    var linEqReifMap: Table[string, LinEqReifEntry]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif" or not con.hasAnnotation("defines_var"): continue
        if con.args.len < 4 or con.args[3].kind != FznIdent: continue
        let boolVar = con.args[3].ident
        if boolVar in tr.definedVarNames or boolVar in tr.channelVarNames: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let varElems = tr.resolveVarArrayElems(con.args[1])
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if coeffs.len != varElems.len: continue
        # Find a variable with coefficient 1 or -1 to be the target
        var targetIdx = -1
        for i in 0..<varElems.len:
            if varElems[i].kind == FznIdent and (coeffs[i] == 1 or coeffs[i] == -1):
                if varElems[i].ident notin tr.definedVarNames and
                     varElems[i].ident notin tr.channelVarNames:
                    targetIdx = i
                    break
        if targetIdx < 0: continue
        var otherVars: seq[string]
        var otherCoeffs: seq[int]
        var allVarsIdent = true
        for i in 0..<varElems.len:
            if i == targetIdx: continue
            if varElems[i].kind != FznIdent:
                allVarsIdent = false
                break
            otherVars.add(varElems[i].ident)
            otherCoeffs.add(coeffs[i])
        if not allVarsIdent: continue
        linEqReifMap[boolVar] = LinEqReifEntry(
            targetVar: varElems[targetIdx].ident,
            otherVars: otherVars,
            otherCoeffs: otherCoeffs,
            rhs: rhs,
            targetCoeff: coeffs[targetIdx],
            constraintIdx: ci)

    # Step 1c: Build leReifMap from int_le_reif :: defines_var for use as conditions.
    # int_le_reif(var, threshold, bool) → bool = (var <= threshold)
    # In a bool_clause, this covers all condition values > threshold.
    type LeReifEntry = object
        condVar: string
        threshold: int
    var leReifMap: Table[string, LeReifEntry]

    for ci in tr.leReifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_le_reif": continue
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if con.args[0].kind != FznIdent: continue
        let condVar = con.args[0].ident
        let threshold = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
        leReifMap[resultVar] = LeReifEntry(condVar: condVar, threshold: threshold)

    if eqReifMap.len == 0 and linEqReifMap.len == 0: return

    # Step 2: Scan non-consumed bool_clause constraints with 2-3 positive literals
    type CaseEntryKind = enum cekSimple, cekLinear
    type CaseEntry = object
        condVarVals: seq[(string, int)]
        boolClauseIdx: int
        case kind: CaseEntryKind
        of cekSimple:
            testVal: FznExpr
        of cekLinear:
            linOtherVars: seq[string]
            linOtherCoeffs: seq[int]
            linRhs: int
            linTargetCoeff: int
            linReifIdx: int  # constraint index of the int_lin_eq_reif

    var casesByTarget: Table[string, seq[CaseEntry]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len > 1: continue
        let nLits = posArg.elems.len

        # Handle 1-positive-1-negative case: bool_clause([A], [B]) = A ∨ ¬B = B → A
        if nLits == 1 and negArg.elems.len == 1:
            let posLit = posArg.elems[0]
            let negLit = negArg.elems[0]
            if posLit.kind != FznIdent or negLit.kind != FznIdent: continue
            # negLit (B) is the condition: eq_reif(condVar, condVal, B)
            # posLit (A) is the consequence: eq_reif(targetVar, val, A)
            if negLit.ident notin eqReifMap: continue
            let condInfo = eqReifMap[negLit.ident]
            let condVal = try: tr.resolveIntArg(condInfo.testVal) except ValueError, KeyError: continue
            if posLit.ident in eqReifMap:
                let eqInfo = eqReifMap[posLit.ident]
                casesByTarget.mgetOrPut(eqInfo.sourceVar, @[]).add(CaseEntry(
                    kind: cekSimple,
                    condVarVals: @[(condInfo.sourceVar, condVal)],
                    boolClauseIdx: ci,
                    testVal: eqInfo.testVal))
            elif posLit.ident in linEqReifMap:
                let linEntry = linEqReifMap[posLit.ident]
                casesByTarget.mgetOrPut(linEntry.targetVar, @[]).add(CaseEntry(
                    kind: cekLinear,
                    condVarVals: @[(condInfo.sourceVar, condVal)],
                    boolClauseIdx: ci,
                    linOtherVars: linEntry.otherVars,
                    linOtherCoeffs: linEntry.otherCoeffs,
                    linRhs: linEntry.rhs,
                    linTargetCoeff: linEntry.targetCoeff,
                    linReifIdx: linEntry.constraintIdx))
            continue

        if negArg.elems.len != 0: continue
        if nLits < 2 or nLits > 3: continue

        # Classify literals: exactly 1 eq_reif (or lin_eq_reif) + rest ne_reif (or le_reif)
        var eqLitVar = ""
        var eqSourceVar = ""
        var eqTestVal: FznExpr
        var eqIsLinear = false
        var eqLinEntry: LinEqReifEntry
        var neLits: seq[(string, int)]
        var leEntries: seq[LeReifEntry]
        var allValid = true

        for elem in posArg.elems:
            if elem.kind != FznIdent:
                allValid = false
                break
            if eqLitVar == "" and elem.ident in eqReifMap:
                eqLitVar = elem.ident
                eqSourceVar = eqReifMap[elem.ident].sourceVar
                eqTestVal = eqReifMap[elem.ident].testVal
            elif eqLitVar == "" and elem.ident in linEqReifMap:
                eqLitVar = elem.ident
                eqLinEntry = linEqReifMap[elem.ident]
                eqSourceVar = eqLinEntry.targetVar
                eqIsLinear = true
            elif elem.ident in neReifMap:
                let info = neReifMap[elem.ident]
                neLits.add((info.condVar, info.condVal))
            elif elem.ident in leReifMap:
                leEntries.add(leReifMap[elem.ident])
            else:
                allValid = false
                break

        if not allValid or eqLitVar == "": continue
        if neLits.len + leEntries.len != nLits - 1: continue

        # For le_reif conditions, expand to individual condition values.
        # int_le_reif(var, threshold, bool) in bool_clause means: var > threshold → eq holds.
        # So the case applies for all domain values > threshold.
        if leEntries.len > 0:
            # Get condition variable domains for le_reif entries
            var expandedNeLists: seq[seq[(string, int)]]
            expandedNeLists.add(neLits.mapIt(@[it]))

            for le in leEntries:
                let dom = tr.lookupVarDomain(le.condVar)
                if dom.len == 0:
                    allValid = false
                    break
                var vals: seq[(string, int)]
                for v in dom:
                    if v > le.threshold:
                        vals.add((le.condVar, v))
                if vals.len == 0:
                    allValid = false
                    break
                expandedNeLists.add(vals)

            if not allValid: continue

            # Build cross-product of all condition combinations
            var combos: seq[seq[(string, int)]] = @[@[]]
            for group in expandedNeLists:
                var newCombos: seq[seq[(string, int)]]
                for existing in combos:
                    for item in group:
                        newCombos.add(existing & item)
                combos = newCombos
                if combos.len > 100_000:
                    allValid = false
                    break
            if not allValid: continue

            # Add a case entry for each expanded combination
            for combo in combos:
                if eqIsLinear:
                    casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
                        kind: cekLinear, condVarVals: combo, boolClauseIdx: ci,
                        linOtherVars: eqLinEntry.otherVars, linOtherCoeffs: eqLinEntry.otherCoeffs,
                        linRhs: eqLinEntry.rhs, linTargetCoeff: eqLinEntry.targetCoeff,
                        linReifIdx: eqLinEntry.constraintIdx))
                else:
                    casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
                        kind: cekSimple, condVarVals: combo, boolClauseIdx: ci,
                        testVal: eqTestVal))
        else:
            # Standard case: all conditions are ne_reif
            if eqIsLinear:
                casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
                    kind: cekLinear, condVarVals: neLits, boolClauseIdx: ci,
                    linOtherVars: eqLinEntry.otherVars, linOtherCoeffs: eqLinEntry.otherCoeffs,
                    linRhs: eqLinEntry.rhs, linTargetCoeff: eqLinEntry.targetCoeff,
                    linReifIdx: eqLinEntry.constraintIdx))
            else:
                casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
                    kind: cekSimple, condVarVals: neLits, boolClauseIdx: ci,
                    testVal: eqTestVal))

    if casesByTarget.len == 0: return

    # Step 3: Build reverse map for channel constraints (var name → constraint index)
    var channelByName: Table[string, int]
    for ci, defName in tr.channelConstraints:
        channelByName[defName] = ci

    var nTargets = 0
    var nConsumed = 0

    for targetVar, entries in casesByTarget:
        # All entries must have same set of condition variables
        var condVarNames: seq[string]
        for (cv, _) in entries[0].condVarVals:
            condVarNames.add(cv)
        condVarNames.sort()

        var valid = true
        for e in entries:
            var evNames: seq[string]
            for (cv, _) in e.condVarVals:
                evNames.add(cv)
            evNames.sort()
            if evNames != condVarNames:
                valid = false
                break
        if not valid: continue

        # Look up condition variable domains
        var condDomains: seq[seq[int]]
        for cv in condVarNames:
            let dom = tr.lookupVarDomain(cv)
            if dom.len == 0:
                valid = false
                break
            condDomains.add(dom)
        if not valid: continue

        # Check completeness: number of cases == product of condition domain sizes
        var expectedCases = 1
        for dom in condDomains:
            expectedCases *= dom.len
        let isComplete = entries.len == expectedCases
        if not isComplete:
            # Incomplete case analysis: all explicit cases must map to the same non-zero
            # literal value, and 0 must be in the domain. This pattern arises from
            # conditional activation (e.g., "size = if selector==k then S else 0").
            # The channel binding replaces the variable entirely, so the default value
            # only needs to be consistent with the domain, not with external constraints.
            let allSameSimple = entries.allIt(it.kind == cekSimple and
                    it.testVal.kind == FznIntLit)
            if not allSameSimple: continue
            let mappedVal = entries[0].testVal.intVal
            if not entries.allIt(it.testVal.intVal == mappedVal): continue
            let tdom = tr.lookupVarDomain(targetVar).sorted()
            if tdom.len < 2: continue
            if tdom.len == 2:
                discard  # binary domain: default is the other value (handled below)
            else:
                # Non-binary domain: default to 0 if it's in the domain and
                # the mapped value is non-zero (conditional activation pattern)
                if mappedVal == 0 or 0 notin tdom: continue

        # Build case map (condValues → CaseEntry)
        var caseMap: Table[seq[int], CaseEntry]
        for e in entries:
            var combo: seq[int]
            var byName: Table[string, int]
            for (cv, val) in e.condVarVals:
                byName[cv] = val
            for cv in condVarNames:
                if cv notin byName:
                    valid = false
                    break
                combo.add(byName[cv])
            if not valid: break
            if combo in caseMap:
                valid = false
                break
            caseMap[combo] = e
        if not valid: continue

        # Collect all "expression variables" from linear entries (otherVars in lin_eq_reif)
        # and from non-linear entries with variable test values.
        var exprVarSet: HashSet[string]
        for e in entries:
            if e.kind == cekLinear:
                for ov in e.linOtherVars:
                    exprVarSet.incl(ov)
            elif e.testVal.kind == FznIdent and e.testVal.ident notin tr.paramValues:
                exprVarSet.incl(e.testVal.ident)

        # Filter expression variables: channel/defined variables are resolved via
        # buildValueMapping during table building, so exclude them here.
        # Do NOT transitively resolve their source variables — that creates wrong
        # multi-dimensional lookup tables with spurious dependencies.
        var resolvedExprVars: HashSet[string]
        for ev in exprVarSet:
            if ev in tr.channelVarNames or ev in tr.definedVarNames:
                continue  # buildValueMapping handles these at table-construction time
            else:
                resolvedExprVars.incl(ev)
        exprVarSet = resolvedExprVars

        # Step 4: Trace condition variables to source variables.
        # Condition variables may be:
        # a) Element channel results → trace to the element index variable
        # b) Direct search variables → use directly as source
        type CondSourceKind = enum cskElement, cskDirect
        type CondSource = object
            kind: CondSourceKind
            varName: string        # source variable name
            constArray: seq[int]   # for cskElement: the lookup array

        var condSources: seq[CondSource]
        var sourceVarNames: seq[string]
        for cv in condVarNames:
            if cv in channelByName:
                # Element channel: trace to index variable
                let ci = channelByName[cv]
                let con = tr.model.constraints[ci]
                if con.args.len < 3:
                    valid = false
                    break
                let idxArg = con.args[0]
                if idxArg.kind != FznIdent:
                    valid = false
                    break
                let srcVar = idxArg.ident
                if srcVar in tr.definedVarNames or srcVar in tr.channelVarNames:
                    valid = false
                    break
                let constArr = try: tr.resolveIntArray(con.args[1])
                                             except ValueError, KeyError:
                                                 valid = false
                                                 @[]
                if not valid: break
                condSources.add(CondSource(kind: cskElement, varName: srcVar, constArray: constArr))
                sourceVarNames.add(srcVar)
            else:
                # Direct search variable: use as-is
                if cv in tr.definedVarNames or cv in tr.channelVarNames:
                    valid = false
                    break
                condSources.add(CondSource(kind: cskDirect, varName: cv))
                sourceVarNames.add(cv)
        if not valid: continue

        # Add expression variables as additional source variables
        # (channel/defined vars already replaced with transitive sources in exprVarSet)
        for ev in exprVarSet:
            if ev in tr.definedVarNames or ev in tr.channelVarNames:
                continue  # Skip residual channel vars — resolved via buildValueMapping
            if ev notin sourceVarNames:
                sourceVarNames.add(ev)
        if sourceVarNames.len == 0: continue

        # Validate source variables are unique
        block uniqueCheck:
            for i in 0..<sourceVarNames.len:
                for j in i+1..<sourceVarNames.len:
                    if sourceVarNames[i] == sourceVarNames[j]:
                        valid = false
                        break uniqueCheck
        if not valid: continue

        # Get source variable domains
        var sourceDomains: seq[seq[int]]
        for sv in sourceVarNames:
            let dom = tr.lookupVarDomain(sv)
            if dom.len == 0:
                valid = false
                break
            sourceDomains.add(dom)
        if not valid: continue

        # Step 5: Build constant lookup table
        var domainOffsets: seq[int]
        var domainSizes: seq[int]
        for dom in sourceDomains:
            domainOffsets.add(dom[0])
            domainSizes.add(dom[^1] - dom[0] + 1)

        var tableSize = 1
        var tableSizeOk = true
        for ds in domainSizes:
            if ds > 100_000 or (ds > 0 and tableSize > 100_000 div ds):
                tableSizeOk = false
                break
            tableSize *= ds
        if not tableSizeOk or tableSize > 100_000: continue

        # Pre-compute mini lookup tables for channel variables referenced in linear entries.
        # For each channel var not in caseAnalysisDefs, determine which source variables
        # it depends on, then build a small lookup table only over those dimensions.
        type MiniTable = object
            table: seq[int]
            srcIndices: seq[int]    # indices into sourceVarNames
            srcOffsets: seq[int]
            srcSizes: seq[int]
        var channelMiniTables: Table[string, MiniTable]
        block precompute:
            var channelVarsNeeded: HashSet[string]
            for e in entries:
                if e.kind == cekLinear:
                    for ov in e.linOtherVars:
                        if ov in tr.channelVarNames or ov in tr.definedVarNames:
                            var isCaseAnalysis = false
                            for caDef in tr.caseAnalysisDefs:
                                if caDef.targetVarName == ov:
                                    isCaseAnalysis = true
                                    break
                            if not isCaseAnalysis:
                                channelVarsNeeded.incl(ov)
            if channelVarsNeeded.len == 0:
                break precompute
            # Compute base mapping once for all channel vars (all sources at domain minimum)
            var baseValues = initTable[string, int]()
            for i, sv in sourceVarNames:
                baseValues[sv] = domainOffsets[i]
            let baseMapping = tr.buildValueMapping(baseValues)

            # Determine dependencies for all channel vars at once: probe each source var
            # with a shifted value and check which channel vars changed.
            # depSets[cv] = set of source indices that affect cv.
            var depSets: Table[string, seq[int]]
            for cv in channelVarsNeeded:
                if cv notin baseMapping:
                    valid = false
                    break
                depSets[cv] = @[]
            if not valid: break

            for i, sv in sourceVarNames:
                if domainSizes[i] <= 1: continue
                var probeValues = baseValues
                probeValues[sv] = domainOffsets[i] + 1
                let probeMapping = tr.buildValueMapping(probeValues)
                for cv in channelVarsNeeded:
                    if cv in probeMapping and probeMapping[cv] != baseMapping[cv]:
                        depSets[cv].add(i)

            for cv in channelVarsNeeded:
                let depIndices = depSets[cv]
                # Build mini table over dependent source vars only
                var miniOffsets: seq[int]
                var miniSizes: seq[int]
                var miniTableSize = 1
                for di in depIndices:
                    miniOffsets.add(domainOffsets[di])
                    miniSizes.add(domainSizes[di])
                    if miniTableSize > 1_000_000 div max(1, domainSizes[di]):
                        valid = false
                        break
                    miniTableSize *= domainSizes[di]
                if not valid: break

                var miniTable = newSeq[int](miniTableSize)
                for mi in 0..<miniTableSize:
                    var vals = baseValues
                    var rem = mi
                    for k in countdown(depIndices.len - 1, 0):
                        let di = depIndices[k]
                        let li = rem mod domainSizes[di]
                        rem = rem div domainSizes[di]
                        vals[sourceVarNames[di]] = domainOffsets[di] + li
                    let m = tr.buildValueMapping(vals)
                    if cv notin m:
                        valid = false
                        break
                    miniTable[mi] = m[cv]
                if not valid: break
                channelMiniTables[cv] = MiniTable(
                    table: miniTable, srcIndices: depIndices,
                    srcOffsets: miniOffsets, srcSizes: miniSizes)
        if not valid: continue

        # For incomplete cases, compute the default value for uncovered cases.
        var defaultVal = 0
        if not isComplete:
            let tdom = tr.lookupVarDomain(targetVar).sorted()
            let mappedVal = entries[0].testVal.intVal
            if tdom.len == 2:
                # Binary domain: default is the other value
                defaultVal = if tdom[0] == mappedVal: tdom[1] else: tdom[0]
            else:
                # Non-binary domain: default to 0 (conditional assignment pattern)
                defaultVal = 0

        var lookupTable = newSeq[int](tableSize)
        var allResolved = true

        for flatIdx in 0..<tableSize:
            # Decode flat index to source values (row-major: first dim varies slowest)
            var sourceValues = initTable[string, int]()
            var remaining = flatIdx
            for i in countdown(sourceVarNames.len - 1, 0):
                let localIdx = remaining mod domainSizes[i]
                remaining = remaining div domainSizes[i]
                sourceValues[sourceVarNames[i]] = localIdx + domainOffsets[i]

            # Compute condition values from source values
            var condValues: seq[int]
            var condOk = true
            for i, cs in condSources:
                let srcVal = sourceValues[cs.varName]
                case cs.kind
                of cskElement:
                    let arrIdx = srcVal - 1  # FZN 1-based to 0-based
                    if arrIdx < 0 or arrIdx >= cs.constArray.len:
                        condOk = false
                        break
                    condValues.add(cs.constArray[arrIdx])
                of cskDirect:
                    condValues.add(srcVal)
            if not condOk:
                lookupTable[flatIdx] = defaultVal
                continue

            if condValues notin caseMap:
                if isComplete:
                    lookupTable[flatIdx] = 0  # dummy for out-of-domain values
                else:
                    lookupTable[flatIdx] = defaultVal  # uncovered case
                continue

            let entry = caseMap[condValues]

            if entry.kind == cekLinear:
                # Compute target from linear equation:
                # targetCoeff * target + sum(otherCoeffs[i] * otherVars[i]) = rhs
                # target = (rhs - sum(otherCoeffs[i] * otherVars[i])) / targetCoeff
                var numerator = entry.linRhs
                var linOk = true
                var needMapping = false
                for j in 0..<entry.linOtherVars.len:
                    let ov = entry.linOtherVars[j]
                    if ov in sourceValues:
                        numerator -= entry.linOtherCoeffs[j] * sourceValues[ov]
                    elif ov in tr.paramValues:
                        numerator -= entry.linOtherCoeffs[j] * tr.paramValues[ov]
                    else:
                        # Try case analysis def lookup first (fast path)
                        var resolved = false
                        for caDef in tr.caseAnalysisDefs:
                            if caDef.targetVarName == ov:
                                var caIdx = 0
                                var caOk = true
                                for si, srcName in caDef.sourceVarNames:
                                    let sv = if srcName in sourceValues: sourceValues[srcName]
                                                     elif srcName in tr.paramValues: tr.paramValues[srcName]
                                                     else: (caOk = false; 0)
                                    if not caOk: break
                                    let li = sv - caDef.domainOffsets[si]
                                    if li < 0 or li >= caDef.domainSizes[si]: caOk = false; break
                                    caIdx = caIdx * caDef.domainSizes[si] + li
                                if caOk and caIdx >= 0 and caIdx < caDef.lookupTable.len:
                                    numerator -= entry.linOtherCoeffs[j] * caDef.lookupTable[caIdx]
                                    resolved = true
                                break
                        if not resolved:
                            # Try pre-computed mini table
                            if ov in channelMiniTables:
                                let mt = channelMiniTables[ov]
                                var mtIdx = 0
                                for k, di in mt.srcIndices:
                                    let sv = sourceValues[sourceVarNames[di]]
                                    let li = sv - mt.srcOffsets[k]
                                    mtIdx = mtIdx * mt.srcSizes[k] + li
                                numerator -= entry.linOtherCoeffs[j] * mt.table[mtIdx]
                            else:
                                linOk = false
                                break
                if not linOk or numerator mod entry.linTargetCoeff != 0:
                    allResolved = false
                    break
                lookupTable[flatIdx] = numerator div entry.linTargetCoeff
            else:
                # Resolve test value to constant (original logic)
                let testValExpr = entry.testVal
                case testValExpr.kind
                of FznIntLit:
                    lookupTable[flatIdx] = testValExpr.intVal
                of FznBoolLit:
                    lookupTable[flatIdx] = if testValExpr.boolVal: 1 else: 0
                of FznIdent:
                    if testValExpr.ident in tr.paramValues:
                        lookupTable[flatIdx] = tr.paramValues[testValExpr.ident]
                    elif testValExpr.ident in sourceValues:
                        lookupTable[flatIdx] = sourceValues[testValExpr.ident]
                    else:
                        let mapping = tr.buildValueMapping(sourceValues)
                        if testValExpr.ident in mapping:
                            lookupTable[flatIdx] = mapping[testValExpr.ident]
                        else:
                            allResolved = false
                            break
                else:
                    allResolved = false
                    break

        if not allResolved: continue

        # Step 6: Register channel and consume constraints
        tr.channelVarNames.incl(targetVar)
        var consumedBoolClauses: HashSet[int]
        var consumedLinReifs: HashSet[int]
        for e in entries:
            if e.boolClauseIdx notin consumedBoolClauses:
                tr.definingConstraints.incl(e.boolClauseIdx)
                consumedBoolClauses.incl(e.boolClauseIdx)
                inc nConsumed
            if e.kind == cekLinear and e.linReifIdx notin consumedLinReifs:
                tr.definingConstraints.incl(e.linReifIdx)
                consumedLinReifs.incl(e.linReifIdx)

        tr.caseAnalysisDefs.add(CaseAnalysisDef(
            targetVarName: targetVar,
            sourceVarNames: sourceVarNames,
            lookupTable: lookupTable,
            domainOffsets: domainOffsets,
            domainSizes: domainSizes
        ))
        inc nTargets

    if nTargets > 0:
        stderr.writeLine(&"[FZN] Detected case-analysis channels: {nTargets} target variables, {nConsumed} bool_clause constraints consumed")


proc detectImplicationPatterns(tr: var FznTranslator) =
    ## Detects boolean implication patterns encoded as:
    ##   bool_clause([neg_b, r], [])
    ## where neg_b = int_ne_reif(B_var, 1, neg_b) :: defines_var(neg_b)
    ##   and r = int_lin_le_reif([-1,...], [Y_1,...], -1, r) :: defines_var(r)
    ##
    ## Traces through reification chains to find the underlying integer variables,
    ## builds table constraints for valid transitions, and detects one-hot channel
    ## variables for indicator-to-integer channeling.

    # Build indexes — single pass over all constraints (including consumed ones for tracing)
    var eqReifDefines: Table[string, (string, int)]          # result → (source, value)
    var eqReifNoDefines: Table[string, (string, int, int)]   # result → (source, value, ci)
    var neReifDefines: Table[string, (string, int, int)]       # result → (source, value, ci)
    var linLeReifDefines: Table[string, int]                  # result → ci
    var eqReifDefinesBySource: Table[string, string]          # source → result (value=1 only)
    var notOneVars: HashSet[string]                           # vars where int_eq_reif(var, 1, false) exists
    var notOneConstraints: Table[string, int]                  # var → constraint index for int_eq_reif(var, 1, false)

    # Pre-build set of bool/0..1 variable names for fast one-hot validation
    var boolVarNames: HashSet[string]
    for decl in tr.model.variables:
        if decl.isArray: continue
        case decl.varType.kind
        of FznBool:
            boolVarNames.incl(decl.name)
        of FznIntRange:
            if decl.varType.lo == 0 and decl.varType.hi == 1:
                boolVarNames.incl(decl.name)
        else: discard

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        case name
        of "int_eq_reif":
            if con.args.len < 3: continue
            let srcArg = con.args[0]
            let valArg = con.args[1]
            let resultArg = con.args[2]
            if srcArg.kind != FznIdent: continue
            # Check for bool literal result: int_eq_reif(bVar, 1, false) → boundary indicator
            if resultArg.kind == FznBoolLit:
                if not resultArg.boolVal:
                    let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
                    if val == 1:
                        notOneVars.incl(srcArg.ident)
                        notOneConstraints[srcArg.ident] = ci
                continue
            if resultArg.kind != FznIdent: continue
            let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
            if con.hasAnnotation("defines_var"):
                eqReifDefines[resultArg.ident] = (srcArg.ident, val)
                if val == 1:
                    eqReifDefinesBySource[srcArg.ident] = resultArg.ident
            else:
                eqReifNoDefines[resultArg.ident] = (srcArg.ident, val, ci)
        of "int_ne_reif":
            if con.args.len < 3: continue
            let srcArg = con.args[0]
            let valArg = con.args[1]
            let resultArg = con.args[2]
            if srcArg.kind != FznIdent or resultArg.kind != FznIdent: continue
            let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
            if con.hasAnnotation("defines_var"):
                neReifDefines[resultArg.ident] = (srcArg.ident, val, ci)
        of "int_lin_le_reif":
            if con.args.len < 4: continue
            let resultArg = con.args[3]
            if resultArg.kind != FznIdent: continue
            if con.hasAnnotation("defines_var"):
                linLeReifDefines[resultArg.ident] = ci
        else: discard

    # Implication detection — scan bool_clause constraints
    var implicationGroups: Table[(string, string), seq[(int, int)]]
    var nConsumed = 0
    var nVacuous = 0
    var nStay = 0

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue

        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 2 or negArg.elems.len != 0: continue

        let lit0 = posArg.elems[0]
        let lit1 = posArg.elems[1]
        if lit0.kind != FznIdent or lit1.kind != FznIdent: continue

        # Identify which literal is neReif
        var neReifLit, otherLit: string
        if lit0.ident in neReifDefines and lit1.ident notin neReifDefines:
            neReifLit = lit0.ident
            otherLit = lit1.ident
        elif lit1.ident in neReifDefines and lit0.ident notin neReifDefines:
            neReifLit = lit1.ident
            otherLit = lit0.ident
        elif lit0.ident in neReifDefines and lit1.ident in neReifDefines:
            # Both are neReif — try both orders for [neReif, linLeReif] or [neReif, eqReif]
            if lit0.ident in linLeReifDefines or lit0.ident in eqReifDefines:
                neReifLit = lit1.ident
                otherLit = lit0.ident
            elif lit1.ident in linLeReifDefines or lit1.ident in eqReifDefines:
                neReifLit = lit0.ident
                otherLit = lit1.ident
            else:
                continue
        else:
            continue

        # Case 1: [ne_reif, lin_le_reif] — transition pattern (agent moves to neighbor)
        if otherLit in linLeReifDefines:
            let (bVar, neVal, neReifCi) = neReifDefines[neReifLit]
            if neVal != 1: continue

            # Trace neReif through indicator chain → integer variable
            if bVar notin eqReifDefinesBySource:
                # Check vacuous boundary: bVar can never be 1 → implication is vacuously true
                if bVar in notOneVars:
                    let linLeIdx = linLeReifDefines[otherLit]
                    tr.definingConstraints.incl(ci)        # bool_clause
                    tr.definingConstraints.incl(linLeIdx)  # int_lin_le_reif
                    tr.definingConstraints.incl(neReifCi)  # int_ne_reif (trivially satisfied)
                    tr.definedVarNames.incl(neReifLit)     # result var of neReif
                    tr.definedVarNames.incl(otherLit)      # result var of linLeReif
                    nConsumed += 3
                    nVacuous += 1
                continue
            let channelVar = eqReifDefinesBySource[bVar]
            if channelVar notin eqReifNoDefines: continue
            let (condVar, condValue, _) = eqReifNoDefines[channelVar]

            # Check int_lin_le_reif: all coefficients = -1, rhs = -1 (encoding sum >= 1)
            let linLeIdx = linLeReifDefines[otherLit]
            let linLeCon = tr.model.constraints[linLeIdx]
            let coeffs = try: tr.resolveIntArray(linLeCon.args[0]) except ValueError, KeyError: continue
            let rhs = try: tr.resolveIntArg(linLeCon.args[2]) except ValueError, KeyError: continue
            if rhs != -1: continue

            var allNegOne = true
            for c in coeffs:
                if c != -1:
                    allNegOne = false
                    break
            if not allNegOne: continue

            let varElems = tr.resolveVarArrayElems(linLeCon.args[1])
            if varElems.len != coeffs.len or varElems.len == 0: continue

            # Trace each indicator variable → target integer variable
            var targetVar = ""
            var targetValues: seq[int]
            var valid = true

            for yi in varElems:
                if yi.kind != FznIdent:
                    valid = false
                    break
                if yi.ident notin eqReifDefinesBySource:
                    valid = false
                    break
                let chVarI = eqReifDefinesBySource[yi.ident]
                if chVarI notin eqReifNoDefines:
                    valid = false
                    break
                let (tVar, tValue, _) = eqReifNoDefines[chVarI]

                if targetVar == "":
                    targetVar = tVar
                elif tVar != targetVar:
                    valid = false
                    break

                targetValues.add(tValue)

            if not valid or targetVar == "": continue

            # Record: (condVar == condValue) → (targetVar in targetValues)
            let key = (condVar, targetVar)
            if key notin implicationGroups:
                implicationGroups[key] = @[]
            for tv in targetValues:
                implicationGroups[key].add((condValue, tv))

            # Mark consumed
            tr.definingConstraints.incl(ci)        # bool_clause
            tr.definingConstraints.incl(linLeIdx)  # int_lin_le_reif
            tr.definedVarNames.incl(otherLit)      # result var of linLeReif
            nConsumed += 2

        # Case 2: [ne_reif, eq_reif] — direct implication (stay at destination)
        # Unlike Case 1, no neVal==1 guard needed: here the ne_reif directly references
        # an integer variable (e.g., int_ne_reif(agentPos, value, B)), so condValue is
        # the actual integer value, not a boolean indicator.
        elif otherLit in eqReifDefines:
            let (condVar, condValue, _) = neReifDefines[neReifLit]
            let (targetVar, targetValue) = eqReifDefines[otherLit]

            # Record: (condVar == condValue) → (targetVar == targetValue)
            let key = (condVar, targetVar)
            if key notin implicationGroups:
                implicationGroups[key] = @[]
            implicationGroups[key].add((condValue, targetValue))

            # Only consume the bool_clause — ne_reif and eq_reif already consumed by detectReifChannels
            tr.definingConstraints.incl(ci)
            nConsumed += 1
            nStay += 1

    # Build table constraints from grouped implications
    for key, tuples in implicationGroups:
        let (condVar, targetVar) = key
        var tableTuples: seq[seq[int]]
        for (cv, tv) in tuples:
            tableTuples.add(@[cv, tv])
        tr.implicationTables.add((condVar: condVar, targetVar: targetVar, tuples: tableTuples))

    # One-hot channel detection — convert indicator vars to channels of integer vars
    for channel, entry in eqReifNoDefines.pairs:
        let (intVar, v, ci) = entry
        if ci in tr.definingConstraints: continue
        if channel notin eqReifDefines: continue
        let (bV, eqVal) = eqReifDefines[channel]
        if eqVal != 1: continue
        if bV in tr.channelVarNames or bV in tr.definedVarNames: continue
        if bV notin boolVarNames: continue

        tr.oneHotChannelDefs.add((indicatorVar: bV, intVar: intVar, value: v))
        tr.definingConstraints.incl(ci)
        tr.channelVarNames.incl(bV)

    # Constant-zero channel detection — boundary B vars that are always 0
    for bVar in notOneVars:
        if bVar in tr.channelVarNames or bVar in tr.definedVarNames: continue
        if bVar notin boolVarNames: continue
        tr.constantZeroChannels.add(bVar)
        tr.channelVarNames.incl(bVar)
        if bVar in notOneConstraints:
            tr.definingConstraints.incl(notOneConstraints[bVar])

    if tr.implicationTables.len > 0:
        stderr.writeLine(&"[FZN] Detected implication table patterns: {tr.implicationTables.len} tables, {nConsumed} constraints consumed (stay={nStay}, vacuous={nVacuous}, notOneVars={notOneVars.len})")
    if tr.oneHotChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected one-hot channels: {tr.oneHotChannelDefs.len} indicator variables")
    if tr.constantZeroChannels.len > 0:
        stderr.writeLine(&"[FZN] Detected constant-zero channels: {tr.constantZeroChannels.len} boundary indicator variables")


proc detectConditionalGainChannels(tr: var FznTranslator) =
    ## Detects variables that are conditionally a linear function of element channels
    ## or zero, where the conditions are also element-channel-derived. Converts them
    ## to element channels with precomputed lookup tables.
    ##
    ## Pattern (per gain variable V):
    ##   int_eq_reif(V, 0, B_zero) :: defines_var(B_zero)
    ##   int_lin_eq_reif(coeffs, [V, W], rhs, B_eq) :: defines_var(B_eq)
    ##   bool_clause([B_eq], [cond1, cond2, ...])
    ##   bool_clause([cond_and_or_cond, B_zero], [])
    ## where W is an element channel and conditions are int_le_reif of element channels,
    ## all sharing the same index (origin) variable.

    # Step 1: Find int_eq_reif(V, 0, B_zero) patterns
    # These may already be consumed by reif channel detection, but we scan all constraints.
    var zeroReifVars: Table[string, tuple[ci: int, boolVar: string]]
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name == "int_eq_reif" and con.args.len >= 3:
            if con.args[0].kind == FznIdent and
                 con.args[1].kind == FznIntLit and con.args[1].intVal == 0 and
                 con.args[2].kind == FznIdent:
                let v = con.args[0].ident
                if v notin tr.channelVarNames and v notin tr.definedVarNames:
                    zeroReifVars[v] = (ci, con.args[2].ident)

    if zeroReifVars.len == 0:
        return

    # Step 2: Find matching int_lin_eq_reif with 2 variables (one is V, other is a channel)
    type LinEqReifInfo = object
        ci: int
        gainVar: string
        otherVar: string
        gainCoeff: int
        otherCoeff: int
        rhs: int
        boolVar: string

    var linEqReifs: Table[string, LinEqReifInfo]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif" or con.args.len < 4: continue
        if not con.hasAnnotation("defines_var"): continue

        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len != 2: continue

        let vars = con.args[1]
        if vars.kind != FznArrayLit or vars.elems.len != 2: continue
        if vars.elems[0].kind != FznIdent or vars.elems[1].kind != FznIdent: continue

        let var0 = vars.elems[0].ident
        let var1 = vars.elems[1].ident
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if con.args[3].kind != FznIdent: continue
        let boolVar = con.args[3].ident

        # The "other" variable must be a channel or element channel alias
        let isVar0Channel = var0 in tr.channelVarNames or var0 in tr.elementChannelAliases
        let isVar1Channel = var1 in tr.channelVarNames or var1 in tr.elementChannelAliases

        if var0 in zeroReifVars and isVar1Channel:
            linEqReifs[var0] = LinEqReifInfo(ci: ci, gainVar: var0, otherVar: var1,
                                                                                gainCoeff: coeffs[0], otherCoeff: coeffs[1],
                                                                                rhs: rhs, boolVar: boolVar)
        elif var1 in zeroReifVars and isVar0Channel:
            linEqReifs[var1] = LinEqReifInfo(ci: ci, gainVar: var1, otherVar: var0,
                                                                                gainCoeff: coeffs[1], otherCoeff: coeffs[0],
                                                                                rhs: rhs, boolVar: boolVar)

    if linEqReifs.len == 0:
        return

    # Step 3: Index bool_clause constraints by positive literals
    type BoolClauseInfo = object
        ci: int
        posLits: seq[string]
        negLits: seq[string]

    var boolClausesByPosLit: Table[string, seq[BoolClauseInfo]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause" or con.args.len < 2: continue

        var info = BoolClauseInfo(ci: ci)
        if con.args[0].kind == FznArrayLit:
            for elem in con.args[0].elems:
                if elem.kind == FznIdent:
                    info.posLits.add(elem.ident)
        if con.args[1].kind == FznArrayLit:
            for elem in con.args[1].elems:
                if elem.kind == FznIdent:
                    info.negLits.add(elem.ident)

        for lit in info.posLits:
            if lit notin boolClausesByPosLit:
                boolClausesByPosLit[lit] = @[]
            boolClausesByPosLit[lit].add(info)

    # Step 4: Index int_le_reif definitions by their boolean output variable
    type LeReifInfo = object
        leftVar: string
        leftConst: int
        rightVar: string
        rightConst: int
        isLeftConst: bool
        isRightConst: bool

    var leReifByBool: Table[string, LeReifInfo]
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin ["int_le_reif", "int_lt_reif"] or con.args.len < 3: continue
        if con.args[2].kind != FznIdent: continue
        let boolVar = con.args[2].ident

        var info: LeReifInfo
        if con.args[0].kind == FznIdent:
            info.leftVar = con.args[0].ident
        elif con.args[0].kind == FznIntLit:
            info.leftConst = con.args[0].intVal
            info.isLeftConst = true
        else: continue

        if con.args[1].kind == FznIdent:
            info.rightVar = con.args[1].ident
        elif con.args[1].kind == FznIntLit:
            info.rightConst = con.args[1].intVal
            info.isRightConst = true
        else: continue

        leReifByBool[boolVar] = info

    # Step 5: Build element channel info: channel var name -> (origin var, constant array)
    type ElementInfo = object
        originVar: string
        constArray: seq[int]

    var elementInfo: Table[string, ElementInfo]
    for ci, chanName in tr.channelConstraints:
        let con = tr.model.constraints[ci]
        if con.args[0].kind == FznIdent:
            try:
                let constArray = tr.resolveIntArray(con.args[1])
                elementInfo[chanName] = ElementInfo(originVar: con.args[0].ident, constArray: constArray)
            except ValueError, KeyError: discard

    for aliasName, originalName in tr.elementChannelAliases:
        if originalName in elementInfo:
            elementInfo[aliasName] = elementInfo[originalName]

    # Step 6: Process each gain variable
    var nConverted = 0
    var consumedBoolClauses: PackedSet[int]

    for gainVar, info in linEqReifs:
        let zeroInfo = zeroReifVars[gainVar]
        let bEq = info.boolVar
        let bZero = zeroInfo.boolVar

        # Find conditional bool_clause: bool_clause([B_eq], [cond1, cond2, ...])
        if bEq notin boolClausesByPosLit: continue
        var condClause: BoolClauseInfo
        var foundCond = false
        for bc in boolClausesByPosLit[bEq]:
            if bc.posLits.len == 1 and bc.negLits.len > 0:
                condClause = bc
                foundCond = true
                break
        if not foundCond: continue

        # Find complementary bool_clause: bool_clause([..., B_zero], [])
        if bZero notin boolClausesByPosLit: continue
        var compClause: BoolClauseInfo
        var foundComp = false
        for bc in boolClausesByPosLit[bZero]:
            if bc.negLits.len == 0:
                compClause = bc
                foundComp = true
                break
        if not foundComp: continue

        # Extract conditions from negative literals of the conditional clause
        type ConditionInfo = object
            channelVar: string
            threshold: int
            isLessEqual: bool  # true: channel <= threshold, false: channel >= threshold

        var conditions: seq[ConditionInfo]
        var allConditionsTraced = true
        for condBool in condClause.negLits:
            if condBool notin leReifByBool:
                allConditionsTraced = false
                break
            let leInfo = leReifByBool[condBool]
            if leInfo.isLeftConst and not leInfo.isRightConst:
                # int_le_reif(constant, channel, bool) → channel >= constant
                conditions.add(ConditionInfo(channelVar: leInfo.rightVar, threshold: leInfo.leftConst, isLessEqual: false))
            elif not leInfo.isLeftConst and leInfo.isRightConst:
                # int_le_reif(channel, constant, bool) → channel <= constant
                conditions.add(ConditionInfo(channelVar: leInfo.leftVar, threshold: leInfo.rightConst, isLessEqual: true))
            else:
                allConditionsTraced = false
                break
        if not allConditionsTraced: continue

        # Trace price channel (W) to element info (may be alias)
        let otherVar = if info.otherVar in tr.elementChannelAliases:
                                         tr.elementChannelAliases[info.otherVar]
                                     else: info.otherVar
        if otherVar notin elementInfo: continue
        let priceElem = elementInfo[otherVar]
        let originVar = priceElem.originVar
        let arrayLen = priceElem.constArray.len

        # Trace condition channels and verify all share the same origin
        type CondEval = object
            constArray: seq[int]
            threshold: int
            isLessEqual: bool

        var condEvals: seq[CondEval]
        var allSameOrigin = true
        for cond in conditions:
            # Resolve alias if needed
            let condChanVar = if cond.channelVar in tr.elementChannelAliases:
                                                    tr.elementChannelAliases[cond.channelVar]
                                                else: cond.channelVar
            if condChanVar notin elementInfo:
                allSameOrigin = false
                break
            let condElem = elementInfo[condChanVar]
            if condElem.originVar != originVar or condElem.constArray.len != arrayLen:
                allSameOrigin = false
                break
            condEvals.add(CondEval(constArray: condElem.constArray, threshold: cond.threshold,
                                                            isLessEqual: cond.isLessEqual))
        if not allSameOrigin: continue

        # Compute the lookup table
        if info.gainCoeff == 0: continue
        var lookupTable = newSeq[int](arrayLen)
        for v in 0..<arrayLen:
            var conditionsMet = true
            for ce in condEvals:
                let val = ce.constArray[v]
                if ce.isLessEqual:
                    if val > ce.threshold:
                        conditionsMet = false
                        break
                else:
                    if val < ce.threshold:
                        conditionsMet = false
                        break

            if conditionsMet:
                let price = priceElem.constArray[v]
                let numerator = info.rhs - info.otherCoeff * price
                lookupTable[v] = numerator div info.gainCoeff
            # else: lookupTable[v] = 0 (default)

        # Convert gain variable to element channel
        tr.channelVarNames.incl(gainVar)
        tr.definedVarNames.excl(gainVar)
        tr.syntheticElementChannels.add((gainVar, originVar, lookupTable))

        # Consume constraints
        tr.definingConstraints.incl(info.ci)  # int_lin_eq_reif
        tr.definingConstraints.incl(condClause.ci)
        consumedBoolClauses.incl(condClause.ci)
        tr.definingConstraints.incl(compClause.ci)
        consumedBoolClauses.incl(compClause.ci)

        nConverted += 1

    if nConverted > 0:
        stderr.writeLine(&"[FZN] Converted {nConverted} conditional gain variables to element channels")


