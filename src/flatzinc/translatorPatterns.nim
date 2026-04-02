## Included from translator.nim -- not a standalone module.
## Miscellaneous pattern detection: weighted same-value, set union, equality copy,
## skill allocation, atMost, argmax, spread, diffn, int_mod/div, net flow, etc.

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

    # Phase 1: Build set of variable names referenced by "real" (non-defines_var) constraints.
    # For expression-defining constraints (int_lin_eq/int_abs/int_times/etc. defines_var
    # where the defined variable is in definedVarNames), include input variable references
    # — inputs to objective/defined expressions are real references that prevent
    # equality-copy elimination. Channel-defining constraints (reif channels, element
    # channels) are excluded since their inputs may be equality copy candidates.
    var nonDefinesVarRefs: HashSet[string]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            # Check if this defines an expression variable (definedVarNames) vs a channel variable
            if con.hasAnnotation("defines_var"):
                let ann = con.getAnnotation("defines_var")
                if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                    let definedName = ann.args[0].ident
                    if definedName in tr.definedVarNames:
                        # Expression-defining constraint — inputs are real references
                        for arg in con.args:
                            if arg.kind == FznIdent:
                                if arg.ident != definedName:
                                    nonDefinesVarRefs.incl(arg.ident)
                            elif arg.kind == FznArrayLit:
                                for elem in arg.elems:
                                    if elem.kind == FznIdent and elem.ident != definedName:
                                        nonDefinesVarRefs.incl(elem.ident)
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
            # Try constant array first
            let arr = try: tr.resolveIntArray(con.args[1])
                             except ValueError, KeyError: @[]
            if arr.len > 0:
                let i = idx - 1  # FZN 1-based to 0-based
                if i < 0 or i >= arr.len: continue
                result[definedName] = arr[i]
                changed = true
            else:
                # Variable array (array_var_int_element): resolve individual element
                let varElems = tr.resolveVarArrayElems(con.args[1])
                let i = idx - 1  # FZN 1-based to 0-based
                if i < 0 or i >= varElems.len: continue
                let elem = varElems[i]
                if elem.kind == FznIntLit:
                    result[definedName] = elem.intVal
                    changed = true
                elif elem.kind == FznBoolLit:
                    result[definedName] = if elem.boolVal: 1 else: 0
                    changed = true
                elif elem.kind == FznIdent:
                    if elem.ident in result:
                        result[definedName] = result[elem.ident]
                        changed = true
                    elif elem.ident in tr.paramValues:
                        result[definedName] = tr.paramValues[elem.ident]
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
        # Evaluate int_times/int_div/int_abs/int_mod/int_plus with defines_var
        for ci, con in tr.model.constraints:
            if ci notin tr.definingConstraints: continue
            let cname = stripSolverPrefix(con.name)
            if cname notin ["int_times", "int_div", "int_abs", "int_mod", "int_plus"]: continue
            if not con.hasAnnotation("defines_var"): continue
            let defIdx = if cname == "int_abs": 1 else: 2
            if con.args[defIdx].kind != FznIdent: continue
            let definedName = con.args[defIdx].ident
            if definedName in result: continue
            var aVal, bVal: int
            case con.args[0].kind
            of FznIntLit: aVal = con.args[0].intVal
            of FznIdent:
                if con.args[0].ident in result: aVal = result[con.args[0].ident]
                else: continue
            else: continue
            if cname != "int_abs":
                case con.args[1].kind
                of FznIntLit: bVal = con.args[1].intVal
                of FznIdent:
                    if con.args[1].ident in result: bVal = result[con.args[1].ident]
                    else: continue
                else: continue
            case cname
            of "int_times": result[definedName] = aVal * bVal
            of "int_div": result[definedName] = if bVal == 0: 0 else: aVal div bVal
            of "int_mod": result[definedName] = if bVal == 0: 0 else: aVal mod bVal
            of "int_plus": result[definedName] = aVal + bVal
            of "int_abs": result[definedName] = abs(aVal)
            else: discard
            changed = true
        # Evaluate expression channel defs (int_div/int_mod/int_plus detected as channels)
        for def in tr.expressionChannelDefs:
            if def.varName in result: continue
            let con = tr.model.constraints[def.ci]
            let cname = stripSolverPrefix(con.name)
            var aVal, bVal: int
            case con.args[0].kind
            of FznIntLit: aVal = con.args[0].intVal
            of FznIdent:
                if con.args[0].ident in result: aVal = result[con.args[0].ident]
                else: continue
            else: continue
            case con.args[1].kind
            of FznIntLit: bVal = con.args[1].intVal
            of FznIdent:
                if con.args[1].ident in result: bVal = result[con.args[1].ident]
                else: continue
            else: continue
            case cname
            of "int_div": result[def.varName] = if bVal == 0: 0 else: aVal div bVal
            of "int_mod": result[def.varName] = if bVal == 0: 0 else: aVal mod bVal
            of "int_plus": result[def.varName] = aVal + bVal
            else: discard
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



proc eliminateDeadIntEqReifChannels(tr: var FznTranslator,
                                    candidateCIs: PackedSet[int]): tuple[count: int, deadVarNames: seq[string]] =
    ## For int_eq_reif constraints in candidateCIs, eliminate those whose boolean
    ## output has no remaining live references (at most 1, from the defining constraint itself).
    var liveRefCount: Table[string, int]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        for arg in con.args:
            if arg.kind == FznIdent:
                liveRefCount.mgetOrPut(arg.ident, 0) += 1
            elif arg.kind == FznArrayLit:
                for elem in arg.elems:
                    if elem.kind == FznIdent:
                        liveRefCount.mgetOrPut(elem.ident, 0) += 1

    var deadCount = 0
    var deadVarNames: seq[string]
    for ci in candidateCIs.items:
        if ci in tr.definingConstraints: continue
        let con = tr.model.constraints[ci]
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let bName = con.args[2].ident
        let refCount = liveRefCount.getOrDefault(bName, 0)
        if refCount <= 1:
            tr.definingConstraints.incl(ci)
            tr.definedVarNames.incl(bName)
            deadVarNames.add(bName)
            inc deadCount
    return (deadCount, deadVarNames)


proc detectSkillAllocationPattern(tr: var FznTranslator) =
    ## Detects the disjunctive skill-assignment pattern from MiniZinc's decomposition:
    ##   set_in_reif(alloc, POSENGS, b_base) :: defines_var(b_base)
    ##   int_eq_reif(new_skills[e,t], skill, b_skill) :: defines_var(b_skill)
    ##   int_eq_reif(alloc, eng, b_alloc) :: defines_var(b_alloc)
    ##   array_bool_and([b_skill, b_alloc], b_both) :: defines_var(b_both)
    ##   bool_clause([b_base, b_both_1, ..., b_both_N], [])
    ##
    ## Replaces ~130 auxiliary booleans per job with compact channel-based constraints:
    ##   learned_t = element(alloc - 1, [new_skills[1,t], ..., new_skills[E,t]])
    ##   alloc in POSENGS OR learned_1 == skill OR learned_2 == skill OR ...

    # Build indices for defines_var constraints (not yet consumed)
    var setInReifByResult: Table[string, int]  # b_name -> constraint index
    var intEqReifByResult: Table[string, int]  # b_name -> constraint index
    var boolAndByResult: Table[string, int]    # b_name -> constraint index

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if not con.hasAnnotation("defines_var"): continue
        let name = stripSolverPrefix(con.name)
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        let defVar = ann.args[0].ident

        if name == "set_in_reif":
            if con.args.len >= 3 and con.args[2].kind == FznIdent and con.args[2].ident == defVar:
                setInReifByResult[defVar] = ci
        elif name == "int_eq_reif":
            if con.args.len >= 3 and con.args[2].kind == FznIdent and con.args[2].ident == defVar:
                intEqReifByResult[defVar] = ci
        elif name == "array_bool_and":
            if con.args.len >= 2 and con.args[1].kind == FznIdent and con.args[1].ident == defVar:
                boolAndByResult[defVar] = ci

    # Scan bool_clause([positives], []) with many positive literals
    var nDetected = 0
    var allConsumedCIs: PackedSet[int]
    var allConsumedVars: HashSet[string]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue

        # Must have empty negatives
        let negArg = con.args[1]
        if negArg.kind != FznArrayLit or negArg.elems.len != 0: continue

        let posArg = con.args[0]
        if posArg.kind != FznArrayLit: continue
        if posArg.elems.len < 10: continue  # Need substantial disjunction

        # Scan all positive literals: find the set_in_reif element (if any) and array_bool_and elements
        var allocVarName = ""
        var posEngs: seq[int]
        var setInReifIdx = -1  # index in posArg.elems of the set_in_reif element, -1 if none
        var localConsumedCIs: seq[int]
        var localConsumedVars: seq[string]

        # First scan: find the set_in_reif element (may be at any position, not just first)
        for i in 0..<posArg.elems.len:
            let bName = if posArg.elems[i].kind == FznIdent: posArg.elems[i].ident else: ""
            if bName != "" and bName in setInReifByResult:
                let setInCI = setInReifByResult[bName]
                let setInCon = tr.model.constraints[setInCI]
                if setInCon.args[0].kind != FznIdent: continue
                allocVarName = setInCon.args[0].ident
                let setArg = setInCon.args[1]
                case setArg.kind
                of FznSetLit: posEngs = setArg.setElems
                of FznRange:
                    for v in setArg.lo..setArg.hi:
                        posEngs.add(v)
                else: continue
                setInReifIdx = i
                localConsumedCIs.add(setInCI)
                localConsumedVars.add(bName)
                break

        localConsumedCIs.add(ci)  # the bool_clause itself

        # When allocVarName is unknown (no set_in_reif), infer it from the disjuncts.
        # The alloc var appears as arg0 in int_eq_reif for ALL disjuncts (same alloc var per job).
        if allocVarName == "":
            var argCounts: Table[string, int]
            for i in 0..<posArg.elems.len:
                let bName = if posArg.elems[i].kind == FznIdent: posArg.elems[i].ident else: ""
                if bName == "" or bName notin boolAndByResult: continue
                let bCon = tr.model.constraints[boolAndByResult[bName]]
                if bCon.args[0].kind != FznArrayLit or bCon.args[0].elems.len != 2: continue
                for elem in bCon.args[0].elems:
                    if elem.kind == FznIdent and elem.ident in intEqReifByResult:
                        let reifCon = tr.model.constraints[intEqReifByResult[elem.ident]]
                        if reifCon.args[0].kind == FznIdent:
                            argCounts.mgetOrPut(reifCon.args[0].ident, 0) += 1
            # The alloc var has the highest count (appears in all disjuncts)
            var maxCount = 0
            for varName, count in argCounts:
                if count > maxCount:
                    maxCount = count
                    allocVarName = varName
            if allocVarName == "": continue

        # Trace disjuncts through array_bool_and -> (int_eq_reif_skill, int_eq_reif_alloc)
        var requiredSkill = -1
        var skillSet = false
        var valid = true
        var nsByEng: Table[int, seq[string]]  # eng -> list of new_skills var names
        var engSet: PackedSet[int]  # all engineer values seen

        for i in 0..<posArg.elems.len:
            if i == setInReifIdx: continue  # Skip the set_in_reif element
            let bAndName = if posArg.elems[i].kind == FznIdent: posArg.elems[i].ident else: ""
            if bAndName == "" or bAndName notin boolAndByResult:
                valid = false
                break

            let bAndCI = boolAndByResult[bAndName]
            let bAndCon = tr.model.constraints[bAndCI]
            # array_bool_and([b1, b2], result) — extract the two inputs
            if bAndCon.args[0].kind != FznArrayLit or bAndCon.args[0].elems.len != 2:
                valid = false
                break

            let inp0 = bAndCon.args[0].elems[0]
            let inp1 = bAndCon.args[0].elems[1]
            if inp0.kind != FznIdent or inp1.kind != FznIdent:
                valid = false
                break

            # One should be int_eq_reif on new_skills (skill match), other on alloc (engineer match)
            # Both inputs must be int_eq_reif defines_var results
            if inp0.ident notin intEqReifByResult or inp1.ident notin intEqReifByResult:
                valid = false
                break

            let ci0 = intEqReifByResult[inp0.ident]
            let ci1 = intEqReifByResult[inp1.ident]
            let con0 = tr.model.constraints[ci0]
            let con1 = tr.model.constraints[ci1]

            if con0.args[0].kind != FznIdent or con1.args[0].kind != FznIdent:
                valid = false
                break

            # Determine which is alloc reif and which is skill reif based on allocVarName
            var skillReifName, allocReifName: string
            if con0.args[0].ident == allocVarName and con1.args[0].ident != allocVarName:
                allocReifName = inp0.ident
                skillReifName = inp1.ident
            elif con1.args[0].ident == allocVarName and con0.args[0].ident != allocVarName:
                allocReifName = inp1.ident
                skillReifName = inp0.ident
            else:
                valid = false
                break

            # Extract skill value from skill reif: int_eq_reif(ns_var, skill_val, b_skill)
            let skillCI = intEqReifByResult[skillReifName]
            let skillCon = tr.model.constraints[skillCI]
            let nsVarName = skillCon.args[0].ident
            let skillVal = try: tr.resolveIntArg(skillCon.args[1]) except ValueError, KeyError: (valid = false; 0)
            if not valid: break

            if not skillSet:
                requiredSkill = skillVal
                skillSet = true
            elif skillVal != requiredSkill:
                valid = false
                break

            # Extract engineer value from alloc reif: int_eq_reif(alloc_var, eng_val, b_alloc)
            let allocCI = intEqReifByResult[allocReifName]
            let allocCon = tr.model.constraints[allocCI]
            let engVal = try: tr.resolveIntArg(allocCon.args[1]) except ValueError, KeyError: (valid = false; 0)
            if not valid: break

            engSet.incl(engVal)
            nsByEng.mgetOrPut(engVal, @[]).add(nsVarName)

            # Only consume the array_bool_and — int_eq_reif constraints are SHARED
            # across multiple jobs (same b_skill/b_alloc used in multiple bool_clauses)
            localConsumedCIs.add(bAndCI)
            localConsumedVars.add(bAndName)

        if not valid or not skillSet or allocVarName == "": continue

        # Determine training slot structure from the grouped new_skills vars.
        # Each engineer should have the same number of ns vars (= nTrainingSlots).
        # Verify all engineers have the same number of training slots
        var nSlots = -1
        var slotCountValid = true
        for eng, nsVars in nsByEng:
            if nSlots < 0:
                nSlots = nsVars.len
            elif nsVars.len != nSlots:
                slotCountValid = false
                break
        if not slotCountValid or nSlots <= 0: continue

        # But wait - the mapping above puts all vars for the same engineer under slot 0.
        # We need to re-trace the array_bool_and to find which ns_var goes with which slot.
        # Actually, the ns_vars per engineer are just the distinct new_skills vars that
        # appear in int_eq_reif for that engineer's conjunctions. We can sort them
        # to get a consistent ordering.
        var nsVarNames = newSeq[seq[string]](nSlots)
        # Collect sorted engineers
        var sortedEngs: seq[int]
        for eng in engSet.items:
            sortedEngs.add(eng)
        sortedEngs.sort()

        for eng in sortedEngs:
            let nsVars = nsByEng[eng]
            # Sort for consistent slot ordering (same var appears in same slot position across engineers)
            var sorted = nsVars
            sorted.sort()
            for t in 0..<nSlots:
                nsVarNames[t].add(sorted[t])

        # Verify the structure: nsVarNames[t] should have one entry per engineer
        var structureValid = true
        for t in 0..<nSlots:
            if nsVarNames[t].len != sortedEngs.len:
                structureValid = false
                break
        if not structureValid: continue

        # Pattern detected!
        tr.skillAllocationDefs.add(SkillAllocationDef(
            allocVarName: allocVarName,
            requiredSkill: requiredSkill,
            posEngs: posEngs,
            sortedEngs: sortedEngs,
            nsVarNames: nsVarNames,
            nTrainingSlots: nSlots
        ))

        # Mark consumed constraints and variables
        for idx in localConsumedCIs:
            allConsumedCIs.incl(idx)
        for vn in localConsumedVars:
            allConsumedVars.incl(vn)

        inc nDetected

    # Apply all consumed constraints and variables
    # Note: int_eq_reif(alloc, eng, b_alloc) constraints are SHARED across jobs,
    # so we collect all consumed CIs globally and apply at the end.
    for idx in allConsumedCIs.items:
        tr.definingConstraints.incl(idx)
    for vn in allConsumedVars:
        tr.definedVarNames.incl(vn)

    # Dead-channel elimination: find int_eq_reif constraints whose outputs
    # have NO remaining (non-consumed) consumers.
    if nDetected > 0:
        var candidateCIs: PackedSet[int]
        for ci, con in tr.model.constraints:
            if ci in tr.definingConstraints: continue
            if not con.hasAnnotation("defines_var"): continue
            if stripSolverPrefix(con.name) != "int_eq_reif": continue
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            candidateCIs.incl(ci)
        let (deadCount, deadNames) = tr.eliminateDeadIntEqReifChannels(candidateCIs)
        if deadCount > 0:
            allConsumedVars = allConsumedVars + toHashSet(deadNames)
            stderr.writeLine(&"[FZN] Dead-channel elimination: {deadCount} int_eq_reif outputs removed")

    if nDetected > 0:
        stderr.writeLine(&"[FZN] Detected {nDetected} skill-allocation patterns ({allConsumedVars.len} vars, {allConsumedCIs.card} constraints consumed)")


proc pruneUnreferencedSkillValues(tr: var FznTranslator) =
    ## For new_skills variables in skill-allocation patterns: variables with domain
    ## containing 0 (meaning "no skill") and size > 10 that appear in
    ## int_eq_reif(var, const, b) constraints get their domain restricted to
    ## {0} ∪ {values actually referenced in int_eq_reif}.
    ## This removes skill values never required by any job.
    var referencedValues: Table[string, PackedSet[int]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3: continue

        let xArg = con.args[0]
        let valArg = con.args[1]

        # One arg must be an identifier (variable), other must be a constant
        if xArg.kind == FznIdent and (valArg.kind == FznIntLit or
                (valArg.kind == FznIdent and valArg.ident in tr.paramValues)):
            let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
            referencedValues.mgetOrPut(xArg.ident, initPackedSet[int]()).incl(val)
        elif valArg.kind == FznIdent and (xArg.kind == FznIntLit or
                (xArg.kind == FznIdent and xArg.ident in tr.paramValues)):
            let val = try: tr.resolveIntArg(xArg) except ValueError, KeyError: continue
            referencedValues.mgetOrPut(valArg.ident, initPackedSet[int]()).incl(val)

    var nPruned = 0
    for varName, refVals in referencedValues:
        if varName notin tr.varPositions: continue
        let pos = tr.varPositions[varName]
        let dom = tr.sys.baseArray.domain[pos]
        if dom.len <= 10 or 0 notin dom: continue
        var newDom: seq[int] = @[0]
        for v in dom:
            if v != 0 and v in refVals:
                newDom.add(v)
        if newDom.len < dom.len:
            tr.sys.baseArray.setDomain(pos, newDom)
            inc nPruned

    if nPruned > 0:
        stderr.writeLine(&"[FZN] Pruned unreferenced domain values from {nPruned} variables")


proc emitSkillAllocationConstraints(tr: var FznTranslator) =
    ## Creates compact channel-based constraints for detected skill-allocation patterns.
    ## For each job requiring skill s with allocation variable alloc:
    ##   1. Create channel vars: learned_t = element(alloc-1, [ns[1,t], ..., ns[E,t]])
    ##   2. Create set-membership lookup: b_base = element(alloc-lo, [1 if v in POSENGS else 0])
    ##   3. Create equality lookups: b_eq_t = element(learned_t, [1 if v==s else 0])
    ##   4. Constraint: b_base + b_eq_1 + ... + b_eq_T >= 1

    var nChannels = 0
    var nConstraints = 0
    var nDomainRestrictions = 0

    for pattern in tr.skillAllocationDefs:
        if pattern.allocVarName notin tr.varPositions: continue
        let allocPos = tr.varPositions[pattern.allocVarName]
        let allocExpr = tr.getExpr(allocPos)
        let allocDomain = tr.sys.baseArray.domain[allocPos]
        if allocDomain.len == 0: continue
        let allocLo = allocDomain[0]
        let allocHi = allocDomain[^1]
        let domainRange = allocHi - allocLo + 1  # element array covers allocLo..allocHi

        # 1. Create learned_t channel variables (variable-array element)
        # learned_t = element(alloc - allocLo, [ns[eng_lo,t], ..., ns[eng_hi,t]])
        var learnedPositions: seq[int]
        for t in 0..<pattern.nTrainingSlots:
            let channelPos = tr.sys.baseArray.len
            let v = tr.sys.newConstrainedVariable()
            # Set domain to union of all new_skills domains for this training slot
            var domSet: PackedSet[int]
            for nsVarName in pattern.nsVarNames[t]:
                if nsVarName in tr.varPositions:
                    let nsPos = tr.varPositions[nsVarName]
                    for dv in tr.sys.baseArray.domain[nsPos]:
                        domSet.incl(dv)
                elif nsVarName in tr.paramValues:
                    domSet.incl(tr.paramValues[nsVarName])
            var domSeq: seq[int]
            for dv in domSet.items:
                domSeq.add(dv)
            domSeq.sort()
            v.setDomain(domSeq)
            tr.sys.baseArray.channelPositions.incl(channelPos)

            # Build the element array: one entry per domain value (allocLo..allocHi)
            # Index = alloc - allocLo
            var arrayElems = newSeq[ArrayElement[int]](domainRange)
            for i, nsVarName in pattern.nsVarNames[t]:
                let engVal = pattern.sortedEngs[i]
                let arrayIdx = engVal - allocLo
                if nsVarName in tr.varPositions:
                    let nsPos = tr.varPositions[nsVarName]
                    let nsDom = tr.sys.baseArray.domain[nsPos]
                    if nsDom.len == 1:
                        arrayElems[arrayIdx] = ArrayElement[int](isConstant: true, constantValue: nsDom[0])
                    else:
                        arrayElems[arrayIdx] = ArrayElement[int](isConstant: false, variablePosition: nsPos)
                elif nsVarName in tr.paramValues:
                    arrayElems[arrayIdx] = ArrayElement[int](isConstant: true, constantValue: tr.paramValues[nsVarName])

            let indexExpr = allocExpr - allocLo
            let binding = ChannelBinding[int](
                channelPosition: channelPos,
                indexExpression: indexExpr,
                arrayElements: arrayElems
            )
            let bindingIdx = tr.sys.baseArray.channelBindings.len
            tr.sys.baseArray.channelBindings.add(binding)

            # Register in channelsAtPosition
            for pos in indexExpr.positions.items:
                if pos notin tr.sys.baseArray.channelsAtPosition:
                    tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
                else:
                    tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)
            for elem in arrayElems:
                if not elem.isConstant:
                    if elem.variablePosition notin tr.sys.baseArray.channelsAtPosition:
                        tr.sys.baseArray.channelsAtPosition[elem.variablePosition] = @[bindingIdx]
                    else:
                        tr.sys.baseArray.channelsAtPosition[elem.variablePosition].add(bindingIdx)

            learnedPositions.add(channelPos)
            inc nChannels

        # 2. Build constraint: alloc in POSENGS OR learned_1 == skill OR ... OR learned_T == skill
        # Express as: set_in_check + eq_check_1 + ... + eq_check_T >= 1
        # Where set_in_check = element(alloc - lo, membership_table)
        #       eq_check_t = element(learned_t - lo_t, equality_table)
        # But we can use algebraic expressions directly instead of channels.

        # Build set-in expression for alloc in POSENGS
        let posEngSet = toHashSet(pattern.posEngs)
        var setInElems: seq[ArrayElement[int]]
        for v in allocLo..allocHi:
            setInElems.add(ArrayElement[int](isConstant: true,
                    constantValue: if v in posEngSet: 1 else: 0))
        # Create channel for set_in check
        let setInPos = tr.sys.baseArray.len
        let setInVar = tr.sys.newConstrainedVariable()
        setInVar.setDomain(@[0, 1])
        tr.sys.baseArray.channelPositions.incl(setInPos)
        block:
            let indexExpr = allocExpr - allocLo
            let binding = ChannelBinding[int](
                channelPosition: setInPos,
                indexExpression: indexExpr,
                arrayElements: setInElems
            )
            let bindingIdx = tr.sys.baseArray.channelBindings.len
            tr.sys.baseArray.channelBindings.add(binding)
            for pos in indexExpr.positions.items:
                if pos notin tr.sys.baseArray.channelsAtPosition:
                    tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
                else:
                    tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)
        inc nChannels

        # Build equality check channels: learned_t == requiredSkill
        var eqCheckPositions: seq[int]
        for t in 0..<pattern.nTrainingSlots:
            let learnedPos = learnedPositions[t]
            let learnedDom = tr.sys.baseArray.domain[learnedPos]
            if learnedDom.len == 0: continue
            let lo = min(learnedDom)
            let hi = max(learnedDom)

            let eqPos = tr.sys.baseArray.len
            let eqVar = tr.sys.newConstrainedVariable()
            eqVar.setDomain(@[0, 1])
            tr.sys.baseArray.channelPositions.incl(eqPos)

            var eqElems: seq[ArrayElement[int]]
            for v in lo..hi:
                eqElems.add(ArrayElement[int](isConstant: true,
                        constantValue: if v == pattern.requiredSkill: 1 else: 0))

            let learnedExpr = tr.getExpr(learnedPos)
            let indexExpr = learnedExpr - lo
            let binding = ChannelBinding[int](
                channelPosition: eqPos,
                indexExpression: indexExpr,
                arrayElements: eqElems
            )
            let bindingIdx = tr.sys.baseArray.channelBindings.len
            tr.sys.baseArray.channelBindings.add(binding)
            for pos in indexExpr.positions.items:
                if pos notin tr.sys.baseArray.channelsAtPosition:
                    tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
                else:
                    tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

            eqCheckPositions.add(eqPos)
            inc nChannels

        # 3. Add constraint: setIn + eq_1 + ... + eq_T >= 1
        var sumExpr = tr.getExpr(setInPos)
        for eqPos in eqCheckPositions:
            sumExpr = sumExpr + tr.getExpr(eqPos)
        tr.sys.addConstraint(sumExpr >= 1)
        inc nConstraints

        # Domain restriction: restrict alloc to engineers who already have the skill OR
        # have at least one training slot whose domain includes the required skill
        var validEngineers: PackedSet[int]
        for e in pattern.posEngs:
            validEngineers.incl(e)
        for t in 0..<pattern.nTrainingSlots:
            for i, nsVarName in pattern.nsVarNames[t]:
                if nsVarName in tr.varPositions:
                    let nsPos = tr.varPositions[nsVarName]
                    let nsDom = tr.sys.baseArray.domain[nsPos]
                    if pattern.requiredSkill in nsDom:
                        validEngineers.incl(pattern.sortedEngs[i])
        var newDom: seq[int]
        for v in allocDomain:
            if v in validEngineers:
                newDom.add(v)
        if newDom.len > 0 and newDom.len < allocDomain.len:
            tr.sys.baseArray.setDomain(allocPos, newDom)
            inc nDomainRestrictions

    if nChannels > 0 or nConstraints > 0:
        stderr.writeLine(&"[FZN] Skill-allocation: {nChannels} channels, {nConstraints} constraints")
    if nDomainRestrictions > 0:
        stderr.writeLine(&"[FZN] Skill-allocation domain restrictions: {nDomainRestrictions} allocation variables")


proc detectAtMostThroughReif*(tr: var FznTranslator) =
    ## Detects int_lin_le([1,...,1], [b_1,...,b_n], rhs) where each b_k comes from
    ## int_eq_reif(x_k, same_value, b_k) :: defines_var(b_k), possibly through
    ## a bool2int(b_k, i_k) :: defines_var(i_k) chain.
    ## This is equivalent to atMost(x_positions, same_value, rhs).
    ## Consumes the int_lin_le, bool2int, and int_eq_reif constraints.

    # Build index: bool output var name -> (constraint index, source var name, constant value)
    var intEqReifByOutput: Table[string, tuple[ci: int, srcVar: string, constVal: int]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if not con.hasAnnotation("defines_var"): continue
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue

        # int_eq_reif(x, c, b) where c is a constant
        let srcVar = con.args[0].ident
        let bName = con.args[2].ident
        let constVal = try: tr.resolveIntArg(con.args[1])
                       except ValueError, KeyError: continue

        intEqReifByOutput[bName] = (ci: ci, srcVar: srcVar, constVal: constVal)

    # Build index: bool2int int output var name -> (constraint index, bool input var name)
    var bool2intByOutput: Table[string, tuple[ci: int, boolVar: string]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if not con.hasAnnotation("defines_var"): continue
        let name = stripSolverPrefix(con.name)
        if name != "bool2int": continue
        if con.args.len < 2: continue
        if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent: continue
        bool2intByOutput[con.args[1].ident] = (ci: ci, boolVar: con.args[0].ident)

    if intEqReifByOutput.len == 0: return

    var nDetected = 0
    var consumedLinLeCIs: PackedSet[int]
    var consumedEqReifCIs: PackedSet[int]
    var consumedBoolVarNames: HashSet[string]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue

        # Resolve coefficients
        let coeffs = try: tr.resolveIntArray(con.args[0])
                     except ValueError, KeyError: continue

        # Check all coefficients are +1
        var allPosOne = true
        for c in coeffs:
            if c != 1:
                allPosOne = false
                break
        if not allPosOne: continue

        # Resolve variable names
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if varElems.len != coeffs.len: continue

        # Check each variable is an int_eq_reif output (directly or through bool2int)
        # with the same constant value
        var targetValue = -1
        var targetSet = false
        var valid = true
        var srcVarNames: seq[string]
        var eqReifCIs: seq[int]
        var bool2intCIs: seq[int]
        var boolNames: seq[string]
        var intNames: seq[string]

        for elem in varElems:
            if elem.kind != FznIdent:
                valid = false
                break
            let varName = elem.ident

            # Try direct: varName is a bool output of int_eq_reif
            if varName in intEqReifByOutput:
                let info = intEqReifByOutput[varName]
                if not targetSet:
                    targetValue = info.constVal
                    targetSet = true
                elif info.constVal != targetValue:
                    valid = false
                    break
                srcVarNames.add(info.srcVar)
                eqReifCIs.add(info.ci)
                boolNames.add(varName)
            # Try through bool2int: varName is int output of bool2int(boolVar, varName)
            elif varName in bool2intByOutput:
                let b2iInfo = bool2intByOutput[varName]
                let boolVar = b2iInfo.boolVar
                if boolVar notin intEqReifByOutput:
                    valid = false
                    break
                let info = intEqReifByOutput[boolVar]
                if not targetSet:
                    targetValue = info.constVal
                    targetSet = true
                elif info.constVal != targetValue:
                    valid = false
                    break
                srcVarNames.add(info.srcVar)
                eqReifCIs.add(info.ci)
                bool2intCIs.add(b2iInfo.ci)
                boolNames.add(boolVar)
                intNames.add(varName)
            else:
                valid = false
                break

        if not valid or not targetSet: continue
        if srcVarNames.len < 2: continue  # Need at least 2 variables for a meaningful atMost

        let rhs = try: tr.resolveIntArg(con.args[2])
                  except ValueError, KeyError: continue

        # Pattern detected!
        tr.atMostThroughReifDefs.add(AtMostThroughReifDef(
            srcVarNames: srcVarNames,
            targetValue: targetValue,
            maxCount: rhs
        ))

        # Consume the int_lin_le constraint
        consumedLinLeCIs.incl(ci)

        # Record the int_eq_reif and bool2int constraints and their output vars
        for eqCi in eqReifCIs:
            consumedEqReifCIs.incl(eqCi)
        for b2iCi in bool2intCIs:
            # Consume the bool2int constraint directly since it's no longer needed
            tr.definingConstraints.incl(b2iCi)
        for bn in boolNames:
            consumedBoolVarNames.incl(bn)
        for iName in intNames:
            tr.definedVarNames.incl(iName)

        inc nDetected

    # Apply consumed int_lin_le constraints
    for idx in consumedLinLeCIs.items:
        tr.definingConstraints.incl(idx)

    # Dead-channel elimination for int_eq_reif outputs that now have no remaining consumers
    if nDetected > 0:
        let (deadCount, _) = tr.eliminateDeadIntEqReifChannels(consumedEqReifCIs)
        stderr.writeLine(&"[FZN] AtMost-through-reif: {nDetected} patterns detected, {deadCount} int_eq_reif channels eliminated")


proc emitAtMostThroughReif*(tr: var FznTranslator) =
    ## Emits direct atMost constraints for detected atMost-through-reification patterns.
    ## When multiple atMost constraints share the same positions, merges them into a
    ## single globalCardinalityBounded constraint for better incremental evaluation.

    # Step 1: Resolve all defs to position sequences
    type ResolvedDef = object
        positions: seq[int]
        targetValue: int
        maxCount: int

    var resolved: seq[ResolvedDef]
    for def in tr.atMostThroughReifDefs:
        var positions: seq[int]
        var allFound = true
        for vn in def.srcVarNames:
            if vn in tr.varPositions:
                positions.add(tr.varPositions[vn])
            elif vn in tr.definedVarExprs:
                allFound = false
                break
            else:
                allFound = false
                break
        if not allFound or positions.len == 0: continue
        resolved.add(ResolvedDef(positions: positions.sorted(), targetValue: def.targetValue, maxCount: def.maxCount))

    # Step 2: Group by sorted position set
    var groups: Table[seq[int], seq[ResolvedDef]]
    for rd in resolved:
        if rd.positions notin groups:
            groups[rd.positions] = @[]
        groups[rd.positions].add(rd)

    var nSingleEmitted = 0
    var nMergedGroups = 0
    var nMergedDefs = 0
    for positions, defs in groups:
        if defs.len == 1:
            # Single def: emit atMost as before
            tr.sys.addConstraint(atMost[int](positions, defs[0].targetValue, defs[0].maxCount))
            inc nSingleEmitted
        else:
            # Multiple defs sharing same positions: merge into GCC
            # Collect all domain values across positions
            var allDomainValues: PackedSet[int]
            for pos in positions:
                for v in tr.sys.baseArray.domain[pos]:
                    allDomainValues.incl(v)

            # Build cover, lbound, ubound (dedup by target value, take min of max counts)
            var coveredBounds: Table[int, int]  # targetValue → min(maxCount)
            for d in defs:
                if d.targetValue in coveredBounds:
                    coveredBounds[d.targetValue] = min(coveredBounds[d.targetValue], d.maxCount)
                else:
                    coveredBounds[d.targetValue] = d.maxCount
            var cover: seq[int]
            var lbound: seq[int]
            var ubound: seq[int]
            for value, maxCount in coveredBounds:
                cover.add(value)
                lbound.add(0)
                ubound.add(maxCount)

            # Add uncovered domain values with trivial bounds to avoid false penalties
            for v in allDomainValues:
                if v notin coveredBounds:
                    cover.add(v)
                    lbound.add(0)
                    ubound.add(positions.len)

            tr.sys.addConstraint(globalCardinalityBounded[int](positions, cover, lbound, ubound))
            inc nMergedGroups
            nMergedDefs += defs.len

    if nSingleEmitted > 0 or nMergedGroups > 0:
        var parts: seq[string]
        if nSingleEmitted > 0:
            parts.add(&"{nSingleEmitted} direct atMost")
        if nMergedGroups > 0:
            parts.add(&"merged {nMergedDefs} atMost into {nMergedGroups} GCC")
        stderr.writeLine(&"[FZN] AtMost-through-reif: {parts.join(\", \")}")

proc detectArgmaxPattern(tr: var FznTranslator) =
    ## Detects argmax decomposition patterns from MiniZinc's arg_max:
    ##   N × int_ne_reif(tower_var, t, ne_var_t) :: defines_var(ne_var_t)
    ##   N × int_lin_le_reif(coeffs, [max_var, ...], rhs, ne_var_t)
    ##   1 × array_int_maximum(max_var, signal_array) :: defines_var(max_var)
    ##
    ## Replaced by a single element constraint: signal_array[tower-1] == max_var
    ## This reduces N BooleanType constraints to 1 ElementType per argmax group.

    # Step 1: Index ne_reif channels by source variable.
    # reifChannelDefs contains CIs of int_eq_reif/int_ne_reif with defines_var.
    # We only care about int_ne_reif with a constant second arg.
    var neReifByTowerVar: Table[string, seq[tuple[tValue: int, neVarName: string, ci: int]]]

    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_ne_reif":
            continue
        if con.args.len < 3:
            continue
        # int_ne_reif(tower_var, const_t, ne_var) :: defines_var(ne_var)
        let towerArg = con.args[0]
        let valArg = con.args[1]
        let neArg = con.args[2]
        if towerArg.kind != FznIdent or neArg.kind != FznIdent:
            continue
        # val must be a constant
        let tVal = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
        let towerVarName = towerArg.ident
        let neVarName = neArg.ident

        if towerVarName notin neReifByTowerVar:
            neReifByTowerVar[towerVarName] = @[]
        neReifByTowerVar[towerVarName].add((tValue: tVal, neVarName: neVarName, ci: ci))

    if neReifByTowerVar.len == 0:
        return

    # Step 2: Build set of max channel variable names (from array_int_maximum defines_var).
    var maxChannelVarNames: HashSet[string]
    var maxVarToCI: Table[string, int]  # max_var_name → CI of array_int_maximum
    for def in tr.minMaxChannelDefs:
        if not def.isMin:
            maxChannelVarNames.incl(def.varName)
            maxVarToCI[def.varName] = def.ci

    if maxChannelVarNames.len == 0:
        return

    # Step 3: Index unconsumed comparison-reif constraints by boolean output variable.
    # Handles both int_lin_le_reif (variable signals) and int_le_reif (constant signals).
    # These are NOT consumed by detectReifChannels (no defines_var annotation).
    var compReifByBoolVar: Table[string, tuple[ci: int, con: FznConstraint]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "int_lin_le_reif":
            if con.hasAnnotation("defines_var"):
                continue  # Already consumed by detectReifChannels
            if con.args.len < 4:
                continue
            # int_lin_le_reif(coeffs, vars, rhs, bool_var)
            let boolArg = con.args[3]
            if boolArg.kind == FznIdent and boolArg.ident in tr.channelVarNames:
                compReifByBoolVar[boolArg.ident] = (ci: ci, con: con)
        elif name == "int_le_reif":
            if con.hasAnnotation("defines_var"):
                continue
            if con.args.len < 3:
                continue
            # int_le_reif(const, var, bool_var)
            let boolArg = con.args[2]
            if boolArg.kind == FznIdent and boolArg.ident in tr.channelVarNames:
                compReifByBoolVar[boolArg.ident] = (ci: ci, con: con)

    if compReifByBoolVar.len == 0:
        return

    # Step 4: Match complete argmax groups.
    var totalConsumedCompReif = 0
    var totalConsumedNeReif = 0
    var consumedMaxCIs: HashSet[int]

    for towerVarName, neReifGroup in neReifByTowerVar:
        if neReifGroup.len < 2:
            continue  # Need at least 2 entries for a meaningful argmax

        # Try to match each ne_reif to a comparison reif (int_lin_le_reif or int_le_reif)
        var matchedMaxVar = ""
        var valid = true
        var compCIs: seq[int]
        var neVarNames: seq[string]
        var neCIs: seq[int]

        # Sort by tValue to get ordered signal array
        var sortedGroup = neReifGroup
        sortedGroup.sort(proc(a, b: auto): int = cmp(a.tValue, b.tValue))

        for entry in sortedGroup:
            if entry.neVarName notin compReifByBoolVar:
                valid = false
                break

            let (compCi, compCon) = compReifByBoolVar[entry.neVarName]
            let compName = stripSolverPrefix(compCon.name)

            var foundMaxVar = ""

            if compName == "int_lin_le_reif":
                # int_lin_le_reif(coeffs, vars, rhs, bool) — variable signal
                let varsArg = compCon.args[1]
                var varElems: seq[FznExpr]
                if varsArg.kind == FznArrayLit:
                    varElems = varsArg.elems
                else:
                    valid = false
                    break

                var coeffs: seq[int]
                try:
                    coeffs = tr.resolveIntArray(compCon.args[0])
                except ValueError, KeyError:
                    valid = false
                    break
                if coeffs.len != varElems.len or varElems.len < 2:
                    valid = false
                    break

                for i in 0..<varElems.len:
                    if varElems[i].kind == FznIdent and varElems[i].ident in maxChannelVarNames and coeffs[i] < 0:
                        foundMaxVar = varElems[i].ident
                        break

            elif compName == "int_le_reif":
                # int_le_reif(const, max_var, bool) — constant signal
                let varArg = compCon.args[1]
                if varArg.kind == FznIdent and varArg.ident in maxChannelVarNames:
                    foundMaxVar = varArg.ident

            if foundMaxVar == "":
                valid = false
                break

            if matchedMaxVar == "":
                matchedMaxVar = foundMaxVar
            elif matchedMaxVar != foundMaxVar:
                valid = false
                break

            compCIs.add(compCi)
            neVarNames.add(entry.neVarName)
            neCIs.add(entry.ci)

        if not valid or matchedMaxVar == "":
            continue

        # Verify the ne_reif tValues form a contiguous 1..N range
        var tValues: seq[int]
        for entry in sortedGroup:
            tValues.add(entry.tValue)
        let minT = tValues[0]
        let maxT = tValues[^1]
        if maxT - minT + 1 != tValues.len:
            continue  # Not contiguous
        for i in 0..<tValues.len:
            if tValues[i] != minT + i:
                valid = false
                break
        if not valid:
            continue

        # Get the signal_array from array_int_maximum(max_var, signal_array)
        if matchedMaxVar notin maxVarToCI:
            continue
        let maxCi = maxVarToCI[matchedMaxVar]
        let maxCon = tr.model.constraints[maxCi]
        let signalArrayArg = maxCon.args[1]
        let signalElems = tr.resolveVarArrayElems(signalArrayArg)
        if signalElems.len != tValues.len:
            continue  # Signal array size must match number of towers

        # Validate signal elements — accept both FznIdent (variable) and FznIntLit (constant)
        var signalValid = true
        for elem in signalElems:
            if elem.kind != FznIdent and elem.kind != FznIntLit:
                signalValid = false
                break
        if not signalValid:
            continue

        # Pattern detected! Use first comp-reif CI as trigger, consume the rest.
        let triggerCI = compCIs[0]
        tr.argmaxPatterns[triggerCI] = ArgmaxPattern(
            towerVarName: towerVarName,
            maxVarName: matchedMaxVar,
            signalElems: signalElems,
        )

        # Consume all comp-reif CIs except the trigger
        for i in 1..<compCIs.len:
            tr.definingConstraints.incl(compCIs[i])

        # Consume the array_int_maximum constraint — the argmax channel replaces it.
        # The max_var keeps its channel position (other channels may depend on its position
        # existing) but its MinMaxChannelBinding is removed so it won't be evaluated.
        tr.definingConstraints.incl(maxCi)
        consumedMaxCIs.incl(maxCi)

        # Dead channel cleanup: remove ne_var channels (their only consumer is consumed)
        for i in 0..<neVarNames.len:
            tr.channelVarNames.excl(neVarNames[i])
            tr.definedVarNames.incl(neVarNames[i])
        # Remove ne_reif CIs from reifChannelDefs
        var neCIset: HashSet[int]
        for ci in neCIs:
            neCIset.incl(ci)
        var filteredReifDefs: seq[int]
        for ci in tr.reifChannelDefs:
            if ci notin neCIset:
                filteredReifDefs.add(ci)
        tr.reifChannelDefs = filteredReifDefs

        totalConsumedCompReif += compCIs.len
        totalConsumedNeReif += neVarNames.len
        stderr.writeLine(&"[FZN] Detected argmax pattern: {towerVarName} = argmax({signalElems.len} signals, max={matchedMaxVar})")

    if tr.argmaxPatterns.len > 0:
        # Remove consumed array_int_maximum entries from minMaxChannelDefs
        if consumedMaxCIs.len > 0:
            var filteredMinMaxDefs: seq[tuple[ci: int, varName: string, isMin: bool]]
            for def in tr.minMaxChannelDefs:
                if def.ci notin consumedMaxCIs:
                    filteredMinMaxDefs.add(def)
            tr.minMaxChannelDefs = filteredMinMaxDefs
        stderr.writeLine(&"[FZN] Argmax detection: {tr.argmaxPatterns.len} groups, consumed {totalConsumedCompReif} comp-reif + {totalConsumedNeReif} int_ne_reif channels + {consumedMaxCIs.len} max channels")

proc findMinimizedVarNames*(tr: FznTranslator): HashSet[string] =
    ## Finds variables that are minimized in the objective function.
    ## Scans for the objective's defining int_lin_eq and returns the set of variable names
    ## whose coefficients have the opposite sign to the objective variable's coefficient.
    if tr.model.solve.kind != Minimize: return
    if tr.model.solve.objective == nil or tr.model.solve.objective.kind != FznIdent: return
    let objName = tr.model.solve.objective.ident

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        if ann.args[0].ident != objName: continue
        # Found the objective defining constraint
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if coeffs.len != varElems.len: continue
        # Find objective's coefficient
        var objIdx = -1
        for i, v in varElems:
            if v.kind == FznIdent and v.ident == objName:
                objIdx = i
                break
        if objIdx < 0: continue
        let objCoeff = coeffs[objIdx]
        # Variables with coefficient sign opposite to objective are minimized
        for i, v in varElems:
            if i == objIdx: continue
            if v.kind != FznIdent: continue
            if (objCoeff > 0 and coeffs[i] < 0) or (objCoeff < 0 and coeffs[i] > 0):
                result.incl(v.ident)
        break

proc findForcedLargeVarNames*(tr: FznTranslator): HashSet[string] =
    ## Finds objective variables that the solver prefers to be LARGE.
    ## Making these max channels (= minimum feasible value) would fight the objective.
    ## For Minimize: variables with same-sign coefficient as objective (increasing them decreases obj).
    ## For Maximize: variables with opposite-sign coefficient (increasing them increases obj).
    ## For Satisfy: empty set.
    if tr.model.solve.kind == Satisfy: return
    if tr.model.solve.objective == nil or tr.model.solve.objective.kind != FznIdent: return
    let objName = tr.model.solve.objective.ident

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        if ann.args[0].ident != objName: continue
        # Found the objective defining constraint
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if coeffs.len != varElems.len: continue
        var objIdx = -1
        for i, v in varElems:
            if v.kind == FznIdent and v.ident == objName:
                objIdx = i
                break
        if objIdx < 0: continue
        let objCoeff = coeffs[objIdx]
        for i, v in varElems:
            if i == objIdx: continue
            if v.kind != FznIdent: continue
            let forcedLarge = case tr.model.solve.kind
                of Minimize:
                    # Same sign as objCoeff → increasing var decreases objective → want large
                    (objCoeff > 0 and coeffs[i] > 0) or (objCoeff < 0 and coeffs[i] < 0)
                of Maximize:
                    # Opposite sign to objCoeff → increasing var increases objective → want large
                    (objCoeff > 0 and coeffs[i] < 0) or (objCoeff < 0 and coeffs[i] > 0)
                of Satisfy:
                    false
            if forcedLarge:
                result.incl(v.ident)
        break

proc detectMaxFromLinLe*(tr: var FznTranslator) =
    ## Detects max-from-lin-le patterns:
    ## Multiple int_lin_le([1,-1], [source, ceiling], -offset) encode ceiling >= source + offset.
    ## When the ceiling variable is not forced-large by the objective, it equals max(source_i + offset_i).
    ## Makes ceiling a max channel, eliminating all those constraints.
    ##
    ## For non-objective ceilings: max channels with many inputs provide sparse penalty signal
    ## (only the argmax source affects the ceiling), so we limit group size. Objective-connected
    ## ceilings get direct signal through the objective expression regardless of input count.
    const MaxNonObjectiveCeilingInputs = 50

    var forcedLargeVarNames = tr.findForcedLargeVarNames()
    var minimizedVarNames = tr.findMinimizedVarNames()

    # Scan all unconsumed int_lin_le constraints.
    # Group by ceiling variable (negative coefficient).
    type LinLeInfo = tuple[sourceVar: string, offset: int, ci: int]
    var groups: Table[string, seq[LinLeInfo]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue

        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len != 2: continue

        let varElems = tr.resolveVarArrayElems(con.args[1])
        if varElems.len != 2: continue
        if varElems[0].kind != FznIdent or varElems[1].kind != FznIdent: continue

        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue

        # Look for pattern: [positive, negative] coefficients
        var sourceIdx, ceilingIdx: int
        if coeffs[0] > 0 and coeffs[1] < 0:
            sourceIdx = 0
            ceilingIdx = 1
        elif coeffs[0] < 0 and coeffs[1] > 0:
            sourceIdx = 1
            ceilingIdx = 0
        else:
            continue

        # Normalize: source * posCoeff - ceiling * negCoeff <= rhs
        # → ceiling >= source * (posCoeff / negCoeff) + (-rhs / negCoeff)
        # For the simple [1, -1] case: ceiling >= source + (-rhs)
        let posCoeff = coeffs[sourceIdx]
        let negCoeff = -coeffs[ceilingIdx]
        if posCoeff != negCoeff: continue  # only handle equal-weight case (typically both 1)

        let sourceName = varElems[sourceIdx].ident
        let ceilingName = varElems[ceilingIdx].ident
        let offset = -(rhs div posCoeff)  # ceiling >= source + offset

        if ceilingName notin groups:
            groups[ceilingName] = @[]
        groups[ceilingName].add((sourceVar: sourceName, offset: offset, ci: ci))

    # Build MaxFromLinLeDefs for groups of size >= 3 where ceiling is safe to channel.
    # Non-objective ceilings with many inputs give sparse signal through max channels,
    # since only the argmax source affects the ceiling value. Keep explicit constraints
    # for those — they provide per-source penalty feedback.
    var totalConsumed = 0
    for ceilingName, infos in groups:
        if infos.len < 3: continue
        if ceilingName in forcedLargeVarNames: continue
        if ceilingName in tr.definedVarNames: continue
        if ceilingName in tr.channelVarNames: continue
        if ceilingName notin minimizedVarNames and infos.len > MaxNonObjectiveCeilingInputs:
            continue

        var def = MaxFromLinLeDef(ceilingVarName: ceilingName)
        for info in infos:
            def.sourceVarNames.add(info.sourceVar)
            def.offsets.add(info.offset)
            def.consumedCIs.add(info.ci)

        # Mark ceiling var as channel (will be computed via MinMaxChannelBinding, not searched)
        # Do NOT add to definedVarNames — the variable needs a position for the channel binding
        tr.channelVarNames.incl(ceilingName)

        # Mark all consumed constraint indices
        for ci in def.consumedCIs:
            tr.definingConstraints.incl(ci)
        totalConsumed += def.consumedCIs.len

        tr.maxFromLinLeDefs.add(def)

    if tr.maxFromLinLeDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.maxFromLinLeDefs.len} max-from-lin-le channels, consumed {totalConsumed} int_lin_le constraints")

proc emitMaxFromLinLeChannels*(tr: var FznTranslator) =
    ## Emits max channel bindings for detected max-from-lin-le patterns.
    var nEmitted = 0
    for def in tr.maxFromLinLeDefs:
        if def.ceilingVarName notin tr.varPositions: continue
        let ceilingPos = tr.varPositions[def.ceilingVarName]

        var inputExprs: seq[AlgebraicExpression[int]]
        for i, srcName in def.sourceVarNames:
            let srcExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: srcName))
            if def.offsets[i] != 0:
                inputExprs.add(srcExpr + def.offsets[i])
            else:
                inputExprs.add(srcExpr)

        tr.sys.baseArray.addMinMaxChannelBinding(ceilingPos, isMin = false, inputExprs)
        inc nEmitted

    if nEmitted > 0:
        stderr.writeLine(&"[FZN] Emitted {nEmitted} max-from-lin-le channel bindings")

proc detectSpreadPattern*(tr: var FznTranslator) =
    ## Detects spread patterns:
    ## Pairwise int_lin_le([1,-1,-1], [y_i, y_j, S], c) encode S >= (y_i + offset_i) - y_j
    ## where c incorporates the offset. Groups by spread variable S.
    ## When S is minimized, replaced by: topVar = max(y_i + offset_i), botVar = min(y_i + offset_i),
    ## and a single constraint topVar - botVar <= S.
    if tr.model.solve.kind != Minimize: return

    var minimizedVarNames = tr.findMinimizedVarNames()

    # Also include variables that are already detected as max-from-lin-le ceilings
    # (they contribute to objective through the max channel)
    for def in tr.maxFromLinLeDefs:
        minimizedVarNames.incl(def.ceilingVarName)

    if minimizedVarNames.len == 0: return

    # Scan unconsumed int_lin_le with 3 variables: [pos, neg, neg] pattern
    # int_lin_le([1,-1,-1], [y_i, y_j, S], c) means y_i - y_j - S <= c
    # i.e., S >= y_i - y_j - c
    type SpreadInfo = tuple[posVar, negVar: string, rhs: int, ci: int]
    var spreadGroups: Table[string, seq[SpreadInfo]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue
        if con.args.len < 3: continue

        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len != 3: continue

        let varElems = tr.resolveVarArrayElems(con.args[1])
        if varElems.len != 3: continue
        var allIdent = true
        for v in varElems:
            if v.kind != FznIdent: allIdent = false; break
        if not allIdent: continue

        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue

        # Identify pattern: exactly one positive coeff and two negative
        var posIdx = -1
        var negIndices: seq[int]
        for i, c in coeffs:
            if c > 0:
                if posIdx >= 0: break  # more than one positive
                posIdx = i
            elif c < 0:
                negIndices.add(i)

        if posIdx < 0 or negIndices.len != 2: continue
        if coeffs[posIdx] != 1 or coeffs[negIndices[0]] != -1 or coeffs[negIndices[1]] != -1: continue

        let posVar = varElems[posIdx].ident
        let negVar1 = varElems[negIndices[0]].ident
        let negVar2 = varElems[negIndices[1]].ident

        # One of the negative-coefficient vars should be a spread var (minimized),
        # and the other should be a source var (not the spread var itself).
        # int_lin_le([1,-1,-1], [y_i, y_j, S], c) → S >= y_i - y_j - c
        var spreadVar, otherNegVar: string
        if negVar1 in minimizedVarNames and negVar2 notin minimizedVarNames:
            spreadVar = negVar1
            otherNegVar = negVar2
        elif negVar2 in minimizedVarNames and negVar1 notin minimizedVarNames:
            spreadVar = negVar2
            otherNegVar = negVar1
        elif negVar1 in minimizedVarNames and negVar2 in minimizedVarNames:
            # Both could be minimized — pick the one that appears more often as spread
            # (heuristic: the spread var appears in all constraints of the group)
            spreadVar = negVar1
            otherNegVar = negVar2
        else:
            continue

        if spreadVar notin spreadGroups:
            spreadGroups[spreadVar] = @[]
        spreadGroups[spreadVar].add((posVar: posVar, negVar: otherNegVar, rhs: rhs, ci: ci))

    # Validate and build SpreadPatternDefs
    var totalRetained = 0
    for spreadVarName, infos in spreadGroups:
        if infos.len < 3: continue

        # Collect unique source variables (appearing in position or negVar)
        var sourceSet: HashSet[string]
        for info in infos:
            sourceSet.incl(info.posVar)
            sourceSet.incl(info.negVar)
        let nSources = sourceSet.len

        # Expected number of pairwise constraints: n*(n-1) ordered pairs
        if infos.len != nSources * (nSources - 1): continue

        # Extract per-source offsets from positive-coefficient appearances.
        # When posVar appears with rhs c: S >= posVar - negVar - c
        # This means the "adjusted value" of posVar is posVar - c.
        # So offset for posVar is -c when it appears as the positive variable.
        # Verify consistency: same source in positive position always has same offset.
        var sourceOffsets: Table[string, int]
        var consistent = true
        for info in infos:
            let offset = -info.rhs
            if info.posVar in sourceOffsets:
                if sourceOffsets[info.posVar] != offset:
                    consistent = false
                    break
            else:
                sourceOffsets[info.posVar] = offset
        if not consistent: continue
        if sourceOffsets.len != nSources: continue

        # Build the def
        var def = SpreadPatternDef(spreadVarName: spreadVarName)
        for srcName in sourceSet:
            def.sourceVarNames.add(srcName)
            def.offsets.add(sourceOffsets[srcName])
        for info in infos:
            def.consumedCIs.add(info.ci)

        # Keep all pairwise constraints for gradient signal in tabu search.
        # Channel replacement loses per-pair gradient, degrading search quality.
        totalRetained += def.consumedCIs.len

        # Do NOT mark spread var as channel — it stays as a search variable
        tr.spreadPatternDefs.add(def)

    if tr.spreadPatternDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.spreadPatternDefs.len} spread patterns ({totalRetained} pairwise constraints retained)")

proc emitSpreadPatternChannels*(tr: var FznTranslator) =
    ## Emits max/min channel bindings + simple constraint for each spread pattern.
    ## For each spread group: topVar = max(src_i + offset_i), botVar = min(src_i),
    ## and topVar - botVar <= S.
    var nEmitted = 0
    for def in tr.spreadPatternDefs:
        if def.spreadVarName notin tr.varPositions: continue
        let spreadPos = tr.varPositions[def.spreadVarName]

        # Build input expressions for max and min channels
        var topInputExprs: seq[AlgebraicExpression[int]]
        var botInputExprs: seq[AlgebraicExpression[int]]
        for i, srcName in def.sourceVarNames:
            let srcExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: srcName))
            if def.offsets[i] != 0:
                topInputExprs.add(srcExpr + def.offsets[i])
            else:
                topInputExprs.add(srcExpr)
            botInputExprs.add(srcExpr)

        # Create auxiliary max channel variable (topVar)
        let topPos = tr.sys.baseArray.len
        discard tr.sys.newConstrainedVariable()
        # Compute domain for topVar: range of (source + offset) values
        var topMin = high(int)
        var topMax = low(int)
        for i, srcName in def.sourceVarNames:
            if srcName in tr.varPositions:
                let srcPos = tr.varPositions[srcName]
                let dom = tr.sys.baseArray.domain[srcPos]
                if dom.len > 0:
                    topMin = min(topMin, dom[0] + def.offsets[i])
                    topMax = max(topMax, dom[^1] + def.offsets[i])
        if topMin <= topMax:
            tr.sys.baseArray.setDomain(topPos, toSeq(topMin..topMax))
        tr.sys.baseArray.addMinMaxChannelBinding(topPos, isMin = false, topInputExprs)

        # Create auxiliary min channel variable (botVar)
        let botPos = tr.sys.baseArray.len
        discard tr.sys.newConstrainedVariable()
        # Compute domain for botVar: range of source values (no offset for min)
        var botMin = high(int)
        var botMax = low(int)
        for i, srcName in def.sourceVarNames:
            if srcName in tr.varPositions:
                let srcPos = tr.varPositions[srcName]
                let dom = tr.sys.baseArray.domain[srcPos]
                if dom.len > 0:
                    botMin = min(botMin, dom[0])
                    botMax = max(botMax, dom[^1])
        if botMin <= botMax:
            tr.sys.baseArray.setDomain(botPos, toSeq(botMin..botMax))
        tr.sys.baseArray.addMinMaxChannelBinding(botPos, isMin = true, botInputExprs)

        # Add constraint: topVar - botVar <= S
        let topExpr = tr.getExpr(topPos)
        let botExpr = tr.getExpr(botPos)
        let spreadExpr = tr.getExpr(spreadPos)
        tr.sys.addConstraint(topExpr - botExpr <= spreadExpr)

        inc nEmitted
        stderr.writeLine(&"[FZN] Spread pattern '{def.spreadVarName}': added max/min channels + 1 constraint over {def.sourceVarNames.len} sources ({def.consumedCIs.len} pairwise constraints retained)")

    if nEmitted > 0:
        stderr.writeLine(&"[FZN] Emitted {nEmitted} spread pattern channel groups")

proc tightenDiffnTimeProfile*(tr: var FznTranslator) =
    ## When diffn has constant x/dx/dy, compute the time profile to derive a lower bound
    ## on max(y + dy). Tightens ceiling variable domains from max-from-lin-le patterns.
    if tr.maxFromLinLeDefs.len == 0: return

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_diffn": continue
        if con.args.len < 4: continue

        # Try to resolve x, dx, dy as constant arrays
        let xVals = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let dxVals = try: tr.resolveIntArray(con.args[2]) except ValueError, KeyError: continue
        let dyVals = try: tr.resolveIntArray(con.args[3]) except ValueError, KeyError: continue

        if xVals.len != dxVals.len or xVals.len != dyVals.len: continue
        if xVals.len == 0: continue

        # Collect y-variable names from the diffn constraint for source matching
        let yElems = tr.resolveVarArrayElems(con.args[1])
        var diffnYVarNames: HashSet[string]
        for elem in yElems:
            if elem.kind == FznIdent:
                diffnYVarNames.incl(elem.ident)

        # Compute time profile via sweep-line
        type Event = tuple[time, delta: int]
        var events: seq[Event]
        for i in 0..<xVals.len:
            events.add((time: xVals[i], delta: dyVals[i]))
            events.add((time: xVals[i] + dxVals[i], delta: -dyVals[i]))
        events.sort(proc(a, b: Event): int =
            result = cmp(a.time, b.time)
            if result == 0:
                # Process end events (negative delta) before start events (positive delta)
                result = cmp(a.delta, b.delta)
        )

        var maxLoad = 0
        var currentLoad = 0
        for ev in events:
            currentLoad += ev.delta
            maxLoad = max(maxLoad, currentLoad)

        if maxLoad <= 0: continue

        stderr.writeLine(&"[FZN] Diffn time profile: max_load = {maxLoad} ({xVals.len} rectangles)")

        # Tighten ceiling variable domains from max-from-lin-le patterns
        # Only apply when the pattern's source variables overlap with the diffn's y-variables
        for def in tr.maxFromLinLeDefs:
            if def.ceilingVarName notin tr.varPositions: continue
            var hasOverlap = false
            for srcName in def.sourceVarNames:
                if srcName in diffnYVarNames:
                    hasOverlap = true; break
            if not hasOverlap: continue
            let ceilingPos = tr.varPositions[def.ceilingVarName]
            let currentDom = tr.sys.baseArray.domain[ceilingPos]
            if currentDom.len == 0: continue

            var newDom: seq[int]
            for v in currentDom:
                if v >= maxLoad:
                    newDom.add(v)
            if newDom.len > 0 and newDom.len < currentDom.len:
                tr.sys.baseArray.setDomain(ceilingPos, newDom)
                stderr.writeLine(&"[FZN] Diffn time profile: tightened '{def.ceilingVarName}' domain from {currentDom.len} to {newDom.len} values (>= {maxLoad})")

        # Separated clustering bound for D upper bound.
        # If spread patterns (airline groups) are detected, each group's flights can be
        # packed into its own band of height = group peak load. Since bands don't overlap,
        # D <= sum(group peaks). Any remaining (ungrouped) rectangles add their own peak.
        # This is provably tight: S[a] >= peak_a - 1 always holds (from diffn), so
        # objective >= D + sum(peak_a - 1), and at D = sum(peaks) the separated
        # solution achieves exactly this bound.
        block separatedClusteringBound:
            if tr.spreadPatternDefs.len == 0: break separatedClusteringBound

            # Build yName → rectangle index map for this diffn constraint
            var yNameToRectIdx: Table[string, int]
            for i, elem in yElems:
                if elem.kind == FznIdent:
                    yNameToRectIdx[elem.ident] = i

            # Compute per-group peak loads
            var groupedRectIndices: HashSet[int]
            var sumGroupPeaks = 0
            var nGroups = 0

            # Compute time horizon for sweep-line
            var tMax = 0
            for i in 0..<xVals.len:
                tMax = max(tMax, xVals[i] + dxVals[i])
            if tMax <= 0: break separatedClusteringBound

            for def in tr.spreadPatternDefs:
                # Map spread sources to diffn rectangle indices
                type GroupRect = tuple[rectIdx, xStart, xEnd, dy: int]
                var groupRects: seq[GroupRect]
                for srcIdx, srcName in def.sourceVarNames:
                    if srcName in yNameToRectIdx:
                        let ri = yNameToRectIdx[srcName]
                        groupRects.add((rectIdx: ri,
                                        xStart: xVals[ri],
                                        xEnd: xVals[ri] + dxVals[ri],
                                        dy: dyVals[ri]))
                        groupedRectIndices.incl(ri)

                if groupRects.len == 0: continue

                # Compute group-only time profile
                var profile = newSeq[int](tMax + 1)
                for r in groupRects:
                    for t in r.xStart ..< r.xEnd:
                        profile[t] += r.dy
                var groupPeak = 0
                for t in 0..tMax:
                    groupPeak = max(groupPeak, profile[t])

                sumGroupPeaks += groupPeak
                inc nGroups

            # Add peak from ungrouped rectangles (if any)
            var ungroupedPeak = 0
            var hasUngrouped = false
            if groupedRectIndices.len < xVals.len:
                var profile = newSeq[int](tMax + 1)
                for i in 0..<xVals.len:
                    if i notin groupedRectIndices:
                        hasUngrouped = true
                        for t in xVals[i] ..< xVals[i] + dxVals[i]:
                            profile[t] += dyVals[i]
                if hasUngrouped:
                    for t in 0..tMax:
                        ungroupedPeak = max(ungroupedPeak, profile[t])

            let dUb = sumGroupPeaks + ungroupedPeak
            if dUb <= 0 or dUb >= maxLoad * xVals.len: break separatedClusteringBound
            # Only apply if tighter than current domain
            stderr.writeLine(&"[FZN] Diffn separated clustering: D upper bound = {dUb} ({nGroups} groups, max_load = {maxLoad})")

            # Tighten ceiling domains (upper bound)
            for def in tr.maxFromLinLeDefs:
                if def.ceilingVarName notin tr.varPositions: continue
                var hasOverlap = false
                for srcName in def.sourceVarNames:
                    if srcName in diffnYVarNames:
                        hasOverlap = true; break
                if not hasOverlap: continue
                let ceilingPos = tr.varPositions[def.ceilingVarName]
                let currentDom = tr.sys.baseArray.domain[ceilingPos]
                if currentDom.len == 0: continue
                if currentDom[^1] <= dUb: continue
                var newDom: seq[int]
                for v in currentDom:
                    if v <= dUb:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < currentDom.len:
                    tr.sys.baseArray.setDomain(ceilingPos, newDom)
                    stderr.writeLine(&"[FZN] Diffn separated clustering: tightened '{def.ceilingVarName}' domain from {currentDom.len} to {newDom.len} values (<= {dUb})")

            # Tighten y-variable upper bounds: y[i] + dy[i] - 1 <= dUb
            var nTightened = 0
            for i in 0..<yElems.len:
                if yElems[i].kind != FznIdent: continue
                if yElems[i].ident notin tr.varPositions: continue
                let yPos = tr.varPositions[yElems[i].ident]
                let yDom = tr.sys.baseArray.domain[yPos]
                if yDom.len == 0: continue
                let yMax = dUb - dyVals[i] + 1
                if yMax >= yDom[^1]: continue
                var newDom: seq[int]
                for v in yDom:
                    if v <= yMax:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < yDom.len:
                    tr.sys.baseArray.setDomain(yPos, newDom)
                    inc nTightened
            if nTightened > 0:
                let samplePos = (if yElems[0].kind == FznIdent and yElems[0].ident in tr.varPositions:
                    tr.varPositions[yElems[0].ident] else: -1)
                if samplePos >= 0:
                    stderr.writeLine(&"[FZN] Diffn separated clustering: tightened {nTightened} y-domains (e.g. domain size {tr.sys.baseArray.domain[samplePos].len})")

            # Tighten spread variable upper bounds: S[a] <= dUb - 1
            # Since all y-positions are in [1, dUb-dy+1], the max spread is dUb - 1.
            var nSpreadTightened = 0
            for def in tr.spreadPatternDefs:
                if def.spreadVarName notin tr.varPositions: continue
                let spreadPos = tr.varPositions[def.spreadVarName]
                let spreadDom = tr.sys.baseArray.domain[spreadPos]
                if spreadDom.len == 0: continue
                let spreadUb = dUb - 1
                if spreadDom[^1] <= spreadUb: continue
                var newDom: seq[int]
                for v in spreadDom:
                    if v <= spreadUb:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < spreadDom.len:
                    tr.sys.baseArray.setDomain(spreadPos, newDom)
                    inc nSpreadTightened
            if nSpreadTightened > 0:
                stderr.writeLine(&"[FZN] Diffn separated clustering: tightened {nSpreadTightened} spread domains (<= {dUb - 1})")

        # Per-rectangle time-table reasoning: compute compulsory y-interval profile
        # from other x-overlapping rectangles, then tighten each y_i domain.
        # Compulsory part of rect j: if latest_start_j < earliest_end_j, then
        # rect j MUST occupy y-interval [latest_start_j, earliest_end_j) regardless of placement.
        # At each y-height, the sum of dx_j for rects with compulsory parts there is "locked width".
        # For rect i at x-interval [x_i, x_i+dx_i): if locked width from other rects >= D at some
        # y-height h, then rect i cannot overlap h, constraining y_i.
        if yElems.len == xVals.len:
            # Build per-rectangle compulsory parts
            type CompulsoryRect = object
                idx: int
                xStart, xEnd: int  # x-interval [xStart, xEnd)
                dy: int
                yLo, yHi: int     # current domain bounds for y
                compStart, compEnd: int  # compulsory y-interval
                hasCompulsory: bool
            var rects: seq[CompulsoryRect]
            for i in 0..<xVals.len:
                var cr = CompulsoryRect(
                    idx: i, xStart: xVals[i], xEnd: xVals[i] + dxVals[i], dy: dyVals[i])
                if yElems[i].kind == FznIdent and yElems[i].ident in tr.varPositions:
                    let yPos = tr.varPositions[yElems[i].ident]
                    let yDom = tr.sys.baseArray.domain[yPos]
                    if yDom.len > 0:
                        cr.yLo = min(yDom)
                        cr.yHi = max(yDom)
                        # Compulsory part: [latest_start, earliest_end)
                        cr.compStart = cr.yHi        # latest start
                        cr.compEnd = cr.yLo + cr.dy   # earliest end
                        cr.hasCompulsory = cr.compEnd > cr.compStart
                rects.add(cr)

            var anyTightened = true
            var iteration = 0
            while anyTightened and iteration < 5:
                anyTightened = false
                inc iteration
                for i in 0..<rects.len:
                    if yElems[i].kind != FznIdent: continue
                    if yElems[i].ident notin tr.varPositions: continue
                    let yPos = tr.varPositions[yElems[i].ident]
                    let yDom = tr.sys.baseArray.domain[yPos]
                    if yDom.len == 0: continue

                    # Compute compulsory load profile from OTHER rects that overlap in x with rect i
                    # For each y-height, sum dy_j of rects j (j != i) whose compulsory part covers that height
                    # and whose x-interval overlaps with rect i's x-interval.
                    # Use sweep-line on compulsory intervals.
                    type YEvent = tuple[y, delta: int]
                    var yEvents: seq[YEvent]
                    for j in 0..<rects.len:
                        if j == i: continue
                        if not rects[j].hasCompulsory: continue
                        # Check x-overlap: [x_i, x_i+dx_i) ∩ [x_j, x_j+dx_j) non-empty
                        if rects[j].xEnd <= rects[i].xStart or rects[i].xEnd <= rects[j].xStart:
                            continue
                        yEvents.add((y: rects[j].compStart, delta: rects[j].dy))
                        yEvents.add((y: rects[j].compEnd, delta: -rects[j].dy))

                    if yEvents.len == 0: continue
                    yEvents.sort(proc(a, b: YEvent): int =
                        result = cmp(a.y, b.y)
                        if result == 0: result = cmp(a.delta, b.delta))

                    # Find y-intervals where compulsory load makes rect i impossible to place
                    # Rect i needs dy_i contiguous height units. Find the maximum compulsory load
                    # within any window of size dy_i in rect i's feasible range.
                    # Simpler: find y-heights where load >= maxLoad - dy_i + 1 (rect i can't overlap)
                    # and use these as "forbidden" zones to tighten rect i's domain.

                    # Build the load profile as (y, load) breakpoints
                    type Breakpoint = tuple[y, load: int]
                    var profile: seq[Breakpoint]
                    var curLoad = 0
                    for ev in yEvents:
                        curLoad += ev.delta
                        if profile.len > 0 and profile[^1].y == ev.y:
                            profile[^1].load = curLoad
                        else:
                            profile.add((y: ev.y, load: curLoad))

                    # For rect i at position y_i, it occupies [y_i, y_i + dy_i).
                    # Infeasible if at any point in [y_i, y_i + dy_i), the compulsory load
                    # plus dy_i > maxLoad (since rect i adds dy_i to the load at its position).
                    # So rect i can't start at y_i if max_load_in([y_i, y_i+dy_i)) + dy_i > maxLoad.
                    # Equivalently: if max_load_in([y_i, y_i+dy_i)) > maxLoad - dy_i.
                    let threshold = maxLoad - rects[i].dy

                    # Compute max compulsory load in sliding window [y, y+dy_i) for each domain value
                    var newDom: seq[int]
                    for v in yDom:
                        let winEnd = v + rects[i].dy
                        # Find max load in [winStart, winEnd) from profile breakpoints
                        var windowMax = 0
                        for bp in profile:
                            if bp.y >= winEnd: break
                            if bp.load > windowMax:
                                windowMax = bp.load
                        # Also check initial load at winStart (before first breakpoint)
                        if windowMax <= threshold:
                            newDom.add(v)

                    if newDom.len > 0 and newDom.len < yDom.len:
                        tr.sys.baseArray.setDomain(yPos, newDom)
                        stderr.writeLine(&"[FZN] Diffn time-table: tightened '{yElems[i].ident}' domain from {yDom.len} to {newDom.len} values")
                        # Update compulsory part for this rect
                        rects[i].yLo = newDom[0]
                        rects[i].yHi = newDom[^1]
                        rects[i].compStart = rects[i].yHi
                        rects[i].compEnd = rects[i].yLo + rects[i].dy
                        rects[i].hasCompulsory = rects[i].compEnd > rects[i].compStart
                        anyTightened = true

            if iteration > 1:
                stderr.writeLine(&"[FZN] Diffn time-table: {iteration} fixpoint iterations")

proc tightenMaxFromLinLeBounds*(tr: var FznTranslator) =
    ## Bidirectional domain tightening for max-from-lin-le patterns.
    ## Given D = max(y_i + offset_i):
    ##   - Upper bound on sources: y_i <= max(dom(D)) - offset_i
    ##   - Lower bound on ceiling: D >= max_i(min(dom(y_i)) + offset_i)
    ## Iterates to fixpoint since tightening one side can enable the other.
    if tr.maxFromLinLeDefs.len == 0: return

    var anyTightened = true
    var iteration = 0
    while anyTightened and iteration < 10:
        anyTightened = false
        inc iteration

        for def in tr.maxFromLinLeDefs:
            if def.ceilingVarName notin tr.varPositions: continue
            let ceilingPos = tr.varPositions[def.ceilingVarName]
            let ceilingDom = tr.sys.baseArray.domain[ceilingPos]
            if ceilingDom.len == 0: continue
            let maxCeiling = max(ceilingDom)

            # Phase 1: Tighten source upper bounds from ceiling max
            # y_i + offset_i <= D, so y_i <= max(dom(D)) - offset_i
            for i, srcName in def.sourceVarNames:
                if srcName notin tr.varPositions: continue
                let srcPos = tr.varPositions[srcName]
                let srcDom = tr.sys.baseArray.domain[srcPos]
                if srcDom.len == 0: continue
                let upperBound = maxCeiling - def.offsets[i]
                if max(srcDom) <= upperBound: continue
                var newDom: seq[int]
                for v in srcDom:
                    if v <= upperBound:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < srcDom.len:
                    tr.sys.baseArray.setDomain(srcPos, newDom)
                    stderr.writeLine(&"[FZN] Max channel: tightened '{srcName}' upper bound to <= {upperBound} ({srcDom.len} -> {newDom.len})")
                    anyTightened = true

            # Phase 2: Tighten ceiling lower bound from source minimums
            # D = max(y_i + offset_i) >= min(dom(y_i)) + offset_i for each i
            # So D >= max_i(min(dom(y_i)) + offset_i)
            var minCeiling = low(int)
            for i, srcName in def.sourceVarNames:
                if srcName notin tr.varPositions: continue
                let srcPos = tr.varPositions[srcName]
                let srcDom = tr.sys.baseArray.domain[srcPos]
                if srcDom.len == 0: continue
                let lb = min(srcDom) + def.offsets[i]
                if lb > minCeiling:
                    minCeiling = lb
            if minCeiling > min(ceilingDom):
                var newDom: seq[int]
                for v in ceilingDom:
                    if v >= minCeiling:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < ceilingDom.len:
                    tr.sys.baseArray.setDomain(ceilingPos, newDom)
                    stderr.writeLine(&"[FZN] Max channel: tightened '{def.ceilingVarName}' lower bound to >= {minCeiling} ({ceilingDom.len} -> {newDom.len})")
                    anyTightened = true

    if iteration > 1:
        stderr.writeLine(&"[FZN] Max channel bounds: {iteration} fixpoint iterations")

proc tightenSpreadFromDiffnProfile*(tr: var FznTranslator) =
    ## For each spread pattern group whose sources overlap with a constant-x diffn's
    ## y-variables, compute the group-only time profile to derive a lower bound on S.
    ## At peak time t, active group rectangles require sum(dy) vertical units
    ## non-overlapping, so spread >= groupMaxLoad - 1.
    if tr.spreadPatternDefs.len == 0: return

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_diffn": continue
        if con.args.len < 4: continue

        # Try to resolve x, dx, dy as constant arrays
        let xVals = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let dxVals = try: tr.resolveIntArray(con.args[2]) except ValueError, KeyError: continue
        let dyVals = try: tr.resolveIntArray(con.args[3]) except ValueError, KeyError: continue

        if xVals.len != dxVals.len or xVals.len != dyVals.len: continue
        if xVals.len == 0: continue

        # Build yName → rectangle index map
        let yElems = tr.resolveVarArrayElems(con.args[1])
        if yElems.len != xVals.len: continue
        var yNameToIdx: Table[string, int]
        for i, elem in yElems:
            if elem.kind == FznIdent:
                yNameToIdx[elem.ident] = i

        # For each spread pattern, compute group-only time profile
        for def in tr.spreadPatternDefs:
            if def.spreadVarName notin tr.varPositions: continue

            # Map spread sources to diffn rectangle indices, verifying offset = dy - 1
            type GroupRect = tuple[xStart, xEnd, dy: int]
            var groupRects: seq[GroupRect]
            var offsetMatchesDy = true
            for srcIdx, srcName in def.sourceVarNames:
                if srcName in yNameToIdx:
                    let rectIdx = yNameToIdx[srcName]
                    if def.offsets[srcIdx] != dyVals[rectIdx] - 1:
                        offsetMatchesDy = false
                        break
                    groupRects.add((xStart: xVals[rectIdx],
                                    xEnd: xVals[rectIdx] + dxVals[rectIdx],
                                    dy: dyVals[rectIdx]))

            if not offsetMatchesDy: continue
            if groupRects.len < 2: continue

            # Compute group-only time profile via sweep-line
            type Event = tuple[time, delta: int]
            var events: seq[Event]
            for r in groupRects:
                events.add((time: r.xStart, delta: r.dy))
                events.add((time: r.xEnd, delta: -r.dy))
            events.sort(proc(a, b: Event): int =
                result = cmp(a.time, b.time)
                if result == 0:
                    result = cmp(a.delta, b.delta)
            )

            var groupMaxLoad = 0
            var currentLoad = 0
            for ev in events:
                currentLoad += ev.delta
                groupMaxLoad = max(groupMaxLoad, currentLoad)

            if groupMaxLoad <= 1: continue

            let spreadLB = groupMaxLoad - 1
            let spreadPos = tr.varPositions[def.spreadVarName]
            let currentDom = tr.sys.baseArray.domain[spreadPos]
            if currentDom.len == 0: continue
            if min(currentDom) >= spreadLB: continue  # already tight enough

            var newDom: seq[int]
            for v in currentDom:
                if v >= spreadLB:
                    newDom.add(v)
            if newDom.len > 0 and newDom.len < currentDom.len:
                tr.sys.baseArray.setDomain(spreadPos, newDom)
                stderr.writeLine(&"[FZN] Spread time profile: tightened '{def.spreadVarName}' domain from {currentDom.len} to {newDom.len} values (>= {spreadLB}, groupMaxLoad={groupMaxLoad})")


proc detectIntModChannels(tr: var FznTranslator) =
    ## Detects int_mod(X, C, Z) where X is a variable and C is a constant.
    ## These can be implemented as element channel bindings with a precomputed
    ## lookup table: Z = table[X - xLo] where table[i] = (xLo + i) mod C.
    var nDetected = 0
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_mod": continue

        let xArg = con.args[0]
        let yArg = con.args[1]
        let zArg = con.args[2]

        # Only handle: variable X, constant C, variable Z
        if yArg.kind != FznIntLit: continue
        if xArg.kind != FznIdent: continue
        if zArg.kind != FznIdent: continue

        let cVal = yArg.intVal
        if cVal <= 0: continue  # mod by non-positive is degenerate

        let xDomain = tr.lookupVarDomain(xArg.ident)
        if xDomain.len == 0: continue

        let xLo = xDomain[0]  # domains are sorted, first element is min
        let xHi = xDomain[^1]

        # Build lookup table: for each value in xLo..xHi, compute ((v mod c) + c) mod c
        var lookupTable: seq[int]
        for v in xLo..xHi:
            lookupTable.add(((v mod cVal) + cVal) mod cVal)

        # Mark Z as a channel variable
        tr.channelVarNames.incl(zArg.ident)
        tr.definedVarNames.excl(zArg.ident)
        tr.definingConstraints.incl(ci)

        tr.intModChannelDefs.add((
            varName: zArg.ident,
            originVar: xArg.ident,
            lookupTable: lookupTable,
            offset: xLo))

        inc nDetected

    if nDetected > 0:
        stderr.writeLine(&"[FZN] Detected {nDetected} int_mod channel bindings")

proc detectIntDivChannels(tr: var FznTranslator) =
    ## Detects int_div(X, C, Z) where X is a variable and C is a positive constant.
    ## These can be implemented as element channel bindings with a precomputed
    ## lookup table: Z = table[X - xLo] where table[i] = (xLo + i) div C.
    var nDetected = 0
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_div": continue

        let xArg = con.args[0]
        let yArg = con.args[1]
        let zArg = con.args[2]

        # Only handle: variable X, constant C, variable Z
        if yArg.kind != FznIntLit: continue
        if xArg.kind != FznIdent: continue
        if zArg.kind != FznIdent: continue

        let cVal = yArg.intVal
        if cVal <= 0: continue  # div by non-positive is degenerate

        let xDomain = tr.lookupVarDomain(xArg.ident)
        if xDomain.len == 0: continue

        let xLo = xDomain[0]  # domains are sorted, first element is min
        let xHi = xDomain[^1]

        # Skip if lookup table would be too large
        if xHi - xLo + 1 > 100_000: continue

        # Build lookup table: for each value in xLo..xHi, compute v div C
        # Nim's div truncates toward zero, matching FlatZinc int_div semantics
        var lookupTable: seq[int]
        for v in xLo..xHi:
            lookupTable.add(v div cVal)

        # Mark Z as a channel variable
        tr.channelVarNames.incl(zArg.ident)
        tr.definedVarNames.excl(zArg.ident)
        tr.definingConstraints.incl(ci)

        tr.intDivChannelDefs.add((
            varName: zArg.ident,
            originVar: xArg.ident,
            lookupTable: lookupTable,
            offset: xLo))

        inc nDetected

    if nDetected > 0:
        stderr.writeLine(&"[FZN] Detected {nDetected} int_div channel bindings")

proc detectSingletonSetChannels(tr: var FznTranslator) =
    ## Detects set_card(S, 1) + set_in(x, S) where x is a variable.
    ## Makes S.bools into indicator channels: S.bools[e] = (x == e) ? 1 : 0.
    ## This eliminates |universe| binary search variables per singleton set.

    # Step 1: Find all set_card(S, 1) constraints
    var cardOneSets: Table[string, int]  # set name -> constraint index
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "set_card" or con.args.len < 2: continue
        if con.args[0].kind != FznIdent: continue
        if con.args[1].kind == FznIntLit and con.args[1].intVal == 1:
            cardOneSets[con.args[0].ident] = ci
        elif con.args[1].kind == FznIdent and con.args[1].ident in tr.paramValues:
            if tr.paramValues[con.args[1].ident] == 1:
                cardOneSets[con.args[0].ident] = ci

    # Step 2: Find matching set_in(x, S) where S is in cardOneSets and x is a variable
    var nDetected = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "set_in" or con.args.len < 2: continue
        let xArg = con.args[0]
        let sArg = con.args[1]
        if sArg.kind != FznIdent: continue
        let sName = sArg.ident
        if sName notin cardOneSets: continue

        # x must be a variable (not constant — constant case already handled by set_in)
        if xArg.kind != FznIdent: continue
        if xArg.ident in tr.paramValues: continue

        # S must be a set variable with bool positions
        if sName notin tr.setVarBoolPositions: continue
        let info = tr.setVarBoolPositions[sName]
        if info.positions.len == 0: continue

        # Mark both constraints as defining
        tr.definingConstraints.incl(ci)  # set_in
        tr.definingConstraints.incl(cardOneSets[sName])  # set_card
        tr.singletonSetChannelDefs.add((
            setName: sName,
            xVarName: xArg.ident,
            cardCI: cardOneSets[sName],
            inCI: ci))
        # Remove S from cardOneSets to prevent double matching
        cardOneSets.del(sName)
        inc nDetected

    if nDetected > 0:
        var totalBools = 0
        for def in tr.singletonSetChannelDefs:
            if def.setName in tr.setVarBoolPositions:
                totalBools += tr.setVarBoolPositions[def.setName].positions.len
        stderr.writeLine(&"[FZN] Detected {nDetected} singleton set channels ({totalBools} bools → channels)")

proc detectValueSupportPattern(tr: var FznTranslator) =
    ## Detects the "neighbours" value-support pattern:
    ## For each cell, a set of bool_clause constraints encoding:
    ##   x[i,j] >= num -> exists(neighbour == num-1)
    ## decomposed as: bool_clause([b_le, b_eq_1, ..., b_eq_k], [])
    ## where b_le <- int_le_reif(cell, num-1, b_le) and b_eq_k <- int_eq_reif(neigh_k, num-1, b_eq_k)
    ##
    ## These are replaced by a single ValueSupport constraint per cell.

    # Step 1: Build reverse maps from bool var name -> defining info
    type
        EqReifInfo = object
            sourceVar: string
            value: int
            ci: int
        LeReifInfo = object
            sourceVar: string
            threshold: int
            ci: int

    var eqReifByBool: Table[string, EqReifInfo]   # b -> (x, v) from int_eq_reif(x, v, b)
    var leReifByBool: Table[string, LeReifInfo]   # b -> (x, t) from int_le_reif(x, t, b)

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 3: continue
        if con.args[2].kind != FznIdent: continue
        let boolVar = con.args[2].ident

        if name == "int_eq_reif":
            # int_eq_reif(x, val, b) :: defines_var(b)
            if con.args[0].kind != FznIdent: continue
            let val = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
            eqReifByBool[boolVar] = EqReifInfo(sourceVar: con.args[0].ident, value: val, ci: ci)
        elif name == "int_le_reif":
            # int_le_reif(x, threshold, b) :: defines_var(b)
            if con.args[0].kind != FznIdent: continue
            let threshold = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
            leReifByBool[boolVar] = LeReifInfo(sourceVar: con.args[0].ident, threshold: threshold, ci: ci)

    # Step 2: Scan each unconsumed bool_clause for the value-support pattern
    type
        ClauseMatch = object
            cellVar: string
            value: int          # the value being constrained (threshold + 1)
            neighbourVars: seq[string]
            boolClauseCI: int
            consumedBools: seq[string]  # bool vars consumed by this clause
            leReifCI: int
            eqReifCIs: seq[int]

    var matches: seq[ClauseMatch]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause" or con.args.len < 2: continue

        # Must have all-positive literals and no negative literals
        if con.args[1].kind == FznArrayLit and con.args[1].elems.len > 0: continue
        if con.args[0].kind != FznArrayLit: continue
        let posLits = con.args[0].elems
        if posLits.len < 2: continue  # need at least escape + one neighbour

        # Classify each literal
        var leCount = 0
        var cellVar = ""
        var threshold = -1
        var leCI = -1
        var neighbourVars: seq[string]
        var eqValue = -1
        var valid = true
        var consumedBools: seq[string]
        var eqCIs: seq[int]

        for lit in posLits:
            if lit.kind != FznIdent:
                valid = false
                break
            let boolName = lit.ident

            if boolName in leReifByBool:
                let info = leReifByBool[boolName]
                leCount += 1
                if leCount > 1:
                    valid = false
                    break
                cellVar = info.sourceVar
                threshold = info.threshold
                leCI = info.ci
                consumedBools.add(boolName)
            elif boolName in eqReifByBool:
                let info = eqReifByBool[boolName]
                if eqValue < 0:
                    eqValue = info.value
                elif info.value != eqValue:
                    valid = false  # inconsistent eq values
                    break
                neighbourVars.add(info.sourceVar)
                eqCIs.add(info.ci)
                consumedBools.add(boolName)
            else:
                valid = false  # unknown literal
                break

        if not valid or leCount != 1 or neighbourVars.len == 0: continue
        # The escape is int_le_reif(cell, threshold, b) meaning cell <= threshold
        # The eq literals check for value = threshold (the predecessor of threshold+1)
        if eqValue != threshold: continue

        matches.add(ClauseMatch(
            cellVar: cellVar,
            value: threshold + 1,  # the cell value that triggers the constraint
            neighbourVars: neighbourVars,
            boolClauseCI: ci,
            consumedBools: consumedBools,
            leReifCI: leCI,
            eqReifCIs: eqCIs))

    if matches.len == 0: return

    # Step 3: Group by cellVar
    var byCellVar: Table[string, seq[ClauseMatch]]
    for m in matches:
        byCellVar.mgetOrPut(m.cellVar, @[]).add(m)

    var nConsumedBoolClauses = 0

    for cellVar, cellMatches in byCellVar.pairs:
        # Sort by value
        var sorted = cellMatches
        sorted.sort(proc(a, b: ClauseMatch): int = cmp(a.value, b.value))

        # Values should form 2..maxVal
        if sorted[0].value != 2: continue
        var maxVal = sorted[^1].value
        if sorted.len != maxVal - 1: continue  # missing values
        var consecutive = true
        for i in 0..<sorted.len:
            if sorted[i].value != i + 2:
                consecutive = false
                break
        if not consecutive: continue

        # Verify neighbour sets are consistent across all values
        # (they should all reference the same set of neighbour variables)
        let refNeighbours = sorted[0].neighbourVars.sorted()
        var consistent = true
        for i in 1..<sorted.len:
            if sorted[i].neighbourVars.sorted() != refNeighbours:
                consistent = false
                break
        if not consistent: continue

        # Create ValueSupportDef — only consume bool_clause CIs, not the reif CIs,
        # because reif constraints may be shared across multiple bool_clauses via CSE
        # (e.g., int_eq_reif(x, v, b) used by both this cell's clause and a neighbour cell's clause)
        var consumedCIs: seq[int]
        for m in sorted:
            if m.boolClauseCI in tr.definingConstraints: continue  # already consumed
            consumedCIs.add(m.boolClauseCI)
        if consumedCIs.len != sorted.len: continue  # some clauses already consumed

        tr.valueSupportDefs.add(ValueSupportDef(
            cellVarName: cellVar,
            neighbourVarNames: sorted[0].neighbourVars,
            maxVal: maxVal,
            consumedCIs: consumedCIs))

        # Mark only bool_clause constraints as consumed
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)

        nConsumedBoolClauses += sorted.len

    if tr.valueSupportDefs.len == 0: return

    # Step 4: Consume orphaned reif constraints whose booleans are ONLY used by consumed bool_clauses.
    # A bool is "orphaned" if no non-consumed constraint (other than its defining reif) references it.

    # Collect all bools from consumed matches and build bool→definingCI map
    var valueSupportBools: HashSet[string]
    var boolDefCI: Table[string, int]  # bool var name → its defining reif CI
    for m in matches:
        if m.boolClauseCI in tr.definingConstraints:
            for b in m.consumedBools:
                valueSupportBools.incl(b)
                if b in eqReifByBool:
                    boolDefCI[b] = eqReifByBool[b].ci
                elif b in leReifByBool:
                    boolDefCI[b] = leReifByBool[b].ci

    # Scan all non-consumed constraints for references to value-support bools
    var boolInUse: HashSet[string]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        for ai in 0..<con.args.len:
            let arg = con.args[ai]
            if arg.kind == FznIdent and arg.ident in valueSupportBools:
                # Skip if this is the bool's own defining constraint
                if ci != boolDefCI.getOrDefault(arg.ident, -1):
                    boolInUse.incl(arg.ident)
            elif arg.kind == FznArrayLit:
                for elem in arg.elems:
                    if elem.kind == FznIdent and elem.ident in valueSupportBools:
                        if ci != boolDefCI.getOrDefault(elem.ident, -1):
                            boolInUse.incl(elem.ident)

    # Consume orphaned bools' defining reif CIs and mark bools as defined (no position creation)
    var nOrphanedReifs = 0
    for b in valueSupportBools:
        if b notin boolInUse and b in boolDefCI:
            let reifCI = boolDefCI[b]
            if reifCI notin tr.definingConstraints:
                tr.definingConstraints.incl(reifCI)
                tr.valueSupportConsumedBools.incl(b)
                inc nOrphanedReifs
            # Mark bool as defined-var so no position is created
            tr.definedVarNames.incl(b)

    stderr.writeLine(&"[FZN] Detected {tr.valueSupportDefs.len} value-support constraints (consumed {nConsumedBoolClauses} bool_clause, {nOrphanedReifs} orphaned reifs)")

proc detectNetFlowPairs*(tr: var FznTranslator) =
    ## Detects EFM / metabolic network patterns: paired variables with opposite-sign
    ## coefficients in int_lin_eq constraints forming a tree-structured constraint graph.
    ##
    ## Pattern:
    ##   - int_lin_eq with all +-1 coefficients, variables in consecutive pairs
    ##   - int_le_reif(1, V, Z) + bool2int(Z, Zint) channeling per variable
    ##   - int_lin_le([1,1], [Zint_in, Zint_out], 1) reversibility per pair
    ##
    ## Reformulation:
    ##   - Replace each (V_in, V_out) pair with net_flow = V_in - V_out
    ##   - Tree-eliminate dependent pairs via channels
    ##   - Channel V_in, V_out, Z_in, Z_out from net_flow

    # Step 1: Find int_lin_eq constraints with paired structure
    type
        PairId = int  # index into pairs array

    # Scan for candidate stoichiometry constraints (int_lin_eq with +-1 coeffs, rhs=0, paired vars)
    var stoichConstraints: seq[int]  # constraint indices
    var stoichCoeffs: seq[seq[int]]
    var stoichVarNames: seq[seq[string]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq":
            continue
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if rhs != 0:
            continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len < 4 or coeffs.len mod 2 != 0:
            continue
        # Check all coefficients are +-1
        var allUnit = true
        for c in coeffs:
            if c != 1 and c != -1:
                allUnit = false
                break
        if not allUnit:
            continue
        # Check variables are all identifiers
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if varElems.len != coeffs.len:
            continue
        var allIdents = true
        var varNames: seq[string]
        for e in varElems:
            if e.kind != FznIdent:
                allIdents = false
                break
            varNames.add(e.ident)
        if not allIdents:
            continue
        # Check paired structure: consecutive pairs with opposite-sign coefficients
        var isPaired = true
        for i in countup(0, coeffs.len - 1, 2):
            if coeffs[i] != -coeffs[i + 1]:
                isPaired = false
                break
        if not isPaired:
            continue
        stoichConstraints.add(ci)
        stoichCoeffs.add(coeffs)
        stoichVarNames.add(varNames)

    if stoichConstraints.len < 10:
        return  # Not enough stoichiometry constraints to be a network

    # Step 2: Build pair map from stoichiometry constraints
    # A "pair" is (V_in, V_out) that always appear with opposite-sign coefficients
    var pairOf: Table[string, PairId]  # variable name → pair index
    var pairInVar: seq[string]   # pair index → V_in name
    var pairOutVar: seq[string]  # pair index → V_out name
    var nPairs = 0

    for si in 0..<stoichConstraints.len:
        let coeffs = stoichCoeffs[si]
        let varNames = stoichVarNames[si]
        for i in countup(0, coeffs.len - 1, 2):
            let v1 = varNames[i]
            let v2 = varNames[i + 1]
            if v1 notin pairOf and v2 notin pairOf:
                # New pair: v1 has coeffs[i], v2 has coeffs[i+1] = -coeffs[i]
                # Convention: "in" has positive coeff in first occurrence
                let pid = nPairs
                if coeffs[i] == 1:
                    pairInVar.add(v1)
                    pairOutVar.add(v2)
                else:
                    pairInVar.add(v2)
                    pairOutVar.add(v1)
                pairOf[v1] = pid
                pairOf[v2] = pid
                inc nPairs
            elif v1 in pairOf and v2 in pairOf:
                # Both already assigned — verify same pair
                if pairOf[v1] != pairOf[v2]:
                    return  # Inconsistent pairing
            else:
                return  # Mixed — one in pair, other not

    if nPairs < 10:
        return

    # Verify all stoichiometry constraints use consistent pairs
    # For each constraint, extract the pair-level representation:
    # which pairs participate and with what sign
    type
        StoichPairTerm = tuple[pairId: PairId, sign: int]  # sign of net_flow in this constraint

    var stoichPairTerms: seq[seq[StoichPairTerm]]
    for si in 0..<stoichConstraints.len:
        let coeffs = stoichCoeffs[si]
        let varNames = stoichVarNames[si]
        var terms: seq[StoichPairTerm]
        for i in countup(0, coeffs.len - 1, 2):
            let v1 = varNames[i]
            let pid = pairOf[v1]
            # net_flow = V_in - V_out
            # If v1 is the "in" var (pairInVar[pid]), then v1 coeff = sign of net_flow
            # If v1 is the "out" var, then v1 coeff = -sign of net_flow
            let sign = if v1 == pairInVar[pid]: coeffs[i] else: -coeffs[i]
            terms.add((pairId: pid, sign: sign))
        stoichPairTerms.add(terms)

    # Step 3: Build bipartite graph (metabolite constraints ↔ pairs) and check tree property
    # metabolite nodes: indexed 0..<stoichConstraints.len
    # pair nodes: indexed 0..<nPairs
    var pairToMetabolites: seq[seq[int]]  # pair → list of metabolite constraint indices (into stoichConstraints)
    pairToMetabolites.setLen(nPairs)
    var metaboliteToPairs: seq[seq[PairId]]
    metaboliteToPairs.setLen(stoichConstraints.len)

    for si in 0..<stoichConstraints.len:
        for term in stoichPairTerms[si]:
            pairToMetabolites[term.pairId].add(si)
            metaboliteToPairs[si].add(term.pairId)

    # Check tree property: edges = metabolites + pairs - 1
    var totalEdges = 0
    for si in 0..<stoichConstraints.len:
        totalEdges += metaboliteToPairs[si].len
    let totalNodes = stoichConstraints.len + nPairs
    if totalEdges != totalNodes - 1:
        stderr.writeLine(&"[FZN] Net flow: not a tree (edges={totalEdges}, nodes={totalNodes})")
        return

    # Verify connectivity via BFS on pairs
    var visited = initPackedSet[int]()
    var queue: seq[int]
    queue.add(0)
    visited.incl(0)
    var head = 0
    while head < queue.len:
        let pid = queue[head]
        inc head
        for si in pairToMetabolites[pid]:
            for otherPid in metaboliteToPairs[si]:
                if otherPid notin visited:
                    visited.incl(otherPid)
                    queue.add(otherPid)
    if visited.len != nPairs:
        stderr.writeLine(&"[FZN] Net flow: not connected ({visited.len}/{nPairs} pairs reachable)")
        return

    # Step 4: Tree peeling — classify pairs as free vs dependent
    # Start from leaf PAIRS (degree 1 = appear in only 1 metabolite constraint).
    # When a leaf pair is eliminated from a metabolite, that metabolite may become
    # a "leaf metabolite" (only 1 remaining pair), making that pair dependent.
    var pairDegree = newSeq[int](nPairs)
    for pid in 0..<nPairs:
        pairDegree[pid] = pairToMetabolites[pid].len
    var metDegree = newSeq[int](stoichConstraints.len)
    for si in 0..<stoichConstraints.len:
        metDegree[si] = metaboliteToPairs[si].len

    var dependentPairs: seq[PairId]  # in elimination order (leaves first)
    var dependentMetabolite: seq[int]  # which metabolite constraint determines this pair
    var isDependentPair = newSeq[bool](nPairs)
    var isDependentMet = newSeq[bool](stoichConstraints.len)

    # Seed queue with degree-1 pairs (leaf pairs in the bipartite tree)
    var pairQueue: seq[PairId]
    for pid in 0..<nPairs:
        if pairDegree[pid] == 1:
            pairQueue.add(pid)

    var pqHead = 0
    while pqHead < pairQueue.len:
        let pid = pairQueue[pqHead]
        inc pqHead
        if isDependentPair[pid]:
            continue
        # Find the single remaining uneliminated metabolite for this pair
        var activeMet = -1
        for si in pairToMetabolites[pid]:
            if not isDependentMet[si]:
                activeMet = si
                break
        if activeMet < 0:
            continue
        # This pair is determined by this metabolite constraint
        isDependentPair[pid] = true
        isDependentMet[activeMet] = true
        dependentPairs.add(pid)
        dependentMetabolite.add(activeMet)
        # When we eliminate this pair from the metabolite, reduce degree of
        # all OTHER pairs that share this metabolite. Also reduce degree of
        # pairs that shared OTHER metabolites with this pair.
        # Actually: in a bipartite tree, eliminating pair pid removes it from
        # all its metabolite connections. For the metabolite we just consumed (activeMet),
        # the other pairs in activeMet lose a neighbor — but that's the metabolite being
        # consumed, not the pair. Let me think again...
        #
        # Tree peeling: we remove the leaf pair pid + its single metabolite edge.
        # This "consumes" metabolite activeMet. All OTHER pairs connected to activeMet
        # now have one fewer metabolite neighbor. If any of them drops to degree 0,
        # that's fine (they become free). If they drop to degree 1, they become leaf pairs.
        for otherPid in metaboliteToPairs[activeMet]:
            if otherPid != pid and not isDependentPair[otherPid]:
                dec pairDegree[otherPid]
                if pairDegree[otherPid] == 1:
                    pairQueue.add(otherPid)

    var freePairs: seq[PairId]
    for pid in 0..<nPairs:
        if not isDependentPair[pid]:
            freePairs.add(pid)

    # In a tree with E edges, M metabolite nodes and P pair nodes: E = M + P - 1.
    # Peeling eliminates exactly M pairs (one per metabolite), leaving P - M free.
    if dependentPairs.len != stoichConstraints.len:
        stderr.writeLine(&"[FZN] Net flow: tree peel incomplete ({dependentPairs.len} deps vs {stoichConstraints.len} constraints)")
        return

    stderr.writeLine(&"[FZN] Detected {nPairs} net flow pairs: {freePairs.len} free, {dependentPairs.len} dependent")

    # Step 5: Build dependency expressions for dependent pairs
    # Each dependent pair d is determined by metabolite constraint si:
    #   sum_over_pairs(sign[p] * net_flow[p]) = 0
    #   → sign[d] * net_flow[d] = -sum_over_other_pairs(sign[p] * net_flow[p])
    #   → net_flow[d] = sign[d] * (-sum_over_other_pairs(sign[p] * net_flow[p]))
    # = -sign[d] * sum_over_other_pairs(sign[p] * net_flow[p])
    # Process in elimination order so dependencies are resolved
    type
        DepTerm = tuple[pairId: PairId, coeff: int]

    var depTerms: seq[seq[DepTerm]]  # for each dependent pair, list of (other pair, coeff)

    for di in 0..<dependentPairs.len:
        let depPid = dependentPairs[di]
        let si = dependentMetabolite[di]
        var depSign = 0
        var terms: seq[DepTerm]
        for term in stoichPairTerms[si]:
            if term.pairId == depPid:
                depSign = term.sign
            else:
                terms.add((pairId: term.pairId, coeff: term.sign))
        # net_flow[d] = (-1/depSign) * sum(coeff[p] * net_flow[p])
        # Since depSign is +-1, -1/depSign = -depSign
        var finalTerms: seq[DepTerm]
        for t in terms:
            finalTerms.add((pairId: t.pairId, coeff: -depSign * t.coeff))
        depTerms.add(finalTerms)

    # Step 6: Find reversibility constraints: int_lin_le([1,1], [Zint_in, Zint_out], 1)
    # These are redundant after net_flow reformulation (only one direction active by construction)
    # Build Zint → V mapping first via int_le_reif + bool2int chains
    var vToZBool: Table[string, string]
    var zToZint: Table[string, string]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "int_le_reif" and con.args.len >= 3:
            if con.args[1].kind == FznIdent and con.args[2].kind == FznIdent:
                let vName = con.args[1].ident
                let zName = con.args[2].ident
                if vName in pairOf:
                    vToZBool[vName] = zName
        elif name == "bool2int" and con.args.len >= 2:
            if con.args[0].kind == FznIdent and con.args[1].kind == FznIdent:
                zToZint[con.args[0].ident] = con.args[1].ident

    # Build Zint name → pair index mapping for fast reversibility lookup
    var zintToPair: Table[string, PairId]
    for pid in 0..<nPairs:
        for v in [pairInVar[pid], pairOutVar[pid]]:
            if v in vToZBool:
                let z = vToZBool[v]
                if z in zToZint:
                    zintToPair[zToZint[z]] = pid

    var revConstraints: seq[int]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le":
            continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len != 2 or coeffs[0] != 1 or coeffs[1] != 1:
            continue
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if rhs != 1:
            continue
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if varElems.len != 2 or varElems[0].kind != FznIdent or varElems[1].kind != FznIdent:
            continue
        let zint1 = varElems[0].ident
        let zint2 = varElems[1].ident
        if zint1 in zintToPair and zint2 in zintToPair:
            if zintToPair[zint1] == zintToPair[zint2]:
                revConstraints.add(ci)

    # Step 7: Register everything
    # V_in, V_out are channel variables (get positions, but computed from net_flow)
    # Z/Zint handling is left to existing detectReifChannels() which chains from V positions
    # Stoichiometry + reversibility constraints are consumed

    # Store pair info for later use
    # Reverse dependent pairs: tree peeling gives leaves-first (outer-to-inner),
    # but expression building needs inner-to-outer (dependencies resolved first).
    tr.netFlowPairInVar = pairInVar
    tr.netFlowPairOutVar = pairOutVar
    tr.netFlowFreePairs = freePairs
    var revDependentPairs = dependentPairs
    var revDepTerms = depTerms
    reverse(revDependentPairs)
    reverse(revDepTerms)
    tr.netFlowDependentPairs = revDependentPairs
    tr.netFlowDepTerms = revDepTerms

    # Mark all stoichiometry constraints as defining (skip during translation)
    for ci in stoichConstraints:
        tr.definingConstraints.incl(ci)

    # Mark reversibility constraints as defining (redundant after reform)
    for ci in revConstraints:
        tr.definingConstraints.incl(ci)

    # Mark V_in, V_out as channel variables — they get positions but won't be searched
    # (Existing int_le_reif + bool2int detection will chain Z/Zint from V positions)
    for pid in 0..<nPairs:
        tr.channelVarNames.incl(pairInVar[pid])
        tr.channelVarNames.incl(pairOutVar[pid])

    # Determine the flux domain upper bound (typically 50)
    tr.netFlowDomainBound = 0
    for pid in 0..<nPairs:
        let dom = tr.lookupVarDomain(pairInVar[pid])
        if dom.len > 0:
            tr.netFlowDomainBound = max(tr.netFlowDomainBound, dom[^1])

    stderr.writeLine(&"[FZN] Net flow pairs: consumed {stoichConstraints.len} stoichiometry + {revConstraints.len} reversibility constraints")


proc detectSharedIndexConsolidation(tr: var FznTranslator) =
    ## Detects groups of element channel constraints that share the same index variable
    ## and all use constant arrays. Consolidates each group into a single table constraint
    ## with functional dependency channels, reducing the number of channel bindings.
    ##
    ## Pattern:
    ##   array_int_element(idx, constArr1, out1) :: defines_var(out1)
    ##   array_int_element(idx, constArr2, out2) :: defines_var(out2)
    ##   ...
    ## → table constraint over (idx, out1, out2, ...) + functional dep channels

    # Group channelConstraints by index variable
    type ElementGroup = object
        indexVar: string
        entries: seq[tuple[ci: int, outputVar: string, constArray: seq[int]]]

    var groupsByIndex = initTable[string, ElementGroup]()

    for ci, defName in tr.channelConstraints:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name notin ["array_int_element", "array_int_element_nonshifted",
                        "array_bool_element"]:
            continue
        if con.args[0].kind != FznIdent: continue
        let indexVar = con.args[0].ident
        # Try to resolve the array as constant
        let constArray = try: tr.resolveIntArray(con.args[1])
                         except ValueError, KeyError: continue
        if indexVar notin groupsByIndex:
            groupsByIndex[indexVar] = ElementGroup(indexVar: indexVar, entries: @[])
        groupsByIndex[indexVar].entries.add((ci: ci, outputVar: defName, constArray: constArray))

    var nConsolidated = 0
    var nBindingsRemoved = 0

    for indexVar, group in groupsByIndex:
        if group.entries.len < 2: continue

        # All entries share the same index variable and have constant arrays
        # Verify the index variable has a position
        if indexVar notin tr.varPositions: continue
        let idxPos = tr.varPositions[indexVar]

        # Verify all output variables have positions
        var allHavePos = true
        for entry in group.entries:
            if entry.outputVar notin tr.varPositions:
                allHavePos = false
                break
        if not allHavePos: continue

        # All arrays must have the same length
        let arrLen = group.entries[0].constArray.len
        if not group.entries.allIt(it.constArray.len == arrLen): continue

        # Get index variable domain to determine valid index range
        let idxDomain = tr.lookupVarDomain(indexVar)
        if idxDomain.len == 0: continue

        # Build tuples: (index_val, out1_val, out2_val, ...)
        # FlatZinc uses 1-based indexing for element constraints
        var positions: seq[int] = @[idxPos]
        for entry in group.entries:
            positions.add(tr.varPositions[entry.outputVar])

        var tuples: seq[seq[int]]
        for idxVal in idxDomain:
            let arrIdx = idxVal - 1  # FZN 1-based to 0-based
            if arrIdx < 0 or arrIdx >= arrLen: continue
            var row = @[idxVal]
            for entry in group.entries:
                row.add(entry.constArray[arrIdx])
            tuples.add(row)

        if tuples.len == 0: continue

        # Try functional dependency detection (index column is the key)
        # This will create channel bindings for the output columns
        if tr.tryTableFunctionalDep(positions, tuples):
            # Success: remove individual channel constraint entries
            for entry in group.entries:
                tr.channelConstraints.del(entry.ci)
                # channelVarNames and channelPositions are already set
            nBindingsRemoved += group.entries.len
            inc nConsolidated

    if nConsolidated > 0:
        stderr.writeLine(&"[FZN] Consolidated {nConsolidated} shared-index element groups ({nBindingsRemoved} bindings → {nConsolidated} tables)")



proc detectConstantElementComposition*(tr: var FznTranslator) =
    ## For each element channel with a constant array and simple ident index var,
    ## stores (indexVar, constArray) in constElementSources so downstream channel
    ## bindings can compose directly from the upstream var instead of through the channel.
    ##
    ## This enables eliminating intermediate channel variables from the penalty graph.
    ## When a constraint (e.g., int_eq_reif, element) uses a var that is itself a const-element
    ## channel, the binding composes through to the original search variable, skipping the
    ## intermediate channel. Each composition logs "[FZN] Composed ..." to stderr.

    # Direct element channels with constant arrays
    for ci, chanName in tr.channelConstraints:
        let con = tr.model.constraints[ci]
        let cname = stripSolverPrefix(con.name)
        if cname notin ["array_int_element", "array_int_element_nonshifted", "array_bool_element"]:
            continue
        if con.args[0].kind != FznIdent:
            continue
        let indexVarName = con.args[0].ident
        # Only vars that have actual positions (search or channel) — skip eliminated vars
        if indexVarName in tr.definedVarNames and indexVarName notin tr.varPositions:
            continue
        try:
            let constArray = tr.resolveIntArray(con.args[1])
            tr.constElementSources[chanName] = (indexVar: indexVarName, constArray: constArray)
        except ValueError, KeyError:
            discard

    # Propagate to aliases (multiple element vars with same index+array share the source)
    for aliasName, originalName in tr.elementChannelAliases:
        if originalName in tr.constElementSources:
            tr.constElementSources[aliasName] = tr.constElementSources[originalName]

    if tr.constElementSources.len > 0:
        stderr.writeLine(&"[FZN] ConstElementComposition: {tr.constElementSources.len} element channels eligible for downstream composition")


proc detectAtMostPairCliques(tr: var FznTranslator) =
    ## Detects pairwise atMost-1 constraints on binary variables that form cliques,
    ## and merges each clique into a single N-variable atMost constraint.
    ## Pattern: int_lin_le([1,1], [x,y], 1) where x,y are binary {0,1} variables.
    ## This is common when MiniZinc decomposes "at most one" constraints into O(n^2) pairs.

    # Step 1: Collect all pairwise atMost-1 constraints on binary variables
    type PairInfo = object
        ci: int
        varA, varB: string  # Canonical order: varA < varB

    var pairs: seq[PairInfo]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        if ci in tr.redundantOrderings:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le":
            continue

        # Resolve coefficients and rhs
        let coeffs = tr.resolveIntArray(con.args[0])
        if coeffs.len != 2 or coeffs[0] != 1 or coeffs[1] != 1:
            continue
        let rhs = tr.resolveIntArg(con.args[2])
        if rhs != 1:
            continue

        # Extract variable names
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if varElems.len != 2:
            continue
        if varElems[0].kind != FznIdent or varElems[1].kind != FznIdent:
            continue
        let nameA = varElems[0].ident
        let nameB = varElems[1].ident

        # Skip parameters, defined vars, channel vars
        if nameA in tr.paramValues or nameB in tr.paramValues:
            continue
        if nameA in tr.definedVarNames or nameB in tr.definedVarNames:
            continue
        if nameA in tr.channelVarNames or nameB in tr.channelVarNames:
            continue

        # Check both variables are binary {0,1}
        var domA = tr.lookupVarDomain(nameA)
        var domB = tr.lookupVarDomain(nameB)
        # Apply presolve domain tightening
        if nameA in tr.presolveDomains:
            domA = tr.presolveDomains[nameA]
        if nameB in tr.presolveDomains:
            domB = tr.presolveDomains[nameB]
        # Skip if either variable is fixed (singleton domain — constraint is tautological)
        if domA.len <= 1 or domB.len <= 1:
            continue
        if domA != @[0, 1] or domB != @[0, 1]:
            continue

        # Canonical ordering
        let (canonA, canonB) = if nameA < nameB: (nameA, nameB) else: (nameB, nameA)
        pairs.add(PairInfo(ci: ci, varA: canonA, varB: canonB))

    if pairs.len < 3:
        # Need at least 3 pairs to form a clique of size 3
        return

    # Step 2: Build adjacency graph
    var adjacency: Table[string, Table[string, int]]  # var -> {partner -> pairIndex}
    for idx, pi in pairs:
        if pi.varA notin adjacency:
            adjacency[pi.varA] = initTable[string, int]()
        adjacency[pi.varA][pi.varB] = idx

        if pi.varB notin adjacency:
            adjacency[pi.varB] = initTable[string, int]()
        adjacency[pi.varB][pi.varA] = idx

    # Step 3: Find connected components via BFS, then detect cliques per component.
    # Processing by component allows us to find ALL cliques in the graph rather than
    # being limited by a global variable-exclusion set.
    var visited: HashSet[string]
    var components: seq[seq[string]]

    for startVar in adjacency.keys:
        if startVar in visited:
            continue
        var component: seq[string]
        var queue = @[startVar]
        visited.incl(startVar)
        while queue.len > 0:
            let v = queue[0]
            queue.delete(0)
            component.add(v)
            for neighbor in adjacency[v].keys:
                if neighbor notin visited:
                    visited.incl(neighbor)
                    queue.add(neighbor)
        components.add(component)

    # Step 4: For each component, detect cliques
    var totalConsumed = 0
    var totalVars = 0

    for component in components:
        if component.len < 3:
            continue

        # Count edges in this component
        var edgeCount = 0
        for v in component:
            for partner in adjacency[v].keys:
                if partner in adjacency and partner > v:
                    # Only count each edge once (canonical direction)
                    if partner in adjacency[v]:
                        inc edgeCount
        let maxEdges = component.len * (component.len - 1) div 2

        if edgeCount == maxEdges:
            # Perfect clique — emit single N-var atMost-1 and consume all pairs
            tr.atMostPairCliques.add(component)
            totalVars += component.len
            for i in 0..<component.len:
                for j in (i+1)..<component.len:
                    let a = component[i]
                    let b = component[j]
                    let canonA = if a < b: a else: b
                    let canonB = if a < b: b else: a
                    if canonB in adjacency.getOrDefault(canonA):
                        let pairIdx = adjacency[canonA][canonB]
                        tr.definingConstraints.incl(pairs[pairIdx].ci)
                        inc totalConsumed
        else:
            # Non-perfect component: greedy clique decomposition within the component
            var assigned: HashSet[string]

            # Sort by degree within component (highest first)
            var compByDegree: seq[(int, string)]
            for v in component:
                var degInComp = 0
                for partner in adjacency[v].keys:
                    # Adjacency already only has binary-var pairs, all are in some component
                    inc degInComp
                compByDegree.add((degInComp, v))
            compByDegree.sort(proc(a, b: (int, string)): int = -cmp(a[0], b[0]))

            for (_, startVar) in compByDegree:
                if startVar in assigned:
                    continue

                # Build clique starting from startVar
                var clique = @[startVar]
                var candidates: seq[string]
                for partner in adjacency[startVar].keys:
                    if partner notin assigned:
                        candidates.add(partner)

                # Sort candidates by degree (descending) to prefer high-connectivity nodes
                candidates.sort(proc(a, b: string): int =
                    -cmp(adjacency[a].len, adjacency[b].len))

                # Greedily add candidates connected to all current clique members
                for candidate in candidates:
                    var connectedToAll = true
                    for member in clique:
                        if candidate notin adjacency.getOrDefault(member):
                            connectedToAll = false
                            break
                    if connectedToAll:
                        clique.add(candidate)

                if clique.len < 3:
                    # Only merge cliques of size >= 3
                    continue

                # Collect pair indices and mark consumed
                for i in 0..<clique.len:
                    for j in (i+1)..<clique.len:
                        let a = clique[i]
                        let b = clique[j]
                        if b in adjacency.getOrDefault(a):
                            let pairIdx = adjacency[a][b]
                            tr.definingConstraints.incl(pairs[pairIdx].ci)
                            inc totalConsumed

                for member in clique:
                    assigned.incl(member)
                tr.atMostPairCliques.add(clique)
                totalVars += clique.len

    if tr.atMostPairCliques.len > 0:
        stderr.writeLine(&"[FZN] AtMost-1 clique merging: {tr.atMostPairCliques.len} cliques " &
                          &"({totalVars} vars), {totalConsumed} pairwise constraints consumed")



proc tightenObjectiveBoundsKnapsack(tr: var FznTranslator) =
    ## Tightens objective bounds using knapsack LP relaxation and at-most-1
    ## clique covering.
    ##
    ## Handles two patterns:
    ## 1. Pure binary: objective is sum over binary vars with knapsack constraints
    ##    → LP relaxation (fractional knapsack) gives tight bound.
    ## 2. Mixed binary/non-binary: objective has binary AND non-binary vars
    ##    → Separate into binary part (bounded by at-most-1 cliques) and
    ##      non-binary part (bounded by domain bounds).

    if tr.model.solve.kind notin {Minimize, Maximize}: return
    let isMaximize = tr.model.solve.kind == Maximize

    # Step 1: Find the int_lin_eq that defines the objective variable.
    # Pattern: int_lin_eq(coeffs, vars, rhs) :: defines_var(objective)
    # where one var is the objective with coefficient -1 (or 1).
    let objVarName = if tr.model.solve.objective != nil and
                        tr.model.solve.objective.kind == FznIdent:
                       tr.model.solve.objective.ident
                     else: ""
    if objVarName == "": return

    var objCoeffs: Table[string, int]  # variable name -> coefficient in objective
    var objConstant = 0
    var objFound = false

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue

        let coeffsArr = tr.resolveIntArray(con.args[0])
        let varsArr = tr.resolveVarArrayElems(con.args[1])
        let rhs = tr.resolveIntArg(con.args[2])
        if coeffsArr.len != varsArr.len: continue

        # Find the objective variable in this constraint
        var objIdx = -1
        for vi, v in varsArr:
            if v.kind == FznIdent and v.ident == objVarName:
                objIdx = vi
                break
        if objIdx < 0: continue

        let objCoeff = coeffsArr[objIdx]
        if abs(objCoeff) != 1: continue

        # obj = (rhs - sum(other_coeffs * vars)) / objCoeff
        for vi, v in varsArr:
            if vi == objIdx: continue
            if v.kind != FznIdent: continue
            let c = if objCoeff == 1: -coeffsArr[vi] else: coeffsArr[vi]
            objCoeffs[v.ident] = c
        objConstant = if objCoeff == 1: rhs else: -rhs
        objFound = true
        break

    if not objFound or objCoeffs.len == 0: return

    # Step 2: Classify objective variables as binary or non-binary.
    var binaryCoeffs: Table[string, int]
    var nonBinaryCoeffs: Table[string, int]
    for varName, coeff in objCoeffs:
        var dom: seq[int]
        if varName in tr.presolveDomains:
            dom = tr.presolveDomains[varName]
        else:
            dom = tr.lookupVarDomain(varName)
        if dom.len >= 1 and dom.len <= 2 and dom[0] >= 0 and dom[^1] <= 1:
            binaryCoeffs[varName] = coeff
        else:
            nonBinaryCoeffs[varName] = coeff

    # --- Path A: Pure binary → knapsack LP relaxation (original logic) ---
    if nonBinaryCoeffs.len == 0 and binaryCoeffs.len > 0:
        # Find knapsack constraints over the binary objective variables
        type KnapsackInfo = object
            weights: Table[string, int]
            capacity: int

        var knapsacks: seq[KnapsackInfo]
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name != "int_lin_le": continue
            if con.args.len < 3: continue

            let coeffsArr = tr.resolveIntArray(con.args[0])
            let varsArr = tr.resolveVarArrayElems(con.args[1])
            let rhs = tr.resolveIntArg(con.args[2])
            if coeffsArr.len != varsArr.len: continue

            var valid = true
            var ks: KnapsackInfo
            ks.capacity = rhs

            for vi, v in varsArr:
                if v.kind != FznIdent:
                    valid = false; break
                if coeffsArr[vi] <= 0:
                    valid = false; break
                if v.ident notin binaryCoeffs:
                    valid = false; break
                ks.weights[v.ident] = coeffsArr[vi]
            if not valid or ks.weights.len < 3 or ks.capacity <= 0: continue
            knapsacks.add(ks)

        for ks in knapsacks:
            type Item = tuple[ratio: float, profit, weight: int]
            var items: seq[Item]
            for varName, weight in ks.weights:
                let profit = binaryCoeffs[varName]
                items.add((ratio: float(profit) / float(weight), profit: profit, weight: weight))

            if items.len == 0: continue

            if isMaximize:
                items.sort(proc(a, b: Item): int =
                    if b.ratio > a.ratio: 1
                    elif b.ratio < a.ratio: -1
                    else: 0
                )
                var totalWeight = 0
                var totalProfit = 0
                var lpBound = 0.0
                var allFit = true
                for item in items:
                    if item.profit <= 0: continue
                    if totalWeight + item.weight <= ks.capacity:
                        totalWeight += item.weight
                        totalProfit += item.profit
                    else:
                        let remaining = ks.capacity - totalWeight
                        lpBound = float(totalProfit) + float(item.profit) * float(remaining) / float(item.weight)
                        allFit = false
                        break
                if allFit:
                    lpBound = float(totalProfit)

                var nonKsContrib = 0
                for varName, coeff in binaryCoeffs:
                    if varName notin ks.weights:
                        nonKsContrib += max(0, coeff)

                let upperBound = int(lpBound) + nonKsContrib + objConstant
                if upperBound < tr.objectiveHiBound:
                    stderr.writeLine(&"[FZN] Knapsack LP relaxation tightened objective upper bound: {tr.objectiveHiBound} → {upperBound}")
                    tr.objectiveHiBound = upperBound
            # Minimize: skip for now

    # --- Path B: Mixed binary/non-binary → at-most-1 clique covering bound ---
    if binaryCoeffs.len > 0:
        # Collect at-most-1 constraints over binary objective variables from:
        # 1. Explicit int_lin_le([1,1,...,1], [vars], 1) in the FZN model
        # 2. Detected pairwise cliques (atMostPairCliques)
        type AtMost1Group = seq[string]  # variable names in the at-most-1 set
        var atMost1Groups: seq[AtMost1Group]

        # Source 1: Explicit int_lin_le with all-1 coefficients and rhs=1
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name != "int_lin_le": continue
            if con.args.len < 3: continue

            let coeffsArr = tr.resolveIntArray(con.args[0])
            if coeffsArr.len < 2: continue
            let rhs = tr.resolveIntArg(con.args[2])
            if rhs != 1: continue
            var allOnes = true
            for c in coeffsArr:
                if c != 1: allOnes = false; break
            if not allOnes: continue

            let varsArr = tr.resolveVarArrayElems(con.args[1])
            if varsArr.len != coeffsArr.len: continue

            var group: AtMost1Group
            var allBinaryObj = true
            for v in varsArr:
                if v.kind != FznIdent or v.ident notin binaryCoeffs:
                    allBinaryObj = false; break
                group.add(v.ident)
            if allBinaryObj and group.len >= 2:
                atMost1Groups.add(group)

        # Source 2: Detected pairwise cliques
        for clique in tr.atMostPairCliques:
            var group: AtMost1Group
            var allBinaryObj = true
            for varName in clique:
                if varName notin binaryCoeffs:
                    allBinaryObj = false; break
                group.add(varName)
            if allBinaryObj and group.len >= 2:
                atMost1Groups.add(group)

        if atMost1Groups.len == 0: return

        # Compute bound using greedy clique covering:
        # For each at-most-1 group, at most 1 variable can be 1, contributing
        # at most max(coeff_i) to the objective. Variables covered by any group
        # are bounded; uncovered variables contribute individually.
        var coveredVars: HashSet[string]
        var groupContrib = 0  # contribution from covered groups

        if isMaximize:
            # Sort groups by size descending (larger groups first to avoid
            # suboptimal partial covering), then by max positive coeff descending.
            var groupsWithMax: seq[(int, int, int)]  # (size, maxCoeff, index)
            for gi, group in atMost1Groups:
                var maxC = low(int)
                for varName in group:
                    maxC = max(maxC, binaryCoeffs[varName])
                groupsWithMax.add((group.len, maxC, gi))
            groupsWithMax.sort(proc(a, b: (int, int, int)): int =
                result = -cmp(a[0], b[0])  # larger groups first
                if result == 0:
                    result = -cmp(a[1], b[1])  # then higher max coeff
            )

            for (_, maxC, gi) in groupsWithMax:
                let group = atMost1Groups[gi]
                # Check if this group covers any new variable
                var hasNew = false
                for varName in group:
                    if varName notin coveredVars:
                        hasNew = true; break
                if not hasNew: continue

                # Find max coeff among UNCOVERED variables in this group
                var bestCoeff = low(int)
                for varName in group:
                    if varName notin coveredVars:
                        bestCoeff = max(bestCoeff, binaryCoeffs[varName])
                if bestCoeff > 0:
                    groupContrib += bestCoeff

                for varName in group:
                    coveredVars.incl(varName)

            # Uncovered binary vars: each can contribute max(0, coeff)
            var uncoveredContrib = 0
            for varName, coeff in binaryCoeffs:
                if varName notin coveredVars:
                    uncoveredContrib += max(0, coeff)

            # Non-binary vars: use domain bounds for best case
            var nonBinaryContrib = 0
            for varName, coeff in nonBinaryCoeffs:
                var dom: seq[int]
                if varName in tr.presolveDomains:
                    dom = tr.presolveDomains[varName]
                else:
                    dom = tr.lookupVarDomain(varName)
                if dom.len == 0: continue
                # For maximize: positive coeff wants max domain value, negative wants min
                if coeff > 0:
                    nonBinaryContrib += coeff * dom[^1]
                elif coeff < 0:
                    nonBinaryContrib += coeff * dom[0]

            let upperBound = groupContrib + uncoveredContrib + nonBinaryContrib + objConstant
            if upperBound < tr.objectiveHiBound:
                stderr.writeLine(&"[FZN] At-most-1 clique covering tightened objective upper bound: {tr.objectiveHiBound} → {upperBound}")
                tr.objectiveHiBound = upperBound

        else:  # Minimize
            # Symmetric: for each at-most-1 group, at least max(1, #positiveCoeffs) contribute
            # Minimum contribution per group = min(coeff_i) if all must contribute, else 0
            # For now: just use domain bounds for non-binary part
            var nonBinaryContrib = 0
            for varName, coeff in nonBinaryCoeffs:
                var dom: seq[int]
                if varName in tr.presolveDomains:
                    dom = tr.presolveDomains[varName]
                else:
                    dom = tr.lookupVarDomain(varName)
                if dom.len == 0: continue
                if coeff > 0:
                    nonBinaryContrib += coeff * dom[0]
                elif coeff < 0:
                    nonBinaryContrib += coeff * dom[^1]

            # Binary vars contribute at least 0 (they can all be 0)
            # but some may be fixed to 1 — their contribution is the coeff
            var fixedBinaryContrib = 0
            for varName, coeff in binaryCoeffs:
                var dom: seq[int]
                if varName in tr.presolveDomains:
                    dom = tr.presolveDomains[varName]
                else:
                    dom = tr.lookupVarDomain(varName)
                if dom.len == 1 and dom[0] == 1:
                    fixedBinaryContrib += coeff

            let lowerBound = fixedBinaryContrib + nonBinaryContrib + objConstant
            if lowerBound > tr.objectiveLoBound:
                stderr.writeLine(&"[FZN] At-most-1 clique covering tightened objective lower bound: {tr.objectiveLoBound} → {lowerBound}")
                tr.objectiveLoBound = lowerBound

proc detectCrossingCountMaxPattern*(tr: var FznTranslator) =
    ## Detect crossing count max pattern:
    ##   array_int_maximum(M, [M_1,...,M_k])
    ## where each M_i = sum of "betweenness" indicators:
    ##   int_lin_eq([1,...,1,-1], [ind_vars..., M_i], 0)
    ## each indicator from:
    ##   bool2int(b, ind)  →  array_bool_and([b1, b2], b)  →  two int_lin_le_reif
    ## The two int_lin_le_reif encode: x_a < x_i AND x_i < x_b (cable crossing).
    ##
    ## Replaces the entire decomposition with a single CrossingCountMaxChannelBinding.

    # Step 1: Index defines_var constraints by defined variable name
    # Note: int_lin_eq constraints may already be consumed by collectDefinedVars,
    # so we index ALL constraints (not just unconsumed ones) for chain tracing.
    var bool2intByDef = initTable[string, int]()        # defined int var → constraint index
    var boolAndByDef = initTable[string, int]()          # defined bool var → constraint index
    var linLeReifByDef = initTable[string, int]()        # defined bool var → constraint index
    var linEqByDef = initTable[string, int]()            # defined int var → constraint index

    for ci in 0..<tr.model.constraints.len:
        let con = tr.model.constraints[ci]
        if not con.hasAnnotation("defines_var"): continue
        let name = stripSolverPrefix(con.name)
        let defVar = con.getAnnotation("defines_var").args[0]
        if defVar.kind != FznIdent: continue
        let defName = defVar.ident

        case name
        of "bool2int":
            if ci notin tr.definingConstraints:
                bool2intByDef[defName] = ci
        of "array_bool_and":
            if ci notin tr.definingConstraints:
                boolAndByDef[defName] = ci
        of "int_lin_le_reif":
            if ci notin tr.definingConstraints:
                linLeReifByDef[defName] = ci
        of "int_lin_eq":
            # Always index — these are consumed by collectDefinedVars but we need to trace through them
            linEqByDef[defName] = ci
        else: discard

    # Step 2: Find array_int_maximum constraints that define channel vars
    for mmDef in tr.minMaxChannelDefs:
        if mmDef.isMin: continue  # Only interested in maximum
        let ci = mmDef.ci
        # Don't check definingConstraints — collectDefinedVars already consumed these
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "array_int_maximum": continue
        if con.args.len < 2: continue

        # Get the array of M_i variables
        let arrArg = con.args[1]
        if arrArg.kind != FznArrayLit and arrArg.kind != FznIdent: continue

        var miNames: seq[string]
        if arrArg.kind == FznArrayLit:
            for elem in arrArg.elems:
                if elem.kind != FznIdent: miNames = @[]; break
                miNames.add(elem.ident)
        else:
            # Named array — resolve element names from variable declarations
            for vd in tr.model.variables:
                if vd.name == arrArg.ident and vd.value != nil and vd.value.kind == FznArrayLit:
                    for elem in vd.value.elems:
                        if elem.kind != FznIdent: miNames = @[]; break
                        miNames.add(elem.ident)
                    break
            if miNames.len == 0 and arrArg.ident in tr.arrayElementNames:
                miNames = tr.arrayElementNames[arrArg.ident]

        if miNames.len == 0: continue

        # Step 3: For each M_i, trace the chain: int_lin_eq → bool2int → array_bool_and → int_lin_le_reif pairs
        # Collect cable pairs: (pos_a, pos_b) where a < i < b is the betweenness test
        var allCablePairs: HashSet[tuple[a, b: string]]  # unordered cable var name pairs
        var consumedConstraints: seq[int]
        var consumedVarNames: seq[string]
        var patternOk = true
        let k = miNames.len  # Number of positions (domain size)

        for miName in miNames:
            if miName notin linEqByDef:
                patternOk = false; break

            let eqCi = linEqByDef[miName]
            let eqCon = tr.model.constraints[eqCi]
            # Expect: int_lin_eq(coeffs, vars, 0) with all coeffs = 1 except last = -1
            if eqCon.args.len < 3: patternOk = false; break
            var coeffs: seq[int]
            try: coeffs = tr.resolveIntArray(eqCon.args[0])
            except: patternOk = false
            if not patternOk: break
            var rhs: int
            try: rhs = tr.resolveIntArg(eqCon.args[2])
            except: patternOk = false
            if not patternOk: break
            if rhs != 0: patternOk = false; break

            # Last coefficient should be -1 (defines M_i), rest should be 1 (indicators)
            if coeffs.len < 2: patternOk = false; break
            if coeffs[^1] != -1: patternOk = false; break
            for j in 0..<coeffs.len - 1:
                if coeffs[j] != 1: patternOk = false; break
            if not patternOk: break

            let varsArg = eqCon.args[1]
            if varsArg.kind != FznArrayLit: patternOk = false; break
            if varsArg.elems.len != coeffs.len: patternOk = false; break

            var localConsumed: seq[int]
            var localVarNames: seq[string]
            localConsumed.add(eqCi)
            localVarNames.add(miName)

            # Trace each indicator (all elements except the last which is M_i)
            for j in 0..<varsArg.elems.len - 1:
                let indElem = varsArg.elems[j]
                if indElem.kind != FznIdent:
                    patternOk = false; break
                let indName = indElem.ident

                # bool2int(b, ind) :: defines_var(ind)
                if indName notin bool2intByDef:
                    patternOk = false; break
                let b2iCi = bool2intByDef[indName]
                let b2iCon = tr.model.constraints[b2iCi]
                if b2iCon.args[0].kind != FznIdent: patternOk = false; break
                let boolName = b2iCon.args[0].ident

                # array_bool_and([b1, b2], b) :: defines_var(b)
                if boolName notin boolAndByDef:
                    patternOk = false; break
                let andCi = boolAndByDef[boolName]
                let andCon = tr.model.constraints[andCi]
                if andCon.args[0].kind != FznArrayLit: patternOk = false; break
                if andCon.args[0].elems.len != 2: patternOk = false; break
                let b1Elem = andCon.args[0].elems[0]
                let b2Elem = andCon.args[0].elems[1]
                if b1Elem.kind != FznIdent or b2Elem.kind != FznIdent: patternOk = false; break

                let b1Name = b1Elem.ident
                let b2Name = b2Elem.ident

                # int_lin_le_reif([1,-1], [x, y], -1, b1) :: defines_var(b1)
                # means: x - y <= -1  i.e., x < y
                if b1Name notin linLeReifByDef or b2Name notin linLeReifByDef:
                    patternOk = false; break
                let reif1Ci = linLeReifByDef[b1Name]
                let reif2Ci = linLeReifByDef[b2Name]
                let reif1Con = tr.model.constraints[reif1Ci]
                let reif2Con = tr.model.constraints[reif2Ci]

                # Validate reif coefficients: [1, -1] and rhs = -1
                var c1, c2: seq[int]
                try: c1 = tr.resolveIntArray(reif1Con.args[0])
                except: patternOk = false
                if not patternOk: break
                try: c2 = tr.resolveIntArray(reif2Con.args[0])
                except: patternOk = false
                if not patternOk: break
                if c1 != @[1, -1] or c2 != @[1, -1]: patternOk = false; break
                var r1, r2: int
                try: r1 = tr.resolveIntArg(reif1Con.args[2])
                except: patternOk = false
                if not patternOk: break
                try: r2 = tr.resolveIntArg(reif2Con.args[2])
                except: patternOk = false
                if not patternOk: break
                if r1 != -1 or r2 != -1: patternOk = false; break

                # Extract variable names from reif: vars = [x, y] → x < y
                if reif1Con.args[1].kind != FznArrayLit or reif1Con.args[1].elems.len != 2:
                    patternOk = false; break
                if reif2Con.args[1].kind != FznArrayLit or reif2Con.args[1].elems.len != 2:
                    patternOk = false; break

                let r1v0 = reif1Con.args[1].elems[0]
                let r1v1 = reif1Con.args[1].elems[1]
                let r2v0 = reif2Con.args[1].elems[0]
                let r2v1 = reif2Con.args[1].elems[1]
                if r1v0.kind != FznIdent or r1v1.kind != FznIdent: patternOk = false; break
                if r2v0.kind != FznIdent or r2v1.kind != FznIdent: patternOk = false; break

                # Betweenness pattern: (a < i) AND (i < b) where i is common.
                # reif1: r1v0 < r1v1, reif2: r2v0 < r2v1
                # Check both orderings: r1v1==r2v0 (standard) or r1v0==r2v1 (swapped AND args)
                var cableA, cableB: string
                if r1v1.ident == r2v0.ident:
                    # Standard: (a < i) AND (i < b) → cable (a, b)
                    cableA = r1v0.ident
                    cableB = r2v1.ident
                elif r1v0.ident == r2v1.ident:
                    # Swapped: (i < b) AND (a < i) → cable (a, b)
                    cableA = r2v0.ident
                    cableB = r1v1.ident
                else:
                    patternOk = false; break

                # Record cable pair (canonical order)
                let cablePair = if cableA < cableB: (a: cableA, b: cableB)
                                else: (a: cableB, b: cableA)
                allCablePairs.incl(cablePair)

                localConsumed.add(b2iCi)
                localConsumed.add(andCi)
                # Don't consume int_lin_le_reif constraints — they might be shared across multiple M_i sums
                localVarNames.add(indName)
                localVarNames.add(boolName)

            if not patternOk: break
            consumedConstraints.add(localConsumed)
            consumedVarNames.add(localVarNames)

        if not patternOk or allCablePairs.len == 0: continue

        # Step 4: Collect the int_lin_le_reif constraints used in this pattern
        # These define bool channels that are ONLY used for crossing count indicators.
        # Collect all reif bool names that feed into consumed array_bool_and constraints.
        var reifBoolNames: HashSet[string]
        for consumed_ci in consumedConstraints:
            let ccon = tr.model.constraints[consumed_ci]
            if stripSolverPrefix(ccon.name) == "array_bool_and":
                for elem in ccon.args[0].elems:
                    if elem.kind == FznIdent:
                        reifBoolNames.incl(elem.ident)

        # Check if these reif bools are used ONLY in consumed array_bool_and constraints
        # (they may be shared across multiple M_i sums, so we check ALL uses)
        var reifConstraintsToConsume: seq[int]
        for bName in reifBoolNames:
            if bName in linLeReifByDef:
                reifConstraintsToConsume.add(linLeReifByDef[bName])

        # Step 5: Pattern detected! Consume everything.
        stderr.writeLine(&"[FZN] Detected crossing count max pattern: {allCablePairs.len} cables, k={k}, M_max={mmDef.varName}")

        # Consume the array_int_maximum constraint
        tr.definingConstraints.incl(ci)
        # Consume all intermediate constraints
        for cc in consumedConstraints:
            tr.definingConstraints.incl(cc)
        # Consume the int_lin_le_reif constraints
        for rc in reifConstraintsToConsume:
            tr.definingConstraints.incl(rc)

        # Mark intermediate variables as channels (not search positions)
        for vn in consumedVarNames:
            tr.channelVarNames.incl(vn)
        for bName in reifBoolNames:
            tr.channelVarNames.incl(bName)

        # Store the pattern for channel binding construction
        var cables: seq[tuple[a, b: string]]
        for pair in allCablePairs:
            cables.add(pair)

        tr.crossingCountMaxDefs.add(CrossingCountMaxDef(
            maxVarName: mmDef.varName,
            cables: cables,
            k: k
        ))

