## Included from translator.nim -- not a standalone module.

proc extractVarElems(tr: FznTranslator, vars: FznExpr): seq[FznExpr] =
    ## Extracts variable elements from an inline array literal or named array reference.
    if vars.kind == FznArrayLit:
        return vars.elems
    elif vars.kind == FznIdent:
        for decl in tr.model.variables:
            if decl.isArray and decl.name == vars.ident and decl.value != nil and decl.value.kind == FznArrayLit:
                return decl.value.elems

proc traceIndicator(tr: FznTranslator, varElem: FznExpr,
                    bool2intDefs, intEqReifDefs: Table[string, int]):
    tuple[valid: bool, countValue: int, arrayVarName: string,
          b2iIdx, eqReifIdx: int, indName, boolVarName: string] =
    ## Traces an indicator variable through bool2int → int_eq_reif chain.
    ## Returns (valid=true, ...) if the chain is complete.
    result.valid = false
    if varElem.kind != FznIdent:
        return
    result.indName = varElem.ident
    if result.indName notin bool2intDefs:
        return
    result.b2iIdx = bool2intDefs[result.indName]
    let b2iCon = tr.model.constraints[result.b2iIdx]
    if b2iCon.args[0].kind != FznIdent:
        return
    result.boolVarName = b2iCon.args[0].ident
    if result.boolVarName notin intEqReifDefs:
        return
    result.eqReifIdx = intEqReifDefs[result.boolVarName]
    let eqReifCon = tr.model.constraints[result.eqReifIdx]
    if eqReifCon.args[0].kind != FznIdent:
        return
    result.countValue = try: tr.resolveIntArg(eqReifCon.args[1]) except ValueError, KeyError: return
    result.arrayVarName = eqReifCon.args[0].ident
    result.valid = true

proc detectConditionalCountPatterns(tr: var FznTranslator) =
    ## Detects int_lin_eq → bool2int → array_bool_and → (int_eq_reif × 2) chains.
    ## Pattern: conditional count where each indicator checks TWO conditions:
    ##   int_eq_reif(x_primary_j, targetVal, b_primary_j) :: defines_var(b_primary_j)
    ##   int_eq_reif(x_filter_j, filterVal, b_filter_j) :: defines_var(b_filter_j)
    ##   array_bool_and([b_primary_j, b_filter_j], b_both_j) :: defines_var(b_both_j)
    ##   bool2int(b_both_j, ind_j) :: defines_var(ind_j)
    ##   int_lin_eq(coeffs, [ind_1, ..., ind_n, target], rhs) :: defines_var(target)
    ## Replaces deep cascade chains with a single conditional count channel binding.

    # Build maps: variable name → defining constraint index
    var bool2intDefs: Table[string, int]  # intVar name → constraint index
    var intEqReifDefs: Table[string, int]  # boolVar name → constraint index
    var arrayBoolAndDefs: Table[string, int]  # AND output var name → constraint index

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
        elif name == "array_bool_and" and con.hasAnnotation("defines_var"):
            if con.args.len >= 2 and con.args[1].kind == FznIdent:
                arrayBoolAndDefs[con.args[1].ident] = ci

    # Scan for int_lin_eq constraints that match the conditional count pattern.
    # Note: also check definingConstraints — collectDefinedVars may have claimed the
    # int_lin_eq for expression inlining, but we want to convert it to a channel instead.
    var nCandidates = 0
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq" or not con.hasAnnotation("defines_var"):
            continue

        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len < 3:  # Need at least 2 indicators + target
            continue
        inc nCandidates

        # Extract variable names
        let varElems = tr.extractVarElems(con.args[1])
        if varElems.len != coeffs.len: continue

        # Find the defines_var target position in the vars array
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0: continue
        var targetIdent: string
        if ann.args[0].kind == FznIdent:
            targetIdent = ann.args[0].ident
        elif ann.args[0].kind == FznStringLit:
            targetIdent = ann.args[0].strVal
        else:
            continue
        var targetIdx = -1
        for i in 0..<varElems.len:
            if varElems[i].kind == FznIdent and varElems[i].ident == targetIdent:
                targetIdx = i
                break
        if targetIdx < 0: continue

        let targetCoeff = coeffs[targetIdx]
        if targetCoeff != 1 and targetCoeff != -1: continue

        # All indicator coefficients must be the opposite sign
        let indCoeff = -targetCoeff
        var allMatch = true
        for i in 0..<coeffs.len:
            if i == targetIdx: continue
            if coeffs[i] != indCoeff:
                allMatch = false
                break
        if not allMatch: continue

        # Trace each indicator through one of two paths:
        # A) Conditional: bool2int → array_bool_and → two int_eq_reif
        # B) Direct: bool2int → int_eq_reif (single condition, no filter)
        type CondPair = tuple
            primaryVar: string   # variable name in primary int_eq_reif
            primaryVal: int      # constant value in primary int_eq_reif
            filterVar: string    # variable name in filter int_eq_reif ("" for direct path)
            filterVal: int       # constant value in filter int_eq_reif
            isDirect: bool       # true if this indicator uses the direct (single-condition) path

        var condPairs: seq[CondPair]
        var consumedConstraints: seq[int]
        var consumedVarNames: seq[string]
        var valid = true
        var hasConditional = false

        for i in 0..<varElems.len:
            if i == targetIdx: continue
            let indArg = varElems[i]
            if indArg.kind != FznIdent:
                valid = false; break
            let indName = indArg.ident

            # Trace: indVar → bool2int → boolVar
            if indName notin bool2intDefs:
                valid = false; break
            let b2iIdx = bool2intDefs[indName]
            let b2iCon = tr.model.constraints[b2iIdx]
            if b2iCon.args[0].kind != FznIdent:
                valid = false; break
            let boolVarName = b2iCon.args[0].ident

            if boolVarName in arrayBoolAndDefs:
                # Conditional path: boolVar → array_bool_and → [b1, b2] → two int_eq_reif
                let andIdx = arrayBoolAndDefs[boolVarName]
                let andCon = tr.model.constraints[andIdx]
                if andCon.args[0].kind != FznArrayLit:
                    valid = false; break
                let andInputs = andCon.args[0].elems
                if andInputs.len != 2:
                    valid = false; break
                if andInputs[0].kind != FznIdent or andInputs[1].kind != FznIdent:
                    valid = false; break

                var pair: CondPair
                pair.isDirect = false
                # Only consume bool2int + array_bool_and, NOT the int_eq_reif constraints
                # or their output boolVars — those may be referenced by other constraints
                # (e.g., bool_clause) and need reification channel positions.
                var pairConsumed: seq[int] = @[b2iIdx, andIdx]
                var pairVarNames: seq[string] = @[indName, boolVarName]
                var gotBoth = true

                for bi in 0..1:
                    let boolName = andInputs[bi].ident
                    if boolName notin intEqReifDefs:
                        gotBoth = false; break
                    let eqReifIdx = intEqReifDefs[boolName]
                    let eqReifCon = tr.model.constraints[eqReifIdx]
                    if eqReifCon.args[0].kind != FznIdent:
                        gotBoth = false; break
                    let xName = eqReifCon.args[0].ident
                    let val = try: tr.resolveIntArg(eqReifCon.args[1])
                               except ValueError, KeyError: (gotBoth = false; 0)
                    if not gotBoth: break
                    if bi == 0:
                        pair.primaryVar = xName
                        pair.primaryVal = val
                    else:
                        pair.filterVar = xName
                        pair.filterVal = val

                if not gotBoth:
                    valid = false; break

                condPairs.add(pair)
                consumedConstraints.add(pairConsumed)
                consumedVarNames.add(pairVarNames)
                hasConditional = true

            elif boolVarName in intEqReifDefs:
                # Direct path: boolVar → int_eq_reif (single condition, no filter)
                let eqReifIdx = intEqReifDefs[boolVarName]
                let eqReifCon = tr.model.constraints[eqReifIdx]
                if eqReifCon.args[0].kind != FznIdent:
                    valid = false; break
                let xName = eqReifCon.args[0].ident
                let val = try: tr.resolveIntArg(eqReifCon.args[1])
                           except ValueError, KeyError: (valid = false; 0)
                if not valid: break
                condPairs.add((primaryVar: xName, primaryVal: val,
                               filterVar: "", filterVal: 0, isDirect: true))
                # Only consume bool2int, not int_eq_reif (may be shared)
                consumedConstraints.add(@[b2iIdx])
                consumedVarNames.add(@[indName])
            else:
                valid = false; break

        if not valid or not hasConditional or condPairs.len < 2:
            continue

        # Determine the target value (all indicators must count the same value)
        # and the filter value (all conditional indicators must share the same filter value).
        # For conditional pairs, we need to figure out which of the two conditions is
        # the "primary" (matching the direct path value) and which is the "filter".

        # First, collect direct-path values to establish the target value
        var directVal = -1
        var directValSet = false
        for cp in condPairs:
            if cp.isDirect:
                if not directValSet:
                    directVal = cp.primaryVal
                    directValSet = true
                elif cp.primaryVal != directVal:
                    valid = false; break
        if not valid: continue

        # For conditional pairs, determine which condition matches the target value
        # Try both orderings: primary-first or filter-first
        var targetValue, filterValue: int
        var primaryVarNames, filterVarNames, directVarNames: seq[string]
        var identified = false

        for swapOrder in 0..1:
            var tryValid = true
            var tryTarget, tryFilter: int
            var tryPrimary, tryFilterNames, tryDirect: seq[string]
            var targetSet = directValSet
            if targetSet:
                tryTarget = directVal

            for cp in condPairs:
                if cp.isDirect:
                    tryDirect.add(cp.primaryVar)
                    continue
                let (pVar, pVal, fVar, fVal) = if swapOrder == 0:
                    (cp.primaryVar, cp.primaryVal, cp.filterVar, cp.filterVal)
                else:
                    (cp.filterVar, cp.filterVal, cp.primaryVar, cp.primaryVal)
                if not targetSet:
                    tryTarget = pVal
                    tryFilter = fVal
                    targetSet = true
                elif pVal != tryTarget:
                    tryValid = false; break
                if tryFilterNames.len == 0:
                    tryFilter = fVal
                elif fVal != tryFilter:
                    tryValid = false; break
                tryPrimary.add(pVar)
                tryFilterNames.add(fVar)

            if tryValid and targetSet:
                # If we had direct indicators, verify their value matches
                if directValSet and tryTarget != directVal:
                    continue
                targetValue = tryTarget
                filterValue = tryFilter
                primaryVarNames = tryPrimary
                filterVarNames = tryFilterNames
                directVarNames = tryDirect
                identified = true
                break

        if not identified: continue

        # Compute constant offset: target = (rhs - sum(indCoeff * ind_j)) / targetCoeff
        # Since ind_j are 0/1: target = (rhs - indCoeff * count) / targetCoeff
        # When count = 0: target = rhs / targetCoeff
        # For targetCoeff=-1, indCoeff=1: target = count - rhs, so constantOffset = -rhs
        # For targetCoeff=1, indCoeff=-1: target = rhs + count, so constantOffset = rhs
        let constantOffset = rhs * targetCoeff  # rhs/targetCoeff = rhs*targetCoeff since |targetCoeff|=1

        # Record the pattern
        tr.conditionalCountEqPatterns[ci] = ConditionalCountEqPattern(
            linEqIdx: ci,
            targetValue: targetValue,
            filterValue: filterValue,
            targetVarName: targetIdent,
            primaryVarNames: primaryVarNames,
            filterVarNames: filterVarNames,
            primaryOnlyVarNames: directVarNames,
            constantOffset: constantOffset
        )

        # If the int_lin_eq was already claimed by collectDefinedVars, undo that:
        # remove the target from definedVarNames/Exprs so it becomes a channel variable instead
        if ci in tr.definingConstraints:
            tr.definingConstraints.excl(ci)
            tr.definedVarNames.excl(targetIdent)
            if targetIdent in tr.definedVarExprs:
                tr.definedVarExprs.del(targetIdent)

        # Mark consumed constraints and variable names
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)
        for vn in consumedVarNames:
            tr.definedVarNames.incl(vn)

        stderr.writeLine(&"[FZN] Detected conditional count_eq pattern: count_if({primaryVarNames.len} pairs + {directVarNames.len} direct, primary=={targetValue} AND filter=={filterValue}) + {constantOffset} -> {targetIdent}")

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

    # Now scan for int_lin_eq constraints that match the pattern.
    # Note: we do NOT skip definingConstraints here — collectDefinedVars may have claimed
    # int_lin_eq constraints with defines_var that are actually countEq patterns.
    # countEq is a better translation; if detected, we unclaim from definingConstraints.
    for ci, con in tr.model.constraints:
        if ci in tr.countEqPatterns:
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

        # Check coefficient pattern:
        # Branch A: [1, -1, -1, ..., -1] — target first
        # Branch B: [1, 1, ..., 1, -1] — target last
        var targetIdx = -1
        var indStart, indEnd: int

        if coeffs[0] == 1:
            var allNeg = true
            for i in 1..<coeffs.len:
                if coeffs[i] != -1: allNeg = false; break
            if allNeg:
                targetIdx = 0; indStart = 1; indEnd = coeffs.len - 1

        if targetIdx < 0 and coeffs[^1] == -1:
            var allPos = true
            for i in 0..<coeffs.len - 1:
                if coeffs[i] != 1: allPos = false; break
            if allPos:
                targetIdx = coeffs.len - 1; indStart = 0; indEnd = coeffs.len - 2

        if targetIdx < 0:
            continue

        # Extract variable names - handle both inline arrays and named array references
        let varElems = tr.extractVarElems(con.args[1])
        if varElems.len != coeffs.len:
            continue

        let targetArg = varElems[targetIdx]
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

        for i in indStart..indEnd:
            let traced = tr.traceIndicator(varElems[i], bool2intDefs, intEqReifDefs)
            if not traced.valid:
                valid = false; break
            if not countValueSet:
                countValue = traced.countValue
                countValueSet = true
            elif traced.countValue != countValue:
                valid = false; break

            arrayVarNames.add(traced.arrayVarName)
            consumedConstraints.add(traced.b2iIdx)
            consumedConstraints.add(traced.eqReifIdx)
            consumedVarNames.add(traced.indName)
            consumedVarNames.add(traced.boolVarName)

        if not valid or not countValueSet:
            continue

        # Pattern detected! Record it.
        tr.countEqPatterns[ci] = CountEqPattern(
            linEqIdx: ci,
            countValue: countValue,
            targetVarName: targetName,
            arrayVarNames: arrayVarNames
        )

        # If this int_lin_eq was claimed by collectDefinedVars, unclaim it —
        # countEq is a better translation than a defined-var expression
        if ci in tr.definingConstraints:
            tr.definingConstraints.excl(ci)
            tr.definedVarNames.excl(targetName)

        # Mark consumed constraints (skip during translation)
        # Note: the int_lin_eq itself (ci) is NOT added to definingConstraints —
        # it's handled by the countEqPatterns check in the main loop
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)  # the bool2int and int_eq_reif

        # Mark intermediate variable names as defined (skip position creation)
        for vn in consumedVarNames:
            tr.definedVarNames.incl(vn)

        stderr.writeLine(&"[FZN] Detected count_eq pattern: count({arrayVarNames.len} vars, {countValue}) == {targetName}")

    # Second pass: balanced count patterns (count(A) = count(B))
    # Pattern: int_lin_eq([1,...,1,-1,...,-1], [indA_1,...,indA_m, indB_1,...,indB_n], 0)
    # where +1 indicators trace to int_eq_reif(x, valueA, b) and -1 to int_eq_reif(x, valueB, b)
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints or ci in tr.countEqPatterns:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq":
            continue
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if rhs != 0:
            continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len < 4:  # Need at least 2+2
            continue

        # Check coeffs are a mix of +1 and -1 (not a single-target pattern)
        var posCount, negCount = 0
        var mixValid = true
        for c in coeffs:
            if c == 1: inc posCount
            elif c == -1: inc negCount
            else: mixValid = false; break
        if not mixValid or posCount < 2 or negCount < 2:
            continue

        # Extract variable elements
        let varElems = tr.extractVarElems(con.args[1])
        if varElems.len != coeffs.len:
            continue

        # Trace +1 group and -1 group separately
        var valueA, valueB: int
        var valueASet, valueBSet = false
        var arrayVarNamesA, arrayVarNamesB: seq[string]
        var consumedConstraints: seq[int]
        var consumedVarNames: seq[string]
        var valid = true

        for i in 0..<coeffs.len:
            let traced = tr.traceIndicator(varElems[i], bool2intDefs, intEqReifDefs)
            if not traced.valid:
                valid = false; break

            if coeffs[i] == 1:
                if not valueASet:
                    valueA = traced.countValue
                    valueASet = true
                elif traced.countValue != valueA:
                    valid = false; break
                arrayVarNamesA.add(traced.arrayVarName)
            else:  # coeffs[i] == -1
                if not valueBSet:
                    valueB = traced.countValue
                    valueBSet = true
                elif traced.countValue != valueB:
                    valid = false; break
                arrayVarNamesB.add(traced.arrayVarName)

            consumedConstraints.add(traced.b2iIdx)
            consumedConstraints.add(traced.eqReifIdx)
            consumedVarNames.add(traced.indName)
            consumedVarNames.add(traced.boolVarName)

        if not valid or not valueASet or not valueBSet:
            continue
        if valueA == valueB:
            continue

        # Find an existing countEqPattern for one of the values to get the target
        var targetName = ""
        var coveredValue, uncoveredValue: int
        var uncoveredArrayVarNames: seq[string]

        for _, pat in tr.countEqPatterns:
            if pat.countValue == valueA and pat.arrayVarNames.len == arrayVarNamesA.len:
                targetName = pat.targetVarName
                coveredValue = valueA
                uncoveredValue = valueB
                uncoveredArrayVarNames = arrayVarNamesB
                break
            elif pat.countValue == valueB and pat.arrayVarNames.len == arrayVarNamesB.len:
                targetName = pat.targetVarName
                coveredValue = valueB
                uncoveredValue = valueA
                uncoveredArrayVarNames = arrayVarNamesA
                break

        if targetName == "":
            continue

        # Emit countEq for the uncovered value
        tr.countEqPatterns[ci] = CountEqPattern(
            linEqIdx: ci,
            countValue: uncoveredValue,
            targetVarName: targetName,
            arrayVarNames: uncoveredArrayVarNames
        )

        # Mark consumed constraints (idempotent for already-consumed ones)
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)
        for vn in consumedVarNames:
            tr.definedVarNames.incl(vn)

        stderr.writeLine(&"[FZN] Detected balanced count pattern: count({uncoveredArrayVarNames.len} vars, {uncoveredValue}) == {targetName} (balanced with value {coveredValue})")

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

    if tr.reifChannelDefs.len > 0 or tr.bool2intChannelDefs.len > 0 or
         tr.boolNotChannelDefs.len > 0 or
         tr.boolClauseReifChannelDefs.len > 0 or tr.setInReifChannelDefs.len > 0 or
         tr.boolAndOrChannelDefs.len > 0 or tr.leReifChannelDefs.len > 0 or
         tr.linLeReifChannelDefs.len > 0 or tr.linEqReifChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected reification channels: {tr.reifChannelDefs.len} int_eq/ne_reif, {tr.bool2intChannelDefs.len} bool2int, {tr.boolNotChannelDefs.len} bool_not, {tr.boolClauseReifChannelDefs.len} bool_clause_reif, {tr.setInReifChannelDefs.len} set_in_reif, {tr.boolAndOrChannelDefs.len} array_bool_and/or, {tr.leReifChannelDefs.len} int_le/lt_reif, {tr.linLeReifChannelDefs.len} int_lin_le_reif")


proc detectLinEqReifChannels*(tr: var FznTranslator) =
    ## Detect int_lin_eq_reif/int_lin_ne_reif(coeffs, vars, rhs, b) :: defines_var(b) patterns.
    ## b becomes a channel: b = (sum(coeffs*vars) == rhs) ? 1 : 0  (or != for ne)
    ## Must run AFTER detectCaseAnalysisChannels (which uses int_lin_eq_reif via linEqReifMap).
    var nEq, nNe = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif" and name != "int_lin_ne_reif": continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 4 or con.args[3].kind != FznIdent: continue
        let bName = con.args[3].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName: continue
        if bName in tr.channelVarNames: continue
        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        tr.linEqReifChannelDefs.add(ci)
        if name == "int_lin_eq_reif": inc nEq
        else: inc nNe
    if tr.linEqReifChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.linEqReifChannelDefs.len} int_lin_eq/ne_reif channels (eq={nEq} ne={nNe})")


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

    # Step 1d: Build setInReifCondMap from set_in_reif :: defines_var for use as conditions.
    # set_in_reif(var, S, bool) → bool = (var ∈ S)
    # In bool_clause as positive literal: bool true means var ∈ S → covers those domain values
    # In bool_clause as negative literal: ¬bool means var ∉ S → covers complement domain values
    type SetInReifEntry = object
        condVar: string
        inSet: seq[int]    # sorted set of values where bool = true
    var setInReifCondMap: Table[string, SetInReifEntry]

    for ci in tr.setInReifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "set_in_reif": continue
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if con.args[0].kind != FznIdent: continue
        let condVar = con.args[0].ident
        var setVals: seq[int]
        let setArg = con.args[1]
        if setArg.kind == FznSetLit:
            setVals = setArg.setElems.sorted()
        elif setArg.kind == FznRange:
            for v in setArg.lo..setArg.hi:
                setVals.add(v)
        else:
            continue
        if setVals.len > 0:
            setInReifCondMap[resultVar] = SetInReifEntry(condVar: condVar, inSet: setVals)

    # Step 1e: Extract single-variable int_lin_eq_reif :: defines_var into eqReifMap.
    # When int_lin_eq_reif has a single variable (coeffs=[c], vars=[x], rhs=r): x == r/c.
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif" or not con.hasAnnotation("defines_var"): continue
        if con.args.len < 4 or con.args[3].kind != FznIdent: continue
        let boolVar = con.args[3].ident
        if boolVar in linEqReifMap: continue
        if boolVar in tr.definedVarNames or boolVar in tr.channelVarNames: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let varElems = tr.resolveVarArrayElems(con.args[1])
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if coeffs.len != varElems.len: continue
        # Extract the single non-constant variable
        var condVar = ""
        var condCoeff = 0
        var allIdent = true
        var adjustedRhs = rhs
        for i in 0..<varElems.len:
            if varElems[i].kind == FznIdent:
                if varElems[i].ident in tr.paramValues:
                    adjustedRhs -= coeffs[i] * tr.paramValues[varElems[i].ident]
                elif condVar == "":
                    condVar = varElems[i].ident
                    condCoeff = coeffs[i]
                else:
                    allIdent = false  # multi-variable — skip
                    break
            elif varElems[i].kind == FznIntLit:
                adjustedRhs -= coeffs[i] * varElems[i].intVal
            else:
                allIdent = false
                break
        if not allIdent or condVar == "" or condCoeff == 0: continue
        if adjustedRhs mod condCoeff == 0:
            let testVal = adjustedRhs div condCoeff
            if boolVar notin eqReifMap:
                eqReifMap[boolVar] = (sourceVar: condVar,
                                      testVal: FznExpr(kind: FznIntLit, intVal: testVal))

    # Step 1f: Extend eqReifMap/neReifMap with bool equivalence aliases.
    # If aliasVar↔canonicalVar and canonicalVar is in eqReifMap, alias inherits the mapping.
    for def in tr.boolEquivAliasDefs:
        if def.canonicalVar in eqReifMap and def.aliasVar notin eqReifMap:
            eqReifMap[def.aliasVar] = eqReifMap[def.canonicalVar]
        if def.canonicalVar in neReifMap and def.aliasVar notin neReifMap:
            neReifMap[def.aliasVar] = neReifMap[def.canonicalVar]

    if eqReifMap.len == 0 and linEqReifMap.len == 0: return

    # Step 2: Scan non-consumed bool_clause constraints
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
        let nNegLits = negArg.elems.len
        let nLits = posArg.elems.len

        # Handle 1-positive-1-negative case: bool_clause([A], [B]) = A ∨ ¬B = B → A
        if nLits == 1 and nNegLits == 1:
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

        # Multi-literal case: up to 6 positive literals + any number of negative literals
        let totalLits = nLits + nNegLits
        if totalLits < 2 or nLits > 6 or nLits < 1: continue

        # Classify literals: exactly 1 eq_reif (or lin_eq_reif) + rest are conditions
        # Positive condition literals: ne_reif, le_reif, set_in_reif (positive = condition NOT met → case applies)
        # Negative literals: eq_reif means condition IS met (negation of eq_reif = condVar == condVal)
        var eqLitVar = ""
        var eqSourceVar = ""
        var eqTestVal: FznExpr
        var eqIsLinear = false
        var eqLinEntry: LinEqReifEntry
        var condLits: seq[(string, int)]  # (condVar, condVal) pairs: case applies when condVar == condVal
        var leEntries: seq[LeReifEntry]
        var setInEntries: seq[SetInReifEntry]
        var allValid = true

        # Process positive literals
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
                condLits.add((info.condVar, info.condVal))
            elif elem.ident in leReifMap:
                leEntries.add(leReifMap[elem.ident])
            elif elem.ident in setInReifCondMap:
                # set_in_reif as positive literal in bool_clause:
                # bool_clause([..., set_in_reif_bool, ...], [...]) means:
                # if set_in_reif_bool is true (var ∈ S), the clause is satisfied.
                # So for the case to apply, set_in_reif_bool must be false → var ∉ S
                setInEntries.add(setInReifCondMap[elem.ident])
            else:
                allValid = false
                break

        # Process negative literals as conditions
        if allValid:
            for elem in negArg.elems:
                if elem.kind != FznIdent:
                    allValid = false
                    break
                # Negative literal: ¬B in bool_clause means B must be true for case to apply
                if elem.ident in eqReifMap:
                    # ¬eq_reif(condVar, condVal, B) → B is true → condVar == condVal
                    let condInfo = eqReifMap[elem.ident]
                    let condVal = try: tr.resolveIntArg(condInfo.testVal) except ValueError, KeyError:
                        allValid = false
                        break
                    condLits.add((condInfo.sourceVar, condVal))
                elif elem.ident in setInReifCondMap:
                    # ¬set_in_reif_bool means bool is true → var ∈ S
                    # This constrains the condition variable to be in S
                    # We handle this as a positive set_in_reif condition (inverted below)
                    # For now, skip this pattern — too complex
                    allValid = false
                    break
                else:
                    allValid = false
                    break

        if not allValid or eqLitVar == "": continue
        # All literals except the target eq_reif must be condition literals
        let nCondLits = condLits.len + leEntries.len + setInEntries.len
        if nCondLits != totalLits - 1: continue

        # For le_reif or set_in_reif conditions, expand to individual condition values.
        # int_le_reif(var, threshold, bool) in bool_clause means: var > threshold → eq holds.
        # set_in_reif(var, S, bool) as positive literal: case applies when var ∉ S
        if leEntries.len > 0 or setInEntries.len > 0:
            # Get condition variable domains for le_reif entries
            var expandedCondLists: seq[seq[(string, int)]]
            expandedCondLists.add(condLits.mapIt(@[it]))

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
                expandedCondLists.add(vals)

            if not allValid: continue

            # Expand set_in_reif conditions: case applies when var ∉ S (complement)
            for sir in setInEntries:
                let dom = tr.lookupVarDomain(sir.condVar)
                if dom.len == 0:
                    allValid = false
                    break
                var vals: seq[(string, int)]
                let inSetHS = sir.inSet.toHashSet()
                for v in dom:
                    if v notin inSetHS:
                        vals.add((sir.condVar, v))
                if vals.len == 0:
                    allValid = false
                    break
                expandedCondLists.add(vals)

            if not allValid: continue

            # Build cross-product of all condition combinations
            var combos: seq[seq[(string, int)]] = @[@[]]
            for group in expandedCondLists:
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
                    kind: cekLinear, condVarVals: condLits, boolClauseIdx: ci,
                    linOtherVars: eqLinEntry.otherVars, linOtherCoeffs: eqLinEntry.otherCoeffs,
                    linRhs: eqLinEntry.rhs, linTargetCoeff: eqLinEntry.targetCoeff,
                    linReifIdx: eqLinEntry.constraintIdx))
            else:
                casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
                    kind: cekSimple, condVarVals: condLits, boolClauseIdx: ci,
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

        if not allResolved:
            continue

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
            let lo = learnedDom[0]
            let hi = learnedDom[^1]

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
    var nEmitted = 0
    for def in tr.atMostThroughReifDefs:
        var positions: seq[int]
        var allFound = true
        for vn in def.srcVarNames:
            if vn in tr.varPositions:
                positions.add(tr.varPositions[vn])
            elif vn in tr.definedVarExprs:
                # Shouldn't happen for source vars, but handle gracefully
                allFound = false
                break
            else:
                allFound = false
                break
        if not allFound or positions.len == 0: continue
        tr.sys.addConstraint(atMost[int](positions, def.targetValue, def.maxCount))
        inc nEmitted

    if nEmitted > 0:
        stderr.writeLine(&"[FZN] AtMost-through-reif: emitted {nEmitted} direct atMost constraints")

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

    # Step 3: Index unconsumed int_lin_le_reif by boolean output variable.
    # These are NOT consumed by detectReifChannels (no defines_var annotation).
    var linLeReifByBoolVar: Table[string, tuple[ci: int, con: FznConstraint]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le_reif":
            continue
        if con.hasAnnotation("defines_var"):
            continue  # Already consumed by detectReifChannels
        if con.args.len < 4:
            continue
        # int_lin_le_reif(coeffs, vars, rhs, bool_var)
        let boolArg = con.args[3]
        if boolArg.kind != FznIdent:
            continue
        # Only index if the bool var is a known ne_reif channel output
        if boolArg.ident in tr.channelVarNames:
            linLeReifByBoolVar[boolArg.ident] = (ci: ci, con: con)

    if linLeReifByBoolVar.len == 0:
        return

    # Step 4: Match complete argmax groups.
    var totalConsumedLinLeReif = 0
    var totalConsumedNeReif = 0

    for towerVarName, neReifGroup in neReifByTowerVar:
        if neReifGroup.len < 2:
            continue  # Need at least 2 entries for a meaningful argmax

        # Try to match each ne_reif to a lin_le_reif
        var matchedMaxVar = ""
        var valid = true
        var linLeCIs: seq[int]
        var neVarNames: seq[string]
        var neCIs: seq[int]

        # Sort by tValue to get ordered signal array
        var sortedGroup = neReifGroup
        sortedGroup.sort(proc(a, b: auto): int = cmp(a.tValue, b.tValue))

        for entry in sortedGroup:
            if entry.neVarName notin linLeReifByBoolVar:
                valid = false
                break

            let (linLeCi, linLeCon) = linLeReifByBoolVar[entry.neVarName]

            # Extract vars array from lin_le_reif
            let varsArg = linLeCon.args[1]
            var varElems: seq[FznExpr]
            if varsArg.kind == FznArrayLit:
                varElems = varsArg.elems
            else:
                valid = false
                break

            # Find the max_var among the variables (should have negative coefficient)
            var coeffs: seq[int]
            try:
                coeffs = tr.resolveIntArray(linLeCon.args[0])
            except ValueError, KeyError:
                valid = false
                break
            if coeffs.len != varElems.len or varElems.len < 2:
                valid = false
                break

            var foundMaxVar = ""
            for i in 0..<varElems.len:
                if varElems[i].kind == FznIdent and varElems[i].ident in maxChannelVarNames and coeffs[i] < 0:
                    foundMaxVar = varElems[i].ident
                    break

            if foundMaxVar == "":
                valid = false
                break

            if matchedMaxVar == "":
                matchedMaxVar = foundMaxVar
            elif matchedMaxVar != foundMaxVar:
                valid = false
                break

            linLeCIs.add(linLeCi)
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

        # Extract signal variable names in order
        var signalVarNames: seq[string]
        var signalValid = true
        for elem in signalElems:
            if elem.kind == FznIdent:
                signalVarNames.add(elem.ident)
            else:
                signalValid = false
                break
        if not signalValid:
            continue

        # Pattern detected! Use first lin_le_reif CI as trigger, consume the rest.
        # Note: array_int_maximum is intentionally NOT consumed — the element constraint
        # needs max_var to be channeled, so we keep its MinMaxChannelBinding active.
        let triggerCI = linLeCIs[0]
        tr.argmaxPatterns[triggerCI] = ArgmaxPattern(
            towerVarName: towerVarName,
            maxVarName: matchedMaxVar,
            signalVarNames: signalVarNames,
        )

        # Consume all lin_le_reif CIs except the trigger
        for i in 1..<linLeCIs.len:
            tr.definingConstraints.incl(linLeCIs[i])

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

        totalConsumedLinLeReif += linLeCIs.len
        totalConsumedNeReif += neVarNames.len
        stderr.writeLine(&"[FZN] Detected argmax pattern: {towerVarName} = argmax({signalVarNames.len} signals, max={matchedMaxVar})")

    if tr.argmaxPatterns.len > 0:
        stderr.writeLine(&"[FZN] Argmax detection: {tr.argmaxPatterns.len} groups, consumed {totalConsumedLinLeReif} int_lin_le_reif + {totalConsumedNeReif} int_ne_reif channels")

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

proc detectMaxFromLinLe*(tr: var FznTranslator) =
    ## Detects max-from-lin-le patterns:
    ## Multiple int_lin_le([1,-1], [source, ceiling], -offset) encode ceiling >= source + offset.
    ## When the ceiling variable is minimized, it equals max(source_i + offset_i).
    ## Makes ceiling a max channel, eliminating all those constraints.
    if tr.model.solve.kind != Minimize: return

    var minimizedVarNames = tr.findMinimizedVarNames()
    if minimizedVarNames.len == 0: return

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

    # Build MaxFromLinLeDefs for groups of size >= 3 where ceiling is minimized
    var totalConsumed = 0
    for ceilingName, infos in groups:
        if infos.len < 3: continue
        if ceilingName notin minimizedVarNames: continue

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
    var totalConsumed = 0
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

        # Mark consumed constraint indices
        for ci in def.consumedCIs:
            tr.definingConstraints.incl(ci)
        totalConsumed += def.consumedCIs.len

        # Do NOT mark spread var as channel — it stays as a search variable
        tr.spreadPatternDefs.add(def)

    if tr.spreadPatternDefs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.spreadPatternDefs.len} spread patterns, consumed {totalConsumed} int_lin_le constraints")

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
        stderr.writeLine(&"[FZN] Spread pattern '{def.spreadVarName}': replaced {def.consumedCIs.len} pairwise constraints with max/min channels + 1 constraint over {def.sourceVarNames.len} sources")

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
                        cr.yLo = yDom[0]
                        cr.yHi = yDom[^1]
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
                        let winStart = v
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
            let maxCeiling = ceilingDom[^1]

            # Phase 1: Tighten source upper bounds from ceiling max
            # y_i + offset_i <= D, so y_i <= max(dom(D)) - offset_i
            for i, srcName in def.sourceVarNames:
                if srcName notin tr.varPositions: continue
                let srcPos = tr.varPositions[srcName]
                let srcDom = tr.sys.baseArray.domain[srcPos]
                if srcDom.len == 0: continue
                let upperBound = maxCeiling - def.offsets[i]
                if srcDom[^1] <= upperBound: continue
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
                let lb = srcDom[0] + def.offsets[i]
                if lb > minCeiling:
                    minCeiling = lb
            if minCeiling > ceilingDom[0]:
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

proc detectBoolAndChannels*(tr: var FznTranslator) =
    ## Detects bool_clause([b], [c1, ..., cn]) where:
    ##   - b is a plain var bool appearing as positive literal in EXACTLY ONE bool_clause
    ##   - all ci are already channel variables (in channelVarNames)
    ##   - n >= 1
    ## These encode b = AND(c1, ..., cn). The constraint is consumed; b becomes a channel.
    ##
    ## In graph-clear: encodes var_i[e,t] = (var_l[e]<=t) AND (var_u[e]>=t) AND (var_t[i]!=t) AND (var_t[j]!=t)
    ## Requires: detectReifChannels() must have run first (to populate channelVarNames).

    # Pass 1: count how many bool_clause constraints have each var as sole positive literal
    var posLiteralCount = initTable[string, int]()
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        if posArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1: continue  # must have exactly 1 positive literal
        let posElem = posArg.elems[0]
        if posElem.kind != FznIdent: continue
        let bName = posElem.ident
        posLiteralCount[bName] = posLiteralCount.getOrDefault(bName, 0) + 1

    # Pass 2: for constraints where the positive literal appears exactly once and
    # all negative literals are channel variables, detect the AND pattern
    var detected = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue

        let posArg = con.args[0]
        if posArg.kind != FznArrayLit or posArg.elems.len != 1: continue
        let posElem = posArg.elems[0]
        if posElem.kind != FznIdent: continue
        let bName = posElem.ident

        # b must appear as positive literal in exactly one bool_clause
        if posLiteralCount.getOrDefault(bName, 0) != 1: continue

        # b must not already be a channel or defined var
        if bName in tr.channelVarNames: continue
        if bName in tr.definedVarNames: continue

        # Gather negative literals — all must be channel variables
        let negArg = con.args[1]
        if negArg.kind != FznArrayLit: continue
        if negArg.elems.len == 0: continue  # need at least 1 condition

        var condNames: seq[string]
        var allChannels = true
        for elem in negArg.elems:
            if elem.kind != FznIdent or elem.ident notin tr.channelVarNames:
                allChannels = false
                break
            condNames.add(elem.ident)
        if not allChannels: continue

        # All checks passed: b = AND(c1, ..., cn)
        tr.boolAndChannelDefs.add((ci: ci, resultVar: bName, condVars: condNames))
        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool AND channels (b = AND(ci) from bool_clause)")

proc detectBoolEquivalenceChannels*(tr: var FznTranslator) =
    ## Detects mutual bool_clause implications that establish equivalence between
    ## boolean variables. For bool_clause([A],[B]) + bool_clause([B],[A]), we have
    ## A↔B. If one of them is already a channel, the other becomes an alias channel.
    ##
    ## Uses union-find for transitive closure: A↔B, B↔C → A↔B↔C.
    ## Must run after detectBoolAndChannels() so channelVarNames includes AND channels.

    # Step 1: Scan non-consumed bool_clause([X],[Y]) (1 pos, 1 neg) to build implication edges
    type ImplEdge = object
        fromVar, toVar: string
        ci: int

    var forwardImpls = initTable[string, seq[ImplEdge]]()  # from → edges (from→to means "to implies from")

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1 or negArg.elems.len != 1: continue
        let posLit = posArg.elems[0]
        let negLit = negArg.elems[0]
        if posLit.kind != FznIdent or negLit.kind != FznIdent: continue
        # bool_clause([A],[B]) means B → A (if B is true then A is true)
        let a = posLit.ident
        let b = negLit.ident
        # Skip if either is a constant parameter
        if a in tr.paramValues or b in tr.paramValues: continue
        # Skip if either is already consumed by value-support
        if a in tr.valueSupportConsumedBools or b in tr.valueSupportConsumedBools: continue
        forwardImpls.mgetOrPut(b, @[]).add(ImplEdge(fromVar: b, toVar: a, ci: ci))

    # Step 2: Find mutual pairs (A→B and B→A both exist)
    type MutualPair = object
        varA, varB: string
        ciAB, ciBA: int  # constraint indices for A→B and B→A

    var mutualPairs: seq[MutualPair]
    var usedCIs: PackedSet[int]

    for bVar, edges in forwardImpls:
        for edge in edges:
            let aVar = edge.toVar
            # Check if there's a reverse edge: aVar → bVar (i.e., aVar in forwardImpls keys with target bVar)
            if aVar in forwardImpls:
                for revEdge in forwardImpls[aVar]:
                    if revEdge.toVar == bVar and edge.ci notin usedCIs and revEdge.ci notin usedCIs:
                        mutualPairs.add(MutualPair(varA: aVar, varB: bVar,
                                                   ciAB: revEdge.ci, ciBA: edge.ci))
                        usedCIs.incl(edge.ci)
                        usedCIs.incl(revEdge.ci)
                        break

    if mutualPairs.len == 0: return

    # Step 3: Union-find for transitive closure
    var parent = initTable[string, string]()

    proc find(x: string): string =
        var cur = x
        while cur in parent and parent[cur] != cur:
            cur = parent[cur]
        # Path compression
        var compress = x
        while compress in parent and parent[compress] != cur:
            let next = parent[compress]
            parent[compress] = cur
            compress = next
        result = cur

    proc union(a, b: string) =
        let ra = find(a)
        let rb = find(b)
        if ra != rb:
            parent[ra] = rb

    for pair in mutualPairs:
        if pair.varA notin parent: parent[pair.varA] = pair.varA
        if pair.varB notin parent: parent[pair.varB] = pair.varB
        union(pair.varA, pair.varB)

    # Step 4: Group into equivalence classes
    var classes = initTable[string, seq[string]]()
    for v in parent.keys:
        let root = find(v)
        classes.mgetOrPut(root, @[]).add(v)

    # Step 5: For each class, find if any member is already a channel.
    # If so, all non-channel members become alias channels.
    var detected = 0
    # Build map from pair to consumed CIs for lookup
    var pairCIs = initTable[(string, string), seq[int]]()
    for pair in mutualPairs:
        pairCIs[(pair.varA, pair.varB)] = @[pair.ciAB, pair.ciBA]
        pairCIs[(pair.varB, pair.varA)] = @[pair.ciAB, pair.ciBA]

    for root, members in classes:
        # Find canonical (channel) member
        var canonical = ""
        for m in members:
            if m in tr.channelVarNames:
                canonical = m
                break
        if canonical == "":
            continue  # No channel in this class — skip

        for m in members:
            if m == canonical: continue
            if m in tr.channelVarNames: continue
            if m in tr.definedVarNames: continue
            # Find the CIs connecting m to canonical (may be indirect through chain)
            # For simplicity, collect all CIs in the class
            var consumedCIs: seq[int]
            if (m, canonical) in pairCIs:
                consumedCIs = pairCIs[(m, canonical)]
            else:
                # Find a chain through the class — collect all pair CIs involving m
                for pair in mutualPairs:
                    if pair.varA == m or pair.varB == m:
                        if find(pair.varA) == find(canonical) or find(pair.varB) == find(canonical):
                            consumedCIs.add(pair.ciAB)
                            consumedCIs.add(pair.ciBA)
                            break
            if consumedCIs.len == 0: continue

            tr.boolEquivAliasDefs.add((aliasVar: m, canonicalVar: canonical,
                                       consumedCIs: consumedCIs))
            tr.channelVarNames.incl(m)
            for ci in consumedCIs:
                tr.definingConstraints.incl(ci)
            inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool equivalence alias channels")

proc detectBoolGatedVariableChannels*(tr: var FznTranslator) =
    ## Detects patterns where a variable is conditionally assigned either a variable
    ## value or a constant, gated by a boolean channel condition:
    ##   x = if cond then y else constant
    ##
    ## Pattern in FlatZinc (via bool_clause implications):
    ##   int_eq_reif(x, y, B_eq)   :: defines_var(B_eq)  -- B_eq ↔ (x == y)
    ##   bool_clause([B_eq], [cond])                       -- cond → x == y
    ##   plus: default value when ¬cond is derivable from target domain + other implications
    ##
    ## The condition variable must be a boolean channel. The target must not already
    ## be a channel or defined. One branch has a variable value, the other a constant.
    ##
    ## Must run after detectConditionalImplicationChannels() and detectBoolEquivalenceChannels().

    # Step 1: Build eq_reif reverse map: output bool var → (sourceVar, testVal)
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        eqReifMap[con.args[2].ident] = (sourceVar: con.args[0].ident, testVal: con.args[1])

    # Step 1b: Extend eqReifMap with bool equivalence aliases
    for def in tr.boolEquivAliasDefs:
        if def.canonicalVar in eqReifMap and def.aliasVar notin eqReifMap:
            eqReifMap[def.aliasVar] = eqReifMap[def.canonicalVar]

    # Step 2: Scan non-consumed bool_clause([A],[B1,...,Bn]) where:
    #   A is eq_reif output with variable testVal → implies cond → target == varValue
    #   B1..Bn are boolean channels (the conditions forming a conjunction)
    #   For multi-neg: look up known AND channel for the conjunction
    type GatedEntry = object
        boolClauseCI: int
        condChannel: string     # the boolean condition (single channel or AND channel)
        valVar: string          # the variable value (from eq_reif testVal)
        eqReifBool: string      # the eq_reif output bool (positive literal)

    # Build reverse map: sorted condVars → AND channel resultVar
    var andChannelByInputs = initTable[seq[string], string]()
    for def in tr.boolAndChannelDefs:
        var sortedConds = def.condVars.sorted()
        andChannelByInputs[sortedConds] = def.resultVar
    # Also include array_bool_and channels
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_and": continue
        if con.args.len < 2 or con.args[1].kind != FznIdent: continue
        let resultVar = con.args[1].ident
        let arrArg = con.args[0]
        if arrArg.kind != FznArrayLit: continue
        var condVars: seq[string]
        var allIdent = true
        for elem in arrArg.elems:
            if elem.kind != FznIdent:
                allIdent = false
                break
            condVars.add(elem.ident)
        if not allIdent: continue
        var sortedConds = condVars.sorted()
        andChannelByInputs[sortedConds] = resultVar

    var entriesByTarget = initTable[string, seq[GatedEntry]]()

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1: continue  # exactly 1 positive literal
        if negArg.elems.len < 1: continue   # at least 1 negative literal
        let posLit = posArg.elems[0]
        if posLit.kind != FznIdent: continue

        # posLit must be an eq_reif output
        if posLit.ident notin eqReifMap: continue
        let eqInfo = eqReifMap[posLit.ident]
        let targetVar = eqInfo.sourceVar

        # testVal must be a variable (not constant)
        if eqInfo.testVal.kind != FznIdent: continue
        let valVarName = eqInfo.testVal.ident
        if valVarName in tr.paramValues: continue

        # Skip if target is already channel or defined
        if targetVar in tr.channelVarNames or targetVar in tr.definedVarNames: continue

        # Determine the effective condition channel
        var condChannel = ""
        if negArg.elems.len == 1:
            # Single negative literal: must be a channel
            let negLit = negArg.elems[0]
            if negLit.kind != FznIdent or negLit.ident notin tr.channelVarNames: continue
            condChannel = negLit.ident
        else:
            # Multi-negative: all must be channels, AND their conjunction must be a known channel
            var negVars: seq[string]
            var allChannels = true
            for elem in negArg.elems:
                if elem.kind != FznIdent or elem.ident notin tr.channelVarNames:
                    allChannels = false
                    break
                negVars.add(elem.ident)
            if not allChannels: continue
            var sortedNegs = negVars.sorted()
            if sortedNegs in andChannelByInputs:
                condChannel = andChannelByInputs[sortedNegs]
            else:
                continue  # no known AND channel for this conjunction

        entriesByTarget.mgetOrPut(targetVar, @[]).add(GatedEntry(
            boolClauseCI: ci,
            condChannel: condChannel,
            valVar: valVarName,
            eqReifBool: posLit.ident))

    if entriesByTarget.len == 0: return

    # Step 2b: Build equivalence map for boolean channels.
    # A bool AND channel with a single condition (AND([c]) = c) is equivalent to c.
    # An equivalence alias is also equivalent. Used to match default clauses.
    var boolEquivSet = initTable[string, HashSet[string]]()  # condChannel → set of equivalents (including self)
    for def in tr.boolAndChannelDefs:
        if def.condVars.len == 1:
            let src = def.condVars[0]
            if src notin boolEquivSet:
                boolEquivSet[src] = [src].toHashSet()
            boolEquivSet[src].incl(def.resultVar)
    for def in tr.boolEquivAliasDefs:
        if def.canonicalVar notin boolEquivSet:
            boolEquivSet[def.canonicalVar] = [def.canonicalVar].toHashSet()
        boolEquivSet[def.canonicalVar].incl(def.aliasVar)

    # Step 3: For each target with exactly 1 entry (binary condition):
    # Check if target has binary domain {constant, ?} and can derive default constant
    var detected = 0
    for targetVar, entries in entriesByTarget:
        if targetVar in tr.channelVarNames: continue  # may have been channelized in this loop
        if entries.len != 1: continue  # only binary case for now

        let entry = entries[0]
        let condDomain = tr.lookupVarDomain(entry.condChannel)
        if condDomain != @[0, 1]: continue  # condition must be boolean

        let targetDomain = tr.lookupVarDomain(targetVar)
        if targetDomain.len < 2: continue

        # We need the default value when cond=0 (condition is false).
        # The implication says: cond=1 → target = valVar
        # When cond=0, target must take a constant value.
        # For binary target domain {a,b}: if valVar's domain covers one value,
        # default is the other. But we need a simpler check:
        # Look for another bool_clause that establishes target = constant when ¬cond.
        # OR: if target domain is {0, k} and there's an eq_reif for target=0 with
        # bool_clause([eq_reif_0], [not_cond_or_similar]) — but this gets complicated.
        #
        # Simpler approach: Check if 0 is in domain and is the obvious default.
        # Pattern: visit=0 means "not visited", visit=1 means "visited" with variable val.
        # The constant branch is typically 0 (the "off" value).
        # Check: is there a bool_clause that implies target=constVal when cond=false?

        # Look for bool_clause([eq_reif(target, constVal)], [negCond]) where negCond
        # is in the class of ¬cond (or cond itself appears as negative literal
        # with eq_reif for a constant value as positive).
        #
        # Alternative pattern: bool_clause([B_eq0, cond], []) means ¬cond → B_eq0 → target==0
        var defaultConstant = int.low
        var defaultCI = -1

        # Search for bool_clause([eq_reif(target, const), cond], []) meaning ¬cond → target==const
        for ci2, con2 in tr.model.constraints:
            if ci2 in tr.definingConstraints: continue
            if ci2 == entry.boolClauseCI: continue
            if stripSolverPrefix(con2.name) != "bool_clause": continue
            if con2.args.len < 2: continue
            let posArg2 = con2.args[0]
            let negArg2 = con2.args[1]
            if posArg2.kind != FznArrayLit or negArg2.kind != FznArrayLit: continue

            # Pattern: bool_clause([B_eq_const, cond], []) — 2 positive, 0 negative
            # This is a disjunction: B_eq_const OR cond
            # ¬cond → B_eq_const → target == const
            if posArg2.elems.len == 2 and negArg2.elems.len == 0:
                var eqReifLit = ""
                var condLit = ""
                let condEquivs = if entry.condChannel in boolEquivSet:
                    boolEquivSet[entry.condChannel]
                else:
                    [entry.condChannel].toHashSet()
                for elem in posArg2.elems:
                    if elem.kind != FznIdent: break
                    if elem.ident in condEquivs:
                        condLit = elem.ident
                    elif elem.ident in eqReifMap:
                        let info = eqReifMap[elem.ident]
                        if info.sourceVar == targetVar and info.testVal.kind == FznIntLit:
                            eqReifLit = elem.ident
                if eqReifLit != "" and condLit != "":
                    defaultConstant = eqReifMap[eqReifLit].testVal.intVal
                    defaultCI = ci2
                    break

            # Pattern: bool_clause([B_eq_const], [neg_cond]) where neg_cond is NOT(cond)
            # i.e., neg_cond → target == const, and neg_cond is the negation of cond
            # This is harder to detect without knowing the negation relationship.
            # Skip for now — the 2-positive pattern above is the common one.

        if defaultConstant == int.low: continue
        if defaultConstant notin targetDomain: continue

        # Determine which index corresponds to cond=0 (default) and cond=1 (variable)
        # cond is boolean {0,1}: when cond=1, target=valVar; when cond=0, target=defaultConstant
        var consumedCIs = @[entry.boolClauseCI]
        if defaultCI >= 0:
            consumedCIs.add(defaultCI)

        tr.boolGatedVarChannelDefs.add((
            targetVar: targetVar,
            condVar: entry.condChannel,
            valVar: entry.valVar,
            constValue: defaultConstant,
            consumedCIs: consumedCIs))
        tr.channelVarNames.incl(targetVar)
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool-gated variable channels")

proc detectOverlapChannels*(tr: var FznTranslator) =
    ## Detects overlap variables connected to time-separation channels through bool_not.
    ## Pattern:
    ##   bool_not(overlap, sep) :: defines_var(sep)   [already consumed, sep is channel]
    ## Records the overlap variable names for use by multi-resource consolidation.
    ## The overlap variable itself stays as a search variable (to avoid circular
    ## channel dependencies).
    ##
    ## Must run after detectReifChannels().

    var detected = 0
    for ci in tr.boolNotChannelDefs:
        let con = tr.model.constraints[ci]
        let aArg = con.args[0]  # the 'overlap' variable
        let bArg = con.args[1]  # the 'sep' variable (already a channel)

        if aArg.kind != FznIdent or bArg.kind != FznIdent: continue
        let aName = aArg.ident
        let bName = bArg.ident

        # b must be a channel (the sep variable)
        if bName notin tr.channelVarNames: continue
        # a must NOT already be a channel or defined
        if aName in tr.channelVarNames or aName in tr.definedVarNames: continue

        # Record for multi-resource consolidation (overlap stays as search variable)
        tr.overlapChannelDefs.add((ci: ci, overlapVar: aName, sepVar: bName))
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} overlap variables (a = NOT sep via bool_not)")


proc detectConditionalImplicationChannels*(tr: var FznTranslator) =
    ## Detects patterns where a variable is fully determined by implications through
    ## bool_clause([eq_reif(target, val)], [cond_channel]).
    ##
    ## Pattern A (Binary conditional / min-max pair):
    ##   bool_clause([eq_reif(Z, X)], [cond_lt]) + bool_clause([eq_reif(Z, Y)], [cond_gt])
    ##   where cond_lt and cond_gt are complementary int_lin_le_reif channels.
    ##   Result: Z = element(cond_lt, [Y, X]) — conditional assignment channel.
    ##
    ## Pattern B (One-hot conditional from allDifferent array):
    ##   bool_clause([eq_reif(Z, v_i)], [eq_reif(X_i, c)]) for i=1..N
    ##   where X_i are N different variables with same domain of size N (allDifferent),
    ##   c is a constant, and the conditions form a one-hot encoding.
    ##   Result: Z = element(weighted_one_hot_index, [v_0, ..., v_{N-1}])
    ##
    ## Requires: detectReifChannels() and detectBoolAndChannels() must have run first.

    # Step 1: Build eq_reif reverse map: output bool var → (sourceVar, testVal)
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        eqReifMap[con.args[2].ident] = (sourceVar: con.args[0].ident, testVal: con.args[1])

    # Step 2: Build int_lin_le_reif reverse map for complementarity checking
    # Maps output bool var → (varA, varB, rhs) for [1,-1] coefficient patterns
    type LinLeInfo = tuple[varA: string, varB: string, rhs: int]
    var linLeReifMap: Table[string, LinLeInfo]
    for ci in tr.linLeReifChannelDefs:
        let con = tr.model.constraints[ci]
        if con.args.len < 4 or con.args[3].kind != FznIdent: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if coeffs.len != 2 or coeffs[0] != 1 or coeffs[1] != -1: continue
        let varArr = con.args[1]
        if varArr.kind != FznArrayLit or varArr.elems.len != 2: continue
        if varArr.elems[0].kind != FznIdent or varArr.elems[1].kind != FznIdent: continue
        linLeReifMap[con.args[3].ident] = (varA: varArr.elems[0].ident,
                                            varB: varArr.elems[1].ident,
                                            rhs: rhs)

    # Step 3: Scan non-consumed bool_clause([A], [B]) and group by target variable
    type ImplEntry = object
        boolClauseCI: int
        condChannel: string    # negative literal (the condition)
        testVal: FznExpr       # value from eq_reif (constant or variable)

    var implByTarget: Table[string, seq[ImplEntry]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1 or negArg.elems.len != 1: continue
        let posLit = posArg.elems[0]
        let negLit = negArg.elems[0]
        if posLit.kind != FznIdent or negLit.kind != FznIdent: continue
        # posLit must be an eq_reif output
        if posLit.ident notin eqReifMap: continue
        # negLit must be a channel variable
        if negLit.ident notin tr.channelVarNames: continue
        let eqInfo = eqReifMap[posLit.ident]
        let targetVar = eqInfo.sourceVar
        # Skip if target is already channel or defined
        if targetVar in tr.channelVarNames or targetVar in tr.definedVarNames: continue
        implByTarget.mgetOrPut(targetVar, @[]).add(ImplEntry(
            boolClauseCI: ci,
            condChannel: negLit.ident,
            testVal: eqInfo.testVal))

    if implByTarget.len == 0: return

    var nBinary = 0
    var nOneHot = 0

    for targetVar, entries in implByTarget:
        if targetVar in tr.channelVarNames: continue  # may have been channelized in this loop

        # Pattern A: Binary conditional (exactly 2 entries with variable test values)
        if entries.len == 2:
            let e0 = entries[0]
            let e1 = entries[1]
            # Both test values must be variable references
            if e0.testVal.kind != FznIdent or e1.testVal.kind != FznIdent: continue
            # Both conditions must be int_lin_le_reif with [1,-1] coefficients
            if e0.condChannel notin linLeReifMap or e1.condChannel notin linLeReifMap: continue
            let info0 = linLeReifMap[e0.condChannel]
            let info1 = linLeReifMap[e1.condChannel]
            # Check complementarity: swapped variable order, rhs=-1 (strict <)
            # rhs=-1 ensures A-B <= -1 i.e. A < B, making the two conditions truly
            # complementary (exactly one is true). Other rhs values (e.g. 0 for <=)
            # would allow both conditions to be true when A == B.
            if info0.rhs != -1 or info1.rhs != -1: continue
            if not (info0.varA == info1.varB and info0.varB == info1.varA):
                continue
            # e0.condChannel = (info0.varA < info0.varB)  [rhs=-1 means strict <]
            # When cond0=1: target = e0.testVal
            # When cond0=0 (so cond1=1): target = e1.testVal
            tr.binaryCondChannelDefs.add((
                targetVar: targetVar,
                condChannel: e0.condChannel,
                val0Var: e1.testVal.ident,  # value when cond0=0
                val1Var: e0.testVal.ident,  # value when cond0=1
                consumedCIs: @[e0.boolClauseCI, e1.boolClauseCI]))
            tr.channelVarNames.incl(targetVar)
            tr.definingConstraints.incl(e0.boolClauseCI)
            tr.definingConstraints.incl(e1.boolClauseCI)
            inc nBinary
            continue

        # Pattern B: One-hot conditional (N entries with constant test values, different cond vars)
        if entries.len < 2: continue
        # All test values must be constants
        var allConst = true
        for e in entries:
            if e.testVal.kind != FznIntLit:
                allConst = false
                break
        if not allConst: continue
        # All conditions must be eq_reif channels from different source variables
        # with the SAME test constant value
        var condSourceVars: seq[string]
        var condConstVal: int = -1
        var condSourceOk = true
        for i, e in entries:
            if e.condChannel notin eqReifMap:
                condSourceOk = false
                break
            let condInfo = eqReifMap[e.condChannel]
            if condInfo.testVal.kind != FznIntLit:
                condSourceOk = false
                break
            if i == 0:
                condConstVal = condInfo.testVal.intVal
            elif condInfo.testVal.intVal != condConstVal:
                condSourceOk = false
                break
            if condInfo.sourceVar in condSourceVars:
                condSourceOk = false  # duplicate source var
                break
            condSourceVars.add(condInfo.sourceVar)
        if not condSourceOk: continue
        # Check completeness: N conditions should equal the domain size of the source vars
        # (ensures exactly one condition is true under allDifferent)
        let firstDom = tr.lookupVarDomain(condSourceVars[0])
        if firstDom.len == 0 or entries.len != firstDom.len: continue
        # Build ordered channels and values (sort by source var for deterministic ordering)
        type CondPair = tuple[sourceVar: string, condChannel: string, targetVal: int, ci: int]
        var pairs: seq[CondPair]
        for i, e in entries:
            pairs.add((sourceVar: condSourceVars[i], condChannel: e.condChannel,
                        targetVal: e.testVal.intVal, ci: e.boolClauseCI))
        pairs.sort(proc(a, b: CondPair): int = cmp(a.sourceVar, b.sourceVar))
        var orderedChannels: seq[string]
        var orderedVals: seq[int]
        var consumedCIs: seq[int]
        for p in pairs:
            orderedChannels.add(p.condChannel)
            orderedVals.add(p.targetVal)
            consumedCIs.add(p.ci)
        tr.oneHotCondChannelDefs.add((
            targetVar: targetVar,
            condChannels: orderedChannels,
            targetVals: orderedVals,
            consumedCIs: consumedCIs))
        tr.channelVarNames.incl(targetVar)
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)
        inc nOneHot

    if nBinary > 0 or nOneHot > 0:
        stderr.writeLine(&"[FZN] Detected conditional implication channels: {nBinary} binary (min/max pair), {nOneHot} one-hot (permutation lookup)")


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


proc detectBoolXorSimplification(tr: var FznTranslator) =
    ## Detects bool_xor constraints where inputs are constants and folds them.
    ## - bool_xor(const_a, const_b, result) → result becomes a defined constant
    ## - bool_xor(const_a, var_b, result) → result = var_b (if a=false) or result = 1-var_b (if a=true)
    ## - bool_xor(var_a, const_b, result) → similarly
    var nFolded = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_xor": continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if resultVar in tr.channelVarNames or resultVar in tr.definedVarNames: continue

        # Resolve arguments — check if they are constants
        var aConst = false
        var aVal = 0
        var bConst = false
        var bVal = 0
        let argA = con.args[0]
        let argB = con.args[1]

        if argA.kind == FznBoolLit:
            aConst = true; aVal = if argA.boolVal: 1 else: 0
        elif argA.kind == FznIntLit:
            aConst = true; aVal = argA.intVal
        elif argA.kind == FznIdent and argA.ident in tr.paramValues:
            aConst = true; aVal = tr.paramValues[argA.ident]

        if argB.kind == FznBoolLit:
            bConst = true; bVal = if argB.boolVal: 1 else: 0
        elif argB.kind == FznIntLit:
            bConst = true; bVal = argB.intVal
        elif argB.kind == FznIdent and argB.ident in tr.paramValues:
            bConst = true; bVal = tr.paramValues[argB.ident]

        if aConst and bConst:
            # Both constants: result is known
            let xorVal = if aVal != bVal: 1 else: 0
            tr.paramValues[resultVar] = xorVal
            tr.definedVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            inc nFolded
        elif aConst:
            # One constant: result is identity or negation of the other variable
            tr.channelVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            if aVal != 0:
                # result = 1 - b (negation) — store (inputVarArg, resultVar) for channel building
                tr.boolXorNegDefs.add((inputArg: argB, resultVar: resultVar))
            else:
                # result = b (identity)
                if argB.kind == FznIdent:
                    tr.equalityCopyAliases[resultVar] = argB.ident
            inc nFolded
        elif bConst:
            # One constant: result is identity or negation of the other variable
            tr.channelVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            if bVal != 0:
                # result = 1 - a (negation)
                tr.boolXorNegDefs.add((inputArg: argA, resultVar: resultVar))
            else:
                # result = a (identity)
                if argA.kind == FznIdent:
                    tr.equalityCopyAliases[resultVar] = argA.ident
            inc nFolded

    if nFolded > 0:
        stderr.writeLine(&"[FZN] Folded {nFolded} bool_xor constraints with constant inputs")
