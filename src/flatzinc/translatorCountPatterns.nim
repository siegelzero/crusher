## Included from translator.nim -- not a standalone module.
## Count pattern detection: conditional counts, simple counts.

proc buildVarRefConstraints(tr: FznTranslator): Table[string, PackedSet[int]] =
    ## Builds a map: variable name → set of constraint indices that reference it.
    ## Used to check if a variable is referenced outside a consumed pattern.
    proc collectIdents(expr: FznExpr, result: var seq[string]) =
        case expr.kind
        of FznIdent:
            result.add(expr.ident)
        of FznArrayLit:
            for e in expr.elems:
                collectIdents(e, result)
        else: discard
    for ci, con in tr.model.constraints:
        var idents: seq[string]
        for arg in con.args:
            collectIdents(arg, idents)
        for id in idents:
            if id notin result:
                result[id] = initPackedSet[int]()
            result[id].incl(ci)

proc isReferencedOutside(varRefMap: Table[string, PackedSet[int]], varName: string,
                         consumedCIs: PackedSet[int], patternCI: int): bool =
    ## Returns true if varName is referenced by any constraint outside consumedCIs and patternCI.
    if varName notin varRefMap:
        return false
    for ci in varRefMap[varName].items:
        if ci != patternCI and ci notin consumedCIs:
            return true
    return false

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

    # Build variable reference map for checking external references
    let varRefMap = tr.buildVarRefConstraints()

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

        # Mark consumed constraints, but only eliminate variables not referenced elsewhere.
        # Only the pattern's own consumed constraints are considered "safe" — other
        # definingConstraints still resolve their inputs and need variables to be available.
        var patternConsumed = initPackedSet[int]()
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)
            patternConsumed.incl(idx)
        patternConsumed.incl(ci)  # the int_lin_eq itself
        for vn in consumedVarNames:
            if not varRefMap.isReferencedOutside(vn, patternConsumed, ci):
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

    # Build variable reference map for checking external references
    let varRefMap = tr.buildVarRefConstraints()

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
            # Do NOT consume int_eq_reif or its bool output variable here.
            # The bool variable may be referenced by other constraints (e.g. bool_clause).
            # Leave int_eq_reif for detectReifChannels() to create proper channel bindings.
            consumedVarNames.add(traced.indName)

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

        # Mark intermediate variable names as defined, but only if not referenced elsewhere
        var patternConsumed = initPackedSet[int]()
        for idx in consumedConstraints:
            patternConsumed.incl(idx)
        patternConsumed.incl(ci)
        for vn in consumedVarNames:
            if not varRefMap.isReferencedOutside(vn, patternConsumed, ci):
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

        # Mark consumed constraints, but only eliminate variables not referenced elsewhere
        var patternConsumed = initPackedSet[int]()
        for idx in consumedConstraints:
            tr.definingConstraints.incl(idx)
            patternConsumed.incl(idx)
        patternConsumed.incl(ci)
        for vn in consumedVarNames:
            if not varRefMap.isReferencedOutside(vn, patternConsumed, ci):
                tr.definedVarNames.incl(vn)

        stderr.writeLine(&"[FZN] Detected balanced count pattern: count({uncoveredArrayVarNames.len} vars, {uncoveredValue}) == {targetName} (balanced with value {coveredValue})")

    # Third pass: constant-count patterns (exactly constraint decomposition)
    # Pattern: int_lin_eq([-1,...,-1], [ind_1,...,ind_n], -k) where ALL coefficients are -1
    # and RHS is -k (a negative constant). Each indicator traces through bool2int → int_eq_reif
    # to the same value. Equivalent to: exactly(k, [x_1,...,x_n], val)
    # For k=0: domain reduction (remove val from all x_j domains)
    # For k>0: emit atLeast + atMost constraints
    #
    # Build separate maps that include consumed constraints — the bool2int/int_eq_reif for
    # zero-count indicators may already be consumed by collectDefinedVars, but we still need
    # to trace through them for pattern detection.
    var allBool2intDefs: Table[string, int]
    var allIntEqReifDefs: Table[string, int]
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name == "bool2int" and con.hasAnnotation("defines_var"):
            if con.args.len >= 2 and con.args[1].kind == FznIdent:
                allBool2intDefs[con.args[1].ident] = ci
        elif name == "int_eq_reif" and con.hasAnnotation("defines_var"):
            if con.args.len >= 3 and con.args[2].kind == FznIdent:
                allIntEqReifDefs[con.args[2].ident] = ci

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints or ci in tr.countEqPatterns or ci in tr.constantCountPatterns:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq":
            continue

        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        if coeffs.len < 1:
            continue

        # Check that ALL coefficients are the same (-1 or +1) — no target variable
        var allSame = true
        let c0 = coeffs[0]
        if c0 != -1 and c0 != 1:
            continue
        for i in 1..<coeffs.len:
            if coeffs[i] != c0: allSame = false; break
        if not allSame:
            continue

        # Compute required count: if coeffs are all -1 and rhs = -k, then sum(inds) = k
        # If coeffs are all +1 and rhs = k, then sum(inds) = k
        let requiredCount = if c0 == -1: -rhs else: rhs
        if requiredCount < 0:
            continue  # Negative count is infeasible — skip

        # Extract variable names
        let varElems = tr.extractVarElems(con.args[1])
        if varElems.len != coeffs.len:
            continue

        # Trace all indicators through bool2int → int_eq_reif
        var countValue: int
        var countValueSet = false
        var arrayVarNames: seq[string]
        var consumedConstraints: seq[int]
        var consumedVarNames: seq[string]
        var valid = true

        for i in 0..<varElems.len:
            let traced = tr.traceIndicator(varElems[i], allBool2intDefs, allIntEqReifDefs)
            if not traced.valid:
                valid = false; break
            if not countValueSet:
                countValue = traced.countValue
                countValueSet = true
            elif traced.countValue != countValue:
                valid = false; break

            arrayVarNames.add(traced.arrayVarName)
            consumedConstraints.add(traced.b2iIdx)
            consumedVarNames.add(traced.indName)

        if not valid or not countValueSet:
            continue

        if requiredCount == 0:
            # Zero-count: remove countValue from all array variable domains
            var nReduced = 0
            for vn in arrayVarNames:
                if vn in tr.presolveDomains:
                    let dom = tr.presolveDomains[vn]
                    var newDom: seq[int]
                    for v in dom:
                        if v != countValue:
                            newDom.add(v)
                    if newDom.len < dom.len:
                        tr.presolveDomains[vn] = newDom
                        inc nReduced
                else:
                    # Build domain from declaration and remove countValue
                    let dom = tr.lookupVarDomain(vn)
                    if dom.len > 0:
                        var newDom: seq[int]
                        for v in dom:
                            if v != countValue:
                                newDom.add(v)
                        if newDom.len < dom.len:
                            tr.presolveDomains[vn] = newDom
                            inc nReduced
            # Mark the int_lin_eq as consumed (it's satisfied by domain reduction)
            tr.definingConstraints.incl(ci)
            var patternConsumed = initPackedSet[int]()
            patternConsumed.incl(ci)
            for idx in consumedConstraints:
                tr.definingConstraints.incl(idx)
                patternConsumed.incl(idx)
            for vn in consumedVarNames:
                if not varRefMap.isReferencedOutside(vn, patternConsumed, ci):
                    tr.definedVarNames.incl(vn)
            if nReduced > 0:
                stderr.writeLine(&"[FZN] Zero-count domain reduction: removed value {countValue} from {nReduced}/{arrayVarNames.len} variable domains")
        else:
            # Positive count: record pattern for atLeast + atMost emission
            tr.constantCountPatterns[ci] = ConstantCountPattern(
                linEqIdx: ci,
                countValue: countValue,
                requiredCount: requiredCount,
                arrayVarNames: arrayVarNames
            )
            # Mark the int_lin_eq and bool2int as consumed
            # Do NOT consume int_eq_reif — bool vars may be shared by other constraints
            var patternConsumed2 = initPackedSet[int]()
            patternConsumed2.incl(ci)
            for idx in consumedConstraints:
                tr.definingConstraints.incl(idx)
                patternConsumed2.incl(idx)
            for vn in consumedVarNames:
                if not varRefMap.isReferencedOutside(vn, patternConsumed2, ci):
                    tr.definedVarNames.incl(vn)
            stderr.writeLine(&"[FZN] Detected constant count pattern: exactly({requiredCount}, {arrayVarNames.len} vars, {countValue})")

