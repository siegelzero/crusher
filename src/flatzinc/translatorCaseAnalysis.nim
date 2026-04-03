## Included from translator.nim -- not a standalone module.
## Case analysis channel detection and conditional source/implication/gain patterns.

proc detectCaseAnalysisChannels(tr: var FznTranslator, timeBudgetMs: float = 2000.0) =
    ## Detects case-analysis patterns in bool_clause constraints where a target variable's
    ## value is fully determined by condition variables through exhaustive case analysis.
    ## Converts target variables to channel variables with constant lookup tables.
    ## Has a time budget (default 2s) to avoid hanging on problems with large reification sets.
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

    let caseAnalysisStartTime = epochTime()
    let caseAnalysisDeadline = caseAnalysisStartTime + timeBudgetMs / 1000.0

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

    # Step 1a: Also pick up int_eq_reif :: defines_var entries where the test value is
    # a defined variable (these were skipped by detectReifChannels because defined vars
    # don't have positions, but they're still useful for case analysis pattern matching).
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif" or not con.hasAnnotation("defines_var"): continue
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if resultVar in eqReifMap: continue  # already handled by reifChannelDefs
        if con.args[0].kind != FznIdent: continue
        # Check that valArg is a defined variable (the reason it was skipped earlier)
        if con.args[1].kind != FznIdent: continue
        if con.args[1].ident notin tr.definedVarNames: continue
        eqReifMap[resultVar] = (sourceVar: con.args[0].ident, testVal: con.args[1])

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

    # Step 1g: Build map from array_bool_and results to their eq_reif/lin_eq_reif component.
    # When a bool_clause uses an AND result as a positive literal, we "see through" it to
    # extract the value consequence (eq_reif or lin_eq_reif) wrapped inside the AND.
    # Pattern: array_bool_and([guard1, guard2, ..., eq_or_lin_reif], and_result)
    var andToEqReifs: Table[string, seq[string]]   # and_result → [eq_reif_vars inside the AND]
    var andToLinReifs: Table[string, seq[string]]  # and_result → [lin_eq_reif_vars inside the AND]
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let cname = stripSolverPrefix(con.name)
        if cname != "array_bool_and": continue
        if con.args.len < 2: continue
        let elems = tr.resolveVarArrayElems(con.args[0])
        if con.args[1].kind != FznIdent: continue
        let andResult = con.args[1].ident
        # Collect all eq_reif and lin_eq_reif components inside the AND
        for elem in elems:
            if elem.kind != FznIdent: continue
            if elem.ident in eqReifMap:
                andToEqReifs.mgetOrPut(andResult, @[]).add(elem.ident)
            elif elem.ident in linEqReifMap:
                andToLinReifs.mgetOrPut(andResult, @[]).add(elem.ident)

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
            if negLit.ident in eqReifMap:
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
            elif negLit.ident in neReifMap:
                let neInfo = neReifMap[negLit.ident]
                let condDom = tr.lookupVarDomain(neInfo.condVar)
                if condDom.len > 0 and condDom.len <= 100:
                    for dv in condDom:
                        if dv == neInfo.condVal: continue
                        if posLit.ident in eqReifMap:
                            let eqInfo = eqReifMap[posLit.ident]
                            casesByTarget.mgetOrPut(eqInfo.sourceVar, @[]).add(CaseEntry(
                                kind: cekSimple,
                                condVarVals: @[(neInfo.condVar, dv)],
                                boolClauseIdx: ci,
                                testVal: eqInfo.testVal))
                        elif posLit.ident in linEqReifMap:
                            let linEntry = linEqReifMap[posLit.ident]
                            casesByTarget.mgetOrPut(linEntry.targetVar, @[]).add(CaseEntry(
                                kind: cekLinear,
                                condVarVals: @[(neInfo.condVar, dv)],
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
            elif eqLitVar == "" and elem.ident in andToEqReifs:
                # See through array_bool_and: extract contained eq_reif(s)
                # Pick the first non-constant-0 eq_reif (skip remainder==0 checks)
                for innerVar in andToEqReifs[elem.ident]:
                    let info = eqReifMap[innerVar]
                    # Prefer eq_reif where testVal is not literal 0 (those are usually
                    # guard checks like "remainder == 0", not value assignments)
                    if info.testVal.kind == FznIntLit and info.testVal.intVal == 0:
                        continue
                    eqLitVar = innerVar
                    eqSourceVar = info.sourceVar
                    eqTestVal = info.testVal
                    break
                if eqLitVar == "":
                    # Fallback: use the first one
                    let innerVar = andToEqReifs[elem.ident][0]
                    eqLitVar = innerVar
                    eqSourceVar = eqReifMap[innerVar].sourceVar
                    eqTestVal = eqReifMap[innerVar].testVal
            elif eqLitVar == "" and elem.ident in andToLinReifs:
                # See through array_bool_and: extract contained lin_eq_reif
                let innerVar = andToLinReifs[elem.ident][0]
                eqLitVar = innerVar
                eqLinEntry = linEqReifMap[innerVar]
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

    # Step 3b: Build local constElement map for fast channel resolution.
    # Maps channel variable names to (indexVar, constArray) for element channels
    # with constant arrays. Used to resolve variable test values without buildValueMapping.
    var localConstElements: Table[string, tuple[indexVar: string, constArray: seq[int]]]
    for ci, chanName in tr.channelConstraints:
        let con = tr.model.constraints[ci]
        let cname = stripSolverPrefix(con.name)
        if cname notin ["array_int_element", "array_int_element_nonshifted", "array_bool_element"]:
            continue
        if con.args[0].kind != FznIdent:
            continue
        let indexVarName = con.args[0].ident
        try:
            let constArray = tr.resolveIntArray(con.args[1])
            localConstElements[chanName] = (indexVar: indexVarName, constArray: constArray)
        except ValueError, KeyError:
            discard
    # Propagate element channel aliases
    for aliasName, originalName in tr.elementChannelAliases:
        if originalName in localConstElements:
            localConstElements[aliasName] = localConstElements[originalName]

    var nTargets = 0
    var nConsumed = 0
    var nRejectedCondVars = 0
    var nRejectedIncomplete = 0
    var nRejectedTableSize = 0
    var nRejectedUnresolved = 0
    var nRejectedCondSource = 0
    var nRejectedOther = 0

    for targetVar, entries in casesByTarget:
        # Time budget check — bail out if we've spent too long
        if epochTime() > caseAnalysisDeadline:
            break
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
        if not valid:
            inc nRejectedCondVars
            continue

        # Look up condition variable domains
        var condDomains: seq[seq[int]]
        for cv in condVarNames:
            let dom = tr.lookupVarDomain(cv)
            if dom.len == 0:
                valid = false
                break
            condDomains.add(dom)
        if not valid:
            inc nRejectedCondVars
            continue

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
            if not allSameSimple:
                inc nRejectedIncomplete
                continue
            let mappedVal = entries[0].testVal.intVal
            if not entries.allIt(it.testVal.intVal == mappedVal):
                inc nRejectedIncomplete
                continue
            let tdom = tr.lookupVarDomain(targetVar).sorted()
            if tdom.len < 2:
                inc nRejectedIncomplete
                continue
            if tdom.len == 2:
                discard  # binary domain: default is the other value (handled below)
            else:
                # Non-binary domain: default to 0 if it's in the domain and
                # the mapped value is non-zero (conditional activation pattern)
                if mappedVal == 0 or 0 notin tdom:
                    inc nRejectedIncomplete
                    continue

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
                # Trace bool2int channels back to their source search variable
                var traced = false
                for b2iCi in tr.bool2intChannelDefs:
                    let b2iCon = tr.model.constraints[b2iCi]
                    if b2iCon.args.len >= 2 and b2iCon.args[1].kind == FznIdent and
                         b2iCon.args[1].ident == ev:
                        let srcBool = b2iCon.args[0].ident
                        if srcBool notin tr.channelVarNames and srcBool notin tr.definedVarNames:
                            resolvedExprVars.incl(srcBool)
                            traced = true
                        break
                if not traced:
                    continue
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
        if not valid:
            inc nRejectedCondSource
            continue

        # Add expression variables as additional source variables
        # (channel/defined vars already replaced with transitive sources in exprVarSet)
        for ev in exprVarSet:
            if ev in tr.definedVarNames or ev in tr.channelVarNames:
                continue  # Skip residual channel vars — resolved via buildValueMapping
            if ev notin sourceVarNames:
                sourceVarNames.add(ev)
        if sourceVarNames.len == 0:
            inc nRejectedOther
            continue

        # Validate source variables are unique
        block uniqueCheck:
            for i in 0..<sourceVarNames.len:
                for j in i+1..<sourceVarNames.len:
                    if sourceVarNames[i] == sourceVarNames[j]:
                        valid = false
                        break uniqueCheck
        if not valid:
            inc nRejectedOther
            continue

        # Get source variable domains
        var sourceDomains: seq[seq[int]]
        for sv in sourceVarNames:
            let dom = tr.lookupVarDomain(sv)
            if dom.len == 0:
                valid = false
                break
            sourceDomains.add(dom)
        if not valid:
            inc nRejectedOther
            continue

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
        if not tableSizeOk or tableSize > 100_000:
            inc nRejectedTableSize
            continue

        # Pre-compute mini lookup tables for channel variables referenced in linear entries.
        # For each channel var not in caseAnalysisDefs, determine which source variables
        # it depends on, then build a small lookup table only over those dimensions.
        type MiniTable = object
            table: seq[int]
            srcIndices: seq[int]    # indices into sourceVarNames
            srcOffsets: seq[int]
            srcSizes: seq[int]
        var channelMiniTables: Table[string, MiniTable]
        var varOffsetChannels: HashSet[string]  # channels handled as variable+offset entries
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
            # Skip expensive buildValueMapping when estimated work is too large.
            # Each buildValueMapping call iterates over all reifChannelDefs in a fixed-point.
            # Precompute needs: 1 base + nSources probes + miniTableEntries per channel var.
            let estimatedCalls = 1 + sourceVarNames.len
            if tr.reifChannelDefs.len * estimatedCalls > 50_000:
                valid = false
                break precompute
            # Time budget check before expensive buildValueMapping calls
            if epochTime() > caseAnalysisDeadline:
                valid = false
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
                    # Check if it's an element channel indexed by a source variable —
                    # handle as variable+offset entry instead of rejecting
                    if cv in channelByName:
                        let elemCi = channelByName[cv]
                        let elemCon = tr.model.constraints[elemCi]
                        if elemCon.args.len >= 3 and elemCon.args[0].kind == FznIdent:
                            let idxVar = elemCon.args[0].ident
                            if idxVar in sourceVarNames:
                                varOffsetChannels.incl(cv)
                                continue
                    valid = false
                    break
                depSets[cv] = @[]
            if not valid: break precompute
            # Remove var+offset channels from channelVarsNeeded
            for cv in varOffsetChannels:
                channelVarsNeeded.excl(cv)

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
                    if mi mod 50 == 49 and epochTime() > caseAnalysisDeadline:
                        valid = false
                        break
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
        var lookupTable = newSeq[int](tableSize)
        var varEntries = initTable[int, CaseAnalysisVarEntry]()

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
                # VarOffset channels are deferred — process all others first.
                var numerator = entry.linRhs
                var linOk = true
                var deferredVarOffset = -1
                for j in 0..<entry.linOtherVars.len:
                    let ov = entry.linOtherVars[j]
                    if ov in varOffsetChannels:
                        deferredVarOffset = j
                        continue
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
                if not linOk:
                    allResolved = false
                    break
                # Handle deferred varOffset: create a variable+offset entry
                if deferredVarOffset >= 0:
                    let j2 = deferredVarOffset
                    let ov2 = entry.linOtherVars[j2]
                    let mult = -entry.linOtherCoeffs[j2] * (1 div entry.linTargetCoeff)
                    if mult != 1 and mult != -1:
                        allResolved = false
                        break
                    let elemCi = channelByName[ov2]
                    let elemCon = tr.model.constraints[elemCi]
                    let idxVar = elemCon.args[0].ident
                    let idxVal = sourceValues[idxVar]
                    let varElems = tr.resolveVarArrayElems(elemCon.args[1])
                    let arrIdx = idxVal - 1  # FZN 1-based to 0-based
                    if arrIdx < 0 or arrIdx >= varElems.len or varElems[arrIdx].kind != FznIdent:
                        allResolved = false
                        break
                    if numerator mod entry.linTargetCoeff != 0:
                        allResolved = false
                        break
                    let offset = numerator div entry.linTargetCoeff
                    varEntries[flatIdx] = CaseAnalysisVarEntry(varName: varElems[arrIdx].ident, offset: offset)
                    lookupTable[flatIdx] = 0
                else:
                    if numerator mod entry.linTargetCoeff != 0:
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
                        # Try fast element-chain resolution via localConstElements
                        var resolved = false
                        var cur = testValExpr.ident
                        var depth = 0
                        while depth < 10:
                            if cur in localConstElements:
                                let src = localConstElements[cur]
                                var idxVal: int
                                var idxOk = false
                                if src.indexVar in sourceValues:
                                    idxVal = sourceValues[src.indexVar]
                                    idxOk = true
                                elif src.indexVar in tr.paramValues:
                                    idxVal = tr.paramValues[src.indexVar]
                                    idxOk = true
                                elif src.indexVar in localConstElements:
                                    # Nested chain: resolve index through another element channel
                                    let innerSrc = localConstElements[src.indexVar]
                                    var innerIdxVal: int
                                    if innerSrc.indexVar in sourceValues:
                                        innerIdxVal = sourceValues[innerSrc.indexVar]
                                    elif innerSrc.indexVar in tr.paramValues:
                                        innerIdxVal = tr.paramValues[innerSrc.indexVar]
                                    else:
                                        break
                                    let innerArrIdx = innerIdxVal - 1
                                    if innerArrIdx >= 0 and innerArrIdx < innerSrc.constArray.len:
                                        idxVal = innerSrc.constArray[innerArrIdx]
                                        idxOk = true
                                    else:
                                        break
                                if not idxOk:
                                    break
                                let arrIdx = idxVal - 1  # FZN 1-based
                                if arrIdx >= 0 and arrIdx < src.constArray.len:
                                    lookupTable[flatIdx] = src.constArray[arrIdx]
                                    resolved = true
                                break
                            elif cur in tr.elementChannelAliases:
                                cur = tr.elementChannelAliases[cur]
                                inc depth
                            else:
                                break
                        if not resolved:
                            if tr.reifChannelDefs.len > 500:
                                allResolved = false
                                break
                            let mapping = tr.buildValueMapping(sourceValues)
                            if testValExpr.ident in mapping:
                                lookupTable[flatIdx] = mapping[testValExpr.ident]
                            elif testValExpr.ident in tr.channelVarNames:
                                varEntries[flatIdx] = CaseAnalysisVarEntry(
                                    varName: testValExpr.ident, offset: 0)
                                lookupTable[flatIdx] = 0
                            else:
                                allResolved = false
                                break
                else:
                    allResolved = false
                    break

        if not allResolved:
            inc nRejectedUnresolved
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
            domainSizes: domainSizes,
            varEntries: varEntries
        ))
        inc nTargets

    let nRejected = nRejectedCondVars + nRejectedIncomplete + nRejectedTableSize +
                    nRejectedUnresolved + nRejectedCondSource + nRejectedOther
    if nTargets > 0 or nRejected > 0:
        stderr.writeLine(&"[FZN] Case-analysis channels: {nTargets} detected, {nConsumed} bool_clause consumed" &
            &" (rejected: {nRejected} = condVars:{nRejectedCondVars} incomplete:{nRejectedIncomplete}" &
            &" tableSize:{nRejectedTableSize} unresolved:{nRejectedUnresolved}" &
            &" condSource:{nRejectedCondSource} other:{nRejectedOther})" &
            &" [candidates: {casesByTarget.len}]")


proc detectConditionalSourceChannels(tr: var FznTranslator) =
    ## Detects conditional variable-source patterns from decomposed step predicates.
    ##
    ## For target variable T, groups all int_eq_reif(T, V_k, B_k) constraints where
    ## V_k is a variable, then traces each B_k to find which condition value it
    ## corresponds to. Tracing goes through:
    ##   - Direct: bool_clause([B_k], [D_k]) where D_k = int_eq_reif(C, val_k, D_k)
    ##   - Via AND: B_k in array_bool_and([...,B_k,...], G), then trace G through
    ##     bool_clause chains to find the condition value
    ##
    ## When all V_k belong to a common variable array A:
    ##   Creates: src_idx = element(C, source_map)  (constant-array channel)
    ##            T = var_element(src_idx, A)         (variable-element channel)

    # Step 1: Build eqReifMap
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if name == "int_eq_reif":
            if con.args[0].kind != FznIdent: continue
            eqReifMap[resultVar] = (sourceVar: con.args[0].ident, testVal: con.args[1])

    if eqReifMap.len == 0: return

    # Step 2: Collect all int_eq_reif(T, V_k, B_k) where both T and V_k are variables
    # Group by target variable T.
    type EqReifEntry = object
        targetVar: string    # T (arg[0])
        sourceVar: string    # V_k (arg[1])
        boolVar: string      # B_k (arg[2])
    var eqReifByTarget: Table[string, seq[EqReifEntry]]

    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent or
           con.args[2].kind != FznIdent: continue
        let targetVar = con.args[0].ident
        let sourceVar = con.args[1].ident
        let boolVar = con.args[2].ident
        # Only interested in variable-to-variable equality tests
        if sourceVar in tr.paramValues: continue
        if targetVar in tr.channelVarNames or targetVar in tr.definedVarNames: continue
        eqReifByTarget.mgetOrPut(targetVar, @[]).add(
            EqReifEntry(targetVar: targetVar, sourceVar: sourceVar, boolVar: boolVar))

    if eqReifByTarget.len == 0:
        return

    # Build set_in_reif condition map: set_in_reif(var, S, bool) → condVar ∈ S
    var setInReifCondMap: Table[string, tuple[sourceVar: string, condVals: seq[int]]]
    for ci in tr.setInReifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "set_in_reif": continue
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        if con.args[0].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        let condVar = con.args[0].ident
        let setArg = con.args[1]
        var vals: seq[int]
        if setArg.kind == FznRange:
            for v in setArg.lo..setArg.hi: vals.add(v)
        elif setArg.kind == FznSetLit:
            vals = setArg.setElems
        if vals.len > 0:
            setInReifCondMap[resultVar] = (sourceVar: condVar, condVals: vals)

    # Step 3: Build index: bool var → which condition values it implies
    # A boolean may map to multiple condition values (from range set_in_reif)
    var boolToCondVals: Table[string, tuple[condVar: string, condVals: seq[int]]]

    proc resolveCondition(negIdent: string, eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]],
                          setInReifCondMap: Table[string, tuple[sourceVar: string, condVals: seq[int]]],
                          tr: FznTranslator): tuple[ok: bool, condVar: string, condVals: seq[int]] =
        if negIdent in eqReifMap:
            let condInfo = eqReifMap[negIdent]
            let condVal = try: tr.resolveIntArg(condInfo.testVal) except ValueError, KeyError: return (false, "", @[])
            return (true, condInfo.sourceVar, @[condVal])
        elif negIdent in setInReifCondMap:
            let info = setInReifCondMap[negIdent]
            return (true, info.sourceVar, info.condVals)
        return (false, "", @[])

    proc resolveNegLiterals(negArg: FznExpr,
                            eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]],
                            setInReifCondMap: Table[string, tuple[sourceVar: string, condVals: seq[int]]],
                            tr: FznTranslator): tuple[ok: bool, condVar: string, condVals: seq[int]] =
        ## Resolve all negative literals in a bool_clause and intersect their condition values.
        var condVar = ""
        var condVals: seq[int]
        for ni in 0..<negArg.elems.len:
            let negLit = negArg.elems[ni]
            if negLit.kind != FznIdent: return (false, "", @[])
            let (condOk, cv, cvs) = resolveCondition(negLit.ident, eqReifMap, setInReifCondMap, tr)
            if not condOk: return (false, "", @[])
            if condVar == "":
                condVar = cv
                condVals = cvs
            elif cv != condVar:
                return (false, "", @[])  # different condition variables
            else:
                let prevSet = condVals.toHashSet()
                var intersection: seq[int]
                for v in cvs:
                    if v in prevSet: intersection.add(v)
                condVals = intersection
                if condVals.len == 0: return (false, "", @[])
        return (ok: condVals.len > 0, condVar: condVar, condVals: condVals)

    proc mapPosLiterals(posArg: FznExpr, condVar: string, condVals: seq[int],
                        eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]],
                        setInReifCondMap: Table[string, tuple[sourceVar: string, condVals: seq[int]]],
                        boolToCondVals: var Table[string, tuple[condVar: string, condVals: seq[int]]]) =
        ## Map positive literals of a bool_clause to the resolved condition.
        for posElem in posArg.elems:
            if posElem.kind != FznIdent: continue
            if posElem.ident in boolToCondVals: continue
            # Skip if this positive literal is on the SAME condition variable
            if posElem.ident in eqReifMap:
                if eqReifMap[posElem.ident].sourceVar == condVar: continue
            if posElem.ident in setInReifCondMap:
                if setInReifCondMap[posElem.ident].sourceVar == condVar: continue
            boolToCondVals[posElem.ident] = (condVar: condVar, condVals: condVals)

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len == 0: continue
        let (ok, condVar, condVals) = resolveNegLiterals(negArg, eqReifMap, setInReifCondMap, tr)
        if not ok: continue
        mapPosLiterals(posArg, condVar, condVals, eqReifMap, setInReifCondMap, boolToCondVals)

    # Step 4: Extend via array_bool_and and fixpoint propagation

    # Propagate: if AND result G has a condition, all its inputs B_k share that condition
    # Note: do NOT skip definingConstraints — AND constraints may be consumed as channels
    # but we still need their structure for propagation.
    # Run as fixpoint since AND results may chain through bool_clause.
    var prevCondCount = -1
    while boolToCondVals.len != prevCondCount:
        prevCondCount = boolToCondVals.len
        # Propagate through array_bool_and: AND result → inputs
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name != "array_bool_and": continue
            if con.args.len < 2 or con.args[1].kind != FznIdent: continue
            let resultVar = con.args[1].ident
            if resultVar in boolToCondVals:
                let cv = boolToCondVals[resultVar]
                let inputElems = tr.resolveVarArrayElems(con.args[0])
                for elem in inputElems:
                    if elem.kind == FznIdent and elem.ident notin boolToCondVals:
                        boolToCondVals[elem.ident] = cv
        # Also propagate through bool_clause chains (including multi-neg patterns)
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name != "bool_clause": continue
            if con.args.len < 2: continue
            let posArg = con.args[0]
            let negArg = con.args[1]
            if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
            if negArg.elems.len == 0: continue
            let (ok, condVar, condVals) = resolveNegLiterals(negArg, eqReifMap, setInReifCondMap, tr)
            if not ok: continue
            mapPosLiterals(posArg, condVar, condVals, eqReifMap, setInReifCondMap, boolToCondVals)

    # Step 5: Build variable array index
    # A variable may appear in multiple arrays. Track ALL memberships.
    var varArrayMembers: Table[string, seq[string]]
    var varToArrays: Table[string, seq[tuple[arrayName: string, idx: int]]]
    for decl in tr.model.variables:
        if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
            var members: seq[string]
            for i, e in decl.value.elems:
                if e.kind == FznIdent:
                    members.add(e.ident)
                    varToArrays.mgetOrPut(e.ident, @[]).add((arrayName: decl.name, idx: i))
                elif e.kind == FznIntLit:
                    members.add("")  # constant element placeholder
                else:
                    members.add("")
            varArrayMembers[decl.name] = members

    # Step 6: For each target, try to build a complete source map
    var nTargets = 0
    var dbgTooFewMapped = 0
    var dbgNoArray = 0
    var dbgOther = 0
    var dbgTotalNoCond = 0
    var dbgTotalNoArr = 0
    var dbgTotalDiffCond = 0

    var dbgSkippedChannel = 0
    var dbgSkippedFew = 0
    for targetVar, eqEntries in eqReifByTarget:
        if targetVar in tr.channelVarNames:
            inc dbgSkippedChannel
            continue
        if eqEntries.len < 1:
            inc dbgSkippedFew
            continue

        # Find condition variable and source array
        var condVar = ""

        type SourceEntry = object
            condVal: int
            arrIdx: int  # 0-based index into array
            boolClauseIdx: int  # -1 if no direct bool_clause

        var sourceEntries: seq[SourceEntry]

        # First pass: collect all entries with valid condition mappings
        type CandidateEntry = object
            condVal: int
            sourceVar: string
            arrays: seq[tuple[arrayName: string, idx: int]]
        var candidates: seq[CandidateEntry]
        var dbgNoArr = 0
        var dbgNoCond = 0
        var dbgDiffCond = 0

        for e in eqEntries:
            if e.boolVar notin boolToCondVals:
                inc dbgNoCond
                continue
            let cv = boolToCondVals[e.boolVar]
            if condVar == "":
                condVar = cv.condVar
            elif cv.condVar != condVar:
                inc dbgDiffCond
                continue
            if e.sourceVar notin varToArrays:
                inc dbgNoArr
                continue
            # Expand range conditions: create one candidate per condVal
            for cv2 in cv.condVals:
                candidates.add(CandidateEntry(
                    condVal: cv2, sourceVar: e.sourceVar,
                    arrays: varToArrays[e.sourceVar]))

        # Find common array: an array that contains ALL candidate source vars
        # For single candidates, require the target to be in the same array (for default)
        if candidates.len == 0:
            dbgTotalNoCond += dbgNoCond
            dbgTotalNoArr += dbgNoArr
            dbgTotalDiffCond += dbgDiffCond
            inc dbgTooFewMapped
            continue

        # Collect all array names that appear in the first candidate
        var commonArrayCandidates: seq[string]
        for a in candidates[0].arrays:
            commonArrayCandidates.add(a.arrayName)

        # Keep only arrays that appear in ALL candidates
        for i in 1..<candidates.len:
            var nextArrayNames: seq[string]
            for a in candidates[i].arrays:
                if a.arrayName in commonArrayCandidates:
                    nextArrayNames.add(a.arrayName)
            commonArrayCandidates = nextArrayNames

        if commonArrayCandidates.len == 0:
            inc dbgNoArray
            continue

        # For single candidates: require the target to also be in a common array
        # (so we can use the target's own index as default for uncovered opcodes).
        # Without this, using an arbitrary default creates noisy penalty signals.
        if candidates.len == 1:
            if targetVar notin varToArrays:
                inc dbgTooFewMapped
                continue
            var found = false
            for a in varToArrays[targetVar]:
                if a.arrayName in commonArrayCandidates:
                    found = true
                    break
            if not found:
                inc dbgTooFewMapped
                continue

        # Prefer smallest array (most specific)
        var commonArrayName = commonArrayCandidates[0]
        var commonArraySize = varArrayMembers.getOrDefault(commonArrayName, @[]).len
        for arrName in commonArrayCandidates:
            let size = varArrayMembers.getOrDefault(arrName, @[]).len
            if size > 0 and size < commonArraySize:
                commonArrayName = arrName
                commonArraySize = size

        # Build source entries using the common array
        for c in candidates:
            for a in c.arrays:
                if a.arrayName == commonArrayName:
                    sourceEntries.add(SourceEntry(
                        condVal: c.condVal, arrIdx: a.idx, boolClauseIdx: -1))
                    break

        if sourceEntries.len == 0:
            inc dbgTooFewMapped
            continue

        # Get condition variable domain
        let condDom = tr.lookupVarDomain(condVar)
        if condDom.len == 0: continue

        # Build source map
        var sourceMap = newSeq[int](condDom.len)
        var condValToIdx: Table[int, int]
        for i, v in condDom:
            condValToIdx[v] = i

        var coveredCount = 0
        for e in sourceEntries:
            if e.condVal notin condValToIdx: continue
            let di = condValToIdx[e.condVal]
            sourceMap[di] = e.arrIdx + 1  # 1-based
            inc coveredCount

        if coveredCount == 0:
            inc dbgOther
            continue

        # Fill uncovered slots: use target's own array index if available
        if coveredCount < condDom.len:
            var hasDefault = false
            if targetVar in varToArrays:
                var tArr = ""
                var tIdx = -1
                for a in varToArrays[targetVar]:
                    if a.arrayName == commonArrayName:
                        tArr = a.arrayName
                        tIdx = a.idx
                        break
                if tArr == commonArrayName and tIdx >= 0:
                    for i in 0..<sourceMap.len:
                        if sourceMap[i] == 0:
                            sourceMap[i] = tIdx + 1
                    hasDefault = true
            if not hasDefault:
                var defaultIdx = 0
                for si in sourceMap:
                    if si > 0: defaultIdx = si; break
                if defaultIdx > 0:
                    for i in 0..<sourceMap.len:
                        if sourceMap[i] == 0: sourceMap[i] = defaultIdx
                    hasDefault = true
            if not hasDefault: continue

        # Validate sourceMap
        let arrayMembers = varArrayMembers[commonArrayName]
        var valid = true
        for si in sourceMap:
            if si < 1 or si > arrayMembers.len: valid = false; break
        if not valid: continue

        # Record pattern (binding construction happens after translateVariables)
        tr.channelVarNames.incl(targetVar)
        tr.conditionalSourceDefs.add(ConditionalSourceDef(
            targetVarName: targetVar,
            condVarName: condVar,
            sourceArrayName: commonArrayName,
            sourceMap: sourceMap,
            condDomMin: min(condDom)))
        inc nTargets

    stderr.writeLine(&"[FZN] Conditional-source channels: {nTargets} targets" &
        &" (skipped: alreadyChannel={dbgSkippedChannel} fewEqReifs={dbgSkippedFew}" &
        &" fewMapped={dbgTooFewMapped}[noCond={dbgTotalNoCond} noArr={dbgTotalNoArr} diffCond={dbgTotalDiffCond}]" &
        &" noArray={dbgNoArray} other={dbgOther})")


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

