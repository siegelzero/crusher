## Included from translator.nim -- not a standalone module.
## Detects and emits circuit-time-propagation constraints (TSPTW/VRP pattern).
##
## Pattern: fzn_circuit(pred) + element distance lookup + variable element
## departure lookup + int_lin_eq arrival computation + int_max departure computation.

proc detectCircuitTimePropagation(tr: var FznTranslator) =
    ## Detect circuit + time chain pattern and mark consumed constraints.
    var circuitCI = -1
    var predArrayName = ""
    var predVarNames: seq[string]

    # Step 1: Find fzn_circuit constraint
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "fzn_circuit": continue
        if con.args.len < 1: continue

        # Get pred array
        let predArg = con.args[0]
        var predElems: seq[FznExpr]
        case predArg.kind
        of FznArrayLit:
            predElems = predArg.elems
        of FznIdent:
            for decl in tr.model.variables:
                if decl.isArray and decl.name == predArg.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        predElems = decl.value.elems
                        predArrayName = predArg.ident
                    break
        else:
            continue
        if predElems.len == 0: continue

        # All pred elements must be variable identifiers
        var allIdent = true
        predVarNames = @[]
        for e in predElems:
            if e.kind != FznIdent:
                allIdent = false
                break
            predVarNames.add(e.ident)
        if not allIdent: continue

        circuitCI = ci
        break

    if circuitCI < 0: return

    let n = predVarNames.len

    # Step 2: Find constant element lookups (distance matrix rows)
    # Pattern: array_int_element(pred[l], constRow, durToPred[l]) :: defines_var
    var distRows: seq[seq[int]]  # distRows[l] = row l of distance matrix
    var durToPredVars: seq[string]  # durToPred var name per location
    var constElementCIs: seq[int]
    distRows.setLen(n)
    durToPredVars.setLen(n)
    constElementCIs.setLen(n)
    var foundDist = newSeq[bool](n)

    for ci, con in tr.model.constraints:
        # Note: don't skip definingConstraints — we need to find defines_var constraints
        let name = stripSolverPrefix(con.name)
        if name notin ["array_int_element", "array_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue

        let idxArg = con.args[0]
        if idxArg.kind != FznIdent: continue

        # Check if index is one of our pred vars
        var predIdx = -1
        for i, pv in predVarNames:
            if pv == idxArg.ident:
                predIdx = i
                break
        if predIdx < 0: continue

        # Resolve constant array
        let constArray = try: tr.resolveIntArray(con.args[1])
                         except ValueError, KeyError: continue
        if constArray.len != n: continue

        let resultArg = con.args[2]
        if resultArg.kind != FznIdent: continue

        distRows[predIdx] = constArray
        durToPredVars[predIdx] = resultArg.ident
        constElementCIs[predIdx] = ci
        foundDist[predIdx] = true

    # All locations must have distance rows
    for i in 0..<n:
        if not foundDist[i]: return

    # Step 3: Find variable element lookups (departure predecessor)
    # Pattern: array_var_int_element(pred[l], departureArray, departurePred[l]) :: defines_var
    var departureVarNames: seq[string]
    var departurePredVars: seq[string]
    var varElementCIs: seq[int]
    departurePredVars.setLen(n)
    varElementCIs.setLen(n)
    var foundVarElem = newSeq[bool](n)

    for ci, con in tr.model.constraints:
        # Note: don't skip definingConstraints — we need to find defines_var constraints
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue

        let idxArg = con.args[0]
        if idxArg.kind != FznIdent: continue

        var predIdx = -1
        for i, pv in predVarNames:
            if pv == idxArg.ident:
                predIdx = i
                break
        if predIdx < 0: continue

        # Get the departure array elements
        let arrElems = tr.presolveResolveVarElems(con.args[1])
        if arrElems.len != n: continue

        # First time: extract departure variable names
        if departureVarNames.len == 0:
            departureVarNames = newSeq[string](n)
            for i, elem in arrElems:
                if elem.kind == FznIdent:
                    departureVarNames[i] = elem.ident
                elif elem.kind == FznIntLit:
                    departureVarNames[i] = ""  # constant (depot)
                else:
                    return  # unsupported element type

        let resultArg = con.args[2]
        if resultArg.kind != FznIdent: continue

        departurePredVars[predIdx] = resultArg.ident
        varElementCIs[predIdx] = ci
        foundVarElem[predIdx] = true

    for i in 0..<n:
        if not foundVarElem[i]: return
    if departureVarNames.len != n: return

    # Step 4: Find int_lin_eq (arrival = departurePred + durToPred)
    # Pattern: int_lin_eq([1,-1,-1], [arrival, departurePred, durToPred], 0) :: defines_var(arrival)
    var arrivalVarNames = newSeq[string](n)
    var linEqCIs = newSeq[int](n)
    var foundLinEq = newSeq[bool](n)

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue

        # Resolve coefficients
        var coeffs: seq[int]
        let coeffsArg = con.args[0]
        if coeffsArg.kind == FznArrayLit:
            for e in coeffsArg.elems:
                if e.kind != FznIntLit: break
                coeffs.add(e.intVal)
        elif coeffsArg.kind == FznIdent:
            coeffs = try: tr.resolveIntArray(coeffsArg)
                     except ValueError, KeyError: @[]
        if coeffs != @[1, -1, -1]: continue

        # Check rhs = 0
        if con.args[2].kind != FznIntLit or con.args[2].intVal != 0: continue

        # Resolve variable array
        let varsArg = con.args[1]
        var varElems: seq[FznExpr]
        if varsArg.kind == FznArrayLit:
            varElems = varsArg.elems
        else: continue
        if varElems.len != 3: continue
        if varElems[0].kind != FznIdent or varElems[1].kind != FznIdent or varElems[2].kind != FznIdent:
            continue

        let arrivalVar = varElems[0].ident
        let depPredVar = varElems[1].ident
        let durPredVar = varElems[2].ident

        # Match departurePred and durToPred to a specific location
        for l in 0..<n:
            if departurePredVars[l] == depPredVar and durToPredVars[l] == durPredVar:
                arrivalVarNames[l] = arrivalVar
                linEqCIs[l] = ci
                foundLinEq[l] = true
                break

    for i in 0..<n:
        if not foundLinEq[i]: return

    # Step 5: Find int_max (departure = max(arrival, early))
    # Pattern: int_max(arrival[l], earlyConst, departure[l])
    var earlyTimes = newSeq[int](n)
    var intMaxCIs = newSeq[int](n)
    var foundMax = newSeq[bool](n)
    var depotIndex = -1
    var depotDeparture = 0

    # First, find the depot: departure with a constant value (typically 0)
    for i in 0..<n:
        if departureVarNames[i] == "":
            # Constant departure element found earlier
            depotIndex = i
            break

    # If no constant departure found, check for a departure variable with singleton domain
    if depotIndex < 0:
        for i in 0..<n:
            let dv = departureVarNames[i]
            if dv in tr.presolveDomains:
                if tr.presolveDomains[dv].len == 1:
                    depotIndex = i
                    depotDeparture = tr.presolveDomains[dv][0]
                    break

    # Find the departure array constant for depot
    if depotIndex >= 0 and departureVarNames[depotIndex] == "":
        # Get from the FlatZinc array literal
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
            if ci notin varElementCIs: continue
            let arrElems = tr.presolveResolveVarElems(con.args[1])
            if arrElems.len == n and arrElems[depotIndex].kind == FznIntLit:
                depotDeparture = arrElems[depotIndex].intVal
                break

    if depotIndex < 0: return

    # Mark depot as found (no int_max needed for depot)
    foundMax[depotIndex] = true
    earlyTimes[depotIndex] = 0

    for ci, con in tr.model.constraints:
        # Note: don't skip definingConstraints — we need to find defines_var constraints
        let name = stripSolverPrefix(con.name)
        if name != "int_max": continue
        if con.args.len < 3: continue

        # int_max(arrival, earlyConst, departure)
        let aArg = con.args[0]
        let bArg = con.args[1]
        let cArg = con.args[2]

        if aArg.kind != FznIdent or cArg.kind != FznIdent: continue
        var earlyVal: int
        if bArg.kind == FznIntLit:
            earlyVal = bArg.intVal
        elif bArg.kind == FznIdent and bArg.ident in tr.paramValues:
            earlyVal = tr.paramValues[bArg.ident]
        else:
            continue

        # Match arrival and departure to a location
        for l in 0..<n:
            if foundMax[l]: continue
            if arrivalVarNames[l] == aArg.ident and departureVarNames[l] == cArg.ident:
                earlyTimes[l] = earlyVal
                intMaxCIs[l] = ci
                foundMax[l] = true
                break

    for i in 0..<n:
        if not foundMax[i]: return

    # Step 6: Extract late times from departure domain upper bounds
    var lateTimes = newSeq[int](n)
    for i in 0..<n:
        let dv = departureVarNames[i]
        if dv == "":
            # Depot - use a large late time
            lateTimes[i] = high(int) div 2
            # Check arrival domain for depot late bound
            let av = arrivalVarNames[i]
            for decl in tr.model.variables:
                if not decl.isArray and decl.name == av:
                    case decl.varType.kind
                    of FznIntRange:
                        lateTimes[i] = decl.varType.hi
                    else: discard
                    break
            continue
        # Check presolveDomains first (tighter)
        if dv in tr.presolveDomains:
            lateTimes[i] = tr.presolveDomains[dv][^1]
            continue
        # Fallback to declared domain
        for decl in tr.model.variables:
            if not decl.isArray and decl.name == dv:
                case decl.varType.kind
                of FznIntRange:
                    lateTimes[i] = decl.varType.hi
                of FznIntSet:
                    lateTimes[i] = decl.varType.values[^1]
                else:
                    lateTimes[i] = high(int) div 2
                break

    # Step 7: Build distance matrix [to][from] 0-based
    var distMatrix = newSeq[seq[int]](n)
    for l in 0..<n:
        distMatrix[l] = distRows[l]  # Already [from] indexed by pred value

    # Success! Mark all consumed constraints
    var consumed = initPackedSet[int]()
    consumed.incl(circuitCI)
    for i in 0..<n:
        consumed.incl(constElementCIs[i])
        consumed.incl(varElementCIs[i])
        consumed.incl(linEqCIs[i])
        if i != depotIndex:
            consumed.incl(intMaxCIs[i])

    # Mark intermediate variables as channels (not searched).
    # Remove from definedVarNames so they get positions (needed for writeback & output).
    for i in 0..<n:
        tr.channelVarNames.incl(durToPredVars[i])
        tr.definedVarNames.excl(durToPredVars[i])
        tr.channelVarNames.incl(departurePredVars[i])
        tr.definedVarNames.excl(departurePredVars[i])
        if departureVarNames[i] != "":
            tr.channelVarNames.incl(departureVarNames[i])
            tr.definedVarNames.excl(departureVarNames[i])
        # Arrival vars: keep as channels for output, objective reads from position
        tr.channelVarNames.incl(arrivalVarNames[i])
        tr.definedVarNames.excl(arrivalVarNames[i])

    # Mark consumed constraints as defining (skip during translation)
    for ci in consumed:
        tr.definingConstraints.incl(ci)

    # Store detection results
    tr.circuitTimePropDetected = true
    tr.circuitTimePropPredVars = predVarNames
    tr.circuitTimePropDistMatrix = distMatrix
    tr.circuitTimePropEarlyTimes = earlyTimes
    tr.circuitTimePropLateTimes = lateTimes
    tr.circuitTimePropDepotIdx = depotIndex
    tr.circuitTimePropDepotDep = depotDeparture
    tr.circuitTimePropArrivalVars = arrivalVarNames
    tr.circuitTimePropDepartureVars = departureVarNames
    tr.circuitTimePropConsumedCIs = consumed

    stderr.writeLine(&"[FZN] Detected circuit-time-propagation pattern: {n} locations, depot={depotIndex+1}")


proc emitCircuitTimePropConstraint(tr: var FznTranslator) =
    ## Emit the CircuitTimePropConstraint after variable positions are created.
    if not tr.circuitTimePropDetected: return

    let n = tr.circuitTimePropPredVars.len

    # Look up pred positions
    var predPositions = newSeq[int](n)
    for i in 0..<n:
        let pv = tr.circuitTimePropPredVars[i]
        if pv notin tr.varPositions:
            stderr.writeLine(&"[FZN] CircuitTimeProp: pred var {pv} not found, aborting")
            return
        predPositions[i] = tr.varPositions[pv]

    # Look up arrival positions
    var arrivalPositions = newSeq[int](n)
    for i in 0..<n:
        let av = tr.circuitTimePropArrivalVars[i]
        if av in tr.varPositions:
            arrivalPositions[i] = tr.varPositions[av]
        else:
            arrivalPositions[i] = -1

    # Look up departure positions
    var departurePositions = newSeq[int](n)
    for i in 0..<n:
        let dv = tr.circuitTimePropDepartureVars[i]
        if dv != "" and dv in tr.varPositions:
            departurePositions[i] = tr.varPositions[dv]
        else:
            departurePositions[i] = -1

    # Detect value offset (same logic as circuit translation)
    var hasZero = false
    var hasN = false
    for pos in predPositions:
        let dom = tr.sys.baseArray.domain[pos]
        for v in dom:
            if v == 0: hasZero = true
            if v == n: hasN = true
    let valueOffset = if hasZero and not hasN: 0 else: 1

    # Add the constraint
    tr.sys.addConstraint(circuitTimeProp[int](
        predPositions,
        tr.circuitTimePropDistMatrix,
        tr.circuitTimePropEarlyTimes,
        tr.circuitTimePropLateTimes,
        tr.circuitTimePropDepotIdx,
        tr.circuitTimePropDepotDep,
        arrivalPositions,
        departurePositions,
        valueOffset
    ))

    # NOTE: No separate allDifferent — the CircuitTimeProp circuit penalty already
    # penalizes duplicate values (they create tail nodes). Adding allDifferent as a
    # separate constraint creates competing penalties that trap the search in local minima.

    stderr.writeLine(&"[FZN] Emitted CircuitTimeProp constraint: {n} nodes, offset={valueOffset}")
