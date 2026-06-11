## Included from translator.nim -- not a standalone module.
## Detects and emits circuit-time-propagation constraints (TSPTW/VRP pattern).
## One instance may be detected per crusher_circuit constraint.
##
## Two encodings are recognised:
##
## 1. Predecessor form (TSPTW, equality times, time windows):
##      crusher_circuit(pred)
##      array_int_element(pred[l], distRow_l, durToPred_l) :: defines_var
##      array_var_int_element(pred[l], departures, depPred_l) :: defines_var
##      int_lin_eq([1,-1,-1], [arrival_l, depPred_l, durToPred_l], 0) :: defines_var
##      int_max(arrival_l, early_l, departure_l)
##
## 2. Successor form (VRP, inequality times):
##      crusher_circuit(succ)            -- may contain fixed (literal) entries
##      array_int_element(succ[n], distRow_n, d_n) :: defines_var
##      array_var_int_element(succ[n], times, at_n) :: defines_var
##      int_lin_le([1,1,-1], [time_n, d_n, at_n], -service_n)       (var time_n)
##      int_lin_le([1,-1], [d_n, at_n], -service_n - time_n)        (fixed time_n)
##    i.e. time_n + service_n + dist[n][succ_n] <= time[succ_n].
##
##    The inequalities are projected to earliest-time equalities (the constraint
##    walks the tour computing times). This is sound only when each time
##    variable is otherwise unobserved, or feeds array_int_maximum outputs that
##    enter a MINIMIZED linear objective with positive weights — then assigning
##    every time its minimum feasible value is WLOG. This is verified before
##    any constraint is consumed; candidates that fail verification are dropped
##    and their constraints translate normally.
##
##    Service times are folded into the distance matrix
##    (dist'[to][from] = dist[to][from] + service[from]).
##
##    Nodes without a time triple (e.g. end depots in multi-vehicle giant
##    tours, where the clock resets on the wrap arc) get outConstrained=false.
##
##    When the objective is objective = sum_i w_i * max_i + offset over the
##    instances' maxima (each covering the instance's full time set), the
##    weights are recorded so the optimizer can distribute objective bounds
##    across instances (see applyCircuitTimeObjectiveBounds).


proc circuitTimeDomainBounds(tr: FznTranslator, name: string): (int, int) =
    ## Domain bounds for a variable by name: presolve domains first, then the
    ## declared domain.
    if name in tr.presolveDomains and tr.presolveDomains[name].len > 0:
        return (tr.presolveDomains[name][0], tr.presolveDomains[name][^1])
    for decl in tr.model.variables:
        if not decl.isArray and decl.name == name:
            case decl.varType.kind
            of FznIntRange:
                return (decl.varType.lo, decl.varType.hi)
            of FznIntSet:
                return (decl.varType.values[0], decl.varType.values[^1])
            else:
                discard
            break
    return (low(int) div 2, high(int) div 2)


proc circuitTimeFixedValue(tr: FznTranslator, e: FznExpr): (bool, int) =
    ## Resolve an expression to a fixed integer (literal, parameter, or
    ## singleton-domain variable).
    case e.kind
    of FznIntLit:
        return (true, e.intVal)
    of FznIdent:
        if e.ident in tr.paramValues:
            return (true, tr.paramValues[e.ident])
        if e.ident in tr.presolveDomains and tr.presolveDomains[e.ident].len == 1:
            return (true, tr.presolveDomains[e.ident][0])
    else:
        discard
    return (false, 0)


proc tryMatchPredFormCircuitTime(tr: var FznTranslator, circuitCI: int,
                                 elems: seq[FznExpr],
                                 cand: var CircuitTimeCandidate): bool =
    ## Legacy TSPTW pattern: equality time chain on predecessor variables.
    var predVarNames: seq[string]
    for e in elems:
        if e.kind != FznIdent:
            return false
        predVarNames.add(e.ident)

    let n = predVarNames.len

    # Step 2: Find constant element lookups (distance matrix rows)
    var distRows: seq[seq[int]]
    var durToPredVars: seq[string]
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

        var predIdx = -1
        for i, pv in predVarNames:
            if pv == idxArg.ident:
                predIdx = i
                break
        if predIdx < 0: continue

        let constArray = try: tr.resolveIntArray(con.args[1])
                         except ValueError, KeyError: continue
        if constArray.len != n: continue

        let resultArg = con.args[2]
        if resultArg.kind != FznIdent: continue

        distRows[predIdx] = constArray
        durToPredVars[predIdx] = resultArg.ident
        constElementCIs[predIdx] = ci
        foundDist[predIdx] = true

    for i in 0..<n:
        if not foundDist[i]: return false

    # Step 3: Find variable element lookups (departure of predecessor)
    var departureVarNames: seq[string]
    var departurePredVars: seq[string]
    var varElementCIs: seq[int]
    departurePredVars.setLen(n)
    varElementCIs.setLen(n)
    var foundVarElem = newSeq[bool](n)

    for ci, con in tr.model.constraints:
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

        let arrElems = tr.presolveResolveVarElems(con.args[1])
        if arrElems.len != n: continue

        if departureVarNames.len == 0:
            departureVarNames = newSeq[string](n)
            for i, elem in arrElems:
                if elem.kind == FznIdent:
                    departureVarNames[i] = elem.ident
                elif elem.kind == FznIntLit:
                    departureVarNames[i] = ""  # constant (depot)
                else:
                    return false

        let resultArg = con.args[2]
        if resultArg.kind != FznIdent: continue

        departurePredVars[predIdx] = resultArg.ident
        varElementCIs[predIdx] = ci
        foundVarElem[predIdx] = true

    for i in 0..<n:
        if not foundVarElem[i]: return false
    if departureVarNames.len != n: return false

    # Step 4: Find int_lin_eq (arrival = departurePred + durToPred)
    var arrivalVarNames = newSeq[string](n)
    var linEqCIs = newSeq[int](n)
    var foundLinEq = newSeq[bool](n)

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq": continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue

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

        if con.args[2].kind != FznIntLit or con.args[2].intVal != 0: continue

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

        for l in 0..<n:
            if departurePredVars[l] == depPredVar and durToPredVars[l] == durPredVar:
                arrivalVarNames[l] = arrivalVar
                linEqCIs[l] = ci
                foundLinEq[l] = true
                break

    for i in 0..<n:
        if not foundLinEq[i]: return false

    # Step 5: Find int_max (departure = max(arrival, early))
    var earlyTimes = newSeq[int](n)
    var intMaxCIs = newSeq[int](n)
    var foundMax = newSeq[bool](n)
    var depotIndex = -1
    var depotDeparture = 0

    for i in 0..<n:
        if departureVarNames[i] == "":
            depotIndex = i
            break

    if depotIndex < 0:
        for i in 0..<n:
            let dv = departureVarNames[i]
            if dv in tr.presolveDomains:
                if tr.presolveDomains[dv].len == 1:
                    depotIndex = i
                    depotDeparture = tr.presolveDomains[dv][0]
                    break

    if depotIndex >= 0 and departureVarNames[depotIndex] == "":
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
            if ci notin varElementCIs: continue
            let arrElems = tr.presolveResolveVarElems(con.args[1])
            if arrElems.len == n and arrElems[depotIndex].kind == FznIntLit:
                depotDeparture = arrElems[depotIndex].intVal
                break

    if depotIndex < 0: return false

    foundMax[depotIndex] = true
    earlyTimes[depotIndex] = 0

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_max": continue
        if con.args.len < 3: continue

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

        for l in 0..<n:
            if foundMax[l]: continue
            if arrivalVarNames[l] == aArg.ident and departureVarNames[l] == cArg.ident:
                earlyTimes[l] = earlyVal
                intMaxCIs[l] = ci
                foundMax[l] = true
                break

    for i in 0..<n:
        if not foundMax[i]: return false

    # Step 6: Extract late times from departure domain upper bounds
    var lateTimes = newSeq[int](n)
    for i in 0..<n:
        let dv = departureVarNames[i]
        if dv == "":
            lateTimes[i] = high(int) div 2
            let av = arrivalVarNames[i]
            for decl in tr.model.variables:
                if not decl.isArray and decl.name == av:
                    case decl.varType.kind
                    of FznIntRange:
                        lateTimes[i] = decl.varType.hi
                    else: discard
                    break
            continue
        if dv in tr.presolveDomains:
            lateTimes[i] = tr.presolveDomains[dv][^1]
            continue
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

    # Step 7: Assemble the candidate
    var consumed = initPackedSet[int]()
    consumed.incl(circuitCI)
    for i in 0..<n:
        consumed.incl(constElementCIs[i])
        consumed.incl(varElementCIs[i])
        consumed.incl(linEqCIs[i])
        if i != depotIndex:
            consumed.incl(intMaxCIs[i])

    var channelVars: seq[string]
    for i in 0..<n:
        channelVars.add(durToPredVars[i])
        channelVars.add(departurePredVars[i])
        if departureVarNames[i] != "":
            channelVars.add(departureVarNames[i])
        channelVars.add(arrivalVarNames[i])

    cand.forward = false
    cand.linkVarNames = predVarNames
    cand.rawFixedLinks = newSeq[int](n)
    cand.distMatrix = distRows  # already dist[to][from]: row l indexed by pred value
    cand.earlyTimes = earlyTimes
    cand.lateTimes = lateTimes
    cand.outConstrained = @[]   # all arcs constrained
    cand.depotIdx = depotIndex
    cand.depotDep = depotDeparture
    cand.arrivalVars = arrivalVarNames
    cand.departureVars = departureVarNames
    cand.consumedCIs = consumed
    cand.channelVars = channelVars
    cand.timeVarNames = @[]     # equality form: no projection, no verification needed
    cand.useMaxMetric = false
    cand.objectiveWeight = 1    # legacy behavior: optimizer bounds arrival at depot
    cand.objectiveMetricLo = 0
    cand.objectiveConstOffset = 0
    return true


proc tryMatchSuccFormCircuitTime(tr: var FznTranslator, circuitCI: int,
                                 elems: seq[FznExpr],
                                 cand: var CircuitTimeCandidate): bool =
    ## VRP pattern: inequality time chain on successor variables. Fixed
    ## (literal) successor entries are allowed; nodes without time triples
    ## become unconstrained arcs (clock reset).
    let n = elems.len
    var linkVarNames = newSeq[string](n)
    var rawFixedLinks = newSeq[int](n)
    var nodeOfLinkVar: Table[string, int]
    var nVarNodes = 0
    for i, e in elems:
        case e.kind
        of FznIdent:
            if e.ident in nodeOfLinkVar: return false  # duplicated var: ambiguous
            linkVarNames[i] = e.ident
            nodeOfLinkVar[e.ident] = i
            inc nVarNodes
        of FznIntLit:
            linkVarNames[i] = ""
            rawFixedLinks[i] = e.intVal
            if e.intVal < 1 or e.intVal > n: return false  # require 1-based values
        else:
            return false
    if nVarNodes == 0: return false

    # The forward walk indexes distance rows by raw successor value - 1, so the
    # circuit must be 1-based. Verified here (before any consumption).
    for vn in linkVarNames:
        if vn == "": continue
        let (lo, hi) = tr.circuitTimeDomainBounds(vn)
        if lo < 1 or hi > n: return false

    # Step 1: constant distance-row elements indexed by link vars
    var distRows = newSeq[seq[int]](n)
    var durVars = newSeq[string](n)
    var constElemCI = newSeq[int](n)
    var hasDist = newSeq[bool](n)
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin ["array_int_element", "array_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args[0].kind != FznIdent: continue
        let nodeIdx = nodeOfLinkVar.getOrDefault(con.args[0].ident, -1)
        if nodeIdx < 0 or hasDist[nodeIdx]: continue
        let row = try: tr.resolveIntArray(con.args[1])
                  except ValueError, KeyError: continue
        if row.len != n: continue
        if con.args[2].kind != FznIdent: continue
        distRows[nodeIdx] = row
        durVars[nodeIdx] = con.args[2].ident
        constElemCI[nodeIdx] = ci
        hasDist[nodeIdx] = true

    # Step 2: var elements on a shared time array, indexed by the same link vars
    var timeElems: seq[FznExpr]
    var atVars = newSeq[string](n)
    var varElemCI = newSeq[int](n)
    var hasAt = newSeq[bool](n)
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args[0].kind != FznIdent: continue
        let nodeIdx = nodeOfLinkVar.getOrDefault(con.args[0].ident, -1)
        if nodeIdx < 0 or hasAt[nodeIdx]: continue
        if not hasDist[nodeIdx]: continue
        let arrElems = tr.presolveResolveVarElems(con.args[1])
        if arrElems.len != n: continue
        var shapeOk = true
        for e in arrElems:
            if e.kind notin {FznIdent, FznIntLit}:
                shapeOk = false
                break
        if not shapeOk: continue
        if timeElems.len == 0:
            timeElems = arrElems
        else:
            var same = true
            for k in 0..<n:
                if arrElems[k].kind != timeElems[k].kind:
                    same = false
                    break
                case arrElems[k].kind
                of FznIdent:
                    if arrElems[k].ident != timeElems[k].ident:
                        same = false
                of FznIntLit:
                    if arrElems[k].intVal != timeElems[k].intVal:
                        same = false
                else:
                    same = false
                if not same: break
            if not same: continue
        if con.args[2].kind != FznIdent: continue
        atVars[nodeIdx] = con.args[2].ident
        varElemCI[nodeIdx] = ci
        hasAt[nodeIdx] = true

    if timeElems.len == 0: return false

    # Step 3: per-node time variable or fixed value
    var timeVarNames = newSeq[string](n)
    var timeFixed = newSeq[bool](n)
    var timeFixedVal = newSeq[int](n)
    for i, e in timeElems:
        case e.kind
        of FznIntLit:
            timeFixed[i] = true
            timeFixedVal[i] = e.intVal
        of FznIdent:
            timeVarNames[i] = e.ident
            let (isFixed, v) = tr.circuitTimeFixedValue(e)
            if isFixed:
                timeFixed[i] = true
                timeFixedVal[i] = v
        else:
            return false

    # Internal vars must be distinct from time and link vars
    var timeNameSet: HashSet[string]
    for tn in timeVarNames:
        if tn != "": timeNameSet.incl(tn)
    for i in 0..<n:
        if hasAt[i]:
            if atVars[i] in timeNameSet or atVars[i] in nodeOfLinkVar: return false
            if durVars[i] in timeNameSet or durVars[i] in nodeOfLinkVar: return false

    # Step 4: int_lin_le time-propagation constraints
    var atOwner: Table[string, int]
    var durOwner: Table[string, int]
    for i in 0..<n:
        if hasAt[i]:
            atOwner[atVars[i]] = i
            durOwner[durVars[i]] = i

    var linLeCI = newSeq[int](n)
    var hasLinLe = newSeq[bool](n)
    var serviceTimes = newSeq[int](n)
    for ci, con in tr.model.constraints:
        if stripSolverPrefix(con.name) != "int_lin_le": continue
        if con.args.len < 3: continue
        var coeffs: seq[int]
        let coeffsArg = con.args[0]
        if coeffsArg.kind == FznArrayLit:
            var allLit = true
            for e in coeffsArg.elems:
                if e.kind != FznIntLit:
                    allLit = false
                    break
                coeffs.add(e.intVal)
            if not allLit: continue
        elif coeffsArg.kind == FznIdent:
            coeffs = try: tr.resolveIntArray(coeffsArg)
                     except ValueError, KeyError: continue
        else: continue
        if con.args[2].kind != FznIntLit: continue
        let rhs = con.args[2].intVal
        let varsArg = con.args[1]
        if varsArg.kind != FznArrayLit: continue
        var varNames: seq[string]
        var allIdent = true
        for e in varsArg.elems:
            if e.kind != FznIdent:
                allIdent = false
                break
            varNames.add(e.ident)
        if not allIdent: continue
        if coeffs.len != varNames.len: continue

        if coeffs.len == 3:
            # time_i + d_i - at_i <= -service_i  (coeffs perm of [1,1,-1])
            var negIdx = -1
            var nNeg = 0
            for vi, c in coeffs:
                if c == -1:
                    negIdx = vi
                    inc nNeg
                elif c != 1:
                    nNeg = -100  # invalid coefficient
            if nNeg != 1: continue
            let nodeIdx = atOwner.getOrDefault(varNames[negIdx], -1)
            if nodeIdx < 0 or hasLinLe[nodeIdx]: continue
            if timeFixed[nodeIdx] and timeVarNames[nodeIdx] == "": continue
            # the two +1 vars: one is d_nodeIdx, the other the node's own time var
            var posNames: seq[string]
            for vi in 0..<3:
                if vi != negIdx: posNames.add(varNames[vi])
            var matched = false
            if posNames[0] == durVars[nodeIdx] and posNames[1] == timeVarNames[nodeIdx]:
                matched = true
            elif posNames[1] == durVars[nodeIdx] and posNames[0] == timeVarNames[nodeIdx]:
                matched = true
            if not matched: continue
            linLeCI[nodeIdx] = ci
            hasLinLe[nodeIdx] = true
            serviceTimes[nodeIdx] = -rhs
        elif coeffs.len == 2:
            # d_i - at_i <= -service_i - time_i  (node's time is fixed)
            var posIdx = -1
            var negIdx = -1
            if coeffs == @[1, -1]:
                posIdx = 0; negIdx = 1
            elif coeffs == @[-1, 1]:
                posIdx = 1; negIdx = 0
            else: continue
            let nodeIdx = atOwner.getOrDefault(varNames[negIdx], -1)
            if nodeIdx < 0 or hasLinLe[nodeIdx]: continue
            if varNames[posIdx] != durVars[nodeIdx]: continue
            if not timeFixed[nodeIdx]: continue
            linLeCI[nodeIdx] = ci
            hasLinLe[nodeIdx] = true
            serviceTimes[nodeIdx] = -rhs - timeFixedVal[nodeIdx]

    # Step 5: matched (out-constrained) node set
    var outConstrained = newSeq[bool](n)
    var nMatched = 0
    for i in 0..<n:
        outConstrained[i] = hasDist[i] and hasAt[i] and hasLinLe[i]
        if outConstrained[i]: inc nMatched
    if nMatched == 0: return false

    # Step 6: distance matrix [to][from] with service times folded in.
    # distRows[from] is indexed by raw successor value (1-based), aligning with
    # 0-based node index `to` because the circuit is verified 1-based above.
    var distMatrix = newSeq[seq[int]](n)
    for toN in 0..<n:
        distMatrix[toN] = newSeq[int](n)
    for fromN in 0..<n:
        if outConstrained[fromN]:
            for toN in 0..<n:
                distMatrix[toN][fromN] = distRows[fromN][toN] + serviceTimes[fromN]

    # Step 7: early/late times from fixed values or domains
    var earlyTimes = newSeq[int](n)
    var lateTimes = newSeq[int](n)
    for i in 0..<n:
        if timeFixed[i]:
            earlyTimes[i] = timeFixedVal[i]
            lateTimes[i] = timeFixedVal[i]
        else:
            let (lo, hi) = tr.circuitTimeDomainBounds(timeVarNames[i])
            earlyTimes[i] = lo
            lateTimes[i] = hi

    # Step 8: depot anchor = first fixed-time node
    var depotIdx = -1
    for i in 0..<n:
        if timeFixed[i]:
            depotIdx = i
            break
    if depotIdx < 0: return false

    # Step 9: assemble candidate
    var consumed = initPackedSet[int]()
    consumed.incl(circuitCI)
    var channelVars: seq[string]
    for i in 0..<n:
        if outConstrained[i]:
            consumed.incl(constElemCI[i])
            consumed.incl(varElemCI[i])
            consumed.incl(linLeCI[i])
            channelVars.add(durVars[i])
            channelVars.add(atVars[i])
    for tn in timeVarNames:
        if tn != "": channelVars.add(tn)

    var metricLo = earlyTimes[depotIdx]
    for i in 0..<n:
        if earlyTimes[i] > metricLo: metricLo = earlyTimes[i]

    cand.forward = true
    cand.linkVarNames = linkVarNames
    cand.rawFixedLinks = rawFixedLinks
    cand.distMatrix = distMatrix
    cand.earlyTimes = earlyTimes
    cand.lateTimes = lateTimes
    cand.outConstrained = outConstrained
    cand.depotIdx = depotIdx
    cand.depotDep = timeFixedVal[depotIdx]
    cand.arrivalVars = newSeq[string](n)   # times are written back as departures
    cand.departureVars = timeVarNames
    cand.consumedCIs = consumed
    cand.channelVars = channelVars
    cand.timeVarNames = timeVarNames
    cand.useMaxMetric = true
    cand.objectiveWeight = 0               # set by verification when linked
    cand.objectiveMetricLo = metricLo
    cand.objectiveConstOffset = 0
    return true


proc verifyCircuitTimeCandidates(tr: var FznTranslator,
                                 candidates: var seq[CircuitTimeCandidate]) =
    ## Projection-soundness verification for successor-form (inequality)
    ## candidates, plus objective linkage extraction. Predecessor-form
    ## candidates compute exact (equality) times and are exempt. Drops
    ## candidates that fail; their constraints then translate normally.
    var allConsumed = initPackedSet[int]()
    for cand in candidates:
        for ci in cand.consumedCIs.items:
            allConsumed.incl(ci)

    # Named-array expansion table. tr.arrayElementNames is not populated yet
    # at detection time (translateVariables runs later), so resolve array
    # declarations directly.
    var arrayDeclElems: Table[string, seq[string]]
    for decl in tr.model.variables:
        if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
            var names: seq[string]
            for e in decl.value.elems:
                if e.kind == FznIdent:
                    names.add(e.ident)
            if names.len > 0:
                arrayDeclElems[decl.name] = names

    let isMinimize = tr.model.solve.kind == Minimize
    var objName = ""
    if tr.model.solve.kind in {Minimize, Maximize} and
       tr.model.solve.objective != nil and tr.model.solve.objective.kind == FznIdent:
        objName = tr.model.solve.objective.ident

    var keep = newSeq[bool](candidates.len)
    var maxCoverage: Table[string, bool]   # max output -> covers the full time set

    for k in 0..<candidates.len:
        keep[k] = true
        if not candidates[k].forward: continue   # equality form: exempt

        var timeSet: HashSet[string]
        for tn in candidates[k].timeVarNames:
            if tn != "": timeSet.incl(tn)
        var internalSet: HashSet[string]
        for vn in candidates[k].channelVars:
            if vn notin timeSet: internalSet.incl(vn)

        var maxOutputs: seq[string]
        var maxCIs: seq[int]
        var ok = true
        for ci, con in tr.model.constraints:
            if ci in allConsumed: continue
            var refsTime = false
            var refsInternal = false
            for arg in con.args:
                case arg.kind
                of FznIdent:
                    if arg.ident in timeSet: refsTime = true
                    if arg.ident in internalSet: refsInternal = true
                    if arg.ident in arrayDeclElems:
                        for en in arrayDeclElems[arg.ident]:
                            if en in timeSet: refsTime = true
                            if en in internalSet: refsInternal = true
                of FznArrayLit:
                    for e in arg.elems:
                        if e.kind == FznIdent:
                            if e.ident in timeSet: refsTime = true
                            if e.ident in internalSet: refsInternal = true
                else: discard
            if refsInternal:
                ok = false
                break
            if not refsTime: continue
            # Allowed observer: array_int_maximum whose variable inputs are a
            # subset of this instance's time variables (max is increasing in
            # them, so minimizing the times remains WLOG if the output is
            # observed minimize-monotonically — checked below).
            let cname = stripSolverPrefix(con.name)
            if cname != "array_int_maximum" or con.args.len < 2 or
               con.args[0].kind != FznIdent:
                ok = false
                break
            let arrElems = tr.presolveResolveVarElems(con.args[1])
            var entryNames: HashSet[string]
            var entryConsts: seq[int]
            var shapeOk = true
            for e in arrElems:
                case e.kind
                of FznIdent: entryNames.incl(e.ident)
                of FznIntLit: entryConsts.add(e.intVal)
                else: shapeOk = false
            if not shapeOk:
                ok = false
                break
            var onlyOurTimes = true
            for en in entryNames:
                if en notin timeSet: onlyOurTimes = false
            if not onlyOurTimes:
                ok = false
                break
            # Full coverage (needed for bound distribution): all time vars
            # present and constant entries matching the fixed node times.
            var fixedVals: seq[int]
            for i, tn in candidates[k].timeVarNames:
                if tn == "": fixedVals.add(candidates[k].earlyTimes[i])
            let covered = entryNames == timeSet and
                          entryConsts.sorted() == fixedVals.sorted()
            maxOutputs.add(con.args[0].ident)
            maxCIs.add(ci)
            maxCoverage[con.args[0].ident] = covered
        if not ok:
            keep[k] = false
            continue
        if maxOutputs.len > 0 and not isMinimize:
            # Times observed through maxima but objective direction does not
            # justify earliest-time projection.
            keep[k] = false
            continue
        candidates[k].maxOutputs = maxOutputs
        candidates[k].maxCIs = maxCIs

    # Objective linkage: usages of the collected maxima must be confined to a
    # single linear definition of the objective (or the objective itself), with
    # positive effective weights under minimization.
    var maxOwner: Table[string, int]
    var maxCIset: PackedSet[int]
    for k in 0..<candidates.len:
        if not keep[k] or not candidates[k].forward: continue
        for mi, m in candidates[k].maxOutputs:
            maxOwner[m] = k
            maxCIset.incl(candidates[k].maxCIs[mi])

    if maxOwner.len > 0:
        var objLinEqCI = -1
        for ci, con in tr.model.constraints:
            if ci in allConsumed or ci in maxCIset: continue
            var refs: seq[string]
            for arg in con.args:
                case arg.kind
                of FznIdent:
                    if arg.ident in maxOwner: refs.add(arg.ident)
                    if arg.ident in arrayDeclElems:
                        for en in arrayDeclElems[arg.ident]:
                            if en in maxOwner: refs.add(en)
                of FznArrayLit:
                    for e in arg.elems:
                        if e.kind == FznIdent and e.ident in maxOwner:
                            refs.add(e.ident)
                else: discard
            if refs.len == 0: continue
            var allowed = false
            if objName != "" and stripSolverPrefix(con.name) == "int_lin_eq" and
               con.hasAnnotation("defines_var"):
                let ann = con.getAnnotation("defines_var")
                if ann.args.len > 0 and ann.args[0].kind == FznIdent and
                   ann.args[0].ident == objName:
                    if objLinEqCI < 0 or objLinEqCI == ci:
                        objLinEqCI = ci
                        allowed = true
            if not allowed:
                for m in refs:
                    keep[maxOwner[m]] = false

        # Direct case: a max output IS the objective
        for m, owner in maxOwner:
            if m == objName and keep[owner]:
                if maxCoverage.getOrDefault(m, false) and
                   candidates[owner].maxOutputs.len == 1:
                    candidates[owner].objectiveWeight = 1
                    candidates[owner].objectiveConstOffset = 0

        # Linear case: objective = sum w_i * m_i + offset
        if objLinEqCI >= 0 and objName != "":
            let con = tr.model.constraints[objLinEqCI]
            var coeffs: seq[int]
            let coeffsArg = con.args[0]
            if coeffsArg.kind == FznArrayLit:
                for e in coeffsArg.elems:
                    if e.kind == FznIntLit: coeffs.add(e.intVal)
            elif coeffsArg.kind == FznIdent:
                coeffs = try: tr.resolveIntArray(coeffsArg)
                         except ValueError, KeyError: @[]
            var varNames: seq[string]
            var rhsVal = 0
            var parseOk = con.args.len >= 3 and con.args[2].kind == FznIntLit
            if parseOk:
                rhsVal = con.args[2].intVal
                if con.args[1].kind == FznArrayLit:
                    for e in con.args[1].elems:
                        if e.kind == FznIdent:
                            varNames.add(e.ident)
                        else:
                            parseOk = false
                else:
                    parseOk = false
            if parseOk and coeffs.len == varNames.len:
                var cObj = 0
                for vi, vn in varNames:
                    if vn == objName: cObj = coeffs[vi]
                # Pass 1: drop candidates whose max enters the objective with a
                # non-positive effective weight (w = -c_v / c_obj): minimizing
                # the objective then presses those times UP, so the
                # earliest-time projection is unsound.
                for vi, vn in varNames:
                    if vn == objName or vn notin maxOwner: continue
                    let signNum = -coeffs[vi] * (if cObj < 0: -1 else: 1)
                    if signNum <= 0:
                        keep[maxOwner[vn]] = false
                # Pass 2: cleanliness — bound distribution is only valid when
                # EVERY non-objective term is a full-coverage max owned by a
                # surviving candidate (a dropped or partial term's objective
                # contribution would be missing from the bound formula).
                var clean = cObj == 1 or cObj == -1
                for vi, vn in varNames:
                    if vn == objName: continue
                    if vn notin maxOwner or not keep[maxOwner[vn]] or
                       not maxCoverage.getOrDefault(vn, false):
                        clean = false
                        break
                if clean:
                    for vi, vn in varNames:
                        if vn == objName or vn notin maxOwner: continue
                        let owner = maxOwner[vn]
                        if not keep[owner]: continue
                        let w = -coeffs[vi] * cObj
                        candidates[owner].objectiveWeight += w
                        candidates[owner].objectiveConstOffset = rhsVal * cObj

    # Compact the candidate list
    var kept: seq[CircuitTimeCandidate]
    for k in 0..<candidates.len:
        if keep[k]:
            kept.add(candidates[k])
        else:
            stderr.writeLine("[FZN] Circuit-time candidate on circuit ci=" &
                             $candidates[k].circuitCI &
                             " failed projection-soundness verification, skipped")
    candidates = kept


proc detectCircuitTimePropagation(tr: var FznTranslator) =
    ## Detect circuit-time patterns (one candidate per crusher_circuit), verify
    ## soundness, then consume the matched constraints and register instances.
    var candidates: seq[CircuitTimeCandidate]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "crusher_circuit": continue
        if con.args.len < 1: continue

        let arg = con.args[0]
        var elems: seq[FznExpr]
        case arg.kind
        of FznArrayLit:
            elems = arg.elems
        of FznIdent:
            for decl in tr.model.variables:
                if decl.isArray and decl.name == arg.ident:
                    if decl.value != nil and decl.value.kind == FznArrayLit:
                        elems = decl.value.elems
                    break
        else:
            discard
        if elems.len < 3: continue

        var cand = CircuitTimeCandidate(circuitCI: ci)
        if tr.tryMatchPredFormCircuitTime(ci, elems, cand):
            candidates.add(cand)
        else:
            cand = CircuitTimeCandidate(circuitCI: ci)
            if tr.tryMatchSuccFormCircuitTime(ci, elems, cand):
                candidates.add(cand)

    if candidates.len == 0: return

    tr.verifyCircuitTimeCandidates(candidates)

    for cand in candidates:
        for ci in cand.consumedCIs.items:
            tr.definingConstraints.incl(ci)
        for vn in cand.channelVars:
            tr.channelVarNames.incl(vn)
            tr.definedVarNames.excl(vn)
        tr.circuitTimeCandidates.add(cand)
        let form = if cand.forward: "successor" else: "predecessor"
        stderr.writeLine("[FZN] Detected circuit-time-propagation pattern (" & form &
                         " form): " & $cand.linkVarNames.len & " nodes, depot=" &
                         $(cand.depotIdx + 1) &
                         (if cand.objectiveWeight > 0: ", objective weight " & $cand.objectiveWeight
                          else: ""))


proc emitCircuitTimePropConstraint(tr: var FznTranslator) =
    ## Emit the CircuitTimeProp constraints after variable positions are created.
    for cand in tr.circuitTimeCandidates:
        let n = cand.linkVarNames.len

        var linkPositions = newSeq[int](n)
        var positionsOk = true
        for i in 0..<n:
            if cand.linkVarNames[i] == "":
                linkPositions[i] = -1
            elif cand.linkVarNames[i] in tr.varPositions:
                linkPositions[i] = tr.varPositions[cand.linkVarNames[i]]
            else:
                stderr.writeLine("[FZN] CircuitTimeProp: link var " &
                                 cand.linkVarNames[i] & " not found, aborting instance")
                positionsOk = false
                break
        if not positionsOk: continue

        # Detect value offset (same logic as circuit translation). Successor
        # form is verified 1-based at detection time.
        var valueOffset = 1
        if not cand.forward:
            var hasZero = false
            var hasN = false
            for pos in linkPositions:
                if pos < 0: continue
                let dom = tr.sys.baseArray.domain[pos]
                for v in dom:
                    if v == 0: hasZero = true
                    if v == n: hasN = true
            valueOffset = if hasZero and not hasN: 0 else: 1

        var fixedLinks = newSeq[int](n)
        for i in 0..<n:
            if cand.linkVarNames[i] == "":
                fixedLinks[i] = cand.rawFixedLinks[i] - valueOffset

        var arrivalPositions = newSeq[int](n)
        var departurePositions = newSeq[int](n)
        for i in 0..<n:
            let av = if i < cand.arrivalVars.len: cand.arrivalVars[i] else: ""
            arrivalPositions[i] = if av != "" and av in tr.varPositions: tr.varPositions[av]
                                  else: -1
            let dv = if i < cand.departureVars.len: cand.departureVars[i] else: ""
            departurePositions[i] = if dv != "" and dv in tr.varPositions: tr.varPositions[dv]
                                    else: -1

        tr.sys.addConstraint(circuitTimeProp[int](
            linkPositions,
            cand.distMatrix,
            cand.earlyTimes,
            cand.lateTimes,
            cand.depotIdx,
            cand.depotDep,
            arrivalPositions,
            departurePositions,
            valueOffset,
            cand.forward,
            fixedLinks,
            cand.outConstrained,
            cand.useMaxMetric,
            cand.objectiveWeight,
            cand.objectiveMetricLo,
            cand.objectiveConstOffset
        ))

        # NOTE: No separate allDifferent — the CircuitTimeProp circuit penalty already
        # penalizes duplicate values (they create tail nodes). Adding allDifferent as a
        # separate constraint creates competing penalties that trap the search in local minima.

        let form = if cand.forward: "successor" else: "predecessor"
        stderr.writeLine("[FZN] Emitted CircuitTimeProp constraint (" & form &
                         " form): " & $n & " nodes, offset=" & $valueOffset)
