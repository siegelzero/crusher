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
##    variable is otherwise unobserved, or observed minimize-monotonically:
##    either through array_int_maximum outputs that enter a MINIMIZED linear
##    objective with positive weights, or directly as a term of the
##    objective-defining int_lin_eq with positive effective weight (CVRP-style
##    objective = sum of arrival times) — then assigning every time its minimum
##    feasible value is WLOG. This is verified before any constraint is
##    consumed; candidates that fail verification are dropped and their
##    constraints translate normally.
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
##    across instances (see applyCircuitTimeObjectiveBounds). When time
##    variables enter the objective directly, the per-node weights are recorded
##    as a weighted-SUM metric on the instance instead, with the same effect.


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

    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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

    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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

    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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
        for ci in 0 ..< tr.model.constraints.len:
            let con {.cursor.} = tr.model.constraints[ci]
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

    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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


proc circuitTimeParseLinEq(tr: FznTranslator, con: FznConstraint):
        tuple[ok: bool, coeffs: seq[int], varNames: seq[string], rhs: int] =
    ## Parse an int_lin_eq into (coeffs, var names, rhs). The variable array
    ## may be a literal or a named array; constant terms are folded into the
    ## rhs. ok=false when the shapes disagree.
    if con.args.len < 3 or con.args[2].kind != FznIntLit:
        return (false, @[], @[], 0)
    var rawCoeffs: seq[int]
    let coeffsArg = con.args[0]
    if coeffsArg.kind == FznArrayLit:
        for e in coeffsArg.elems:
            if e.kind != FznIntLit:
                return (false, @[], @[], 0)
            rawCoeffs.add(e.intVal)
    elif coeffsArg.kind == FznIdent:
        rawCoeffs = try: tr.resolveIntArray(coeffsArg)
                    except ValueError, KeyError: @[]
    else:
        return (false, @[], @[], 0)
    let terms = tr.presolveResolveVarElems(con.args[1])
    if rawCoeffs.len != terms.len or terms.len == 0:
        return (false, @[], @[], 0)
    var coeffs: seq[int]
    var varNames: seq[string]
    var rhs = con.args[2].intVal
    for ti, e in terms:
        case e.kind
        of FznIdent:
            coeffs.add(rawCoeffs[ti])
            varNames.add(e.ident)
        of FznIntLit:
            rhs -= rawCoeffs[ti] * e.intVal
        else:
            return (false, @[], @[], 0)
    return (true, coeffs, varNames, rhs)


proc tryMatchSuccFormAccumulators(tr: var FznTranslator, circuitCI: int,
                                  elems: seq[FznExpr],
                                  claimed: PackedSet[int],
                                  accumArrays: var HashSet[string],
                                  outCands: var seq[CircuitTimeCandidate]) =
    ## Equality accumulator chains along a circuit (one candidate per value
    ## array). Pattern, per node n with a variable link:
    ##   array_var_int_element(link[n], A, r_n) :: defines_var(r_n)
    ##   int_lin_eq: r_n = A_n + offset_n            (offset_n constant)
    ## or, when the element result is a constant:
    ##   array_var_int_element(link[n], A, c)        (A_n fixed; offset = c - A_n)
    ## i.e. A[link[n]] = A[n] + offset_n. Values are anchored at fixed nodes
    ## and computed exactly along the tour, the variables' domain bounds act
    ## as two-sided windows (CVRP capacity = load domain), and no projection-
    ## soundness verification is needed. Nodes without a matched out-arc reset
    ## the accumulator at their successor, which is only exact when every node
    ## they can link to holds a fixed value (e.g. giant-tour end depots
    ## wrapping to fixed-load start depots); otherwise the family is rejected
    ## (e.g. vehicle-painting chains, whose anchor sits at segment ENDS).
    let n = elems.len
    var linkVarNames = newSeq[string](n)
    var rawFixedLinks = newSeq[int](n)
    var nodeOfLinkVar: Table[string, int]
    var nVarNodes = 0
    for i, e in elems:
        case e.kind
        of FznIdent:
            if e.ident in nodeOfLinkVar: return  # duplicated var: ambiguous
            linkVarNames[i] = e.ident
            nodeOfLinkVar[e.ident] = i
            inc nVarNodes
        of FznIntLit:
            linkVarNames[i] = ""
            rawFixedLinks[i] = e.intVal
            if e.intVal < 1 or e.intVal > n: return  # require 1-based values
        else:
            return
    if nVarNodes == 0: return
    for vn in linkVarNames:
        if vn == "": continue
        let (lo, hi) = tr.circuitTimeDomainBounds(vn)
        if lo < 1 or hi > n: return

    # Pre-index untaken int_lin_eq constraints by referenced variable for the
    # offset lookups (r_n = A_n + offset_n).
    var linEqByVar: Table[string, seq[int]]
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        if ci in claimed: continue
        if stripSolverPrefix(con.name) != "int_lin_eq": continue
        let (parsed, _, eqVars, _) = tr.circuitTimeParseLinEq(con)
        if not parsed: continue
        for vn in eqVars:
            linEqByVar.mgetOrPut(vn, @[]).add(ci)

    # Group var-elements indexed by this circuit's link vars into families by
    # (named) value array.
    type AccElemInfo = object
        ci: int
        resultName: string   # "" when the result is a constant
        resultConst: int
        hasDefVar: bool
    var families: OrderedTable[string, Table[int, AccElemInfo]]
    var familyElems: Table[string, seq[FznExpr]]
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        if ci in claimed: continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]:
            continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent: continue
        let nodeIdx = nodeOfLinkVar.getOrDefault(con.args[0].ident, -1)
        if nodeIdx < 0: continue
        if con.args[1].kind != FznIdent: continue   # families keyed by named arrays
        let arrName = con.args[1].ident
        var info = AccElemInfo(ci: ci)
        case con.args[2].kind
        of FznIdent:
            # defines_var is required for introduced result vars (checked at
            # match time); the unified zero-offset form A[link[n]] = A_n has
            # the node's own var as result and carries no annotation.
            info.hasDefVar = con.hasAnnotation("defines_var")
            info.resultName = con.args[2].ident
        of FznIntLit:
            info.resultConst = con.args[2].intVal
        else:
            continue
        if arrName notin families:
            let arrElems = tr.presolveResolveVarElems(con.args[1])
            if arrElems.len != n: continue
            var shapeOk = true
            for e in arrElems:
                if e.kind notin {FznIdent, FznIntLit}:
                    shapeOk = false
                    break
            if not shapeOk: continue
            families[arrName] = initTable[int, AccElemInfo]()
            familyElems[arrName] = arrElems
        if nodeIdx notin families[arrName]:
            families[arrName][nodeIdx] = info

    for arrName, byNode in families.pairs:
        # One instance per value array across all circuits: a redundant
        # mirror circuit (e.g. predecessor of an inverse pair) chains the same
        # values and would emit a duplicate, possibly on channelized links.
        if arrName in accumArrays: continue
        # Per-node value variable or fixed value
        var valueVarNames = newSeq[string](n)
        var valueFixed = newSeq[bool](n)
        var valueFixedVal = newSeq[int](n)
        var familyOk = true
        for i, e in familyElems[arrName]:
            case e.kind
            of FznIntLit:
                valueFixed[i] = true
                valueFixedVal[i] = e.intVal
            of FznIdent:
                valueVarNames[i] = e.ident
                let (isFixed, v) = tr.circuitTimeFixedValue(e)
                if isFixed:
                    valueFixed[i] = true
                    valueFixedVal[i] = v
            else:
                familyOk = false
                break
        if not familyOk: continue

        var valueNameSet: HashSet[string]
        for vn in valueVarNames:
            if vn != "": valueNameSet.incl(vn)

        # Per-node out-arc: constant offset + the constraints it consumes
        var outConstrained = newSeq[bool](n)
        var offsets = newSeq[int](n)
        var elemCI = newSeq[int](n)
        var eqCI = newSeq[int](n)
        var nMatched = 0
        for i in 0..<n:
            if i notin byNode: continue
            let info = byNode[i]
            if info.resultName == "":
                # A[link[i]] = const: needs A_i fixed to derive the offset
                if not valueFixed[i]: continue
                outConstrained[i] = true
                offsets[i] = info.resultConst - valueFixedVal[i]
                elemCI[i] = info.ci
                eqCI[i] = -1
                inc nMatched
                continue
            if info.resultName == valueVarNames[i]:
                # Unified zero-offset chain: A[link[i]] = A_i (vehicle painting)
                outConstrained[i] = true
                offsets[i] = 0
                elemCI[i] = info.ci
                eqCI[i] = -1
                inc nMatched
                continue
            if not info.hasDefVar: continue
            if info.resultName in valueNameSet or info.resultName in nodeOfLinkVar:
                continue
            for ci in linEqByVar.getOrDefault(info.resultName, @[]):
                let (parsed, coeffs, eqVars, rhs) =
                    tr.circuitTimeParseLinEq(tr.model.constraints[ci])
                if not parsed: continue
                var off = 0
                var matched = false
                if eqVars.len == 2:
                    # c_A*A_i + c_r*r = rhs with c_A = -c_r, |c_r| = 1
                    # => r = A_i + rhs*c_r
                    var aIdx = -1
                    var rIdx = -1
                    for vi, vn in eqVars:
                        if vn == info.resultName: rIdx = vi
                        elif vn == valueVarNames[i]: aIdx = vi
                    if aIdx >= 0 and rIdx >= 0 and
                       coeffs[rIdx] in [-1, 1] and coeffs[aIdx] == -coeffs[rIdx]:
                        off = rhs * coeffs[rIdx]
                        matched = true
                elif eqVars.len == 1 and eqVars[0] == info.resultName and
                     coeffs[0] in [-1, 1] and valueFixed[i]:
                    # A_i folded into the rhs as a constant: r = rhs*c_r
                    off = rhs * coeffs[0] - valueFixedVal[i]
                    matched = true
                if matched:
                    outConstrained[i] = true
                    offsets[i] = off
                    elemCI[i] = info.ci
                    eqCI[i] = ci
                    inc nMatched
                    break
        if nMatched == 0: continue

        # Anchor: first fixed-value node
        var depotIdx = -1
        for i in 0..<n:
            if valueFixed[i]:
                depotIdx = i
                break
        if depotIdx < 0: continue

        # Reset guard (exactness): every chained segment must have an anchored
        # end in any closed tour. Forward anchoring: every node a reset arc can
        # lead to (a segment start) is value-fixed (CVRP load: start depots).
        # Backward anchoring: every reset source (a segment end) is itself
        # value-fixed (vehicle painting: depots fixed, customers chained).
        # The runtime walk anchors each segment from whichever end is fixed.
        var forwardGuard = true
        var backwardGuard = true
        for i in 0..<n:
            if outConstrained[i]: continue
            if not valueFixed[i]:
                backwardGuard = false
            if linkVarNames[i] == "":
                if not valueFixed[rawFixedLinks[i] - 1]:
                    forwardGuard = false
            else:
                let (lo, hi) = tr.circuitTimeDomainBounds(linkVarNames[i])
                for v in lo..hi:
                    if not valueFixed[v - 1]:
                        forwardGuard = false
                        break
            if not forwardGuard and not backwardGuard: break
        if not (forwardGuard or backwardGuard): continue

        # Two-sided windows from fixed values or domain bounds
        var earlyTimes = newSeq[int](n)
        var lateTimes = newSeq[int](n)
        for i in 0..<n:
            if valueFixed[i]:
                earlyTimes[i] = valueFixedVal[i]
                lateTimes[i] = valueFixedVal[i]
            else:
                let (lo, hi) = tr.circuitTimeDomainBounds(valueVarNames[i])
                earlyTimes[i] = lo
                lateTimes[i] = hi

        # Offset matrix: dist[to][from] = offset_from (uniform rows)
        var distMatrix = newSeq[seq[int]](n)
        for toN in 0..<n:
            distMatrix[toN] = newSeq[int](n)
        for fromN in 0..<n:
            if outConstrained[fromN]:
                for toN in 0..<n:
                    distMatrix[toN][fromN] = offsets[fromN]

        var consumed = initPackedSet[int]()
        consumed.incl(circuitCI)
        var channelVars: seq[string]
        for i in 0..<n:
            if outConstrained[i]:
                consumed.incl(elemCI[i])
                if eqCI[i] >= 0:
                    consumed.incl(eqCI[i])
                if byNode[i].resultName != "" and
                   byNode[i].resultName != valueVarNames[i]:
                    channelVars.add(byNode[i].resultName)
        for vn in valueVarNames:
            if vn != "": channelVars.add(vn)

        var cand = CircuitTimeCandidate(circuitCI: circuitCI)
        cand.forward = true
        cand.equalityChain = true
        cand.linkVarNames = linkVarNames
        cand.rawFixedLinks = rawFixedLinks
        cand.distMatrix = distMatrix
        cand.earlyTimes = earlyTimes
        cand.lateTimes = lateTimes
        cand.outConstrained = outConstrained
        cand.depotIdx = depotIdx
        cand.depotDep = valueFixedVal[depotIdx]
        cand.arrivalVars = newSeq[string](n)
        cand.departureVars = valueVarNames
        cand.consumedCIs = consumed
        cand.channelVars = channelVars
        cand.timeVarNames = valueVarNames
        cand.useMaxMetric = false
        accumArrays.incl(arrName)
        outCands.add(cand)
        stderr.writeLine("[FZN] Detected circuit-accumulator chain on array '" &
                         arrName & "': " & $nMatched & "/" & $n &
                         " arcs matched, anchor=" & $(depotIdx + 1))


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
    # Per candidate: CI of the objective-defining int_lin_eq observing this
    # candidate's times directly (-1 = none).
    var directCIs = newSeq[int](candidates.len)
    for k in 0..<directCIs.len: directCIs[k] = -1

    for k in 0..<candidates.len:
        keep[k] = true
        if not candidates[k].forward or candidates[k].exactChain: continue   # equality form: exempt

        var timeSet: HashSet[string]
        for tn in candidates[k].timeVarNames:
            if tn != "": timeSet.incl(tn)
        var internalSet: HashSet[string]
        for vn in candidates[k].channelVars:
            if vn notin timeSet: internalSet.incl(vn)

        var maxOutputs: seq[string]
        var maxCIs: seq[int]
        var ok = true
        for ci in 0 ..< tr.model.constraints.len:
            let con {.cursor.} = tr.model.constraints[ci]
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
            # Equality-chain instances compute exact values, so outside
            # observers of the value vars are unrestricted (only references to
            # consumed internals are disqualifying, checked above).
            if candidates[k].equalityChain: continue
            let cname = stripSolverPrefix(con.name)
            # Allowed observer 1: the objective-defining int_lin_eq referencing
            # times directly (objective = ... + sum c_v * t_v). Sound under
            # minimization iff every observed time enters with positive
            # effective weight — validated after this loop once the
            # coefficients are parsed.
            if cname == "int_lin_eq" and isMinimize and objName != "" and
               con.hasAnnotation("defines_var"):
                let ann = con.getAnnotation("defines_var")
                if ann.args.len > 0 and ann.args[0].kind == FznIdent and
                   ann.args[0].ident == objName and
                   (directCIs[k] < 0 or directCIs[k] == ci):
                    directCIs[k] = ci
                    continue
                ok = false
                break
            # Allowed observer 2: array_int_maximum whose variable inputs are a
            # subset of this instance's time variables (max is increasing in
            # them, so minimizing the times remains WLOG if the output is
            # observed minimize-monotonically — checked below).
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
        if ok and directCIs[k] >= 0:
            # Direct observer sign check: every time var of this candidate in
            # the objective equation must have positive effective weight
            # (w = -c_v / c_obj > 0), so minimizing presses each time DOWN and
            # the earliest-time projection is WLOG.
            let (parsed, coeffs, varNames, _) =
                tr.circuitTimeParseLinEq(tr.model.constraints[directCIs[k]])
            if not parsed:
                ok = false
            else:
                var cObj = 0
                for vi, vn in varNames:
                    if vn == objName: cObj = coeffs[vi]
                if cObj == 0:
                    ok = false
                else:
                    for vi, vn in varNames:
                        if vn in timeSet:
                            let signNum = -coeffs[vi] * (if cObj < 0: -1 else: 1)
                            if signNum <= 0:
                                ok = false
                                break
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

    # Times observed directly by the objective equation: time var -> candidate.
    # Candidates mixing max observers and direct terms are excluded (their
    # metric kind would be ambiguous); they stay sound but unlinked.
    var directOwner: Table[string, int]
    var directCI = -1
    var directConflict = false
    for k in 0..<candidates.len:
        if not keep[k] or not candidates[k].forward: continue
        if directCIs[k] < 0 or candidates[k].maxOutputs.len > 0: continue
        if directCI < 0:
            directCI = directCIs[k]
        elif directCI != directCIs[k]:
            directConflict = true
        for tn in candidates[k].timeVarNames:
            if tn != "": directOwner[tn] = k

    var objLinEqCI = -1
    if maxOwner.len > 0:
        for ci in 0 ..< tr.model.constraints.len:
            let con {.cursor.} = tr.model.constraints[ci]
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

    # The direct observers' equation IS the objective definition; merge it with
    # whatever the maxima usage scan found (they must agree on a single CI).
    if directConflict:
        directOwner.clear()
    elif directCI >= 0:
        if objLinEqCI < 0:
            objLinEqCI = directCI
        elif objLinEqCI != directCI:
            directOwner.clear()

    # Linear case: objective = sum w_i * max_i + sum w_v * t_v + offset
    if objLinEqCI >= 0 and objName != "":
        let (parsed, coeffs, varNames, rhsVal) =
            tr.circuitTimeParseLinEq(tr.model.constraints[objLinEqCI])
        if parsed:
            var cObj = 0
            for vi, vn in varNames:
                if vn == objName: cObj = coeffs[vi]
            # Pass 1: drop candidates whose max enters the objective with a
            # non-positive effective weight (w = -c_v / c_obj): minimizing
            # the objective then presses those times UP, so the
            # earliest-time projection is unsound. (Directly-observed times
            # were sign-checked per candidate above.)
            for vi, vn in varNames:
                if vn == objName or vn notin maxOwner: continue
                let signNum = -coeffs[vi] * (if cObj < 0: -1 else: 1)
                if signNum <= 0:
                    keep[maxOwner[vn]] = false
            # Pass 2: cleanliness — bound distribution is only valid when
            # EVERY non-objective term is attributable to a surviving
            # candidate: a full-coverage max, or a directly-observed time (a
            # dropped or partial term's objective contribution would be
            # missing from the bound formula).
            var clean = cObj == 1 or cObj == -1
            for vi, vn in varNames:
                if vn == objName: continue
                let isMaxTerm = vn in maxOwner and keep[maxOwner[vn]] and
                                maxCoverage.getOrDefault(vn, false)
                let isDirectTerm = vn in directOwner and keep[directOwner[vn]]
                if not (isMaxTerm or isDirectTerm):
                    clean = false
                    break
            if clean:
                for vi, vn in varNames:
                    if vn == objName: continue
                    let w = -coeffs[vi] * cObj
                    if vn in maxOwner:
                        let owner = maxOwner[vn]
                        if not keep[owner]: continue
                        candidates[owner].objectiveWeight += w
                        candidates[owner].objectiveConstOffset = rhsVal * cObj
                    elif vn in directOwner:
                        # Directly-observed time: record the per-node weight on
                        # a weighted-sum metric; the instance enters the bound
                        # formula with weight 1.
                        let owner = directOwner[vn]
                        if candidates[owner].sumMetricWeights.len == 0:
                            candidates[owner].sumMetricWeights =
                                newSeq[int](candidates[owner].timeVarNames.len)
                        for ni, tn in candidates[owner].timeVarNames:
                            if tn == vn:
                                candidates[owner].sumMetricWeights[ni] += w
                                break
                        candidates[owner].useSumMetric = true
                        candidates[owner].objectiveWeight = 1
                        candidates[owner].objectiveConstOffset = rhsVal * cObj
                # Static metric lower bound for sum-metric instances:
                # sum w_i * earliest_i (weights are positive by the per-
                # candidate sign check).
                for k in 0..<candidates.len:
                    if keep[k] and candidates[k].useSumMetric:
                        var lo = 0
                        for ni, w in candidates[k].sumMetricWeights:
                            lo += w * candidates[k].earlyTimes[ni]
                        candidates[k].objectiveMetricLo = lo

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


proc tryMatchReifArcFamilies(tr: var FznTranslator, circuitCI: int,
                              elems: seq[FznExpr], claimed: PackedSet[int],
                              candidates: var seq[CircuitTimeCandidate]) =
    ## Reified-arc chains on a successor circuit (e.g. single-machine scheduling
    ## with sequence-dependent setups, atp-stage2):
    ##   bool_clause([ne(succ_i, j), B], [])    -- succ_i = j  ->  B
    ##   bool_clause([B], [eq(succ_i, j)])       -- (same, other polarity)
    ## where B is int_lin_eq_reif / int_eq_reif / array_bool_and of those, each
    ## an exact equation  T_F[j] = T_F[i] + c(i, j)  for some family F of
    ## per-node variables (start times, per-product accumulators, ...), and
    ## depot arcs give  T_F[j] = c(depot, j).  Defined variables are resolved
    ## through their int_lin_eq definitions (end_i = start_i + d_i).
    ##
    ## Every complete family (an equation on every arc out of every node) becomes
    ## an exact CircuitTimeProp equality chain: its variables turn into channels
    ## computed by walking the tour, so the search only moves successors. The
    ## circuit constraint itself is kept (circuit moves; CTP circuit weight 0).
    let n = elems.len
    var linkVarNames = newSeq[string](n)
    var rawFixedLinks = newSeq[int](n)
    var nodeOfLinkVar: Table[string, int]
    for i, e in elems:
        case e.kind
        of FznIdent:
            if e.ident in nodeOfLinkVar: return
            linkVarNames[i] = e.ident
            nodeOfLinkVar[e.ident] = i
        of FznIntLit:
            rawFixedLinks[i] = e.intVal
        else: return
    if nodeOfLinkVar.len == 0: return
    # Successor value offset: 0-based iff some link can take 0 (and none n).
    var offset = 1
    block:
        var hasZero, hasN = false
        for vn in linkVarNames:
            if vn == "": continue
            let (lo, hi) = tr.circuitTimeDomainBounds(vn)
            if lo <= 0: hasZero = true
            if hi >= n: hasN = true
        if hasZero and not hasN: offset = 0
        elif hasZero and hasN: return

    # --- Defined-variable resolution: v = sign*w + k from int_lin_eq definitions
    type Lin = tuple[ok: bool, coeffs: Table[string, int], k: int]   # sum(coeffs*vars) + k
    var defOf: Table[string, (string, int, int)]   # v -> (w, a, b) with v = a*w + b
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        if stripSolverPrefix(con.name) != "int_lin_eq": continue
        if not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        let dv = ann.args[0].ident
        let cs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let vs = tr.resolveVarArrayElems(con.args[1])
        if cs.len != 2 or vs.len != 2: continue
        if vs[0].kind != FznIdent or vs[1].kind != FznIdent: continue
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        let (di, oi) = if vs[0].ident == dv: (0, 1) elif vs[1].ident == dv: (1, 0) else: (-1, -1)
        if di < 0 or abs(cs[di]) != 1 or abs(cs[oi]) != 1: continue
        # cd*dv + co*w = rhs  ->  dv = (rhs - co*w)/cd
        defOf[dv] = (vs[oi].ident, -cs[oi] * cs[di], rhs * cs[di])

    proc addTerm(t: var Table[string, int], k: var int, name: string, c: int,
                 defOf: Table[string, (string, int, int)]) =
        if name in defOf:
            let (w, a, b) = defOf[name]
            t.mgetOrPut(w, 0) += c * a
            k += c * b
        else:
            t.mgetOrPut(name, 0) += c

    # --- Equation bools: b <-> (sum(coeffs*vars) + k == 0)
    var eqOf: Table[string, Lin]
    var eqDefCI: Table[string, int]
    var andOf: Table[string, seq[string]]
    var andDefCI: Table[string, int]
    var neOf, eqLinkOf: Table[string, (int, int)]   # bool -> (node i, node j)
    var reifDefCI: Table[string, int]
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if not con.hasAnnotation("defines_var"): continue
        case name
        of "int_lin_eq_reif":
            if con.args.len < 4 or con.args[3].kind != FznIdent: continue
            let cs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
            let vs = tr.resolveVarArrayElems(con.args[1])
            let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
            var t: Table[string, int]
            var k = -rhs
            var ok = cs.len == vs.len
            for q in 0..<min(cs.len, vs.len):
                if vs[q].kind == FznIdent: addTerm(t, k, vs[q].ident, cs[q], defOf)
                elif vs[q].kind == FznIntLit: k += cs[q] * vs[q].intVal
                else: ok = false
            if ok:
                eqOf[con.args[3].ident] = (ok: true, coeffs: t, k: k)
                eqDefCI[con.args[3].ident] = ci
        of "int_eq_reif", "int_ne_reif":
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            let b = con.args[2].ident
            if con.args[0].kind == FznIdent and con.args[0].ident in nodeOfLinkVar and
               con.args[1].kind == FznIntLit:
                let i = nodeOfLinkVar[con.args[0].ident]
                let j = con.args[1].intVal - offset
                if j >= 0 and j < n:
                    if name == "int_ne_reif": neOf[b] = (i, j) else: eqLinkOf[b] = (i, j)
                    reifDefCI[b] = ci
            elif name == "int_eq_reif" and con.args[0].kind == FznIdent and
                 con.args[1].kind == FznIntLit:
                var t: Table[string, int]
                var k = -con.args[1].intVal
                addTerm(t, k, con.args[0].ident, 1, defOf)
                eqOf[b] = (ok: true, coeffs: t, k: k)
                eqDefCI[b] = ci
            elif name == "int_eq_reif" and con.args[0].kind == FznIdent and
                 con.args[1].kind == FznIdent and con.args[0].ident notin nodeOfLinkVar and
                 con.args[1].ident notin nodeOfLinkVar:
                # x == y (zero increment on this arc)
                var t: Table[string, int]
                var k = 0
                addTerm(t, k, con.args[0].ident, 1, defOf)
                addTerm(t, k, con.args[1].ident, -1, defOf)
                eqOf[b] = (ok: true, coeffs: t, k: k)
                eqDefCI[b] = ci
        of "array_bool_and":
            if con.args.len < 2 or con.args[1].kind != FznIdent: continue
            let lits = tr.resolveVarArrayElems(con.args[0])
            var names: seq[string]
            var ok = true
            for l in lits:
                if l.kind == FznIdent: names.add(l.ident) else: ok = false
            if ok:
                andOf[con.args[1].ident] = names
                andDefCI[con.args[1].ident] = ci
        else: discard

    # --- Arc implications
    type ArcEq = tuple[i, j: int, coeffs: Table[string, int], k: int]
    var arcEqs: seq[ArcEq]
    var clauseOfEq: seq[int]           # arcEqs index -> clause CI
    var clauseEqs: Table[int, seq[int]]  # clause CI -> arcEqs indices
    var clauseBools: Table[int, seq[string]]  # clause CI -> bools it references
    for ci in 0 ..< tr.model.constraints.len:
        if ci in claimed or ci in tr.definingConstraints: continue
        let con {.cursor.} = tr.model.constraints[ci]
        if stripSolverPrefix(con.name) != "bool_clause" or con.args.len < 2: continue
        let pos = tr.resolveVarArrayElems(con.args[0])
        let neg = tr.resolveVarArrayElems(con.args[1])
        var arc = (-1, -1)
        var body = ""
        if pos.len == 2 and neg.len == 0 and pos[0].kind == FznIdent and pos[1].kind == FznIdent:
            if pos[0].ident in neOf: (arc, body) = (neOf[pos[0].ident], pos[1].ident)
            elif pos[1].ident in neOf: (arc, body) = (neOf[pos[1].ident], pos[0].ident)
        elif pos.len == 1 and neg.len == 1 and pos[0].kind == FznIdent and neg[0].kind == FznIdent:
            if neg[0].ident in eqLinkOf: (arc, body) = (eqLinkOf[neg[0].ident], pos[0].ident)
        if arc[0] < 0: continue
        var parts = if body in andOf: andOf[body] else: @[body]
        var ok = true
        for b in parts:
            if b notin eqOf: ok = false
        if not ok: continue
        var bools = parts
        if body in andOf: bools.add(body)
        for pl in pos:
            if pl.kind == FznIdent: bools.add(pl.ident)
        for nl in neg:
            if nl.kind == FznIdent: bools.add(nl.ident)
        clauseBools[ci] = bools
        for b in parts:
            let e = eqOf[b]
            var t: Table[string, int]
            for v, c in e.coeffs.pairs:
                if c != 0: t[v] = c
            arcEqs.add((i: arc[0], j: arc[1], coeffs: t, k: e.k))
            clauseOfEq.add(ci)
            clauseEqs.mgetOrPut(ci, @[]).add(arcEqs.len - 1)
    if arcEqs.len == 0: return

    # --- Depot: the node whose outgoing equations are all single-variable
    var depot = -1
    for i in 0..<n:
        var nOut, nSingle = 0
        for e in arcEqs:
            if e.i == i:
                inc nOut
                if e.coeffs.len == 1: inc nSingle
        if nOut > 0 and nSingle == nOut:
            if depot >= 0: return   # ambiguous
            depot = i
    if depot < 0: return

    # --- Seeds: variable -> node from depot arcs (T[j] = const)
    var nodeOfVar: Table[string, int]
    for e in arcEqs:
        if e.i != depot: continue
        for v, c in e.coeffs.pairs:
            if abs(c) != 1: return
            if v in nodeOfVar and nodeOfVar[v] != e.j: return
            nodeOfVar[v] = e.j
    # --- Families: union-find over variables linked by arc equations
    var parent: Table[string, string]
    proc find(parent: var Table[string, string], x: string): string =
        var r = x
        while parent.getOrDefault(r, r) != r: r = parent[r]
        r
    for v in nodeOfVar.keys: parent[v] = v
    var eqFamily = newSeq[string](arcEqs.len)   # root var per equation ("" = unusable)
    for q, e in arcEqs:
        if e.i == depot:
            for v in e.coeffs.keys: eqFamily[q] = v
            continue
        if e.coeffs.len != 2: continue
        var vs: seq[(string, int)]
        for v, c in e.coeffs.pairs: vs.add((v, c))
        if vs[0][1] + vs[1][1] != 0 or abs(vs[0][1]) != 1: continue
        if vs[0][0] notin nodeOfVar or vs[1][0] notin nodeOfVar: continue
        let ra = find(parent, vs[0][0])
        let rb = find(parent, vs[1][0])
        if ra != rb: parent[ra] = rb
        eqFamily[q] = vs[0][0]
    for q in 0..<arcEqs.len:
        if eqFamily[q] != "": eqFamily[q] = find(parent, eqFamily[q])

    # --- Build each family's chain and check completeness
    var famIdx: Table[string, int]
    var famT: seq[seq[string]]
    var famDist: seq[seq[seq[int]]]
    var famHas: seq[seq[seq[bool]]]
    var famBad: seq[bool]
    for v in nodeOfVar.keys:
        let r = find(parent, v)
        if r notin famIdx:
            famIdx[r] = famT.len
            famT.add(newSeq[string](n))
            famDist.add(newSeqWith(n, newSeq[int](n)))
            famHas.add(newSeqWith(n, newSeq[bool](n)))
            famBad.add(false)
        let f = famIdx[r]
        let node = nodeOfVar[v]
        if famT[f][node] != "" and famT[f][node] != v: famBad[f] = true
        famT[f][node] = v
    for q, e in arcEqs:
        if eqFamily[q] == "" or eqFamily[q] notin famIdx: continue
        let f = famIdx[eqFamily[q]]
        var d: int
        if e.i == depot:
            # c*T[j] + k = 0  ->  T[j] = -k/c   (c = +-1)
            var c = 0
            var v = ""
            for vv, cc in e.coeffs.pairs: (v, c) = (vv, cc)
            if famT[f][e.j] != v: famBad[f] = true; continue
            d = -e.k * c
        else:
            let tj = famT[f][e.j]
            let ti = famT[f][e.i]
            if tj == "" or ti == "" or e.coeffs.getOrDefault(tj, 0) == 0 or
               e.coeffs.getOrDefault(ti, 0) == 0 or tj == ti:
                famBad[f] = true; continue
            # cj*Tj + ci*Ti + k = 0 with cj = -ci = +-1  ->  Tj = Ti - k/cj
            let cj = e.coeffs[tj]
            d = -e.k * cj
        if famHas[f][e.j][e.i] and famDist[f][e.j][e.i] != d: famBad[f] = true
        famHas[f][e.j][e.i] = true
        famDist[f][e.j][e.i] = d
    # Completeness: every arc (i -> j), j != depot, j in dom(succ_i)
    var accepted: seq[int]
    for f in 0..<famT.len:
        if famBad[f]: continue
        var complete = true
        for i in 0..<n:
            if linkVarNames[i] == "": continue
            let dom = if linkVarNames[i] in tr.presolveDomains: tr.presolveDomains[linkVarNames[i]]
                      else:
                          let (lo, hi) = tr.circuitTimeDomainBounds(linkVarNames[i])
                          toSeq(lo..hi)
            for v in dom:
                let j = v - offset
                if j < 0 or j >= n or j == i or j == depot: continue
                if not famHas[f][j][i] or famT[f][j] == "" or (i != depot and famT[f][i] == ""):
                    complete = false
                    break
            if not complete: break
        if complete: accepted.add(f)
    if accepted.len == 0: return
    var acceptedRoots: HashSet[string]
    for f in accepted:
        for v in famT[f]:
            if v != "": acceptedRoots.incl(find(parent, v))

    # --- Consumable clauses: every equation in the body belongs to an accepted family
    var consumed: PackedSet[int]
    for ci, eqs in clauseEqs.pairs:
        var ok = true
        for q in eqs:
            if eqFamily[q] == "" or eqFamily[q] notin acceptedRoots: ok = false
        if ok: consumed.incl(ci)
    if consumed.len == 0: return
    # Bools used only by consumed clauses (and their defining reifs) are dead too
    var useCount: CountTable[string]
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        for arg in con.args:
            if arg.kind == FznIdent: useCount.inc(arg.ident)
            elif arg.kind == FznArrayLit:
                for e in arg.elems:
                    if e.kind == FznIdent: useCount.inc(e.ident)
    var consumedUse: CountTable[string]
    for ci in consumed.items:
        for b in clauseBools[ci]: consumedUse.inc(b)
    # array_bool_and outputs' own args count as uses of their literals
    var allConsumed = consumed
    for b, cnt in consumedUse.pairs:
        # uses outside consumed clauses: total - consumed - its own definition (1)
        let defCI = if b in eqDefCI: eqDefCI[b] elif b in andDefCI: andDefCI[b]
                    elif b in reifDefCI: reifDefCI[b] else: -1
        if defCI < 0: continue
        var extra = useCount.getOrDefault(b, 0) - cnt - 1
        if b in andOf: discard
        # literals of a consumed array_bool_and are used by that and
        for a, lits in andOf.pairs:
            if a in consumedUse and b in lits: extra -= 1
        if extra <= 0: allConsumed.incl(defCI)

    for f in accepted:
        var cand = CircuitTimeCandidate(circuitCI: circuitCI)
        cand.forward = true
        cand.linkVarNames = linkVarNames
        cand.rawFixedLinks = rawFixedLinks
        cand.distMatrix = famDist[f]
        cand.earlyTimes = newSeq[int](n)
        cand.lateTimes = newSeq[int](n)
        cand.arrivalVars = newSeq[string](n)
        cand.departureVars = newSeq[string](n)
        cand.timeVarNames = newSeq[string](n)
        cand.outConstrained = newSeqWith(n, true)
        for node in 0..<n:
            let v = famT[f][node]
            if node == depot or v == "":
                cand.earlyTimes[node] = 0
                cand.lateTimes[node] = 0
            else:
                let (lo, hi) = tr.circuitTimeDomainBounds(v)
                cand.earlyTimes[node] = lo
                cand.lateTimes[node] = hi
                cand.arrivalVars[node] = v
                cand.timeVarNames[node] = v
                cand.channelVars.add(v)
        cand.depotIdx = depot
        cand.depotDep = 0
        cand.equalityChain = true
        cand.exactChain = true
        cand.closureFree = true
        cand.keepCircuit = true
        cand.hasValueOffset = true
        cand.valueOffset = offset
        cand.consumedCIs = allConsumed   # shared; definingConstraints is a set
        candidates.add(cand)
    stderr.writeLine("[FZN] Reified-arc circuit chains: " & $accepted.len & "/" & $famT.len &
                     " families exact (" & $consumed.len & " arc clauses consumed, depot node " &
                     $depot & ")")

proc detectCircuitTimePropagation(tr: var FznTranslator) =
    ## Detect circuit-time patterns (one time-chain candidate plus any number
    ## of accumulator-chain candidates per crusher_circuit), verify soundness,
    ## then consume the matched constraints and register instances.
    var candidates: seq[CircuitTimeCandidate]
    var claimed: PackedSet[int]   # constraints already matched by a candidate
    var accumArrays: HashSet[string]   # value arrays already chained by an accumulator
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
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
        var matchedTimeChain = false
        if tr.tryMatchPredFormCircuitTime(ci, elems, cand):
            candidates.add(cand)
            matchedTimeChain = true
        else:
            cand = CircuitTimeCandidate(circuitCI: ci)
            if tr.tryMatchSuccFormCircuitTime(ci, elems, cand):
                candidates.add(cand)
                matchedTimeChain = true
        if matchedTimeChain:
            for cci in candidates[^1].consumedCIs.items:
                claimed.incl(cci)
        # Equality accumulator chains may share the circuit with the time
        # chain (e.g. CVRP: time chain + load chain on the same successors).
        let nBefore = candidates.len
        tr.tryMatchSuccFormAccumulators(ci, elems, claimed, accumArrays, candidates)
        for k in nBefore..<candidates.len:
            for cci in candidates[k].consumedCIs.items:
                claimed.incl(cci)
        if not matchedTimeChain and candidates.len == nBefore:
            let nB2 = candidates.len
            tr.tryMatchReifArcFamilies(ci, elems, claimed, candidates)
            for k in nB2..<candidates.len:
                for cci in candidates[k].consumedCIs.items:
                    claimed.incl(cci)

    if candidates.len == 0: return

    tr.verifyCircuitTimeCandidates(candidates)

    for cand in candidates:
        for ci in cand.consumedCIs.items:
            tr.definingConstraints.incl(ci)
        for vn in cand.channelVars:
            tr.channelVarNames.incl(vn)
            tr.definedVarNames.excl(vn)
        tr.circuitTimeCandidates.add(cand)
        let form = if cand.equalityChain: "accumulator"
                   elif cand.forward: "successor"
                   else: "predecessor"
        stderr.writeLine("[FZN] Detected circuit-time-propagation pattern (" & form &
                         " form): " & $cand.linkVarNames.len & " nodes, depot=" &
                         $(cand.depotIdx + 1) &
                         (if cand.objectiveWeight > 0: ", objective weight " & $cand.objectiveWeight
                          else: "") &
                         (if cand.useSumMetric: " (sum metric)" else: ""))


proc emitCircuitTimePropConstraint(tr: var FznTranslator) =
    ## Emit the CircuitTimeProp constraints after variable positions are created.
    var keepCircuitCharged: PackedSet[int]
    var nLinked = 0
    var linkedExact = false
    for cand in tr.circuitTimeCandidates:
        if cand.objectiveWeight > 0:
            inc nLinked
            # Successor-form linkage is extracted from the objective's linear
            # definition (clean coverage); pred-form weight is a legacy
            # heuristic and not exact.
            linkedExact = cand.forward
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
        if cand.hasValueOffset:
            valueOffset = cand.valueOffset
        elif not cand.forward:
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

        var ctpCon = circuitTimeProp[int](
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
            cand.objectiveConstOffset,
            cand.useSumMetric,
            cand.sumMetricWeights,
            cand.equalityChain
        )
        if cand.closureFree:
            ctpCon.circuitTimePropState.closureFree = true
        if cand.keepCircuit:
            # The crusher_circuit constraint stays and drives circuit moves. Off
            # the depot's tour the chain values are meaningless defaults, so the
            # first chain on this circuit charges each unvisited node more than
            # any single arc can cost elsewhere; further chains don't re-charge.
            if cand.circuitCI in keepCircuitCharged:
                ctpCon.circuitTimePropState.circuitWeight = 0
            else:
                keepCircuitCharged.incl(cand.circuitCI)
                var maxD = 1
                for other in tr.circuitTimeCandidates:
                    if other.circuitCI != cand.circuitCI: continue
                    for row in other.distMatrix:
                        for d in row: maxD = max(maxD, abs(d))
                ctpCon.circuitTimePropState.circuitWeight = max(n, 2 * maxD)
        tr.sys.addConstraint(ctpCon)

        # NOTE: No separate allDifferent — the CircuitTimeProp circuit penalty already
        # penalizes duplicate values (they create tail nodes). Adding allDifferent as a
        # separate constraint creates competing penalties that trap the search in local minima.

        let form = if cand.forward: "successor" else: "predecessor"
        stderr.writeLine("[FZN] Emitted CircuitTimeProp constraint (" & form &
                         " form): " & $n & " nodes, offset=" & $valueOffset)

    # With exactly one exact linkage, metric <= (target - offset)/w is
    # equivalent to objective <= target — the optimizer can skip the explicit
    # relational bound over the objective's (channel) terms.
    if nLinked == 1 and linkedExact:
        tr.sys.circuitTimeObjectiveExact = true
        stderr.writeLine("[FZN] Objective bound delegated to CircuitTimeProp metric (exact single-instance linkage)")
