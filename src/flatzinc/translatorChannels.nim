## Included from translator.nim -- not a standalone module.

proc buildVarDomainIndex(tr: var FznTranslator) =
    ## Build a hash table index from variable name to declaration index
    ## for O(1) domain lookups instead of O(n) linear scans.
    if tr.varDomainIndex.len > 0: return  # already built
    for i, decl in tr.model.variables:
        if decl.isArray: continue
        tr.varDomainIndex[decl.name] = i

proc lookupVarDomain(tr: var FznTranslator, varName: string): seq[int] =
    ## Look up a variable's domain from the FznModel declarations.
    tr.buildVarDomainIndex()
    if varName in tr.varDomainIndex:
        let decl = tr.model.variables[tr.varDomainIndex[varName]]
        case decl.varType.kind
        of FznIntRange:
            return toSeq(decl.varType.lo..decl.varType.hi)
        of FznIntSet:
            return decl.varType.values
        of FznBool:
            return @[0, 1]
        else:
            return @[]
    return @[]

proc resolveActualDomain(tr: var FznTranslator, expr: AlgebraicExpression[int],
                                                  identName: string): seq[int] =
    ## Resolve the actual domain for an expression. If it maps to a single position,
    ## use the base array's domain (which reflects aliasing). Otherwise fall back to
    ## the FZN declaration domain via lookupVarDomain.
    let positions = toSeq(expr.positions.items)
    if positions.len == 1:
        return tr.sys.baseArray.domain[positions[0]].sorted()
    else:
        return tr.lookupVarDomain(identName)


proc unchannelSkippedReifs(tr: var FznTranslator, skipped: HashSet[int],
                                                      defs: var seq[int], label: string) =
    ## Un-channel skipped reif variables — they couldn't have bindings built due to
    ## large domains, so they must be treated as normal constraints instead.
    if skipped.len == 0: return
    for ci in skipped:
        let con = tr.model.constraints[ci]
        if con.args.len >= 3 and con.args[2].kind == FznIdent:
            let bName = con.args[2].ident
            tr.channelVarNames.excl(bName)
        tr.definingConstraints.excl(ci)
    var filtered: seq[int]
    for ci in defs:
        if ci notin skipped:
            filtered.add(ci)
    defs = filtered
    stderr.writeLine(&"[FZN] Un-channeled {skipped.len} {label} bindings (domain too large)")


proc canComposeConstElement(tr: var FznTranslator, idxArgName: string):
    tuple[success: bool, indexVar: string, constArray: seq[int], upDomain: seq[int], adjustedIdx: AlgebraicExpression[int]] =
    ## Helper: check if a const-element channel can be composed, and if so, return the upstream info.
    ## Caller applies the specific mapping logic based on constraint semantics.
    if idxArgName.len == 0 or idxArgName notin tr.constElementSources:
        return (false, "", @[], @[], AlgebraicExpression[int]())

    let sourceInfo = tr.constElementSources[idxArgName]
    if sourceInfo.indexVar notin tr.varPositions:
        return (false, "", @[], @[], AlgebraicExpression[int]())

    let upDomain = tr.lookupVarDomain(sourceInfo.indexVar)
    if upDomain.len == 0 or upDomain.len != sourceInfo.constArray.len:
        return (false, "", @[], @[], AlgebraicExpression[int]())

    let upPos = tr.varPositions[sourceInfo.indexVar]
    let adjustedIdx = tr.getExpr(upPos) - upDomain[0]

    return (true, sourceInfo.indexVar, sourceInfo.constArray, upDomain, adjustedIdx)

proc buildReifChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for int_eq_reif and bool2int patterns detected
    ## by detectReifChannels. Must be called after translateVariables.
    ##
    ## int_eq_reif(x, val, b): b = element(x - lo, [1 if v==val else 0 for v in domain])
    ## int_ne_reif(x, val, b): b = element(x - lo, [0 if v==val else 1 for v in domain])
    ## int_eq_reif(x, y, b):   b = element((x-lo_x)*size_y + (y-lo_y), equality_table)
    ## bool2int(b, i):          i = element(b, [0, 1])

    # Process int_eq_reif channels first (bool2int depends on these)
    var skippedReifCIs: HashSet[int]
    for ci in tr.reifChannelDefs:
        if ci in tr.equalityCopyReifCIs:
            # Equality copy: copy == original is always true, build constant-1 channel for indicator
            let con = tr.model.constraints[ci]
            let bName = con.args[2].ident
            if bName in tr.varPositions:
                let bPos = tr.varPositions[bName]
                let indexExpr = AlgebraicExpression[int](
                    node: ExpressionNode[int](kind: LiteralNode, value: 0),
                    positions: initPackedSet[int](),
                    linear: true
                )
                let binding = ChannelBinding[int](
                    channelPosition: bPos,
                    indexExpression: indexExpr,
                    arrayElements: @[ArrayElement[int](isConstant: true, constantValue: 1)]
                )
                tr.sys.baseArray.channelBindings.add(binding)
                tr.sys.baseArray.channelPositions.incl(bPos)
                # No entries in channelsAtPosition — no source positions, binding is constant
            continue
        let con = tr.model.constraints[ci]
        let bName = con.args[2].ident
        if bName notin tr.varPositions:
            continue

        let bPos = tr.varPositions[bName]
        let xArg = con.args[0]
        let valArg = con.args[1]

        # Skip if source var has been eliminated (e.g., dead element result)
        var deadSource = false
        for arg in [xArg, valArg]:
            if arg.kind == FznIdent and arg.ident in tr.definedVarNames and
                  arg.ident notin tr.varPositions and arg.ident notin tr.definedVarExprs:
                deadSource = true
                break
        if deadSource:
            # Dead source: mark the bool output as defined to cascade elimination
            tr.channelVarNames.excl(bName)
            tr.definedVarNames.incl(bName)
            continue

        var indexExpr: AlgebraicExpression[int]
        var arrayElems: seq[ArrayElement[int]]

        let isEq = stripSolverPrefix(con.name) == "int_eq_reif"

        if valArg.kind == FznIntLit or (valArg.kind == FznIdent and valArg.ident in tr.paramValues):
            # Constant val: b = element(x - lo, [1 if v==val else 0]) (inverted for ne)
            let val = if valArg.kind == FznIntLit: valArg.intVal
                                else: tr.paramValues[valArg.ident]
            let xExpr = tr.resolveExprArg(xArg)
            var didCompose = false

            # Check if x var is itself a const-element channel — compose directly from upstream
            if xArg.kind == FznIdent:
                let (canCompose, indexVar, constArray, upDomain, adjustedIdx) = canComposeConstElement(tr, xArg.ident)
                if canCompose:
                    indexExpr = adjustedIdx
                    for v in upDomain:
                        let mappedVal = constArray[v - upDomain[0]]
                        arrayElems.add(ArrayElement[int](isConstant: true,
                            constantValue: if (mappedVal == val) == isEq: 1 else: 0))
                    didCompose = true
                    stderr.writeLine(&"[FZN] Composed int_eq_reif({xArg.ident}, {val}) from upstream element")

            if not didCompose:
                let domain = tr.resolveActualDomain(xExpr, xArg.ident)
                if domain.len == 0:
                    skippedReifCIs.incl(ci)
                    continue
                let lo = domain[0]
                let hi = domain[^1]
                if hi - lo + 1 > 100_000:
                    skippedReifCIs.incl(ci)
                    continue

                indexExpr = xExpr - lo
                for v in lo..hi:
                    arrayElems.add(ArrayElement[int](isConstant: true,
                            constantValue: if (v == val) == isEq: 1 else: 0))

        elif valArg.kind == FznIdent and valArg.ident notin tr.definedVarNames:
            # Variable val: b = element((x-lo_x)*range_y + (y-lo_y), equality_table)
            let xExpr = tr.resolveExprArg(xArg)
            let yExpr = tr.resolveExprArg(valArg)
            let domainX = tr.resolveActualDomain(xExpr, xArg.ident)
            let domainY = tr.resolveActualDomain(yExpr, valArg.ident)
            if domainX.len == 0 or domainY.len == 0:
                skippedReifCIs.incl(ci)
                continue
            let loX = domainX[0]
            let hiX = domainX[^1]
            let loY = domainY[0]
            let hiY = domainY[^1]
            let rangeX = hiX - loX + 1
            let rangeY = hiY - loY + 1
            # Guard against huge 2D tables (use ranges, not domain sizes, since we fill gaps)
            if rangeX > 10_000 or rangeY > 10_000 or
                  rangeX * rangeY > 100_000:
                skippedReifCIs.incl(ci)
                continue

            # index = (x - lo_x) * range_y + (y - lo_y)
            indexExpr = (xExpr - loX) * rangeY + (yExpr - loY)

            # Build 2D equality table for full ranges (row-major: x varies in outer loop, y in inner)
            for vx in loX..hiX:
                for vy in loY..hiY:
                    arrayElems.add(ArrayElement[int](isConstant: true,
                            constantValue: if (vx == vy) == isEq: 1 else: 0))
        else:
            skippedReifCIs.incl(ci)
            continue

        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

    tr.unchannelSkippedReifs(skippedReifCIs, tr.reifChannelDefs, "reif")

    # Process bool2int channels (after reif channels so b positions are set up)
    for ci in tr.bool2intChannelDefs:
        let con = tr.model.constraints[ci]
        let iName = con.args[1].ident
        let bArg = con.args[0]

        if iName notin tr.varPositions:
            continue

        # Skip if source var is dead (cascade from dead element chain)
        if bArg.kind == FznIdent and bArg.ident in tr.definedVarNames and
              bArg.ident notin tr.varPositions and bArg.ident notin tr.definedVarExprs:
            # Mark the output as defined too to cascade
            tr.channelVarNames.excl(iName)
            tr.definedVarNames.incl(iName)
            continue

        let iPos = tr.varPositions[iName]

        let bExpr = tr.resolveExprArg(bArg)

        # i = element(b, [0, 1])  — identity mapping for domain {0, 1}
        let arrayElems = @[
            ArrayElement[int](isConstant: true, constantValue: 0),
            ArrayElement[int](isConstant: true, constantValue: 1)
        ]

        tr.sys.baseArray.addChannelBinding(iPos, bExpr, arrayElems)

    # Process bool_not channels: b = 1 - a = element(a, [1, 0])
    for ci in tr.boolNotChannelDefs:
        let con = tr.model.constraints[ci]
        let bName = con.args[1].ident
        let aArg = con.args[0]

        if bName notin tr.varPositions:
            continue
        let bPos = tr.varPositions[bName]

        let aExpr = tr.resolveExprArg(aArg)

        # b = element(a, [1, 0]) — negation for domain {0, 1}
        let arrayElems = @[
            ArrayElement[int](isConstant: true, constantValue: 1),
            ArrayElement[int](isConstant: true, constantValue: 0)
        ]

        tr.sys.baseArray.addChannelBinding(bPos, aExpr, arrayElems)

    # Process bool_xor negation channels: result = 1 - input = element(input, [1, 0])
    for def in tr.boolXorNegDefs:
        if def.resultVar notin tr.varPositions: continue
        let rPos = tr.varPositions[def.resultVar]
        let aExpr = tr.resolveExprArg(def.inputArg)
        let arrayElems = @[
            ArrayElement[int](isConstant: true, constantValue: 1),
            ArrayElement[int](isConstant: true, constantValue: 0)
        ]
        tr.sys.baseArray.addChannelBinding(rPos, aExpr, arrayElems)

    # Process bool_clause_reif channels
    for ci in tr.boolClauseReifChannelDefs:
        let con = tr.model.constraints[ci]
        let rName = con.args[2].ident
        if rName notin tr.varPositions:
            continue
        let rPos = tr.varPositions[rName]

        # Build index expression: sum(pos_exprs) - sum(neg_exprs) + len(neg)
        let posExprs = tr.resolveExprArray(con.args[0])
        let negExprs = tr.resolveExprArray(con.args[1])
        let n = posExprs.len + negExprs.len

        var indexExpr: AlgebraicExpression[int]
        if n == 0:
            # Empty clause — index is always 0 (clause always false)
            indexExpr = newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: 0),
                linear = true
            )
        else:
            # Start with first positive or negative expression
            var started = false
            for e in posExprs:
                if not started:
                    indexExpr = e
                    started = true
                else:
                    indexExpr = indexExpr + e
            for e in negExprs:
                if not started:
                    indexExpr = 0 - e
                    started = true
                else:
                    indexExpr = indexExpr - e
            # Add constant offset: len(neg)
            if negExprs.len > 0:
                indexExpr = indexExpr + negExprs.len

        # Array: [0, 1, 1, ..., 1] of length N+M+1
        # index 0 means all pos are 0 and all neg are 1 → clause false → r=0
        # any other index → clause true → r=1
        var arrayElems: seq[ArrayElement[int]]
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
        for i in 1..n:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))

        tr.sys.baseArray.addChannelBinding(rPos, indexExpr, arrayElems)

    # Process set_in_reif channels
    var skippedSetInReifCIs: HashSet[int]
    for ci in tr.setInReifChannelDefs:
        let con = tr.model.constraints[ci]
        let bName = con.args[2].ident
        if bName notin tr.varPositions:
            continue

        let bPos = tr.varPositions[bName]
        let xArg = con.args[0]
        let setArg = con.args[1]

        # Build the set membership channel binding
        var indexExpr: AlgebraicExpression[int]
        var arrayElems: seq[ArrayElement[int]]

        case setArg.kind
        of FznRange, FznSetLit:
            # S is a constant set: b = element(x - lo, [1 if v in S else 0 for v in lo..hi])
            var setValues: seq[int]
            if setArg.kind == FznRange:
                for v in setArg.lo..setArg.hi:
                    setValues.add(v)
            else:
                setValues = setArg.setElems
            let setAsHashSet = toHashSet(setValues)

            let xExpr = tr.resolveExprArg(xArg)
            var didCompose = false

            # Check if x var is itself a const-element channel — compose directly from upstream
            if xArg.kind == FznIdent:
                let (canCompose, indexVar, constArray, upDomain, adjustedIdx) = canComposeConstElement(tr, xArg.ident)
                if canCompose:
                    indexExpr = adjustedIdx
                    for v in upDomain:
                        let mappedVal = constArray[v - upDomain[0]]
                        arrayElems.add(ArrayElement[int](isConstant: true,
                            constantValue: if mappedVal in setAsHashSet: 1 else: 0))
                    didCompose = true
                    stderr.writeLine(&"[FZN] Composed set_in_reif({xArg.ident}) from upstream element")

            if not didCompose:
                let domain = tr.resolveActualDomain(xExpr, xArg.ident)
                if domain.len == 0:
                    skippedSetInReifCIs.incl(ci)
                    continue
                let lo = domain[0]
                let hi = domain[^1]
                if hi - lo + 1 > 100_000:
                    skippedSetInReifCIs.incl(ci)
                    continue

                indexExpr = xExpr - lo
                for v in lo..hi:
                    arrayElems.add(ArrayElement[int](isConstant: true,
                            constantValue: if v in setAsHashSet: 1 else: 0))
        of FznIdent:
            # S is a set variable: b = element(x - lo, S.bools)
            let sName = setArg.ident
            if sName notin tr.setVarBoolPositions:
                skippedSetInReifCIs.incl(ci)
                continue
            let sInfo = tr.setVarBoolPositions[sName]
            if sInfo.positions.len == 0:
                skippedSetInReifCIs.incl(ci)
                continue

            if xArg.kind == FznIntLit or (xArg.kind == FznIdent and xArg.ident in tr.paramValues):
                # x is a constant: b = S.bools[x - lo] (direct identity channel)
                let xVal = tr.resolveIntArg(xArg)
                let sBoolPos = getSetBoolPosition(sInfo, xVal)
                if sBoolPos >= 0:
                    # b = element(0, [S.bools[x-lo]])
                    indexExpr = newAlgebraicExpression[int](
                        positions = initPackedSet[int](),
                        node = ExpressionNode[int](kind: LiteralNode, value: 0),
                        linear = true)
                    arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: sBoolPos))
                else:
                    # x outside set universe: b = 0
                    tr.sys.baseArray.setDomain(bPos, @[0])
                    continue
            else:
                # x is a variable: b = element(x - lo, S.bools)
                let xExpr = tr.resolveExprArg(xArg)
                indexExpr = xExpr - sInfo.lo
                for pos in sInfo.positions:
                    arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: pos))
        else:
            skippedSetInReifCIs.incl(ci)
            continue

        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

    tr.unchannelSkippedReifs(skippedSetInReifCIs, tr.setInReifChannelDefs, "set_in_reif")

    # Process int_le_reif / int_lt_reif channels
    var skippedLeReifCIs: HashSet[int]
    for ci in tr.leReifChannelDefs:
        let con = tr.model.constraints[ci]
        let bName = con.args[2].ident
        if bName notin tr.varPositions:
            continue
        let bPos = tr.varPositions[bName]
        let arg0 = con.args[0]
        let arg1 = con.args[1]
        let name = stripSolverPrefix(con.name)
        let isLe = (name == "int_le_reif")  # le: <=, lt: <

        var indexExpr: AlgebraicExpression[int]
        var arrayElems: seq[ArrayElement[int]]

        # Determine which arg is constant and which is variable
        let arg0IsConst = arg0.kind == FznIntLit or (arg0.kind == FznIdent and arg0.ident in tr.paramValues)
        let arg1IsConst = arg1.kind == FznIntLit or (arg1.kind == FznIdent and arg1.ident in tr.paramValues)

        if arg0IsConst and not arg1IsConst:
            # int_le_reif(const, x, b): b = (const <= x) for le, b = (const < x) for lt
            let c = if arg0.kind == FznIntLit: arg0.intVal
                            else: tr.paramValues[arg0.ident]
            let xExpr = tr.resolveExprArg(arg1)
            let domain = tr.resolveActualDomain(xExpr, arg1.ident)
            if domain.len == 0:
                skippedLeReifCIs.incl(ci)
                continue
            let lo = domain[0]
            let hi = domain[^1]
            if hi - lo + 1 > 100_000:
                skippedLeReifCIs.incl(ci)
                continue
            indexExpr = xExpr - lo
            for v in lo..hi:
                let cmp = if isLe: (c <= v) else: (c < v)
                arrayElems.add(ArrayElement[int](isConstant: true,
                        constantValue: if cmp: 1 else: 0))

        elif not arg0IsConst and arg1IsConst:
            # int_le_reif(x, const, b): b = (x <= const) for le, b = (x < const) for lt
            let c = if arg1.kind == FznIntLit: arg1.intVal
                            else: tr.paramValues[arg1.ident]
            let xExpr = tr.resolveExprArg(arg0)
            let domain = tr.resolveActualDomain(xExpr, arg0.ident)
            if domain.len == 0:
                skippedLeReifCIs.incl(ci)
                continue
            let lo = domain[0]
            let hi = domain[^1]
            if hi - lo + 1 > 100_000:
                skippedLeReifCIs.incl(ci)
                continue
            indexExpr = xExpr - lo
            for v in lo..hi:
                let cmp = if isLe: (v <= c) else: (v < c)
                arrayElems.add(ArrayElement[int](isConstant: true,
                        constantValue: if cmp: 1 else: 0))

        elif not arg0IsConst and not arg1IsConst:
            # int_le_reif(x, y, b): b = (x <= y) for le, b = (x < y) for lt
            let xExpr = tr.resolveExprArg(arg0)
            let yExpr = tr.resolveExprArg(arg1)
            let xName = if arg0.kind == FznIdent: arg0.ident else: ""
            let yName = if arg1.kind == FznIdent: arg1.ident else: ""
            let domainX = tr.resolveActualDomain(xExpr, xName)
            let domainY = tr.resolveActualDomain(yExpr, yName)
            if domainX.len == 0 or domainY.len == 0:
                skippedLeReifCIs.incl(ci)
                continue
            let loX = domainX[0]
            let hiX = domainX[^1]
            let loY = domainY[0]
            let hiY = domainY[^1]
            let rangeX = hiX - loX + 1
            let rangeY = hiY - loY + 1
            if rangeX > 10_000 or rangeY > 10_000 or
                  rangeX * rangeY > 100_000:
                skippedLeReifCIs.incl(ci)
                continue
            indexExpr = (xExpr - loX) * rangeY + (yExpr - loY)
            for vx in loX..hiX:
                for vy in loY..hiY:
                    let cmp = if isLe: (vx <= vy) else: (vx < vy)
                    arrayElems.add(ArrayElement[int](isConstant: true,
                            constantValue: if cmp: 1 else: 0))
        else:
            # Both constant — skip
            skippedLeReifCIs.incl(ci)
            continue

        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

    tr.unchannelSkippedReifs(skippedLeReifCIs, tr.leReifChannelDefs, "le_reif")

    # Process int_lin_le_reif channels
    # b <-> sum(coeffs[i] * vars[i]) <= rhs
    # Compute the linear expression, determine its domain range, build a 0/1 lookup table.
    var skippedLinLeReifCIs: HashSet[int]
    for ci in tr.linLeReifChannelDefs:
        let con = tr.model.constraints[ci]
        let bName = con.args[3].ident
        if bName notin tr.varPositions:
            skippedLinLeReifCIs.incl(ci)
            continue
        let bPos = tr.varPositions[bName]
        let coeffs = tr.resolveIntArray(con.args[0])
        let rhs = tr.resolveIntArg(con.args[2])

        # Build the scalar product expression
        let exprs = tr.resolveExprArray(con.args[1])
        if exprs.len != coeffs.len:
            skippedLinLeReifCIs.incl(ci)
            continue

        # Build the linear expression as AlgebraicExpression (not SumExpression)
        var sp = coeffs[0] * exprs[0]
        for i in 1..<coeffs.len:
            sp = sp + coeffs[i] * exprs[i]

        # Compute bounds of the expression from variable domains
        var exprMin, exprMax: int = 0
        var boundsOk = true
        for i in 0..<coeffs.len:
            let positions = toSeq(exprs[i].positions.items)
            var lo, hi: int
            if positions.len == 1:
                let dom = tr.sys.baseArray.domain[positions[0]]
                if dom.len == 0:
                    boundsOk = false
                    break
                lo = dom[0]
                hi = dom[^1]
            elif positions.len == 0:
                # Constant expression
                lo = exprs[i].evaluate(newSeq[int](0))
                hi = lo
            else:
                # Multi-position expression — compute bounds from linear decomposition
                if exprs[i].linear:
                    let lin = linearize(exprs[i])
                    var minVal = lin.constant
                    var maxVal = lin.constant
                    var linOk = true
                    for pos in lin.coefficient.keys:
                        let c = lin.coefficient[pos]
                        let dom = tr.sys.baseArray.domain[pos]
                        if dom.len == 0:
                            linOk = false; break
                        if c > 0:
                            minVal += c * dom[0]
                            maxVal += c * dom[^1]
                        else:
                            minVal += c * dom[^1]
                            maxVal += c * dom[0]
                    if not linOk:
                        boundsOk = false; break
                    lo = minVal
                    hi = maxVal
                else:
                    # Non-linear multi-position — try declared domain as fallback
                    let argExpr = con.args[1]
                    if argExpr.kind == FznArrayLit:
                        let elem = argExpr.elems[i]
                        if elem.kind == FznIdent:
                            let dom = tr.lookupVarDomain(elem.ident)
                            if dom.len == 0:
                                boundsOk = false; break
                            lo = dom[0]
                            hi = dom[^1]
                        else:
                            boundsOk = false; break
                    else:
                        boundsOk = false; break
            if coeffs[i] > 0:
                exprMin += coeffs[i] * lo
                exprMax += coeffs[i] * hi
            else:
                exprMin += coeffs[i] * hi
                exprMax += coeffs[i] * lo

        if not boundsOk or exprMax - exprMin + 1 > 100_000:
            skippedLinLeReifCIs.incl(ci)
            continue

        # Build lookup table: for each value v of the expression, b = (v <= rhs)
        var arrayElems: seq[ArrayElement[int]]
        for v in exprMin..exprMax:
            arrayElems.add(ArrayElement[int](isConstant: true,
                    constantValue: if v <= rhs: 1 else: 0))

        let indexExpr = sp - exprMin
        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

    # Un-channel skipped int_lin_le_reif vars
    if skippedLinLeReifCIs.len > 0:
        for ci in skippedLinLeReifCIs:
            let con = tr.model.constraints[ci]
            if con.args.len >= 4 and con.args[3].kind == FznIdent:
                let bName = con.args[3].ident
                tr.channelVarNames.excl(bName)
            tr.definingConstraints.excl(ci)
        var filtered: seq[int]
        for ci in tr.linLeReifChannelDefs:
            if ci notin skippedLinLeReifCIs:
                filtered.add(ci)
        tr.linLeReifChannelDefs = filtered

    # Process int_lin_eq_reif channels
    # b <-> sum(coeffs[i] * vars[i]) == rhs
    # Compute the linear expression, determine its domain range, build a 0/1 lookup table.
    var skippedLinEqReifCIs: HashSet[int]
    for ci in tr.linEqReifChannelDefs:
        let con = tr.model.constraints[ci]
        let bName = con.args[3].ident
        if bName notin tr.varPositions:
            skippedLinEqReifCIs.incl(ci)
            continue
        let bPos = tr.varPositions[bName]
        let coeffs = tr.resolveIntArray(con.args[0])
        let rhs = tr.resolveIntArg(con.args[2])

        # Build the scalar product expression
        let exprs = tr.resolveExprArray(con.args[1])
        if exprs.len != coeffs.len:
            skippedLinEqReifCIs.incl(ci)
            continue

        # Build the linear expression as AlgebraicExpression
        var sp = coeffs[0] * exprs[0]
        for i in 1..<coeffs.len:
            sp = sp + coeffs[i] * exprs[i]

        # Compute bounds of the expression from variable domains
        var exprMin, exprMax: int = 0
        var boundsOk = true
        for i in 0..<coeffs.len:
            let positions = toSeq(exprs[i].positions.items)
            var lo, hi: int
            if positions.len == 1:
                let dom = tr.sys.baseArray.domain[positions[0]]
                if dom.len == 0:
                    boundsOk = false
                    break
                lo = dom[0]
                hi = dom[^1]
            elif positions.len == 0:
                # Constant expression
                lo = exprs[i].evaluate(newSeq[int](0))
                hi = lo
            else:
                # Multi-position expression — compute bounds from linear decomposition
                if exprs[i].linear:
                    let lin = linearize(exprs[i])
                    var minVal = lin.constant
                    var maxVal = lin.constant
                    var linOk = true
                    for pos in lin.coefficient.keys:
                        let c = lin.coefficient[pos]
                        let dom = tr.sys.baseArray.domain[pos]
                        if dom.len == 0:
                            linOk = false; break
                        if c > 0:
                            minVal += c * dom[0]
                            maxVal += c * dom[^1]
                        else:
                            minVal += c * dom[^1]
                            maxVal += c * dom[0]
                    if not linOk:
                        boundsOk = false; break
                    lo = minVal
                    hi = maxVal
                else:
                    # Non-linear multi-position — try declared domain as fallback
                    let argExpr = con.args[1]
                    if argExpr.kind == FznArrayLit:
                        let elem = argExpr.elems[i]
                        if elem.kind == FznIdent:
                            let dom = tr.lookupVarDomain(elem.ident)
                            if dom.len == 0:
                                boundsOk = false; break
                            lo = dom[0]
                            hi = dom[^1]
                        else:
                            boundsOk = false; break
                    else:
                        boundsOk = false; break
            if coeffs[i] > 0:
                exprMin += coeffs[i] * lo
                exprMax += coeffs[i] * hi
            else:
                exprMin += coeffs[i] * hi
                exprMax += coeffs[i] * lo

        if not boundsOk or exprMax - exprMin + 1 > 100_000:
            skippedLinEqReifCIs.incl(ci)
            continue

        # Build lookup table: for each value v of the expression, b = (v == rhs) or (v != rhs)
        let isLinEq = stripSolverPrefix(con.name) == "int_lin_eq_reif"
        var arrayElems: seq[ArrayElement[int]]
        for v in exprMin..exprMax:
            arrayElems.add(ArrayElement[int](isConstant: true,
                    constantValue: if (v == rhs) == isLinEq: 1 else: 0))

        let indexExpr = sp - exprMin
        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

    # Un-channel skipped int_lin_eq_reif vars
    if skippedLinEqReifCIs.len > 0:
        for ci in skippedLinEqReifCIs:
            let con = tr.model.constraints[ci]
            if con.args.len >= 4 and con.args[3].kind == FznIdent:
                let bName = con.args[3].ident
                tr.channelVarNames.excl(bName)
            tr.definingConstraints.excl(ci)
        var filtered: seq[int]
        for ci in tr.linEqReifChannelDefs:
            if ci notin skippedLinEqReifCIs:
                filtered.add(ci)
        tr.linEqReifChannelDefs = filtered

    # Process bool_eq_reif / bool_ne_reif channels
    # bool_eq_reif(a, b, r): r = (a == b) = element(a*2 + b, [1, 0, 0, 1])
    # bool_ne_reif(a, b, r): r = (a != b) = element(a*2 + b, [0, 1, 1, 0])
    for ci in tr.boolEqReifChannelDefs:
        let con = tr.model.constraints[ci]
        let rName = con.args[2].ident
        if rName notin tr.varPositions:
            continue
        let rPos = tr.varPositions[rName]
        let aArg = con.args[0]
        let bArg = con.args[1]

        let aExpr = tr.resolveExprArg(aArg)
        let bExpr = tr.resolveExprArg(bArg)

        let isEq = stripSolverPrefix(con.name) == "bool_eq_reif"

        # index = a*2 + b, domain {0,1} × {0,1} → range 0..3
        let indexExpr = aExpr * 2 + bExpr

        # eq: [1, 0, 0, 1] — (0,0)→1, (0,1)→0, (1,0)→0, (1,1)→1
        # ne: [0, 1, 1, 0] — (0,0)→0, (0,1)→1, (1,0)→1, (1,1)→0
        var arrayElems: seq[ArrayElement[int]]
        if isEq:
            arrayElems = @[
                ArrayElement[int](isConstant: true, constantValue: 1),
                ArrayElement[int](isConstant: true, constantValue: 0),
                ArrayElement[int](isConstant: true, constantValue: 0),
                ArrayElement[int](isConstant: true, constantValue: 1)]
        else:
            arrayElems = @[
                ArrayElement[int](isConstant: true, constantValue: 0),
                ArrayElement[int](isConstant: true, constantValue: 1),
                ArrayElement[int](isConstant: true, constantValue: 1),
                ArrayElement[int](isConstant: true, constantValue: 0)]

        tr.sys.baseArray.addChannelBinding(rPos, indexExpr, arrayElems)

    let totalReifChannels = tr.reifChannelDefs.len + tr.bool2intChannelDefs.len +
                                                    tr.boolNotChannelDefs.len +
                                                    tr.boolClauseReifChannelDefs.len + tr.setInReifChannelDefs.len +
                                                    tr.leReifChannelDefs.len + tr.linLeReifChannelDefs.len +
                                                    tr.linEqReifChannelDefs.len +
                                                    tr.boolEqReifChannelDefs.len
    if totalReifChannels > 0:
        stderr.writeLine(&"[FZN] Built {totalReifChannels} reification channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildConditionalBinaryChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for conditional binary channels detected by
    ## detectConditionalBinaryChannels.
    ## X = element(cond*2 + b2, [0, 0, 0, 1])  (AND gate: X = cond AND b2)
    for def in tr.conditionalBinaryChannelDefs:
        if def.targetVar notin tr.varPositions: continue
        if def.condVar notin tr.varPositions: continue
        if def.neqVar notin tr.varPositions: continue

        let xPos = tr.varPositions[def.targetVar]
        let condExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: def.condVar))
        let b2Expr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: def.neqVar))

        # index = cond*2 + b2, lookup = [0, 0, 0, 1] (AND gate)
        let indexExpr = condExpr * 2 + b2Expr
        let arrayElems = @[
            ArrayElement[int](isConstant: true, constantValue: 0),
            ArrayElement[int](isConstant: true, constantValue: 0),
            ArrayElement[int](isConstant: true, constantValue: 0),
            ArrayElement[int](isConstant: true, constantValue: 1)]

        tr.sys.baseArray.addChannelBinding(xPos, indexExpr, arrayElems)

    if tr.conditionalBinaryChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Built {tr.conditionalBinaryChannelDefs.len} conditional binary channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildBoolLogicChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for array_bool_and/array_bool_or with defines_var.
    ## array_bool_and([a,b,...], r): r = (a AND b AND ...) = element(a+b+..., [0,..,0,1])
    ## array_bool_or([a,b,...], r):  r = (a OR b OR ...) = element(a+b+..., [0,1,..,1])
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        let isAnd = (name == "array_bool_and")
        let rName = con.args[1].ident
        if rName notin tr.varPositions:
            continue

        # Check if any input var is dead (cascade from dead element chain)
        var hasDead = false
        if con.args[0].kind == FznArrayLit:
            for elem in con.args[0].elems:
                if elem.kind == FznIdent and elem.ident in tr.definedVarNames and
                      elem.ident notin tr.varPositions and elem.ident notin tr.definedVarExprs:
                    hasDead = true
                    break
        if hasDead:
            tr.channelVarNames.excl(rName)
            tr.definedVarNames.incl(rName)
            continue

        let rPos = tr.varPositions[rName]

        # Build index expression: sum of input expressions
        let inputExprs = tr.resolveExprArray(con.args[0])
        let n = inputExprs.len

        var indexExpr: AlgebraicExpression[int]
        if n == 0:
            indexExpr = newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: 0),
                linear = true
            )
        else:
            indexExpr = inputExprs[0]
            for i in 1..<n:
                indexExpr = indexExpr + inputExprs[i]

        # Build lookup array of length n+1
        var arrayElems: seq[ArrayElement[int]]
        if isAnd:
            # AND: only all-true (index n) maps to 1
            for i in 0..<n:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))
        else:
            # OR: only all-false (index 0) maps to 0
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
            for i in 1..n:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))

        tr.sys.baseArray.addChannelBinding(rPos, indexExpr, arrayElems)

    if tr.boolAndOrChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Built {tr.boolAndOrChannelDefs.len} array_bool_and/or channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildOneHotChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for one-hot indicator variables detected by
    ## detectImplicationPatterns. Each indicator B_v = (intVar == value) becomes
    ## a channel: B_v = element(intVar - lo, [1 if v==value else 0 for v in domain])

    for def in tr.oneHotChannelDefs:
        let indicatorVar = def.indicatorVar
        let intVar = def.intVar
        let value = def.value

        if indicatorVar notin tr.varPositions: continue
        if intVar notin tr.varPositions: continue

        let indicatorPos = tr.varPositions[indicatorVar]
        let intPos = tr.varPositions[intVar]
        let intExpr = tr.getExpr(intPos)
        let domain = tr.sys.baseArray.domain[intPos].sorted()
        if domain.len == 0: continue

        let lo = domain[0]
        let hi = domain[^1]
        if hi - lo + 1 > 100_000: continue
        let indexExpr = intExpr - lo

        var arrayElems: seq[ArrayElement[int]]
        for v in lo..hi:
            arrayElems.add(ArrayElement[int](isConstant: true,
                    constantValue: if v == value: 1 else: 0))

        tr.sys.baseArray.addChannelBinding(indicatorPos, indexExpr, arrayElems)

    if tr.oneHotChannelDefs.len > 0:
        stderr.writeLine(&"[FZN] Built {tr.oneHotChannelDefs.len} one-hot channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")

    # Build constant-zero channel bindings for boundary indicator variables
    var nConstZero = 0
    for bVar in tr.constantZeroChannels:
        if bVar notin tr.varPositions: continue
        let bPos = tr.varPositions[bVar]

        # Constant binding: element(0, [0]) — always evaluates to 0
        let indexExpr = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 0),
            linear = true
        )
        tr.sys.baseArray.addChannelBinding(bPos, indexExpr,
            @[ArrayElement[int](isConstant: true, constantValue: 0)])
        nConstZero += 1

    if nConstZero > 0:
        stderr.writeLine(&"[FZN] Built {nConstZero} constant-zero channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings from element constraints with defines_var annotations.
    ## Must be called after all constraints are translated and all positions are known.
    for ci, definedName in tr.channelConstraints:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)

        # The defined variable must have a position (it was NOT added to definedVarNames)
        if definedName notin tr.varPositions:
            continue

        let channelPos = tr.varPositions[definedName]

        # Build the adjusted index expression (0-based)
        let indexExpr = tr.resolveExprArg(con.args[0])
        var adjustedIndex = indexExpr - 1

        # Build the array elements
        var arrayElems: seq[ArrayElement[int]]
        if name in ["array_var_int_element", "array_var_int_element_nonshifted",
                                "array_var_bool_element", "array_var_bool_element_nonshifted"]:
            arrayElems = tr.resolveMixedArray(con.args[1])
        else:
            # array_int_element / array_bool_element: constant array
            let constArray = tr.resolveIntArray(con.args[1])

            # Check if index var is itself a const-element channel — compose if so
            # (double-hop: upstream var → intermediate element → final array value)
            let idxArgName = if con.args[0].kind == FznIdent: con.args[0].ident else: ""
            var didCompose = false
            if idxArgName.len > 0:
                let (canCompose, indexVar, upstreamConstArray, upDomain, adjustedIdx) = canComposeConstElement(tr, idxArgName)
                if canCompose:
                    var composedArr: seq[int]
                    var valid = true
                    # Double-hop: upstream constArray values are 1-based indices into constArray
                    for v in upDomain:
                        let midIdx = upstreamConstArray[v - upDomain[0]]
                        let finalIdx = midIdx - 1  # convert to 0-based
                        if finalIdx < 0 or finalIdx >= constArray.len:
                            valid = false
                            break
                        composedArr.add(constArray[finalIdx])
                    if valid and composedArr.len > 0:
                        adjustedIndex = adjustedIdx
                        for v in composedArr:
                            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))
                        didCompose = true
                        stderr.writeLine(&"[FZN] Composed element({idxArgName}) from upstream element (double-hop)")

            # Fall through if composition failed: build normal binding from constArray
            if not didCompose:
                for v in constArray:
                    arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

        tr.sys.baseArray.addChannelBinding(channelPos, adjustedIndex, arrayElems)

    if tr.sys.baseArray.channelBindings.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.sys.baseArray.channelBindings.len} channel variables (element defines_var)")

proc buildSyntheticElementChannelBindings(tr: var FznTranslator) =
    ## Builds element channel bindings for synthetic channels (precomputed lookup tables
    ## from detectConditionalGainChannels).
    for syn in tr.syntheticElementChannels:
        if syn.varName notin tr.varPositions:
            continue
        let channelPos = tr.varPositions[syn.varName]

        if syn.originVar notin tr.varPositions:
            continue
        let originPos = tr.varPositions[syn.originVar]
        let indexExpr = tr.getExpr(originPos) - 1  # FZN is 1-based

        var arrayElems: seq[ArrayElement[int]]
        for v in syn.lookupTable:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

        tr.sys.baseArray.addChannelBinding(channelPos, indexExpr, arrayElems)

proc buildSingletonSetChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for singleton set booleans detected by detectSingletonSetChannels.
    ## For set_card(S, 1) + set_in(x, S): S.bools[e] = element(x - lo, indicator_e)
    ## where indicator_e[i] = 1 if (i + lo) == e, else 0.
    var nBuilt = 0
    for def in tr.singletonSetChannelDefs:
        if def.setName notin tr.setVarBoolPositions: continue
        let info = tr.setVarBoolPositions[def.setName]
        if info.positions.len == 0: continue

        # Resolve x expression
        if def.xVarName notin tr.varPositions and
           def.xVarName notin tr.definedVarExprs: continue
        let xExpr = if def.xVarName in tr.varPositions:
                        tr.getExpr(tr.varPositions[def.xVarName])
                    else:
                        tr.definedVarExprs[def.xVarName]

        # Get x's domain range for the lookup table size
        let xDomain = tr.lookupVarDomain(def.xVarName)
        if xDomain.len == 0: continue
        let xLo = xDomain[0]
        let xHi = xDomain[^1]
        let indexExpr = xExpr - xLo

        # For each boolean in S's universe, create a channel binding
        for idx in 0..<info.positions.len:
            let e = info.lo + idx
            let boolPos = info.positions[idx]
            # Build indicator lookup table: 1 at position (e - xLo), 0 elsewhere
            var arrayElems: seq[ArrayElement[int]]
            for v in xLo..xHi:
                arrayElems.add(ArrayElement[int](isConstant: true,
                    constantValue: if v == e: 1 else: 0))
            tr.sys.baseArray.addChannelBinding(boolPos, indexExpr, arrayElems)
            inc nBuilt

    if nBuilt > 0:
        stderr.writeLine(&"[FZN] Built {nBuilt} singleton set channel bindings")

proc buildIntModChannelBindings(tr: var FznTranslator) =
    ## Builds element channel bindings for int_mod channels (Z = X mod C).
    ## Uses precomputed lookup tables from detectIntModChannels.
    var nBuilt = 0
    for def in tr.intModChannelDefs:
        if def.varName notin tr.varPositions:
            continue
        let channelPos = tr.varPositions[def.varName]

        # Resolve origin variable: may be a position or a defined-var expression
        var indexExpr: AlgebraicExpression[int]
        if def.originVar in tr.varPositions:
            indexExpr = tr.getExpr(tr.varPositions[def.originVar]) - def.offset
        elif def.originVar in tr.definedVarExprs:
            indexExpr = tr.definedVarExprs[def.originVar] - def.offset
        else:
            continue

        var arrayElems: seq[ArrayElement[int]]
        for v in def.lookupTable:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

        tr.sys.baseArray.addChannelBinding(channelPos, indexExpr, arrayElems)
        inc nBuilt

    if nBuilt > 0:
        stderr.writeLine(&"[FZN] Built {nBuilt} int_mod channel bindings")

proc buildMinMaxChannelBindings(tr: var FznTranslator) =
    ## Builds min/max channel bindings from array_int_minimum/maximum and int_min/int_max
    ## constraints with defines_var annotations. Must be called after buildDefinedExpressions
    ## so that defined-var inputs can be resolved.
    for def in tr.minMaxChannelDefs:
        let con = tr.model.constraints[def.ci]
        if def.varName notin tr.varPositions:
            continue
        let channelPos = tr.varPositions[def.varName]
        let name = stripSolverPrefix(con.name)
        var inputExprs: seq[AlgebraicExpression[int]]
        if name in ["int_min", "int_max"]:
            # int_min(a, b, c) / int_max(a, b, c) → inputs are [a, b]
            inputExprs = @[tr.resolveExprArg(con.args[0]), tr.resolveExprArg(con.args[1])]
        else:
            # array_int_minimum(m, array) / array_int_maximum(m, array) → inputs are array
            inputExprs = tr.resolveExprArray(con.args[1])
        if inputExprs.len == 0:
            continue
        let defCon = tr.model.constraints[def.ci]
        let isImplicit = not defCon.hasAnnotation("defines_var")
        tr.sys.baseArray.addMinMaxChannelBinding(channelPos, def.isMin, inputExprs, isImplicit)

    if tr.sys.baseArray.minMaxChannelBindings.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.sys.baseArray.minMaxChannelBindings.len} min/max channel variables")

proc buildRescuedChannelBindings(tr: var FznTranslator) =
    ## Builds single-input MinMaxChannelBindings for rescued defined vars.
    ## These are defined vars that appear in var-indexed arrays and need positions.
    ## Each gets a channel binding: min(expr) = expr (identity for single input).
    if tr.rescuedChannelDefs.len == 0: return

    var nBuilt = 0
    for def in tr.rescuedChannelDefs:
        if def.varName notin tr.varPositions: continue
        let channelPos = tr.varPositions[def.varName]
        let con = tr.model.constraints[def.ci]
        let name = stripSolverPrefix(con.name)

        var expr: AlgebraicExpression[int]

        if name == "int_lin_eq":
            # Solve: coeffs . vars = rhs for the rescued var
            let coeffs = tr.resolveIntArray(con.args[0])
            let varElems = tr.resolveVarArrayElems(con.args[1])
            let rhs = tr.resolveIntArg(con.args[2])

            # Find the rescued var's index and coefficient
            var definedIdx = -1
            for vi, v in varElems:
                if v.kind == FznIdent and v.ident == def.varName:
                    definedIdx = vi
                    break
            if definedIdx < 0: continue

            let defCoeff = coeffs[definedIdx]
            # defined = (rhs - sum(other_coeffs * other_vars)) / defCoeff
            let sign = if defCoeff == 1: -1 else: 1

            var first = true
            for vi, v in varElems:
                if vi == definedIdx: continue
                let otherExpr = tr.resolveExprArg(v)
                let scaledCoeff = sign * coeffs[vi]
                let term = scaledCoeff * otherExpr
                if first:
                    expr = term
                    first = false
                else:
                    expr = expr + term

            let constTerm = if defCoeff == 1: rhs else: -rhs
            if constTerm != 0:
                if first:
                    expr = newAlgebraicExpression[int](
                        positions = initPackedSet[int](),
                        node = ExpressionNode[int](kind: LiteralNode, value: constTerm),
                        linear = true
                    )
                    first = false
                else:
                    expr = expr + constTerm

            if expr.isNil: continue

        elif name == "int_abs":
            # int_abs(a, b) :: defines_var(b) → b = abs(a)
            expr = abs(tr.resolveExprArg(con.args[0]))

        elif name == "int_times":
            # int_times(a, b, c) → c = a * b
            expr = tr.resolveExprArg(con.args[0]) * tr.resolveExprArg(con.args[1])

        else:
            continue  # unsupported defining constraint type

        tr.sys.baseArray.addMinMaxChannelBinding(channelPos, true, @[expr])
        inc nBuilt

    if nBuilt > 0:
        stderr.writeLine(&"[FZN] Built {nBuilt} rescued channel bindings (from var-indexed arrays)")

proc buildSetUnionChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for set_union patterns:
    ## - Individual unions: max(A_bool, B_bool) per boolean
    ## - Chains with comprehension pattern: N-ary max over product expressions
    ## - Chains without comprehension: N-ary max over leaf booleans

    let zeroExpr = newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: 0),
        linear = true)
    let oneExpr = newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: 1),
        linear = true)

    var nIndividual = 0
    var nChainBindings = 0
    var nCompBindings = 0

    # --- Handle individual (non-chain) set_union channels ---
    for def in tr.setUnionChannelDefs:
        let con = tr.model.constraints[def.ci]
        let cName = def.resultName
        if cName notin tr.setVarBoolPositions:
            continue
        let cVar = tr.setVarBoolPositions[cName]
        if cVar.positions.len == 0:
            continue

        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])

        for idx in 0..<cVar.positions.len:
            let elem = cVar.lo + idx
            let cBoolPos = cVar.positions[idx]

            var aExpr: AlgebraicExpression[int]
            var aIsConst = false
            var aConstVal = 0
            if aInfo.isConst:
                aIsConst = true
                aConstVal = if elem in aInfo.constVals: 1 else: 0
            else:
                let aPos = getSetBoolPosition(aInfo.varInfo, elem)
                if aPos >= 0:
                    aExpr = tr.getExpr(aPos)
                else:
                    aIsConst = true
            if aIsConst:
                aExpr = if aConstVal == 1: oneExpr else: zeroExpr

            var bExpr: AlgebraicExpression[int]
            var bIsConst = false
            var bConstVal = 0
            if bInfo.isConst:
                bIsConst = true
                bConstVal = if elem in bInfo.constVals: 1 else: 0
            else:
                let bPos = getSetBoolPosition(bInfo.varInfo, elem)
                if bPos >= 0:
                    bExpr = tr.getExpr(bPos)
                else:
                    bIsConst = true
            if bIsConst:
                bExpr = if bConstVal == 1: oneExpr else: zeroExpr

            if aIsConst and bIsConst:
                tr.sys.baseArray.setDomain(cBoolPos, @[max(aConstVal, bConstVal)])
            else:
                tr.sys.baseArray.addMinMaxChannelBinding(cBoolPos, false, @[aExpr, bExpr])
                inc nIndividual

    # --- Handle chains with set comprehension pattern ---
    # R.bools[v] = max over products where sumVal=v of (product_expression)
    # R.bools[0] = 1 if base contains 0 (always true for gt-sort)
    var comprehensionChainIndices: PackedSet[int]
    for comp in tr.setComprehensions:
        comprehensionChainIndices.incl(comp.chainIdx)
        let chain = tr.setUnionChains[comp.chainIdx]
        let rName = chain.resultName
        if rName notin tr.setVarBoolPositions:
            continue
        let rVar = tr.setVarBoolPositions[rName]
        if rVar.positions.len == 0:
            continue

        # Group pairs by sumVal
        var pairsBySumVal: Table[int, seq[string]]  # sumVal -> product var names
        for pair in comp.pairs:
            pairsBySumVal.mgetOrPut(pair.sumVal, @[]).add(pair.productVarName)

        for idx in 0..<rVar.positions.len:
            let v = rVar.lo + idx
            let rBoolPos = rVar.positions[idx]

            if chain.baseIsConst and v in chain.baseConstVals:
                # Base set always contributes this value
                tr.sys.baseArray.setDomain(rBoolPos, @[1])
                continue

            if v notin pairsBySumVal:
                # No pair contributes this value
                if not chain.baseIsConst:
                    # If base is variable, include its boolean
                    let baseInfo = tr.setVarBoolPositions.getOrDefault(chain.baseName)
                    let bPos = getSetBoolPosition(baseInfo, v)
                    if bPos >= 0:
                        tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, @[tr.getExpr(bPos)])
                        inc nCompBindings
                    else:
                        tr.sys.baseArray.setDomain(rBoolPos, @[0])
                else:
                    tr.sys.baseArray.setDomain(rBoolPos, @[0])
                continue

            # Collect product expressions for all pairs with this sumVal
            var inputExprs: seq[AlgebraicExpression[int]]

            # Include base boolean if base is a variable set
            if not chain.baseIsConst:
                let baseInfo = tr.setVarBoolPositions.getOrDefault(chain.baseName)
                let bPos = getSetBoolPosition(baseInfo, v)
                if bPos >= 0:
                    inputExprs.add(tr.getExpr(bPos))

            for productName in pairsBySumVal[v]:
                if productName in tr.definedVarExprs:
                    inputExprs.add(tr.definedVarExprs[productName])
                elif productName in tr.varPositions:
                    inputExprs.add(tr.getExpr(tr.varPositions[productName]))

            if inputExprs.len == 0:
                tr.sys.baseArray.setDomain(rBoolPos, @[0])
            elif inputExprs.len == 1:
                # Single input: direct channel binding (avoid max overhead)
                tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, inputExprs)
                inc nCompBindings
            else:
                # N-ary max over all product expressions
                tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, inputExprs)
                inc nCompBindings

    # --- Handle chains WITHOUT comprehension pattern (plain chain collapse) ---
    for chainIdx in 0..<tr.setUnionChains.len:
        if chainIdx in comprehensionChainIndices:
            continue
        let chain = tr.setUnionChains[chainIdx]
        let rName = chain.resultName
        if rName notin tr.setVarBoolPositions:
            continue
        let rVar = tr.setVarBoolPositions[rName]
        if rVar.positions.len == 0:
            continue

        for idx in 0..<rVar.positions.len:
            let v = rVar.lo + idx
            let rBoolPos = rVar.positions[idx]

            var inputExprs: seq[AlgebraicExpression[int]]

            # Include base
            if chain.baseIsConst:
                if v in chain.baseConstVals:
                    tr.sys.baseArray.setDomain(rBoolPos, @[1])
                    continue
            else:
                let baseInfo = tr.setVarBoolPositions.getOrDefault(chain.baseName)
                let bPos = getSetBoolPosition(baseInfo, v)
                if bPos >= 0:
                    inputExprs.add(tr.getExpr(bPos))

            # Include all leaves
            for leafName in chain.leafNames:
                if leafName in tr.setVarBoolPositions:
                    let leafInfo = tr.setVarBoolPositions[leafName]
                    let lPos = getSetBoolPosition(leafInfo, v)
                    if lPos >= 0:
                        inputExprs.add(tr.getExpr(lPos))

            if inputExprs.len == 0:
                tr.sys.baseArray.setDomain(rBoolPos, @[0])
            else:
                tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, inputExprs)
                inc nChainBindings

    if nIndividual > 0:
        stderr.writeLine(&"[FZN] Built {nIndividual} individual set_union channel bindings")
    if nChainBindings > 0:
        stderr.writeLine(&"[FZN] Built {nChainBindings} chain-collapsed set_union channel bindings")
    if nCompBindings > 0:
        stderr.writeLine(&"[FZN] Built {nCompBindings} set comprehension channel bindings (from {tr.setComprehensions.len} patterns)")

proc buildCaseAnalysisChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for case-analysis patterns detected by
    ## detectCaseAnalysisChannels. Each target variable becomes a channel
    ## with a constant lookup table indexed by source variable positions.
    var nBuilt = 0
    for def in tr.caseAnalysisDefs:
        if def.targetVarName notin tr.varPositions: continue
        let channelPos = tr.varPositions[def.targetVarName]

        # Build array elements (all constants from precomputed lookup table)
        var arrayElems: seq[ArrayElement[int]]
        for v in def.lookupTable:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

        # Build index expression from source positions
        # Row-major: index = (src0 - off0) * size1 * ... * sizeN + ... + (srcN - offN)
        var indexExpr: AlgebraicExpression[int]
        var valid = true
        for i, srcName in def.sourceVarNames:
            if srcName notin tr.varPositions:
                valid = false
                break
            let srcPos = tr.varPositions[srcName]
            let srcExpr = tr.getExpr(srcPos)
            let termExpr = srcExpr - def.domainOffsets[i]
            if i == 0:
                indexExpr = termExpr
            else:
                indexExpr = indexExpr * def.domainSizes[i] + termExpr
        if not valid: continue

        # Create and register channel binding
        tr.sys.baseArray.addChannelBinding(channelPos, indexExpr, arrayElems)
        inc nBuilt

    if nBuilt > 0:
        stderr.writeLine(&"[FZN] Built {nBuilt} case-analysis channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")

proc buildConditionalSourceChannelBindings(tr: var FznTranslator) =
    ## Builds channel bindings for conditional variable-source patterns.
    ## Creates two bindings per target:
    ##   1. src_idx = element(condVar, sourceMap)  (constant-array element)
    ##   2. target = var_element(src_idx, sourceArray)  (variable-element)
    var nBuilt = 0
    for def in tr.conditionalSourceDefs:
        if def.targetVarName notin tr.varPositions: continue
        if def.condVarName notin tr.varPositions: continue
        let targetPos = tr.varPositions[def.targetVarName]
        let condPos = tr.varPositions[def.condVarName]

        # Create synthetic source-index variable
        let srcIdxVarName = "CRUSHER_SRC_IDX_" & def.targetVarName
        let srcIdxDomain = block:
            var vals: seq[int]
            var seen: PackedSet[int]
            for si in def.sourceMap:
                if si notin seen: seen.incl(si); vals.add(si)
            vals.sort()
            vals

        let srcIdxPos = tr.sys.baseArray.len
        tr.sys.baseArray.extendArray(1)
        tr.sys.baseArray.setDomain(srcIdxPos, srcIdxDomain)
        tr.varPositions[srcIdxVarName] = srcIdxPos
        tr.sys.baseArray.channelPositions.incl(srcIdxPos)

        # Build constant-array element binding: src_idx = element(condVar, sourceMap)
        var srcIdxArray: seq[ArrayElement[int]]
        for i in 0..<def.sourceMap.len:
            srcIdxArray.add(ArrayElement[int](isConstant: true,
                constantValue: def.sourceMap[i]))

        let indexExpr = tr.sys.baseArray[condPos] - def.condDomMin
        tr.sys.baseArray.addChannelBinding(srcIdxPos, indexExpr, srcIdxArray)

        # Build variable-element binding: target = var_element(src_idx - 1, sourceArray)
        var varArrayElems: seq[ArrayElement[int]]
        for decl in tr.model.variables:
            if decl.isArray and decl.name == def.sourceArrayName and
               decl.value != nil and decl.value.kind == FznArrayLit:
                varArrayElems = tr.resolveMixedArray(decl.value)
                break
        let valid = varArrayElems.len > 0

        if valid:
            let srcIdxExpr = tr.sys.baseArray[srcIdxPos] - 1  # 1-based to 0-based
            tr.sys.baseArray.addChannelBinding(targetPos, srcIdxExpr, varArrayElems)
            inc nBuilt

    if nBuilt > 0:
        stderr.writeLine(&"[FZN] Built {nBuilt} conditional-source channel bindings " &
                                          &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildInverseChannelBindings(tr: var FznTranslator) =
    ## Builds inverse channel groups from patterns detected by detectInverseChannelPatterns.
    for pi, pattern in tr.inverseChannelPatterns:
        if pi in tr.suppressedInversePatterns: continue
        let arrayPositions = tr.arrayPositions[pattern.arrayName]
        # Resolve forward (index) positions
        var forwardPositions: seq[int]
        for vn in pattern.indexVarNames:
            forwardPositions.add(tr.varPositions[vn])

        # Determine the forward base (minimum result value = the "name" of forwardPositions[0])
        # and sort by result value to align positions with their result values
        var pairs: seq[(int, int, string)]  # (resultValue, forwardPosition, varName)
        for i in 0..<pattern.resultValues.len:
            pairs.add((pattern.resultValues[i], forwardPositions[i], pattern.indexVarNames[i]))
        pairs.sort(proc(a, b: (int, int, string)): int = cmp(a[0], b[0]))

        var sortedForward: seq[int]
        var sortedResults: seq[int]
        for (rv, fp, _) in pairs:
            sortedForward.add(fp)
            sortedResults.add(rv)

        let forwardBase = sortedResults[0]
        # Verify result values are consecutive
        var consecutive = true
        for i in 1..<sortedResults.len:
            if sortedResults[i] != sortedResults[i-1] + 1:
                consecutive = false
                break
        if not consecutive:
            stderr.writeLine(&"[FZN] Warning: inverse channel on '{pattern.arrayName}' has non-consecutive results, skipping")
            continue

        # Inverse base is 1 (FlatZinc arrays are 1-based)
        let inverseBase = 1

        # Default value: find a value in the inverse domain that is NOT in the result values
        # Typically 0 for alldifferent_except_0 patterns
        let resultSet = sortedResults.toHashSet()
        var defaultValue = 0
        if defaultValue in resultSet:
            # Find any value not in the result set from the inverse domain
            let dom = tr.sys.baseArray.domain[arrayPositions[0]]
            for v in dom:
                if v notin resultSet:
                    defaultValue = v
                    break

        tr.sys.baseArray.addInverseChannelGroup(
            sortedForward, arrayPositions, forwardBase, inverseBase, defaultValue)

        # Domain reduction: if the inverse array has all-constant elements,
        # each forward position is uniquely determined.
        # element(forward[i], constantArray, i+forwardBase) means constantArray[forward[i]] = i+forwardBase
        # So forward[i] = the unique index where constantArray has value (i+forwardBase).
        var nReduced = 0
        block:
            # Get the array declaration elements
            var arrayArg = FznExpr(kind: FznIdent, ident: pattern.arrayName)
            let elems = tr.resolveVarArrayElems(arrayArg)
            if elems.len > 0:
                # Check if all elements are integer literals (constant array)
                var allConstant = true
                var constValues: seq[int]
                for elem in elems:
                    if elem.kind == FznIntLit:
                        constValues.add(elem.intVal)
                    else:
                        allConstant = false
                        break

                if allConstant:
                    # Build value -> 1-based index lookup
                    var valueToIndex: Table[int, int]
                    for idx, v in constValues:
                        valueToIndex[v] = idx + inverseBase  # 1-based FlatZinc index

                    # Reduce each forward position's domain to its unique value
                    for i, fpos in sortedForward:
                        let targetValue = i + forwardBase  # what constantArray[forward[i]] must equal
                        if targetValue in valueToIndex:
                            let requiredIdx = valueToIndex[targetValue]
                            tr.sys.baseArray.domain[fpos] = @[requiredIdx]
                            inc nReduced

        stderr.writeLine(&"[FZN] Built inverse channel group on '{pattern.arrayName}': " &
                                          &"{sortedForward.len} forward + {arrayPositions.len} inverse positions, " &
                                          &"forwardBase={forwardBase}, defaultValue={defaultValue}" &
                                          (if nReduced > 0: &", {nReduced} forward domains fixed" else: ""))

proc resolveVarNames(tr: FznTranslator, arg: FznExpr): seq[string] =
    ## Resolves a FznExpr to variable names (for ordering detection).
    ## Only handles inline array literals since this runs before translateVariables.
    case arg.kind
    of FznArrayLit:
        for e in arg.elems:
            if e.kind == FznIdent:
                result.add(e.ident)
            else:
                return @[]  # non-variable element, bail out
    else:
        return @[]

proc detectInversePatterns(tr: var FznTranslator) =
    ## Detects involution patterns from array_var_int_element constraints.
    ## Pattern: for an n-element array A, n constraints of the form
    ##   array_var_int_element(A[i], A, i)  for i in 1..n
    ## encode the involution A[A[i]] = i. These are replaced by an InverseGroup
    ## that maintains the invariant via compound moves.
    ## Also removes matching fzn_all_different_int constraints (implied by involution).

    # Step 1: Group array_var_int_element constraints by their array argument
    var arrayGroups: Table[string, seq[int]]  # array name -> constraint indices
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted",
                                      "array_var_bool_element", "array_var_bool_element_nonshifted"]:
            continue
        if con.hasAnnotation("defines_var"):
            continue
        # Array argument is arg[1]
        let arrArg = con.args[1]
        if arrArg.kind != FznIdent:
            continue
        let arrName = arrArg.ident
        if arrName notin arrayGroups:
            arrayGroups[arrName] = @[]
        arrayGroups[arrName].add(ci)

    # Step 2: For each group, check if it forms an involution pattern
    for arrName, ciList in arrayGroups:
        # Get the element names for this array
        if arrName notin tr.arrayElementNames:
            continue
        let elemNames = tr.arrayElementNames[arrName]
        let n = elemNames.len
        if ciList.len != n:
            continue  # must have exactly one constraint per element

        # Build map: element name -> 0-based index in the array
        var nameToIdx: Table[string, int]
        for i, name in elemNames:
            nameToIdx[name] = i

        # Check each constraint: arg[0] must be one of the array elements,
        # arg[2] must be the constant (1-based index) of that element
        var matched = newSeq[bool](n)
        var allMatch = true
        for ci in ciList:
            let con = tr.model.constraints[ci]
            # arg[0] = index (should be one of the array's element variables)
            if con.args[0].kind != FznIdent:
                allMatch = false
                break
            let indexName = con.args[0].ident
            # The index might be a defined variable — resolve through definedVarNames
            # But for the involution, the index should be one of the array elements directly
            if indexName notin nameToIdx:
                allMatch = false
                break
            let elemIdx = nameToIdx[indexName]  # 0-based

            # arg[2] = value (should be constant = elemIdx + 1, i.e., 1-based)
            if con.args[2].kind != FznIntLit:
                allMatch = false
                break
            let constVal = con.args[2].intVal
            if constVal != elemIdx + 1:
                allMatch = false
                break

            if matched[elemIdx]:
                allMatch = false  # duplicate
                break
            matched[elemIdx] = true

        if not allMatch:
            continue
        # Verify all elements matched
        var complete = true
        for m in matched:
            if not m:
                complete = false
                break
        if not complete:
            continue

        # All checks passed — this is an involution group!
        # Get positions for all elements
        if arrName notin tr.arrayPositions:
            continue
        let positions = tr.arrayPositions[arrName]
        if positions.len != n:
            continue

        # Mark all element constraints as consumed
        for ci in ciList:
            tr.definingConstraints.incl(ci)

        # Find and mark matching fzn_all_different_int constraints on the same positions
        var nAllDiffRemoved = 0
        for ci2, con2 in tr.model.constraints:
            if ci2 in tr.definingConstraints:
                continue
            let cname = stripSolverPrefix(con2.name)
            if cname notin ["fzn_all_different_int", "all_different_int"]:
                continue
            # Check if the constraint's variable set matches our positions
            let varElems = tr.resolveVarArrayElems(con2.args[0])
            if varElems.len != n:
                continue
            var allInGroup = true
            for elem in varElems:
                if elem.kind != FznIdent or elem.ident notin nameToIdx:
                    allInGroup = false
                    break
            if allInGroup:
                tr.definingConstraints.incl(ci2)
                inc nAllDiffRemoved

        # Register the inverse group (valueOffset = -1 for 1-based FlatZinc indexing)
        tr.sys.baseArray.addInverseGroup(positions, -1)

        stderr.writeLine(&"[FZN] Detected involution on array '{arrName}': {n} positions, " &
                                          &"{ciList.len} element + {nAllDiffRemoved} all_different constraints consumed")


proc detectInverseChannelPatterns(tr: var FznTranslator) =
    ## Detects inverse channel patterns from array_var_int_element constraints.
    ## Pattern: for an array A of size S, P constraints of the form
    ##   array_var_int_element(index_p, A, p)  for p in 1..P
    ## where index_p are distinct positioned variables NOT in A, and p is a constant.
    ## This encodes A[index_p] = p, i.e., A is the inverse of the index variables.
    ## The A positions become channel variables.
    ## Also consumes matching GCC/alldifferent_except_0 constraints on A.

    # Step 1: Group array_var_int_element constraints by their array argument
    var arrayGroups: Table[string, seq[int]]  # array name -> constraint indices
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]:
            continue
        if con.hasAnnotation("defines_var"):
            continue
        # Array argument is arg[1] — must be a named array
        let arrArg = con.args[1]
        if arrArg.kind != FznIdent:
            continue
        # Index arg[0] must be a named variable
        if con.args[0].kind != FznIdent:
            continue
        # Result arg[2] must be a constant integer
        if con.args[2].kind != FznIntLit:
            continue
        let arrName = arrArg.ident
        if arrName notin arrayGroups:
            arrayGroups[arrName] = @[]
        arrayGroups[arrName].add(ci)

    # Step 2: For each group, check if it forms an inverse channel pattern
    for arrName, ciList in arrayGroups:
        if arrName notin tr.arrayPositions:
            continue
        let arrayPositions = tr.arrayPositions[arrName]
        let arraySize = arrayPositions.len

        # Get element names for the array (to detect involution overlap)
        var arrayElemNames: HashSet[string]
        if arrName in tr.arrayElementNames:
            for n in tr.arrayElementNames[arrName]:
                arrayElemNames.incl(n)

        # Collect index var names and result values
        var indexVarNames: seq[string]
        var resultValues: seq[int]
        var resultSet: HashSet[int]
        var allValid = true
        var isInvolution = true  # check if index vars ARE the array elements
        for ci in ciList:
            let con = tr.model.constraints[ci]
            let indexName = con.args[0].ident
            let resultVal = con.args[2].intVal

            # Index must be a positioned variable
            if indexName notin tr.varPositions:
                allValid = false
                break
            # Check for duplicate result values
            if resultVal in resultSet:
                allValid = false
                break
            resultSet.incl(resultVal)
            indexVarNames.add(indexName)
            resultValues.add(resultVal)

            # Check if this is an involution (index var is from the same array)
            if indexName notin arrayElemNames:
                isInvolution = false

        if not allValid:
            continue
        # Skip involution patterns (handled by detectInversePatterns)
        if isInvolution:
            continue
        # Need at least 2 constraints
        if ciList.len < 2:
            continue
        # All index vars must be distinct
        if indexVarNames.toHashSet().len != indexVarNames.len:
            continue

        # Result values must be valid indices into the array (1-based)
        var resultValsValid = true
        for rv in resultValues:
            if rv < 1 or rv > arraySize:
                resultValsValid = false
                break
        if not resultValsValid:
            continue

        # Find matching GCC or alldifferent_except_0 constraints on the array positions
        let arrayPosSet = toPackedSet(arrayPositions)
        var gccCIs: seq[int]
        for ci2, con2 in tr.model.constraints:
            if ci2 in tr.definingConstraints:
                continue
            let cname = stripSolverPrefix(con2.name)
            case cname
            of "fzn_global_cardinality", "fzn_global_cardinality_closed",
                  "fzn_global_cardinality_low_up", "fzn_global_cardinality_low_up_closed":
                # Check if the x array covers our array positions
                let varElems = tr.resolveVarArrayElems(con2.args[0])
                if varElems.len == 0: continue
                var positions: seq[int]
                var match = true
                for elem in varElems:
                    if elem.kind != FznIdent or elem.ident notin tr.varPositions:
                        match = false
                        break
                    positions.add(tr.varPositions[elem.ident])
                if not match: continue
                if toPackedSet(positions) == arrayPosSet:
                    gccCIs.add(ci2)
            of "fzn_all_different_int", "all_different_int", "fzn_alldifferent_except_0":
                let varElems = tr.resolveVarArrayElems(con2.args[0])
                if varElems.len == 0: continue
                var positions: seq[int]
                var match = true
                for elem in varElems:
                    if elem.kind != FznIdent or elem.ident notin tr.varPositions:
                        match = false
                        break
                    positions.add(tr.varPositions[elem.ident])
                if not match: continue
                if toPackedSet(positions) == arrayPosSet:
                    gccCIs.add(ci2)
            else:
                discard

        # Mark element constraints as consumed
        for ci in ciList:
            tr.definingConstraints.incl(ci)
        # Mark GCC/alldifferent constraints as consumed
        for ci2 in gccCIs:
            tr.definingConstraints.incl(ci2)

        # Store the pattern
        tr.inverseChannelPatterns.add((
            arrayName: arrName,
            elementCIs: ciList,
            indexVarNames: indexVarNames,
            resultValues: resultValues,
            gccCIs: gccCIs
        ))

        stderr.writeLine(&"[FZN] Detected inverse channel on array '{arrName}': " &
                                          &"{ciList.len} element + {gccCIs.len} GCC/alldiff constraints consumed, " &
                                          &"{arraySize} inverse positions become channels")

    # Detect mutual inverse pairs: patA channels array B using A's elements as indices,
    # and patB channels array A using B's elements as indices → suppress the secondary.
    var posToVarName: Table[int, string]
    for k, v in tr.varPositions: posToVarName[v] = k
    for i, patA in tr.inverseChannelPatterns:
        if i in tr.suppressedInversePatterns: continue
        var channeledByA: HashSet[string]
        for pos in tr.arrayPositions[patA.arrayName]:
            if pos in posToVarName: channeledByA.incl(posToVarName[pos])
        for j, patB in tr.inverseChannelPatterns:
            if j <= i or j in tr.suppressedInversePatterns: continue
            var channeledByB: HashSet[string]
            for pos in tr.arrayPositions[patB.arrayName]:
                if pos in posToVarName: channeledByB.incl(posToVarName[pos])
            if patA.indexVarNames.toHashSet() == channeledByB and
               patB.indexVarNames.toHashSet() == channeledByA:
                # Mutual inverse pair: keep i (patA), suppress j (patB)
                tr.suppressedInversePatterns.incl(j)
                # Un-consume the suppressed pattern's constraints so they remain active
                for ci in patB.elementCIs:
                    tr.definingConstraints.excl(ci)
                for ci in patB.gccCIs:
                    tr.definingConstraints.excl(ci)
                stderr.writeLine(&"[FZN] Suppressed mutual-inverse secondary pattern on " &
                                 &"'{patB.arrayName}' ('{patA.arrayName}' is channel, " &
                                 &"'{patB.arrayName}' positions remain searchable)")


proc detectIfThenElseChannels(tr: var FznTranslator) =
    ## Detects if-then-else patterns encoded as:
    ##   int_lin_ne_reif([1,-1], [prev, curr], 0, b) :: defines_var(b)
    ##   int_eq_reif(result, curr, b1) :: defines_var(b1)
    ##   int_eq_reif(result, elseVal, b2) :: defines_var(b2)
    ##   bool_clause([b1], [b])          -- b → b1: if prev!=curr then result==curr
    ##   bool_clause([b, b2], [])        -- ¬b → b2: if prev==curr then result==elseVal
    ## Converts result to a 2D table channel: result = if prev != curr then curr else elseVal

    # Phase 1: Index int_lin_ne_reif with defines_var → condition bool var
    # Maps condBoolVar → (ci, prevVarName, currVarName)
    type LinNeReifEntry = object
        ci: int
        prevVar, currVar: string

    var linNeReifMap: Table[string, LinNeReifEntry]

    for ci, con in tr.model.constraints:
        # Don't skip definingConstraints: int_lin_ne_reif may already be channelized
        # by detectLinEqReifChannels, but we still need prevVar/currVar info to detect
        # the full if-then-else pattern and convert the result to a 2D table channel.
        if con.name != "int_lin_ne_reif": continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 4: continue
        if con.args[3].kind != FznIdent: continue
        # Check coefficients are [1,-1] or [-1,1]
        var coeffs: seq[int]
        try:
            coeffs = tr.resolveIntArray(con.args[0])
        except CatchableError: continue
        if coeffs.len != 2: continue
        if not ((coeffs[0] == 1 and coeffs[1] == -1) or (coeffs[0] == -1 and coeffs[1] == 1)): continue
        # Check RHS is 0
        var rhs: int
        try:
            rhs = tr.resolveIntArg(con.args[2])
        except CatchableError: continue
        if rhs != 0: continue
        # Get the two variable names
        if con.args[1].kind != FznArrayLit or con.args[1].elems.len != 2: continue
        if con.args[1].elems[0].kind != FznIdent or con.args[1].elems[1].kind != FznIdent: continue
        let v0 = con.args[1].elems[0].ident
        let v1 = con.args[1].elems[1].ident
        let boolVar = con.args[3].ident
        # coeffs [1,-1] means v0 - v1 != 0, i.e., v0 != v1
        if coeffs[0] == 1:
            linNeReifMap[boolVar] = LinNeReifEntry(ci: ci, prevVar: v0, currVar: v1)
        else:
            linNeReifMap[boolVar] = LinNeReifEntry(ci: ci, prevVar: v1, currVar: v0)

    if linNeReifMap.len == 0: return

    # Phase 2: Index int_eq_reif with defines_var where first arg is a result variable
    # Maps resultVarName → seq of (ci, testArg, boolVar)
    type EqReifEntry = object
        ci: int
        boolVar: string
        # The test value: either a variable name or a constant
        isConstTest: bool
        constVal: int
        varName: string  # if not const

    var eqReifByResult: Table[string, seq[EqReifEntry]]

    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        if con.name != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent: continue
        if con.args[2].kind != FznIdent: continue
        let resultVar = con.args[0].ident
        let boolVar = con.args[2].ident
        var entry: EqReifEntry
        entry.ci = ci
        entry.boolVar = boolVar
        if con.args[1].kind == FznIntLit:
            entry.isConstTest = true
            entry.constVal = con.args[1].intVal
        elif con.args[1].kind == FznIdent:
            entry.isConstTest = false
            entry.varName = con.args[1].ident
        else:
            continue
        if resultVar notin eqReifByResult:
            eqReifByResult[resultVar] = @[]
        eqReifByResult[resultVar].add(entry)

    # Phase 3: Index bool_clause constraints
    # For each bool_clause, check if it matches one of the two patterns:
    # Pattern A: bool_clause([b1], [b]) — 1 positive, 1 negative
    # Pattern B: bool_clause([b, b2], []) — 2 positive, 0 negative
    type BoolClauseEntry = object
        ci: int
        # For Pattern A: posLit is b1 (eq_reif bool), negLit is b (condition bool)
        # For Pattern B: lit1 is b (condition bool), lit2 is b2 (eq_reif bool)
        posLits: seq[string]
        negLits: seq[string]

    var boolClausesByLit: Table[string, seq[BoolClauseEntry]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if con.name != "bool_clause": continue
        if con.args.len < 2: continue
        var posLits, negLits: seq[string]
        if con.args[0].kind == FznArrayLit:
            for e in con.args[0].elems:
                if e.kind == FznIdent: posLits.add(e.ident)
        if con.args[1].kind == FznArrayLit:
            for e in con.args[1].elems:
                if e.kind == FznIdent: negLits.add(e.ident)
        let entry = BoolClauseEntry(ci: ci, posLits: posLits, negLits: negLits)
        for lit in posLits:
            if lit notin boolClausesByLit: boolClausesByLit[lit] = @[]
            boolClausesByLit[lit].add(entry)
        for lit in negLits:
            if lit notin boolClausesByLit: boolClausesByLit[lit] = @[]
            boolClausesByLit[lit].add(entry)

    # Phase 4: Match the full pattern for each candidate result variable
    var totalChannels = 0

    for resultVar, eqEntries in eqReifByResult:
        if eqEntries.len != 2: continue
        if resultVar notin tr.varPositions: continue
        if resultVar in tr.channelVarNames: continue
        if resultVar in tr.definedVarNames: continue

        # Identify which eq_reif is the "then" (variable test) and which is "else" (constant test)
        var thenIdx, elseIdx: int = -1
        for i, e in eqEntries:
            if e.isConstTest:
                elseIdx = i
            else:
                thenIdx = i
        if thenIdx < 0 or elseIdx < 0: continue

        let thenEntry = eqEntries[thenIdx]
        let elseEntry = eqEntries[elseIdx]
        let elseVal = elseEntry.constVal
        let thenVarName = thenEntry.varName

        # Find bool_clause linking thenEntry.boolVar to a condition b
        # Pattern A: bool_clause([thenEntry.boolVar], [b]) — b → result==curr
        var condBoolVar = ""
        var clauseA_ci = -1
        if thenEntry.boolVar in boolClausesByLit:
            for bc in boolClausesByLit[thenEntry.boolVar]:
                if bc.ci in tr.definingConstraints: continue
                if bc.posLits.len == 1 and bc.negLits.len == 1 and bc.posLits[0] == thenEntry.boolVar:
                    # bool_clause([b1], [b]) → b → b1
                    let candidateB = bc.negLits[0]
                    if candidateB in linNeReifMap:
                        condBoolVar = candidateB
                        clauseA_ci = bc.ci
                        break

        if condBoolVar == "": continue
        let linNeEntry = linNeReifMap[condBoolVar]

        # Verify: thenVarName must be the "curr" variable from int_lin_ne_reif
        if thenVarName != linNeEntry.currVar: continue

        # Find bool_clause Pattern B: bool_clause([condBoolVar, elseEntry.boolVar], [])
        # — ¬b → b2: if prev==curr then result==elseVal
        var clauseB_ci = -1
        if condBoolVar in boolClausesByLit:
            for bc in boolClausesByLit[condBoolVar]:
                if bc.ci in tr.definingConstraints: continue
                if bc.ci == clauseA_ci: continue
                if bc.posLits.len == 2 and bc.negLits.len == 0:
                    if (bc.posLits[0] == condBoolVar and bc.posLits[1] == elseEntry.boolVar) or
                          (bc.posLits[1] == condBoolVar and bc.posLits[0] == elseEntry.boolVar):
                        clauseB_ci = bc.ci
                        break

        if clauseB_ci < 0: continue

        # Full pattern matched! Build 2D table channel.
        let prevVarName = linNeEntry.prevVar
        let currVarName = linNeEntry.currVar

        if prevVarName notin tr.varPositions and prevVarName notin tr.definedVarExprs: continue
        if currVarName notin tr.varPositions and currVarName notin tr.definedVarExprs: continue

        let prevExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: prevVarName))
        let currExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: currVarName))
        let resultPos = tr.varPositions[resultVar]

        # Get domains for the 2D table
        var prevPos, currPos: int
        if prevExpr.node.kind == RefNode:
            prevPos = prevExpr.node.position
        else: continue
        if currExpr.node.kind == RefNode:
            currPos = currExpr.node.position
        else: continue

        let prevDom = tr.sys.baseArray.domain[prevPos].sorted()
        let currDom = tr.sys.baseArray.domain[currPos].sorted()
        if prevDom.len == 0 or currDom.len == 0: continue

        let loPrev = prevDom[0]
        let hiPrev = prevDom[^1]
        let loCurr = currDom[0]
        let hiCurr = currDom[^1]
        let rangePrev = hiPrev - loPrev + 1
        let rangeCurr = hiCurr - loCurr + 1
        let tableSize = rangePrev * rangeCurr

        if tableSize > 100_000: continue  # safety limit

        var arrayElems = newSeq[ArrayElement[int]](tableSize)
        for vp in loPrev..hiPrev:
            for vc in loCurr..hiCurr:
                let idx = (vp - loPrev) * rangeCurr + (vc - loCurr)
                if vp != vc:
                    arrayElems[idx] = ArrayElement[int](isConstant: true, constantValue: vc)
                else:
                    arrayElems[idx] = ArrayElement[int](isConstant: true, constantValue: elseVal)

        # Build index expression: (prev - loPrev) * rangeCurr + (curr - loCurr)
        let indexExpr = (prevExpr - loPrev) * rangeCurr + (currExpr - loCurr)

        tr.sys.baseArray.addChannelBinding(resultPos, indexExpr, arrayElems)
        tr.channelVarNames.incl(resultVar)

        # Mark consumed constraints
        tr.definingConstraints.incl(linNeEntry.ci)  # int_lin_ne_reif
        tr.definingConstraints.incl(clauseA_ci)     # bool_clause pattern A
        tr.definingConstraints.incl(clauseB_ci)     # bool_clause pattern B
        # The two int_eq_reif are already reif channel defs — mark them as consumed too
        # so their channel bindings for b1/b2 are not created (they're no longer needed)
        tr.definingConstraints.incl(thenEntry.ci)
        tr.definingConstraints.incl(elseEntry.ci)

        inc totalChannels

    if totalChannels > 0:
        stderr.writeLine(&"[FZN] Detected {totalChannels} if-then-else channels")

proc detectGccCountChannels(tr: var FznTranslator) =
    ## Detects fzn_global_cardinality constraints whose count outputs are pure channels
    ## (only used by the GCC itself and downstream min/max/objective chains).
    ## Converts count outputs to CountEqChannelBindings, eliminating the need for
    ## indicator decomposition.
    ##
    ## Pattern: fzn_global_cardinality(x, cover, counts) where each count var is
    ## referenced only by this GCC + array_int_minimum/maximum defines_var constraints.

    # Build set of min/max channel def constraint indices for fast lookup
    var minMaxCIs: PackedSet[int]
    for def in tr.minMaxChannelDefs:
        minMaxCIs.incl(def.ci)

    var totalChannels = 0

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = con.name
        if name != "fzn_global_cardinality": continue

        # Extract count variable names (skip if counts are all constants)
        let countArg = con.args[2]
        if countArg.kind != FznArrayLit and countArg.kind != FznIdent: continue

        var countNames: seq[string]
        if countArg.kind == FznArrayLit:
            var hasVariable = false
            for elem in countArg.elems:
                if elem.kind == FznIdent and elem.ident notin tr.paramValues:
                    hasVariable = true
                    countNames.add(elem.ident)
                elif elem.kind == FznIdent and elem.ident in tr.paramValues:
                    countNames.setLen(0); break  # mixed constant/variable — skip
                else:
                    countNames.setLen(0); break
            if not hasVariable: continue
        elif countArg.kind == FznIdent:
            # Array variable reference — resolve to element names
            if countArg.ident in tr.arrayElementNames:
                countNames = tr.arrayElementNames[countArg.ident]
            else:
                continue

        if countNames.len == 0: continue

        # Check all count vars have positions (not already eliminated)
        var allHavePos = true
        for cname in countNames:
            if cname notin tr.varPositions:
                allHavePos = false; break
        if not allHavePos: continue

        # Count variables may be referenced by downstream constraints (e.g., cnt <= limit).
        # This is fine: they become CountEq channels, and downstream constraints become
        # channel-dep constraints evaluated through the cascade system.

        # All checks passed — convert count outputs to channel bindings
        let cover = tr.resolveIntArray(con.args[1])
        let xArg = con.args[0]
        var inputPositions: seq[int]
        var constantValues: seq[int]  # constant elements in the x-array
        var xArgValid = true
        if xArg.kind == FznArrayLit:
            for elem in xArg.elems:
                if elem.kind == FznIdent:
                    if elem.ident in tr.paramValues:
                        constantValues.add(tr.paramValues[elem.ident])
                    elif elem.ident in tr.varPositions:
                        inputPositions.add(tr.varPositions[elem.ident])
                    elif elem.ident in tr.definedVarExprs:
                        let expr = tr.definedVarExprs[elem.ident]
                        if expr.node.kind == RefNode:
                            inputPositions.add(expr.node.position)
                        else:
                            xArgValid = false; break
                    else:
                        xArgValid = false; break
                elif elem.kind == FznIntLit:
                    constantValues.add(elem.intVal)
                else:
                    xArgValid = false; break
        elif xArg.kind == FznIdent and xArg.ident in tr.arrayPositions:
            inputPositions = tr.arrayPositions[xArg.ident]
        else:
            continue

        if not xArgValid or inputPositions.len == 0: continue
        let totalElements = inputPositions.len + constantValues.len

        # Build expressions for input positions (needed for bound constraints)
        var inputExprs: seq[AlgebraicExpression[int]]
        for pos in inputPositions:
            inputExprs.add(tr.getExpr(pos))

        for i, cname in countNames:
            let countPos = tr.varPositions[cname]
            # Count how many constant elements match this cover value
            var constOffset = 0
            for cv in constantValues:
                if cv == cover[i]: inc constOffset
            tr.sys.baseArray.addCountEqChannelBinding(countPos, cover[i], inputPositions, constOffset)
            tr.channelVarNames.incl(cname)

            # MiniZinc may have absorbed bound constraints (cnt <= limit) into the
            # variable domain. Since channel positions don't enforce domains during
            # search, we must add explicit atMost/atLeast constraints.
            let dom = tr.sys.baseArray.domain[countPos]
            if dom.len > 0:
                let domMin = dom[0]
                let domMax = dom[^1]
                let effectiveMax = totalElements - constOffset  # max possible from variable positions
                if domMax < effectiveMax:
                    tr.sys.addConstraint(atMost[int](inputExprs, cover[i], domMax - constOffset))
                if domMin > constOffset:
                    tr.sys.addConstraint(atLeast[int](inputExprs, cover[i], domMin - constOffset))

            inc totalChannels

        tr.definingConstraints.incl(ci)  # GCC is consumed — counts are channels now

    if totalChannels > 0:
        stderr.writeLine(&"[FZN] Detected {totalChannels} GCC count channels")

proc buildBoolAndChannelBindings*(tr: var FznTranslator) =
    ## Builds channel bindings for bool AND patterns detected by detectBoolAndChannels().
    ## For bool_clause([b], [c1, ..., cn]): b = AND(c1, ..., cn)
    ##   index = c1 + c2 + ... + cn  (sum of n boolean channels, range 0..n)
    ##   array = [0, 0, ..., 0, 1]   (size n+1, value 1 only when all n conditions are 1)
    ## Must be called after translateVariables() and buildReifChannelBindings().

    var built = 0
    for pattern in tr.boolAndChannelDefs:
        let bName = pattern.resultVar
        if bName notin tr.varPositions:
            continue  # Variable was eliminated — skip
        let bPos = tr.varPositions[bName]
        let n = pattern.condVars.len

        # Build index expression: sum of all condition channels
        var condExprs: seq[AlgebraicExpression[int]]
        var allValid = true
        for cName in pattern.condVars:
            if cName in tr.varPositions:
                condExprs.add(tr.getExpr(tr.varPositions[cName]))
            elif cName in tr.definedVarExprs:
                condExprs.add(tr.definedVarExprs[cName])
            else:
                allValid = false
                break
        if not allValid or condExprs.len == 0: continue

        # Build linear sum: c1 + c2 + ... + cn as AlgebraicExpression
        var indexExpr = condExprs[0]
        for i in 1..<condExprs.len:
            indexExpr = indexExpr + condExprs[i]

        # Build array: [0, 0, ..., 0, 1] — true only when ALL n conditions are 1
        var arrayElems: seq[ArrayElement[int]]
        for i in 0..n:
            arrayElems.add(ArrayElement[int](isConstant: true,
                    constantValue: if i == n: 1 else: 0))

        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)
        inc built

    if built > 0:
        stderr.writeLine(&"[FZN] Built {built} bool AND channel bindings")

proc buildConditionalImplicationChannelBindings*(tr: var FznTranslator) =
    ## Builds channel bindings for conditional implication patterns detected by
    ## detectConditionalImplicationChannels().
    ##
    ## Binary conditional: Z = element(cond, [val_when_0, val_when_1])
    ##   where val_when_0/1 are variable positions (e.g., min/max of two vars).
    ##
    ## One-hot conditional: Z = element(weighted_sum, [v_0, ..., v_{N-1}])
    ##   where weighted_sum = sum(i * cond_i), cond_i are boolean eq_reif channels.
    ## Must be called after translateVariables() and buildReifChannelBindings().

    var nBinary = 0
    var nOneHot = 0

    # Build binary conditional channel bindings
    for def in tr.binaryCondChannelDefs:
        if def.targetVar notin tr.varPositions: continue
        if def.condChannel notin tr.varPositions: continue
        if def.val0Var notin tr.varPositions: continue
        if def.val1Var notin tr.varPositions: continue
        let targetPos = tr.varPositions[def.targetVar]
        let condPos = tr.varPositions[def.condChannel]
        let val0Pos = tr.varPositions[def.val0Var]
        let val1Pos = tr.varPositions[def.val1Var]

        let indexExpr = tr.getExpr(condPos)
        var arrayElems: seq[ArrayElement[int]]
        arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: val0Pos))
        arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: val1Pos))

        tr.sys.baseArray.addChannelBinding(targetPos, indexExpr, arrayElems)
        inc nBinary

    # Build one-hot conditional channel bindings
    for def in tr.oneHotCondChannelDefs:
        if def.targetVar notin tr.varPositions: continue
        let targetPos = tr.varPositions[def.targetVar]
        let n = def.condChannels.len

        # Build index expression: sum(i * cond_i) for i=0..N-1
        # Since cond_i is boolean (0/1), exactly one is 1 under allDifferent
        # Index = the i for which cond_i = 1
        var condExprs: seq[AlgebraicExpression[int]]
        var allValid = true
        for cName in def.condChannels:
            if cName in tr.varPositions:
                condExprs.add(tr.getExpr(tr.varPositions[cName]))
            elif cName in tr.definedVarExprs:
                condExprs.add(tr.definedVarExprs[cName])
            else:
                allValid = false
                break
        if not allValid or condExprs.len == 0: continue

        # weighted_sum = 0*cond_0 + 1*cond_1 + 2*cond_2 + ... + (N-1)*cond_{N-1}
        # = cond_1 + 2*cond_2 + ... + (N-1)*cond_{N-1}
        var indexExpr: AlgebraicExpression[int]
        var hasTerms = false
        for i in 1..<n:  # skip i=0 (coefficient 0)
            let term = i * condExprs[i]
            if not hasTerms:
                indexExpr = term
                hasTerms = true
            else:
                indexExpr = indexExpr + term
        if not hasTerms:
            # n=1 should not occur (detection requires entries.len >= 2), but handle defensively
            indexExpr = newAlgebraicExpression[int](
                positions=initPackedSet[int](),
                node=ExpressionNode[int](kind: LiteralNode, value: 0),
                linear=true)

        # Build constant array: [val_0, val_1, ..., val_{N-1}]
        var arrayElems: seq[ArrayElement[int]]
        for v in def.targetVals:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

        tr.sys.baseArray.addChannelBinding(targetPos, indexExpr, arrayElems)
        inc nOneHot

    if nBinary > 0 or nOneHot > 0:
        stderr.writeLine(&"[FZN] Built conditional implication channel bindings: {nBinary} binary, {nOneHot} one-hot")

proc buildBoolEquivAliasBindings*(tr: var FznTranslator) =
    ## Builds channel bindings for bool equivalence alias patterns detected by
    ## detectBoolEquivalenceChannels().
    ## For aliasVar ↔ canonicalVar: alias = element(canonical, [0, 1])
    ## which is an identity channel binding.
    ## Must be called after translateVariables() and buildReifChannelBindings().

    var built = 0
    for def in tr.boolEquivAliasDefs:
        if def.aliasVar notin tr.varPositions: continue
        if def.canonicalVar notin tr.varPositions:
            # canonical may be in definedVarExprs
            if def.canonicalVar notin tr.definedVarExprs: continue
        let aliasPos = tr.varPositions[def.aliasVar]

        let indexExpr = if def.canonicalVar in tr.varPositions:
            tr.getExpr(tr.varPositions[def.canonicalVar])
        else:
            tr.definedVarExprs[def.canonicalVar]

        # Identity lookup: [0, 1] indexed by canonical value
        var arrayElems: seq[ArrayElement[int]]
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))

        tr.sys.baseArray.addChannelBinding(aliasPos, indexExpr, arrayElems)
        inc built

    if built > 0:
        stderr.writeLine(&"[FZN] Built {built} bool equivalence alias channel bindings")

proc buildBoolGatedVarChannelBindings*(tr: var FznTranslator) =
    ## Builds channel bindings for bool-gated variable channel patterns detected by
    ## detectBoolGatedVariableChannels().
    ## For targetVar = if condVar then valVar else constValue:
    ##   target = element(cond, [constValue, valVarPos])
    ## where cond=0 → constValue, cond=1 → valVar.
    ## Must be called after translateVariables() and buildReifChannelBindings().

    var built = 0
    for def in tr.boolGatedVarChannelDefs:
        if def.targetVar notin tr.varPositions: continue
        if def.condVar notin tr.varPositions:
            if def.condVar notin tr.definedVarExprs: continue
        if def.valVar notin tr.varPositions:
            if def.valVar notin tr.definedVarExprs: continue

        let targetPos = tr.varPositions[def.targetVar]

        let indexExpr = if def.condVar in tr.varPositions:
            tr.getExpr(tr.varPositions[def.condVar])
        else:
            tr.definedVarExprs[def.condVar]

        # Build array: [constValue, valVar] indexed by condition (0=const, 1=var)
        var arrayElems: seq[ArrayElement[int]]
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: def.constValue))
        if def.valVar in tr.varPositions:
            arrayElems.add(ArrayElement[int](isConstant: false,
                                             variablePosition: tr.varPositions[def.valVar]))
        else:
            # valVar is a defined expression — we need a position for it.
            # Skip this binding if valVar doesn't have a position.
            continue

        tr.sys.baseArray.addChannelBinding(targetPos, indexExpr, arrayElems)
        inc built

    if built > 0:
        stderr.writeLine(&"[FZN] Built {built} bool-gated variable channel bindings")

    # Build variable-default bool-gated channels: target = element(cond, [val0Var, val1Var])
    var builtVV = 0
    for def in tr.boolGatedVarVarChannelDefs:
        if def.targetVar notin tr.varPositions: continue
        if def.condVar notin tr.varPositions:
            if def.condVar notin tr.definedVarExprs: continue
        if def.val1Var notin tr.varPositions:
            if def.val1Var notin tr.definedVarExprs: continue
        if def.val0Var notin tr.varPositions:
            if def.val0Var notin tr.definedVarExprs: continue

        let targetPos = tr.varPositions[def.targetVar]
        let indexExpr = if def.condVar in tr.varPositions:
            tr.getExpr(tr.varPositions[def.condVar])
        else:
            tr.definedVarExprs[def.condVar]

        # array[0] = val0Var (when cond=0), array[1] = val1Var (when cond=1)
        var arrayElems: seq[ArrayElement[int]]
        if def.val0Var in tr.varPositions:
            arrayElems.add(ArrayElement[int](isConstant: false,
                                             variablePosition: tr.varPositions[def.val0Var]))
        else: continue
        if def.val1Var in tr.varPositions:
            arrayElems.add(ArrayElement[int](isConstant: false,
                                             variablePosition: tr.varPositions[def.val1Var]))
        else: continue

        tr.sys.baseArray.addChannelBinding(targetPos, indexExpr, arrayElems)
        inc builtVV

    if builtVV > 0:
        stderr.writeLine(&"[FZN] Built {builtVV} bool-gated variable-default channel bindings")

proc buildNetFlowVariables*(tr: var FznTranslator) =
    ## Creates net_flow search variables for free pairs, defined expressions for dependent
    ## pairs, and channel bindings for V_in/V_out from net_flow.
    ##
    ## After this proc:
    ## - Free net_flow vars have positions in varPositions (search variables)
    ## - Dependent net_flow vars have expressions in definedVarExprs
    ## - V_in/V_out positions are channel-bound to their net_flow expression
    ## - Existing int_le_reif + bool2int detection will chain Z/Zint from V_in/V_out

    let D = tr.netFlowDomainBound  # e.g., 50
    let nPairs = tr.netFlowPairInVar.len

    # Map pair index → net_flow variable name
    var pairNetFlowName = newSeq[string](nPairs)
    for pid in 0..<nPairs:
        pairNetFlowName[pid] = "net_flow_" & $pid

    # Step 1: Create free net_flow search variables with domain [-D, D]
    for pid in tr.netFlowFreePairs:
        let nfName = pairNetFlowName[pid]
        let pos = tr.sys.baseArray.len
        let v = tr.sys.newConstrainedVariable()
        v.setDomain(toSeq(-D..D))
        tr.varPositions[nfName] = pos

    stderr.writeLine(&"[FZN] Created {tr.netFlowFreePairs.len} free net_flow search positions (domain [{-D}..{D}])")

    # Step 2: Build defined expressions for dependent net_flow pairs (topo order).
    # Reversed peel order guarantees each term's pair is already resolved (free pair
    # in varPositions, or earlier dependent pair in definedVarExprs).
    var nDepBuilt = 0
    for di in 0..<tr.netFlowDependentPairs.len:
        let depPid = tr.netFlowDependentPairs[di]
        let nfName = pairNetFlowName[depPid]
        let terms = tr.netFlowDepTerms[di]
        # Build expression: sum of coeff * net_flow[other_pair]
        var expr = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 0),
            linear = true
        )
        for term in terms:
            let otherName = pairNetFlowName[term.pairId]
            assert otherName in tr.varPositions or otherName in tr.definedVarExprs,
                "net_flow dependency " & otherName & " not yet resolved for " & nfName
            let otherExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: otherName))
            if term.coeff == 1:
                expr = expr + otherExpr
            elif term.coeff == -1:
                expr = expr - otherExpr
            else:
                expr = expr + term.coeff * otherExpr
        tr.definedVarExprs[nfName] = expr
        inc nDepBuilt

    stderr.writeLine(&"[FZN] Built {nDepBuilt} dependent net_flow defined expressions")

    # Step 3: Domain reduction through tree propagation
    # Every pair's net_flow must be in [-D, D] (V_in/V_out must be in [0, D]).
    # For dependent pairs that are sums of other pairs, the unconstrained range
    # can exceed [-D, D]. Propagate backwards to tighten free pair domains.
    type PairRange = tuple[lo, hi: int]

    var pairRange = newSeq[PairRange](nPairs)
    # Initialize free pairs to [-D, D]
    for pid in tr.netFlowFreePairs:
        pairRange[pid] = (-D, D)

    # Initialize dependent pair ranges to 0 (will be computed)
    for pid in tr.netFlowDependentPairs:
        pairRange[pid] = (0, 0)

    # Forward pass: compute dependent pair ranges in topo order
    for di in 0..<tr.netFlowDependentPairs.len:
        let depPid = tr.netFlowDependentPairs[di]
        let terms = tr.netFlowDepTerms[di]
        var lo, hi = 0
        for term in terms:
            let r = pairRange[term.pairId]
            if term.coeff > 0:
                lo += term.coeff * r.lo
                hi += term.coeff * r.hi
            else:
                lo += term.coeff * r.hi
                hi += term.coeff * r.lo
        pairRange[depPid] = (lo, hi)

    # Iterate: clamp dependent ranges to [-D, D] and propagate backward
    var changed = true
    var iterations = 0
    while changed and iterations < 100:
        changed = false
        inc iterations

        # Backward pass: process dependent pairs in reverse topo order
        for di in countdown(tr.netFlowDependentPairs.len - 1, 0):
            let depPid = tr.netFlowDependentPairs[di]
            let terms = tr.netFlowDepTerms[di]

            # Clamp this pair's range to [-D, D]
            var r = pairRange[depPid]
            if r.lo < -D: r.lo = -D; changed = true
            if r.hi > D: r.hi = D; changed = true
            pairRange[depPid] = r

            # Propagate to contributing pairs
            for ti, term in terms:
                # Compute range of all OTHER terms
                var othersLo, othersHi = 0
                for tj, otherTerm in terms:
                    if tj == ti: continue
                    let oRange = pairRange[otherTerm.pairId]
                    if otherTerm.coeff > 0:
                        othersLo += otherTerm.coeff * oRange.lo
                        othersHi += otherTerm.coeff * oRange.hi
                    else:
                        othersLo += otherTerm.coeff * oRange.hi
                        othersHi += otherTerm.coeff * oRange.lo

                # depRange.lo <= coeff * term_val + others <= depRange.hi
                # => (depRange.lo - othersHi) / coeff <= term_val <= (depRange.hi - othersLo) / coeff
                var newLo, newHi: int
                if term.coeff > 0:  # coeff = 1
                    newLo = r.lo - othersHi
                    newHi = r.hi - othersLo
                else:  # coeff = -1
                    newLo = othersLo - r.hi
                    newHi = othersHi - r.lo

                # Intersect with current range
                let cur = pairRange[term.pairId]
                let tLo = max(cur.lo, newLo)
                let tHi = min(cur.hi, newHi)
                if tLo > cur.lo or tHi < cur.hi:
                    pairRange[term.pairId] = (tLo, tHi)
                    changed = true

        # Forward pass: recompute dependent pair ranges with tightened inputs
        for di in 0..<tr.netFlowDependentPairs.len:
            let depPid = tr.netFlowDependentPairs[di]
            let terms = tr.netFlowDepTerms[di]
            var lo, hi = 0
            for term in terms:
                let r = pairRange[term.pairId]
                if term.coeff > 0:
                    lo += term.coeff * r.lo
                    hi += term.coeff * r.hi
                else:
                    lo += term.coeff * r.hi
                    hi += term.coeff * r.lo
            # Clamp to [-D, D]
            lo = max(-D, lo)
            hi = min(D, hi)
            let prev = pairRange[depPid]
            if lo != prev.lo or hi != prev.hi:
                pairRange[depPid] = (lo, hi)
                changed = true

    # Apply domain reductions to free pair positions
    var nDomainReductions = 0
    var totalSaved = 0
    for pid in tr.netFlowFreePairs:
        let r = pairRange[pid]
        if r.lo > -D or r.hi < D:
            let nfName = pairNetFlowName[pid]
            let pos = tr.varPositions[nfName]
            let oldSize = 2 * D + 1
            tr.sys.baseArray.setDomain(pos, toSeq(r.lo..r.hi))
            totalSaved += oldSize - (r.hi - r.lo + 1)
            inc nDomainReductions

    # Add range constraints for dependent pairs whose unclamped range exceeds [-D, D]
    # These enforce |net_flow[d]| ≤ D which is required for V_in/V_out ∈ [0, D]
    # Recompute unclamped ranges to check which pairs actually need constraints
    var nRangeConstraints = 0
    for di in 0..<tr.netFlowDependentPairs.len:
        let depPid = tr.netFlowDependentPairs[di]
        let terms = tr.netFlowDepTerms[di]
        var uLo, uHi = 0  # unclamped range
        for term in terms:
            let r = pairRange[term.pairId]
            if term.coeff > 0:
                uLo += term.coeff * r.lo
                uHi += term.coeff * r.hi
            else:
                uLo += term.coeff * r.hi
                uHi += term.coeff * r.lo
        if uLo < -D or uHi > D:
            let nfName = pairNetFlowName[depPid]
            let expr = tr.definedVarExprs[nfName]
            if uLo < -D:
                tr.sys.addConstraint(expr >= -D)
            if uHi > D:
                tr.sys.addConstraint(expr <= D)
            inc nRangeConstraints

    stderr.writeLine(&"[FZN] Net flow domain reduction: {nDomainReductions}/{tr.netFlowFreePairs.len} free pairs tightened, {nRangeConstraints} range constraints added ({iterations} iterations, {totalSaved} values removed)")

    # Step 4: Build channel bindings for V_in/V_out from net_flow
    # Per-pair tables cover the actual range [lo, hi] of each pair's net_flow
    # V_in = max(0, net_flow) = element(net_flow - lo, [max(0, v) for v in lo..hi])
    # V_out = max(0, -net_flow) = element(net_flow - lo, [max(0, -v) for v in lo..hi])
    var nChannelBindings = 0
    for pid in 0..<nPairs:
        let nfName = pairNetFlowName[pid]
        let nfExpr = tr.resolveExprArg(FznExpr(kind: FznIdent, ident: nfName))
        let r = pairRange[pid]
        let indexExpr = nfExpr - r.lo  # shift to 0-based

        # Build per-pair lookup tables
        var tableVin: seq[ArrayElement[int]]
        var tableVout: seq[ArrayElement[int]]
        for v in r.lo..r.hi:
            tableVin.add(ArrayElement[int](isConstant: true, constantValue: max(0, v)))
            tableVout.add(ArrayElement[int](isConstant: true, constantValue: max(0, -v)))

        # V_in channel binding
        let inVarName = tr.netFlowPairInVar[pid]
        if inVarName in tr.varPositions:
            let inPos = tr.varPositions[inVarName]
            tr.sys.baseArray.addChannelBinding(inPos, indexExpr, tableVin)
            inc nChannelBindings

        # V_out channel binding
        let outVarName = tr.netFlowPairOutVar[pid]
        if outVarName in tr.varPositions:
            let outPos = tr.varPositions[outVarName]
            tr.sys.baseArray.addChannelBinding(outPos, indexExpr, tableVout)
            inc nChannelBindings

    stderr.writeLine(&"[FZN] Built {nChannelBindings} V_in/V_out channel bindings from net_flow")

