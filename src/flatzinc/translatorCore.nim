## Included from translator.nim -- not a standalone module.

proc translateParameters(tr: var FznTranslator) =
    ## Process parameter declarations (constant values and arrays).
    ## Must be called before collectDefinedVars since it needs resolveIntArray.
    for decl in tr.model.parameters:
        let isSetType = decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}
        if decl.isArray:
            if isSetType:
                # Array of set parameters: store per-element set values
                if decl.value != nil and decl.value.kind == FznArrayLit:
                    var setVals = newSeq[seq[int]](decl.value.elems.len)
                    for i, e in decl.value.elems:
                        case e.kind
                        of FznSetLit, FznRange:
                            setVals[i] = extractSetValues(e)
                        of FznIdent:
                            if e.ident in tr.setParamValues:
                                setVals[i] = tr.setParamValues[e.ident]
                            else:
                                setVals[i] = @[]
                        else:
                            setVals[i] = @[]
                    tr.setArrayValues[decl.name] = setVals
            elif decl.value != nil and decl.value.kind == FznArrayLit:
                var vals = newSeq[int](decl.value.elems.len)
                for i, e in decl.value.elems:
                    case e.kind
                    of FznIntLit:
                        vals[i] = e.intVal
                    of FznBoolLit:
                        vals[i] = if e.boolVal: 1 else: 0
                    of FznIdent:
                        if e.ident in tr.paramValues:
                            vals[i] = tr.paramValues[e.ident]
                        else:
                            vals[i] = 0  # fallback
                    else:
                        vals[i] = 0
                tr.arrayValues[decl.name] = vals
        else:
            # Single parameter
            if isSetType:
                if decl.value != nil:
                    tr.setParamValues[decl.name] = extractSetValues(decl.value)
            elif decl.value != nil:
                case decl.value.kind
                of FznIntLit:
                    tr.paramValues[decl.name] = decl.value.intVal
                of FznBoolLit:
                    tr.paramValues[decl.name] = if decl.value.boolVal: 1 else: 0
                else:
                    discard

proc translateVariables(tr: var FznTranslator) =
    ## Creates ConstrainedVariables for all FZN variable declarations and sets domains.

    # First pass: create all variables (non-array), skipping defined variables
    var nSetVars = 0
    var nSetBools = 0
    for decl in tr.model.variables:
        if decl.isArray:
            continue
        # Skip variables that will be replaced by defining expressions
        if decl.name in tr.definedVarNames:
            if decl.hasAnnotation("output_var"):
                tr.outputVars.add(decl.name)
                if decl.varType.kind == FznBool:
                    tr.outputBoolVars.incl(decl.name)
            # Record domain bounds for later constraint generation
            if decl.varType.kind == FznIntRange:
                tr.definedVarBounds[decl.name] = (decl.varType.lo, decl.varType.hi)
            continue

        # Handle set variables: decompose into boolean arrays
        if decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
            # Skip boolean creation for chain intermediates and singletons
            if decl.name in tr.skipSetVarNames:
                tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: 0, hi: -1)
                if decl.hasAnnotation("output_var"):
                    tr.outputSetVars.incl(decl.name)
                continue
            var lo, hi: int
            case decl.varType.kind
            of FznSetOfIntRange:
                lo = decl.varType.setLo
                hi = decl.varType.setHi
            of FznSetOfIntSet:
                if decl.varType.setValues.len == 0:
                    tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: 0, hi: -1)
                    continue
                lo = decl.varType.setValues.min
                hi = decl.varType.setValues.max
            of FznSetOfInt:
                stderr.writeLine(&"[FZN] Warning: unbounded 'set of int' variable '{decl.name}', skipping decomposition")
                tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: 0, hi: -1)
                if decl.hasAnnotation("output_var"):
                    tr.outputSetVars.incl(decl.name)
                continue
            else: discard

            if lo > hi:
                tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: lo, hi: hi)
                if decl.hasAnnotation("output_var"):
                    tr.outputSetVars.incl(decl.name)
                continue

            let size = hi - lo + 1
            var boolPositions = newSeq[int](size)

            # Determine fixed values if the variable has an assignment
            var fixedValues: seq[int]
            var hasFixed = false
            if decl.value != nil:
                fixedValues = extractSetValues(decl.value)
                hasFixed = true

            for i in 0..<size:
                let bpos = tr.sys.baseArray.len
                let bv = tr.sys.newConstrainedVariable()
                if hasFixed:
                    # Fix boolean: 1 if element is in the fixed set, 0 otherwise
                    if (lo + i) in fixedValues:
                        bv.setDomain(@[1])
                    else:
                        bv.setDomain(@[0])
                else:
                    bv.setDomain(@[0, 1])
                boolPositions[i] = bpos

            tr.setVarBoolPositions[decl.name] = SetVarInfo(
                positions: boolPositions, lo: lo, hi: hi)
            inc nSetVars
            nSetBools += size

            if decl.hasAnnotation("output_var"):
                tr.outputSetVars.incl(decl.name)
            continue

        let pos = tr.sys.baseArray.len
        let v = tr.sys.newConstrainedVariable()
        tr.varPositions[decl.name] = pos

        # Set domain based on type, considering fixed values and presolve tightening
        if decl.value != nil and decl.value.kind == FznBoolLit:
            v.setDomain(@[if decl.value.boolVal: 1 else: 0])
            tr.channelVarNames.incl(decl.name)
        elif decl.value != nil and decl.value.kind == FznIntLit:
            v.setDomain(@[decl.value.intVal])
            tr.channelVarNames.incl(decl.name)
        elif decl.name in tr.presolveDomains:
            # Presolve tightened this domain
            let pdom = tr.presolveDomains[decl.name]
            v.setDomain(pdom)
            if pdom.len == 1:
                tr.channelVarNames.incl(decl.name)
        else:
            case decl.varType.kind
            of FznIntRange:
                v.setDomain(toSeq(decl.varType.lo..decl.varType.hi))
            of FznIntSet:
                v.setDomain(decl.varType.values)
            of FznBool:
                v.setDomain(@[0, 1])
            of FznInt:
                # Unbounded int - use a reasonable range
                v.setDomain(toSeq(-1000..1000))
            else:
                v.setDomain(toSeq(-100..100))

        # Check for output annotations
        if decl.hasAnnotation("output_var"):
            tr.outputVars.add(decl.name)
            if decl.varType.kind == FznBool:
                tr.outputBoolVars.incl(decl.name)

    if nSetVars > 0:
        stderr.writeLine(&"[FZN] Set decomposition: {nSetVars} set variables -> {nSetBools} boolean variables")

    # Second pass: process variable arrays (they reference already-created variables)
    for decl in tr.model.variables:
        if not decl.isArray:
            continue

        # Handle set-typed arrays: decompose into per-element SetArrayElement records
        if decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
            if decl.value != nil and decl.value.kind == FznArrayLit:
                var elems = newSeq[SetArrayElement](decl.value.elems.len)
                for i, e in decl.value.elems:
                    case e.kind
                    of FznIdent:
                        if e.ident in tr.setVarBoolPositions:
                            elems[i] = SetArrayElement(isConstant: false, varName: e.ident)
                        elif e.ident in tr.setParamValues:
                            elems[i] = SetArrayElement(isConstant: true, constantValues: tr.setParamValues[e.ident])
                        else:
                            elems[i] = SetArrayElement(isConstant: true, constantValues: @[])
                    of FznSetLit, FznRange:
                        elems[i] = SetArrayElement(isConstant: true, constantValues: extractSetValues(e))
                    else:
                        elems[i] = SetArrayElement(isConstant: true, constantValues: @[])
                tr.setArrayDecompositions[decl.name] = elems
            if decl.hasAnnotation("output_array"):
                tr.outputSetArrays.incl(decl.name)
            continue

        if decl.value != nil and decl.value.kind == FznArrayLit:
            var positions = newSeq[int](decl.value.elems.len)
            var allConstants = true
            var constantVals = newSeq[int](decl.value.elems.len)

            var elemNames = newSeq[string](decl.value.elems.len)
            for i, e in decl.value.elems:
                case e.kind
                of FznIdent:
                    elemNames[i] = e.ident
                    if e.ident in tr.definedVarNames:
                        # Defined variable - use sentinel position, expression will be used later
                        positions[i] = -1
                        allConstants = false
                    elif e.ident in tr.varPositions:
                        positions[i] = tr.varPositions[e.ident]
                        allConstants = false
                    elif e.ident in tr.paramValues:
                        # Constant in a "var" array - create a variable with singleton domain
                        let cpos = tr.sys.baseArray.len
                        let v = tr.sys.newConstrainedVariable()
                        let val = tr.paramValues[e.ident]
                        v.setDomain(@[val])
                        tr.varPositions[e.ident & "_const_" & $i] = cpos
                        positions[i] = cpos
                        constantVals[i] = val
                    else:
                        raise newException(KeyError, &"Unknown identifier '{e.ident}' in array '{decl.name}'")
                of FznIntLit:
                    # Constant in a variable array - create a variable with singleton domain
                    let cpos = tr.sys.baseArray.len
                    let v = tr.sys.newConstrainedVariable()
                    v.setDomain(@[e.intVal])
                    positions[i] = cpos
                    constantVals[i] = e.intVal
                of FznBoolLit:
                    let val = if e.boolVal: 1 else: 0
                    let cpos = tr.sys.baseArray.len
                    let v = tr.sys.newConstrainedVariable()
                    v.setDomain(@[val])
                    positions[i] = cpos
                    constantVals[i] = val
                else:
                    discard

            tr.arrayPositions[decl.name] = positions
            tr.arrayElementNames[decl.name] = elemNames
            if allConstants:
                tr.arrayValues[decl.name] = constantVals

        # Check for output_array annotation
        if decl.hasAnnotation("output_array"):
            let ann = decl.getAnnotation("output_array")
            var lo = 1
            var hi = decl.arraySize
            if ann.args.len > 0 and ann.args[0].kind == FznArrayLit:
                let indexRanges = ann.args[0]
                if indexRanges.elems.len > 0 and indexRanges.elems[0].kind == FznRange:
                    lo = indexRanges.elems[0].lo
                    hi = indexRanges.elems[0].hi
            tr.outputArrays.add((name: decl.name, lo: lo, hi: hi))
            if decl.varType.kind == FznBool:
                tr.outputBoolArrays.incl(decl.name)

proc decomposeWithIndicators(tr: var FznTranslator,
        exprs: seq[AlgebraicExpression[int]],
        cover: seq[int],
        countExprs: seq[AlgebraicExpression[int]]) =
    ## Decompose a global cardinality constraint into indicator variables.
    ## For each cover value v, creates: sum_j (x_j == v ? 1 : 0) == counts[i]
    for i, v in cover:
        var indicators: seq[AlgebraicExpression[int]]
        for xExpr in exprs:
            let pos = tr.sys.baseArray.len
            let indicatorVar = tr.sys.newConstrainedVariable()
            indicatorVar.setDomain(@[0, 1])
            let indicatorExpr = tr.getExpr(pos)
            indicators.add(indicatorExpr)
            let litV = newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: v),
                linear = true
            )
            tr.sys.addConstraint((xExpr == litV) <-> (indicatorExpr == 1))
        tr.sys.addConstraint(sum[int](indicators) == countExprs[i])

proc trySingleColumnKey(tr: var FznTranslator, positions: seq[int],
                        tuples: seq[seq[int]], keyCol: int): bool =
    ## Try column keyCol as a unique functional key.
    ## If successful, all other columns become channel variables.
    let nCols = positions.len
    if nCols < 2:
        return false

    var keyValues: PackedSet[int]
    var keyMin = high(int)
    var keyMax = low(int)
    for t in tuples:
        let k = t[keyCol]
        if k in keyValues:
            return false  # duplicate — not a unique key
        keyValues.incl(k)
        if k < keyMin: keyMin = k
        if k > keyMax: keyMax = k

    let keyRange = keyMax - keyMin + 1
    if keyRange > tuples.len * 2:
        return false  # too sparse

    # Dependent columns: all columns except keyCol
    var depCols: seq[int]
    for c in 0..<nCols:
        if c != keyCol:
            depCols.add(c)

    var lookups = newSeq[seq[int]](depCols.len)
    for i in 0..<depCols.len:
        lookups[i] = newSeqWith(keyRange, low(int))
    for t in tuples:
        let idx = t[keyCol] - keyMin
        for i, depCol in depCols:
            lookups[i][idx] = t[depCol]

    # Filter key position's domain to values present in the table
    let keyPos = positions[keyCol]
    let keyDomain = tr.sys.baseArray.domain[keyPos]
    var filteredDomain: seq[int]
    for v in keyDomain:
        if v in keyValues:
            filteredDomain.add(v)
    if filteredDomain.len < keyDomain.len:
        tr.sys.baseArray.domain[keyPos] = filteredDomain

    let keyExpr = tr.getExpr(keyPos) - keyMin
    for i, depCol in depCols:
        let depPos = positions[depCol]
        var arrayElems = newSeq[ArrayElement[int]](keyRange)
        for j in 0..<keyRange:
            arrayElems[j] = ArrayElement[int](isConstant: true, constantValue: lookups[i][j])
        tr.sys.baseArray.addChannelBinding(depPos, keyExpr, arrayElems)

    return true

proc tryMultiColumnKey(tr: var FznTranslator, positions: seq[int],
                       tuples: seq[seq[int]], keyCols: seq[int],
                       maxTotalRange: int = 500_000,
                       maxSparsity: int = 0): bool =
    ## Try keyCols as a composite functional key determining all other columns.
    ## Generalizes tryCompositeColumnKey to N key columns.
    ## If maxSparsity > 0, reject when totalRange > tuples.len * maxSparsity.
    let nCols = positions.len
    let nKeys = keyCols.len

    if nKeys < 1 or nKeys >= nCols:
        return false

    # Compute ranges for each key column
    var keyMins = newSeq[int](nKeys)
    var keyMaxs = newSeq[int](nKeys)
    for i in 0..<nKeys:
        keyMins[i] = high(int)
        keyMaxs[i] = low(int)
    for t in tuples:
        for i in 0..<nKeys:
            let v = t[keyCols[i]]
            if v < keyMins[i]: keyMins[i] = v
            if v > keyMaxs[i]: keyMaxs[i] = v

    var keyRanges = newSeq[int](nKeys)
    var totalRange = 1
    for i in 0..<nKeys:
        keyRanges[i] = keyMaxs[i] - keyMins[i] + 1
        if keyRanges[i] > maxTotalRange div totalRange:
            return false
        totalRange *= keyRanges[i]

    if maxSparsity > 0 and totalRange > tuples.len * maxSparsity:
        return false

    # Compute linearized key for each tuple and check uniqueness
    proc linearizeKey(t: seq[int], keyCols: seq[int], keyMins: seq[int],
                      keyRanges: seq[int]): int =
        result = 0
        for i in 0..<keyCols.len:
            result = result * keyRanges[i] + (t[keyCols[i]] - keyMins[i])

    var compositeKeys: PackedSet[int]
    for t in tuples:
        let lk = linearizeKey(t, keyCols, keyMins, keyRanges)
        if lk in compositeKeys:
            return false
        compositeKeys.incl(lk)

    # Filter key columns' domains to values present in the table
    var keyValueSets = newSeq[PackedSet[int]](nKeys)
    for t in tuples:
        for i in 0..<nKeys:
            keyValueSets[i].incl(t[keyCols[i]])
    for i in 0..<nKeys:
        let kPos = positions[keyCols[i]]
        let kDomain = tr.sys.baseArray.domain[kPos]
        var filtered: seq[int]
        for v in kDomain:
            if v in keyValueSets[i]:
                filtered.add(v)
        if filtered.len < kDomain.len:
            tr.sys.baseArray.domain[kPos] = filtered

    # Dependent columns: all columns not in keyCols
    var keyColSet: PackedSet[int]
    for c in keyCols: keyColSet.incl(c)
    var depCols: seq[int]
    for c in 0..<nCols:
        if c notin keyColSet:
            depCols.add(c)

    if depCols.len == 0:
        return false

    # Build linearized lookup arrays, using first tuple's values as default
    # for gaps (avoids sentinel low(int) causing overflow in constraint evaluation)
    var lookups = newSeq[seq[int]](depCols.len)
    for i in 0..<depCols.len:
        let defaultVal = tuples[0][depCols[i]]
        lookups[i] = newSeqWith(totalRange, defaultVal)
    for t in tuples:
        let idx = linearizeKey(t, keyCols, keyMins, keyRanges)
        for i, depCol in depCols:
            lookups[i][idx] = t[depCol]

    # Build composite index expression
    var compositeExpr = tr.getExpr(positions[keyCols[0]]) - keyMins[0]
    for i in 1..<nKeys:
        compositeExpr = compositeExpr * keyRanges[i] + (tr.getExpr(positions[keyCols[i]]) - keyMins[i])

    for i, depCol in depCols:
        let depPos = positions[depCol]
        var arrayElems = newSeq[ArrayElement[int]](totalRange)
        for j in 0..<totalRange:
            arrayElems[j] = ArrayElement[int](isConstant: true, constantValue: lookups[i][j])
        tr.sys.baseArray.addChannelBinding(depPos, compositeExpr, arrayElems)

    return true

proc tryCompositeColumnKey(tr: var FznTranslator, positions: seq[int],
                           tuples: seq[seq[int]], keyCol0, keyCol1: int): bool =
    ## Try (keyCol0, keyCol1) as a composite functional key.
    ## Delegates to tryMultiColumnKey with sparsity check.
    tr.tryMultiColumnKey(positions, tuples, @[keyCol0, keyCol1],
                         maxSparsity = 5)

proc tryTableFunctionalDep(tr: var FznTranslator, positions: seq[int],
                           tuples: seq[seq[int]],
                           definesVarCol: int = -1): bool =
    ## Detects functional keys in table constraints and converts dependent columns
    ## to channel variables. If definesVarCol >= 0, tries the remaining columns as
    ## a composite key first (guided by defines_var annotation). Otherwise tries
    ## all single columns, pairs, and triples as keys.
    if positions.len < 2 or tuples.len == 0:
        return false

    let nCols = positions.len

    # If defines_var tells us which column is dependent, try remaining cols as key
    if definesVarCol >= 0 and definesVarCol < nCols:
        var keyCols: seq[int]
        for c in 0..<nCols:
            if c != definesVarCol:
                keyCols.add(c)
        # Use relaxed sparsity for annotation-guided detection since we know
        # the dependency is real
        if tr.tryMultiColumnKey(positions, tuples, keyCols):
            return true

    # Try each single column as a unique key
    for keyCol in 0..<nCols:
        if tr.trySingleColumnKey(positions, tuples, keyCol):
            return true

    # Try each column pair as a composite key
    if nCols >= 3:
        for keyCol0 in 0..<nCols:
            for keyCol1 in (keyCol0 + 1)..<nCols:
                if tr.tryCompositeColumnKey(positions, tuples, keyCol0, keyCol1):
                    return true

    # Try each column triple as a composite key (for 4+ column tables)
    if nCols >= 4:
        for k0 in 0..<nCols:
            for k1 in (k0 + 1)..<nCols:
                for k2 in (k1 + 1)..<nCols:
                    if tr.tryMultiColumnKey(positions, tuples, @[k0, k1, k2],
                                            maxSparsity = 10):
                        return true

    return false

proc tryTableComplementConversion(tr: var FznTranslator, positions: seq[int],
                                                          tuples: seq[seq[int]]): bool =
    ## Detects when a tableIn constraint has a small forbidden complement and
    ## converts it to a more efficient representation:
    ## - tableNotIn (binary cost) when the forbidden set is small
    ## - allDifferentExcept0 when the pattern matches "no duplicate nonzero values"
    ## - Tautology (skip entirely) when all combinations are allowed
    ##
    ## tableNotIn uses O(1) zeroCount tracking vs tableIn's O(tuples) Hamming
    ## distance computation, giving major speedups for near-complete tables.
    let arity = positions.len
    if arity < 2 or tuples.len == 0:
        return false

    # Compute Cartesian product size from domains at each position
    var productSize = 1
    var domains = newSeq[seq[int]](arity)
    for col in 0..<arity:
        domains[col] = tr.sys.baseArray.domain[positions[col]]
        let domSize = domains[col].len
        if domSize == 0:
            return false
        # Guard against overflow: bail if product exceeds threshold
        if productSize > 1_000_000 div domSize:
            return false
        productSize *= domSize

    let forbiddenCount = productSize - tuples.len

    # Tautology: all combinations allowed, constraint is vacuous
    if forbiddenCount <= 0:
        return true

    # Only convert when forbidden set is small (much cheaper to enumerate and store)
    const maxForbiddenTuples = 100
    if forbiddenCount > maxForbiddenTuples:
        return false

    # Build set of allowed tuples for fast lookup
    var allowedSet = initHashSet[seq[int]](tuples.len)
    for t in tuples:
        allowedSet.incl(t)

    # Enumerate Cartesian product and collect forbidden tuples
    var forbidden = newSeqOfCap[seq[int]](forbiddenCount)
    var indices = newSeq[int](arity)  # current index into each domain

    block enumeration:
        while true:
            # Build current tuple from indices
            var current = newSeq[int](arity)
            for col in 0..<arity:
                current[col] = domains[col][indices[col]]

            if current notin allowedSet:
                forbidden.add(current)

            # Increment indices (odometer style)
            var carry = arity - 1
            while carry >= 0:
                inc indices[carry]
                if indices[carry] < domains[carry].len:
                    break
                indices[carry] = 0
                dec carry
            if carry < 0:
                break enumeration

    if forbidden.len == 0:
        return true  # Tautology after enumeration

    # Pattern: allDifferentExcept0 — forbidden set is exactly {(v,v) : v != 0, v in both domains}
    if arity == 2:
        var isAllDiffExcept0 = true
        let dom1Set = toHashSet(domains[1])
        # Check: every forbidden tuple is (v,v) with v != 0
        for f in forbidden:
            if f[0] != f[1] or f[0] == 0:
                isAllDiffExcept0 = false
                break
        # Check: every nonzero value in the intersection is forbidden
        if isAllDiffExcept0:
            for v in domains[0]:
                if v != 0 and v in dom1Set:
                    let pair = @[v, v]
                    if pair notin allowedSet:
                        discard  # Already in forbidden, good
                    else:
                        isAllDiffExcept0 = false
                        break
        if isAllDiffExcept0 and forbidden.len > 0:
            # Don't use allDifferentExcept0 for just 2 positions — the overhead of the
            # allDifferent data structure isn't worthwhile. tableNotIn with few tuples is cheaper.
            discard

    # Emit tableNotIn with the small forbidden set
    tr.sys.addConstraint(tableNotIn[int](positions, forbidden))
    inc tr.nTableToNotIn
    return true

proc resolveSetArg(tr: FznTranslator, arg: FznExpr): tuple[isConst: bool, constVals: HashSet[int], varInfo: SetVarInfo] =
    ## Resolves a FznExpr that refers to a set (variable or constant).
    ## Constant sets are returned as HashSet[int] for O(1) membership tests.
    case arg.kind
    of FznSetLit:
        return (true, toHashSet(arg.setElems), SetVarInfo())
    of FznRange:
        if arg.lo > arg.hi:
            return (true, initHashSet[int](), SetVarInfo())
        return (true, toHashSet(toSeq(arg.lo..arg.hi)), SetVarInfo())
    of FznIdent:
        if arg.ident in tr.setVarBoolPositions:
            return (false, initHashSet[int](), tr.setVarBoolPositions[arg.ident])
        elif arg.ident in tr.setParamValues:
            return (true, toHashSet(tr.setParamValues[arg.ident]), SetVarInfo())
        else:
            raise newException(KeyError, &"Unknown set identifier '{arg.ident}'")
    else:
        raise newException(ValueError, &"Cannot resolve {arg.kind} as set")

proc getSetBoolPosition(info: SetVarInfo, element: int): int {.inline.} =
    ## Returns the boolean variable position for a given element, or -1 if outside universe.
    if element < info.lo or element > info.hi:
        return -1
    return info.positions[element - info.lo]

proc constSetExpr(info: tuple[isConst: bool, constVals: HashSet[int], varInfo: SetVarInfo],
                                    tr: FznTranslator, elem: int): AlgebraicExpression[int] =
    ## Returns an expression for a set's boolean value at `elem`:
    ## literal 0/1 for constant sets, variable expression for set variables.
    if info.isConst:
        let val = if elem in info.constVals: 1 else: 0
        return newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: val),
            linear = true)
    else:
        let pos = getSetBoolPosition(info.varInfo, elem)
        if pos >= 0:
            return tr.getExpr(pos)
        else:
            return newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: 0),
                linear = true)


proc getExprBounds(tr: var FznTranslator, arg: FznExpr): tuple[lo: int, hi: int, known: bool] =
    ## Returns domain bounds (min, max) for a FznExpr element.
    ## known=false if bounds cannot be determined.
    case arg.kind
    of FznIntLit:
        return (arg.intVal, arg.intVal, true)
    of FznBoolLit:
        let val = if arg.boolVal: 1 else: 0
        return (val, val, true)
    of FznIdent:
        if arg.ident in tr.paramValues:
            let val = tr.paramValues[arg.ident]
            return (val, val, true)
        elif arg.ident in tr.varPositions:
            let pos = tr.varPositions[arg.ident]
            let dom = tr.sys.baseArray.domain[pos]
            if dom.len > 0:
                return (dom[0], dom[^1], true)
            else:
                return (0, 0, false)
        elif arg.ident in tr.definedVarBounds:
            let (lo, hi) = tr.definedVarBounds[arg.ident]
            return (lo, hi, true)
        else:
            return (0, 0, false)
    else:
        return (0, 0, false)

proc isLinTautological(tr: var FznTranslator, coeffs: seq[int], varArrayArg: FznExpr, rhs: int): bool =
    ## Check if int_lin_le(coeffs, vars, rhs) is tautological by computing
    ## the maximum possible value of sum(coeffs*vars) from domain bounds.
    ## Returns true if the constraint is always satisfied.
    var elems: seq[FznExpr]
    case varArrayArg.kind
    of FznArrayLit:
        elems = varArrayArg.elems
    of FznIdent:
        if varArrayArg.ident in tr.arrayElementNames:
            let names = tr.arrayElementNames[varArrayArg.ident]
            for n in names:
                elems.add(FznExpr(kind: FznIdent, ident: n))
        else:
            return false
    else:
        return false

    if elems.len != coeffs.len:
        return false

    var maxLHS = 0
    for i in 0..<coeffs.len:
        let (lo, hi, known) = tr.getExprBounds(elems[i])
        if not known:
            return false
        if coeffs[i] > 0:
            maxLHS += coeffs[i] * hi
        else:
            maxLHS += coeffs[i] * lo
    return maxLHS <= rhs

proc isLinNeTautological(tr: var FznTranslator, coeffs: seq[int], varArrayArg: FznExpr, rhs: int): bool =
    ## Check if int_lin_ne(coeffs, vars, rhs) is tautological by computing
    ## the achievable range [minLHS, maxLHS] of sum(coeffs*vars) from domain bounds.
    ## Returns true if rhs is outside this range (the constraint is always satisfied).
    var elems: seq[FznExpr]
    case varArrayArg.kind
    of FznArrayLit:
        elems = varArrayArg.elems
    of FznIdent:
        if varArrayArg.ident in tr.arrayElementNames:
            let names = tr.arrayElementNames[varArrayArg.ident]
            for n in names:
                elems.add(FznExpr(kind: FznIdent, ident: n))
        else:
            return false
    else:
        return false

    if elems.len != coeffs.len:
        return false

    var minLHS = 0
    var maxLHS = 0
    for i in 0..<coeffs.len:
        let (lo, hi, known) = tr.getExprBounds(elems[i])
        if not known:
            return false
        if coeffs[i] > 0:
            minLHS += coeffs[i] * lo
            maxLHS += coeffs[i] * hi
        else:
            minLHS += coeffs[i] * hi
            maxLHS += coeffs[i] * lo
    return rhs < minLHS or rhs > maxLHS

proc isNeTautological(tr: var FznTranslator, argA: FznExpr, argB: FznExpr): bool =
    ## Check if int_ne(a, b) is tautological because the domain bounds of a and b
    ## don't overlap (max(a) < min(b) or max(b) < min(a)).
    let (loA, hiA, knownA) = tr.getExprBounds(argA)
    let (loB, hiB, knownB) = tr.getExprBounds(argB)
    if not knownA or not knownB:
        return false
    return hiA < loB or hiB < loA

proc detectNandRedundancy*(tr: var FznTranslator) =
    ## Pre-compute NAND bool pairs and bool2int source mapping for
    ## detecting redundant int_lin_le constraints that duplicate bool_clause NANDs.

    # Build bool2int source map from bool2intChannelDefs
    for ci in tr.bool2intChannelDefs:
        let con = tr.model.constraints[ci]
        if con.args.len >= 2 and con.args[0].kind == FznIdent and con.args[1].kind == FznIdent:
            tr.bool2intSourceMap[con.args[1].ident] = con.args[0].ident

    # Collect NAND pairs from bool_clause([], [b1, b2])
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 0 or negArg.elems.len != 2: continue
        let b1 = negArg.elems[0]
        let b2 = negArg.elems[1]
        if b1.kind != FznIdent or b2.kind != FznIdent: continue
        # Store both orderings so lookup is symmetric
        tr.nandBoolPairs.incl((b1.ident, b2.ident))
        tr.nandBoolPairs.incl((b2.ident, b1.ident))

    if tr.nandBoolPairs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.nandBoolPairs.len div 2} NAND bool pairs, {tr.bool2intSourceMap.len} bool2int sources")

proc isRedundantNandLinLe(tr: FznTranslator, coeffs: seq[int], varArrayArg: FznExpr, rhs: int): bool =
    ## Check if int_lin_le(coeffs, vars, rhs) is a NAND constraint on bool2int outputs
    ## that duplicates an existing bool_clause([], [b1, b2]) NAND.
    if tr.nandBoolPairs.len == 0:
        return false

    # Only handle 2-variable case with equal positive coefficients and rhs = coefficient
    if coeffs.len != 2: return false
    if coeffs[0] != coeffs[1] or coeffs[0] <= 0: return false
    if rhs != coeffs[0]: return false  # rhs = c means c*x1 + c*x2 <= c → x1+x2 <= 1

    var elems: seq[FznExpr]
    if varArrayArg.kind == FznArrayLit:
        elems = varArrayArg.elems
    else:
        return false
    if elems.len != 2: return false

    # Both variables must be bool2int outputs
    for e in elems:
        if e.kind != FznIdent: return false
        if e.ident notin tr.bool2intSourceMap: return false

    let boolA = tr.bool2intSourceMap[elems[0].ident]
    let boolB = tr.bool2intSourceMap[elems[1].ident]
    return (boolA, boolB) in tr.nandBoolPairs

proc translateConstraint(tr: var FznTranslator, con: FznConstraint) =
    ## Translates a single FlatZinc constraint to a Crusher constraint.
    let name = stripSolverPrefix(con.name)

    case name
    # ===== Linear constraints =====
    of "int_lin_eq":
        # int_lin_eq(coeffs, vars, rhs)
        let coeffs = tr.resolveIntArray(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let rhs = tr.resolveIntArg(con.args[2])
        let sp = scalarProduct[int](coeffs, exprs)
        tr.sys.addConstraint(sp == rhs)

    of "int_lin_le":
        # int_lin_le(coeffs, vars, rhs) means sum(coeffs*vars) <= rhs
        let coeffs = tr.resolveIntArray(con.args[0])
        let rhs = tr.resolveIntArg(con.args[2])

        # Tautological check: if max possible LHS <= rhs, constraint is always satisfied
        if tr.isLinTautological(coeffs, con.args[1], rhs):
            inc tr.nSkippedTautological
            return

        # Redundant NAND check: int_lin_le encoding x1+x2<=1 duplicating a bool_clause NAND
        if tr.isRedundantNandLinLe(coeffs, con.args[1], rhs):
            inc tr.nSkippedRedundantNand
            return

        let exprs = tr.resolveExprArray(con.args[1])

        # Check for unit-coefficient pattern on binary variables → atMost/atLeast
        # Positions fixed to 0 or 1 are excluded (they contribute a known constant).
        var emittedUnitCoeff = false
        let (allRefsLe, positionsLe) = isAllRefs(exprs)
        if allRefsLe:
            var allPosOne = true
            var allNegOne = true
            for c in coeffs:
                if c != 1: allPosOne = false
                if c != -1: allNegOne = false
            if allPosOne or allNegOne:
                var allBinary = true
                var unfixedPositions: seq[int]
                var fixedLhsContribution = 0  # fixed positions' contribution to LHS
                for pos in positionsLe:
                    let dom = tr.sys.baseArray.domain[pos]
                    if dom.len == 2 and dom[0] == 0 and dom[1] == 1:
                        unfixedPositions.add(pos)
                    elif dom.len == 1 and (dom[0] == 0 or dom[0] == 1):
                        # Fixed binary variable — contributes coeff * value to LHS
                        if allPosOne:
                            fixedLhsContribution += dom[0]
                        else:  # allNegOne
                            fixedLhsContribution -= dom[0]
                    else:
                        allBinary = false
                        break
                if allBinary:
                    let adjustedRhs = rhs - fixedLhsContribution
                    if adjustedRhs < 0:
                        # Infeasible: fixed values already exceed rhs — fall through to generic scalarProduct
                        discard
                    elif unfixedPositions.len == 0:
                        # All positions fixed — constraint is tautological (checked earlier) or infeasible
                        discard
                    else:
                        if allPosOne:
                            # sum([1,1,...,1], x) <= rhs  →  atMost(adjustedRhs, unfixed, 1)
                            tr.sys.addConstraint(atMost[int](unfixedPositions, 1, adjustedRhs))
                        else:
                            # sum([-1,-1,...,-1], x) <= rhs  →  sum(x) >= -rhs
                            tr.sys.addConstraint(atLeast[int](unfixedPositions, 1, -(adjustedRhs)))
                        emittedUnitCoeff = true

        if not emittedUnitCoeff:
            let sp = scalarProduct[int](coeffs, exprs)
            tr.sys.addConstraint(sp <= rhs)

    of "int_lin_ne":
        let coeffs = tr.resolveIntArray(con.args[0])
        let rhs = tr.resolveIntArg(con.args[2])

        if tr.isLinNeTautological(coeffs, con.args[1], rhs):
            inc tr.nSkippedTautological
            return

        let exprs = tr.resolveExprArray(con.args[1])
        let sp = scalarProduct[int](coeffs, exprs)
        tr.sys.addConstraint(sp != rhs)

    of "int_lin_eq_reif":
        # int_lin_eq_reif(coeffs, vars, rhs, b) means (sum == rhs) <-> (b == 1)
        let coeffs = tr.resolveIntArray(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let rhs = tr.resolveIntArg(con.args[2])
        let sp = scalarProduct[int](coeffs, exprs)
        if con.args[3].kind == FznBoolLit:
            if con.args[3].boolVal:
                tr.sys.addConstraint(sp == rhs)
            else:
                tr.sys.addConstraint(sp != rhs)
        else:
            let bExpr = tr.resolveExprArg(con.args[3])
            tr.sys.addConstraint((sp == rhs) <-> (bExpr == 1))

    of "int_lin_le_reif":
        let coeffs = tr.resolveIntArray(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let rhs = tr.resolveIntArg(con.args[2])
        let sp = scalarProduct[int](coeffs, exprs)
        if con.args[3].kind == FznBoolLit:
            if con.args[3].boolVal:
                tr.sys.addConstraint(sp <= rhs)
            else:
                tr.sys.addConstraint(sp > rhs)
        else:
            let bExpr = tr.resolveExprArg(con.args[3])
            tr.sys.addConstraint((sp <= rhs) <-> (bExpr == 1))

    of "int_lin_ne_reif":
        let coeffs = tr.resolveIntArray(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let rhs = tr.resolveIntArg(con.args[2])
        let sp = scalarProduct[int](coeffs, exprs)
        if con.args[3].kind == FznBoolLit:
            if con.args[3].boolVal:
                tr.sys.addConstraint(sp != rhs)
            else:
                tr.sys.addConstraint(sp == rhs)
        else:
            let bExpr = tr.resolveExprArg(con.args[3])
            tr.sys.addConstraint((sp != rhs) <-> (bExpr == 1))

    # ===== Integer comparison constraints =====
    of "int_eq":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a == b)

    of "int_ne":
        if tr.isNeTautological(con.args[0], con.args[1]):
            inc tr.nSkippedTautological
            return

        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a != b)

    of "int_lt":
        block:
            let (_, hiA, knownA) = tr.getExprBounds(con.args[0])
            let (loB, _, knownB) = tr.getExprBounds(con.args[1])
            if knownA and knownB and hiA < loB:
                inc tr.nSkippedTautological
                return
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a < b)

    of "int_le":
        block:
            let (_, hiA, knownA) = tr.getExprBounds(con.args[0])
            let (loB, _, knownB) = tr.getExprBounds(con.args[1])
            if knownA and knownB and hiA <= loB:
                inc tr.nSkippedTautological
                return
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a <= b)

    of "int_gt":
        block:
            let (loA, _, knownA) = tr.getExprBounds(con.args[0])
            let (_, hiB, knownB) = tr.getExprBounds(con.args[1])
            if knownA and knownB and loA > hiB:
                inc tr.nSkippedTautological
                return
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a > b)

    of "int_ge":
        block:
            let (loA, _, knownA) = tr.getExprBounds(con.args[0])
            let (_, hiB, knownB) = tr.getExprBounds(con.args[1])
            if knownA and knownB and loA >= hiB:
                inc tr.nSkippedTautological
                return
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a >= b)

    of "int_eq_reif":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint((a == b) <-> (r == 1))

    of "int_ne_reif":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint((a != b) <-> (r == 1))

    of "int_lt_reif":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint((a < b) <-> (r == 1))

    of "int_le_reif":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint((a <= b) <-> (r == 1))

    # ===== Arithmetic constraints =====
    of "int_plus":
        # int_plus(x, y, z) means x + y = z
        let x = tr.resolveExprArg(con.args[0])
        let y = tr.resolveExprArg(con.args[1])
        let z = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint(x + y == z)

    of "int_times":
        let x = tr.resolveExprArg(con.args[0])
        let y = tr.resolveExprArg(con.args[1])
        let z = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint(x * y == z)

    of "int_abs":
        let x = tr.resolveExprArg(con.args[0])
        let y = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(abs(x) == y)

    of "int_min":
        # int_min(x, y, z) means z = min(x, y)
        let x = tr.resolveExprArg(con.args[0])
        let y = tr.resolveExprArg(con.args[1])
        let z = tr.resolveExprArg(con.args[2])
        let m = min[int](@[x, y])
        tr.sys.addConstraint(m == z)

    of "int_max":
        let x = tr.resolveExprArg(con.args[0])
        let y = tr.resolveExprArg(con.args[1])
        let z = tr.resolveExprArg(con.args[2])
        let m = max[int](@[x, y])
        tr.sys.addConstraint(m == z)

    of "int_div":
        # int_div(x, y, z) means z = x div y (integer division, rounding towards zero)
        # Channel cases (variable X, constant C) are handled by detectIntDivChannels.
        # For non-negative x and positive constant y:
        #   z * y <= x  and  x <= z * y + (y - 1)
        # For local search with variable y, fall back to approximate equality z * y == x
        let x = tr.resolveExprArg(con.args[0])
        let y = tr.resolveExprArg(con.args[1])
        let z = tr.resolveExprArg(con.args[2])
        if con.args[1].kind == FznIntLit and con.args[1].intVal > 0:
            let yVal = con.args[1].intVal
            # z * y <= x  =>  x - z * y >= 0
            tr.sys.addConstraint(x - z * y >= 0)
            # x - z * y <= y - 1  =>  x - z * y - (y-1) <= 0
            tr.sys.addConstraint(x - z * y <= yVal - 1)
        else:
            tr.sys.addConstraint(z * y == x)

    of "int_mod":
        # x mod y = z
        # Channel cases (variable X, constant C) are handled by detectIntModChannels.
        # Here we handle remaining cases: both constants, or variable C.
        let xArg = con.args[0]
        let yArg = con.args[1]
        let zArg = con.args[2]
        if xArg.kind == FznIntLit and yArg.kind == FznIntLit:
            # Both constants: compute result and fix Z's domain
            let cVal = yArg.intVal
            if cVal > 0:
                let result = ((xArg.intVal mod cVal) + cVal) mod cVal
                if zArg.kind == FznIdent and zArg.ident in tr.varPositions:
                    tr.sys.baseArray.setDomain(tr.varPositions[zArg.ident], @[result])
        elif yArg.kind != FznIntLit:
            # Variable C: introduce quotient variable q, enforce x == y * q + z, 0 <= z < y
            let x = tr.resolveExprArg(xArg)
            let y = tr.resolveExprArg(yArg)
            let z = tr.resolveExprArg(zArg)
            let xDomain = if xArg.kind == FznIdent and xArg.ident in tr.varPositions:
                              tr.sys.baseArray.domain[tr.varPositions[xArg.ident]].sorted()
                          elif xArg.kind == FznIntLit: @[xArg.intVal]
                          else: @[0]
            let yDomain = if yArg.kind == FznIdent and yArg.ident in tr.varPositions:
                              tr.sys.baseArray.domain[tr.varPositions[yArg.ident]].sorted()
                          elif yArg.kind == FznIntLit: @[yArg.intVal]
                          else: @[1]
            let qVar = tr.sys.newConstrainedVariable()
            let qLo = if yDomain[^1] > 0: xDomain[0] div yDomain[^1] else: 0
            let qHi = if yDomain[0] > 0: xDomain[^1] div yDomain[0] else: xDomain[^1]
            tr.sys.baseArray.setDomain(qVar.offset, toSeq(qLo..qHi))
            let q = tr.getExpr(qVar.offset)
            tr.sys.addConstraint(x == y * q + z)
            tr.sys.addConstraint(z >= 0)
            tr.sys.addConstraint(z < y)

    # ===== All-different =====
    of "fzn_all_different_int", "all_different_int":
        let exprs = tr.resolveExprArray(con.args[0])
        tr.sys.addConstraint(allDifferent[int](exprs))

    # ===== Element constraints =====
    of "array_int_element", "array_int_element_nonshifted":
        # array_int_element(index, array, value)
        # FlatZinc uses 1-based indexing, Crusher uses 0-based
        let indexExpr = tr.resolveExprArg(con.args[0])
        let valueExpr = tr.resolveExprArg(con.args[2])
        let adjustedIndex = indexExpr - 1
        # Use elementExpr since adjustedIndex is an expression (not a simple RefNode)
        try:
            let constArray = tr.resolveIntArray(con.args[1])
            tr.sys.addConstraint(elementExpr(adjustedIndex, constArray, valueExpr))
        except:
            let arrayExprs = tr.resolveExprArray(con.args[1])
            tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

    of "array_var_int_element", "array_var_int_element_nonshifted":
        # array_var_int_element(index, var_array, value)
        # FlatZinc uses 1-based indexing
        let indexExpr = tr.resolveExprArg(con.args[0])
        let valueExpr = tr.resolveExprArg(con.args[2])
        let adjustedIndex = indexExpr - 1

        # Try matrix element pattern: index is a simple RefNode and value is a simple RefNode
        var emitted = false
        if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode and
             tr.matrixInfos.len > 0:
                # Resolve inline array as mixed elements for matching
                let inlineElems = tr.resolveMixedArray(con.args[1])
                let indexPos = adjustedIndex.node.position
                let valuePos = valueExpr.node.position
                for name, minfo in tr.matrixInfos:
                        # Try row match
                        let rowIdx = tr.matchMatrixRow(inlineElems, minfo)
                        if rowIdx >= 0:
                                # Constant row, variable col: matrix[rowIdx, indexPos] == valuePos
                                tr.sys.addConstraint(stateful.matrixElement[int](
                                        minfo.elements, minfo.numRows, minfo.numCols,
                                        rowIdx, indexPos, valuePos))
                                emitted = true
                                break
                        # Try column match
                        let colIdx = tr.matchMatrixCol(inlineElems, minfo)
                        if colIdx >= 0:
                                # Variable row, constant col: matrix[indexPos, colIdx] == valuePos
                                tr.sys.addConstraint(stateful.matrixElement[int](
                                        minfo.elements, minfo.numRows, minfo.numCols,
                                        indexPos, colIdx, valuePos, rowIsVariable = true))
                                emitted = true
                                break

        if not emitted:
                let arrayExprs = tr.resolveExprArray(con.args[1])
                # Use position-based element if index is a RefNode, else expression-based
                if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode:
                        let mixedElems = tr.resolveMixedArray(con.args[1])
                        tr.sys.addConstraint(element(adjustedIndex, mixedElems, valueExpr))
                else:
                        tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

    of "array_bool_element":
        # Same as array_int_element but with booleans
        let indexExpr = tr.resolveExprArg(con.args[0])
        let valueExpr = tr.resolveExprArg(con.args[2])
        let adjustedIndex = indexExpr - 1
        try:
            let constArray = tr.resolveIntArray(con.args[1])
            tr.sys.addConstraint(elementExpr(adjustedIndex, constArray, valueExpr))
        except:
            let arrayExprs = tr.resolveExprArray(con.args[1])
            tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

    of "array_var_bool_element", "array_var_bool_element_nonshifted":
        # Same as array_var_int_element but with booleans (bools are 0/1 ints)
        let indexExpr = tr.resolveExprArg(con.args[0])
        let valueExpr = tr.resolveExprArg(con.args[2])
        let adjustedIndex = indexExpr - 1

        var emitted = false
        if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode and
             tr.matrixInfos.len > 0:
                let inlineElems = tr.resolveMixedArray(con.args[1])
                let indexPos = adjustedIndex.node.position
                let valuePos = valueExpr.node.position
                for name, minfo in tr.matrixInfos:
                        let rowIdx = tr.matchMatrixRow(inlineElems, minfo)
                        if rowIdx >= 0:
                                tr.sys.addConstraint(stateful.matrixElement[int](
                                        minfo.elements, minfo.numRows, minfo.numCols,
                                        rowIdx, indexPos, valuePos))
                                emitted = true
                                break
                        let colIdx = tr.matchMatrixCol(inlineElems, minfo)
                        if colIdx >= 0:
                                tr.sys.addConstraint(stateful.matrixElement[int](
                                        minfo.elements, minfo.numRows, minfo.numCols,
                                        indexPos, colIdx, valuePos, rowIsVariable = true))
                                emitted = true
                                break

        if not emitted:
                let arrayExprs = tr.resolveExprArray(con.args[1])
                if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode:
                        let mixedElems = tr.resolveMixedArray(con.args[1])
                        tr.sys.addConstraint(element(adjustedIndex, mixedElems, valueExpr))
                else:
                        tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

    # ===== Array aggregate constraints =====
    of "array_int_maximum":
        # array_int_maximum(max_var, array)
        let maxExpr = tr.resolveExprArg(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let m = max[int](exprs)
        tr.sys.addConstraint(m == maxExpr)

    of "array_int_minimum":
        let minExpr = tr.resolveExprArg(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let m = min[int](exprs)
        tr.sys.addConstraint(m == minExpr)

    # ===== Boolean constraints =====
    of "bool2int":
        # bool2int(b, i) means i = b (both are 0/1 integers in Crusher)
        let b = tr.resolveExprArg(con.args[0])
        let i = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(b == i)

    of "bool_eq":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a == b)

    of "bool_ne":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a != b)

    of "bool_le":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a <= b)

    of "bool_lt":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a < b)

    of "bool_and":
        # bool_and(a, b, r) means r = (a AND b) i.e. r = 1 iff a=1 and b=1
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint((a == 1) and (b == 1) <-> (r == 1))

    of "bool_or":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint(((a == 1) or (b == 1)) <-> (r == 1))

    of "bool_xor":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint(((a == 1) xor (b == 1)) <-> (r == 1))

    of "bool_not":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        tr.sys.addConstraint(a + b == 1)

    of "bool_clause":
        # bool_clause(pos_lits, neg_lits) means OR(pos) OR NOT(neg) >= 1
        # At least one positive lit is 1 or one negative lit is 0
        let posExprs = tr.resolveExprArray(con.args[0])
        let negExprs = tr.resolveExprArray(con.args[1])
        # sum(pos) + (len(neg) - sum(neg)) >= 1
        # sum(pos) - sum(neg) >= 1 - len(neg)
        var allExprs: seq[AlgebraicExpression[int]]
        var coeffs: seq[int]
        for e in posExprs:
            allExprs.add(e)
            coeffs.add(1)
        for e in negExprs:
            allExprs.add(e)
            coeffs.add(-1)
        if allExprs.len > 0:
            let sp = scalarProduct[int](coeffs, allExprs)
            tr.sys.addConstraint(sp >= 1 - negExprs.len)

    of "bool_clause_reif":
        # bool_clause_reif(pos_lits, neg_lits, b) means b <-> (OR(pos) OR NOT(neg))
        let posExprs = tr.resolveExprArray(con.args[0])
        let negExprs = tr.resolveExprArray(con.args[1])
        let bExpr = tr.resolveExprArg(con.args[2])
        var allExprs: seq[AlgebraicExpression[int]]
        var coeffs: seq[int]
        for e in posExprs:
            allExprs.add(e)
            coeffs.add(1)
        for e in negExprs:
            allExprs.add(e)
            coeffs.add(-1)
        if allExprs.len > 0:
            let sp = scalarProduct[int](coeffs, allExprs)
            tr.sys.addConstraint((sp >= 1 - negExprs.len) <-> (bExpr == 1))
        else:
            # Empty clause is always false
            tr.sys.addConstraint(bExpr == 0)

    of "array_bool_and":
        # array_bool_and(array, r) means r = AND(array)
        let exprs = tr.resolveExprArray(con.args[0])
        let r = tr.resolveExprArg(con.args[1])
        # r = 1 iff sum(array) == len(array)
        let s = sum[int](exprs)
        tr.sys.addConstraint((s == exprs.len) <-> (r == 1))

    of "array_bool_or":
        let exprs = tr.resolveExprArray(con.args[0])
        let r = tr.resolveExprArg(con.args[1])
        let s = sum[int](exprs)
        tr.sys.addConstraint((s >= 1) <-> (r == 1))

    of "array_bool_xor":
        # array_bool_xor(array): XOR (parity) of all elements must be true (odd count)
        let exprs = tr.resolveExprArray(con.args[0])
        if exprs.len == 1:
            tr.sys.addConstraint(exprs[0] == 1)
        elif exprs.len == 2:
            # a XOR b = true ↔ a + b == 1 (they differ)
            tr.sys.addConstraint(exprs[0] + exprs[1] == 1)
        elif exprs.len >= 3:
            # Chain XOR of first n-1 elements, assert XOR with last = true
            # (a XOR b) XOR c = true ↔ (a XOR b) ↔ (c == 0)
            var xorChain = (exprs[0] == 1) xor (exprs[1] == 1)
            for i in 2 ..< exprs.len - 1:
                xorChain = xorChain xor (exprs[i] == 1)
            tr.sys.addConstraint(xorChain <-> (exprs[^1] == 0))

    of "bool_eq_reif":
        let a = tr.resolveExprArg(con.args[0])
        let b = tr.resolveExprArg(con.args[1])
        let r = tr.resolveExprArg(con.args[2])
        tr.sys.addConstraint((a == b) <-> (r == 1))

    # ===== Global constraints =====
    of "fzn_cumulative", "fzn_cumulatives":
        # cumulative(starts, durations, heights, limit)
        let startExprs = tr.resolveExprArray(con.args[0])
        # Durations/heights might be in variable arrays - try constant first, fall back to extracting from assignment
        var durations: seq[int]
        var heights: seq[int]
        var durPositions: seq[int]  # per-task position of variable duration (-1 = constant)
        var heightPositions: seq[int]  # per-task position of variable height (-1 = constant)
        var hasVarDur = false
        var hasVarHeight = false
        try:
            durations = tr.resolveIntArray(con.args[1])
            durPositions = newSeq[int](durations.len)
            for i in 0..<durPositions.len: durPositions[i] = -1
        except:
            # Variable array — extract positions for channel-aware cumulative
            let dExprs = tr.resolveExprArray(con.args[1])
            durations = newSeq[int](dExprs.len)
            durPositions = newSeq[int](dExprs.len)
            for i, e in dExprs:
                if e.node.kind == LiteralNode:
                    durations[i] = e.node.value
                    durPositions[i] = -1
                elif e.node.kind == RefNode:
                    durPositions[i] = e.node.position
                    hasVarDur = true
                    let dom = tr.sys.baseArray.domain[e.node.position]
                    if dom.len == 1:
                        durations[i] = dom[0]
                    else:
                        durations[i] = dom[dom.len div 2]  # fallback for initial value
                else:
                    durations[i] = 1  # fallback
                    durPositions[i] = -1
        try:
            heights = tr.resolveIntArray(con.args[2])
            heightPositions = newSeq[int](heights.len)
            for i in 0..<heightPositions.len: heightPositions[i] = -1
        except:
            let hExprs = tr.resolveExprArray(con.args[2])
            heights = newSeq[int](hExprs.len)
            heightPositions = newSeq[int](hExprs.len)
            for i, e in hExprs:
                if e.node.kind == LiteralNode:
                    heights[i] = e.node.value
                    heightPositions[i] = -1
                elif e.node.kind == RefNode:
                    heightPositions[i] = e.node.position
                    hasVarHeight = true
                    let dom = tr.sys.baseArray.domain[e.node.position]
                    if dom.len == 1:
                        heights[i] = dom[0]
                    else:
                        heights[i] = dom[dom.len div 2]
                else:
                    heights[i] = 0
                    heightPositions[i] = -1
        # Limit might be a variable - try constant, fall back to variable limit
        var limit: int
        var limitPos = -1
        try:
            limit = tr.resolveIntArg(con.args[3])
        except:
            # Variable limit - extract position, use domain upper bound as initial value
            let limitExpr = tr.resolveExprArg(con.args[3])
            if limitExpr.node.kind == RefNode:
                limitPos = limitExpr.node.position
                let dom = tr.sys.baseArray.domain[limitPos]
                limit = dom[^1]  # upper bound as initial value
            else:
                limit = 10  # fallback
        # Filter out tasks with zero height (only if height is constant zero)
        var filteredStarts: seq[AlgebraicExpression[int]]
        var filteredDurations: seq[int]
        var filteredHeights: seq[int]
        var filteredDurPos: seq[int]
        var filteredHeightPos: seq[int]
        for i in 0..<heights.len:
            # Only filter if height is constant zero (position == -1 and value == 0)
            if heights[i] == 0 and (heightPositions.len == 0 or heightPositions[i] < 0):
                continue
            filteredStarts.add(startExprs[i])
            filteredDurations.add(durations[i])
            filteredHeights.add(heights[i])
            if durPositions.len > 0: filteredDurPos.add(durPositions[i])
            if heightPositions.len > 0: filteredHeightPos.add(heightPositions[i])
        let nFiltered = heights.len - filteredHeights.len
        if nFiltered > 0:
            stderr.writeLine(&"[FZN] cumulative: filtered {nFiltered} zero-height tasks")
        # Skip if trivially satisfied (only when all heights are constant)
        var totalHeight = 0
        for h in filteredHeights: totalHeight += h
        if filteredStarts.len <= 1 or (totalHeight <= limit and not hasVarHeight):
            if nFiltered > 0:
                stderr.writeLine(&"[FZN] cumulative: constraint eliminated (trivially satisfied)")
        else:
            if hasVarDur or hasVarHeight:
                stderr.writeLine(&"[FZN] cumulative: variable dur/height ({filteredStarts.len} tasks, varDur={hasVarDur} varHeight={hasVarHeight})")
            tr.sys.addConstraint(cumulative[int](filteredStarts, filteredDurations, filteredHeights, limit, limitPos, filteredDurPos, filteredHeightPos))

    of "fzn_disjunctive", "fzn_disjunctive_strict":
        # disjunctive(starts, durations) = cumulative(starts, durations, heights=[1,...], limit=1)
        let startExprs = tr.resolveExprArray(con.args[0])
        var durations: seq[int]
        try:
            durations = tr.resolveIntArray(con.args[1])
        except CatchableError:
            let dExprs = tr.resolveExprArray(con.args[1])
            durations = newSeq[int](dExprs.len)
            for i, e in dExprs:
                if e.node.kind == LiteralNode:
                    durations[i] = e.node.value
                elif e.node.kind == RefNode:
                    let dom = tr.sys.baseArray.domain[e.node.position]
                    if dom.len == 1:
                        durations[i] = dom[0]
                    else:
                        durations[i] = dom[dom.len div 2]
                        stderr.writeLine(&"[FZN] Warning: disjunctive duration variable has non-singleton domain (size {dom.len}), using median value {durations[i]}")
        let heights = newSeqWith(durations.len, 1)
        tr.sys.addConstraint(cumulative[int](startExprs, durations, heights, 1))

    of "fzn_diffn":
        # diffn(x, y, dx, dy) - non-overlapping rectangles
        let xExprs = tr.resolveExprArray(con.args[0])
        let yExprs = tr.resolveExprArray(con.args[1])
        let dxExprs = tr.resolveExprArray(con.args[2])
        let dyExprs = tr.resolveExprArray(con.args[3])
        tr.sys.addConstraint(diffn[int](xExprs, yExprs, dxExprs, dyExprs))
        # Check if all x/dx are constants (y-only moves → sweep-line fast path)
        var allXDXConst = true
        for i in 0..<xExprs.len:
            if xExprs[i].positions.len > 0 or dxExprs[i].positions.len > 0:
                allXDXConst = false; break
        if allXDXConst:
            stderr.writeLine(&"[FZN] Diffn: all x/dx constant ({xExprs.len} rects), y-only moves")

    of "fzn_crusher_diffn_k":
        let n = tr.resolveIntArg(con.args[0])
        let k = tr.resolveIntArg(con.args[1])
        let flatPosn = tr.resolveExprArray(con.args[2])
        let flatSize = tr.resolveExprArray(con.args[3])
        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        for i in 0..<n:
                posExprs[i] = flatPosn[i*k ..< (i+1)*k]
                sizeExprs[i] = flatSize[i*k ..< (i+1)*k]
        tr.sys.addConstraint(diffnK[int](n, k, posExprs, sizeExprs))

    of "fzn_circuit":
        let exprs = tr.resolveExprArray(con.args[0])
        let (allRefs, positions) = isAllRefs(exprs)
        # Detect value offset: 0-based (offset=0) if values include 0 but not n
        var circuitPositions: seq[int]
        if allRefs:
            circuitPositions = positions
        else:
            for e in exprs:
                if e.node.kind == RefNode:
                    circuitPositions.add(e.node.position)
                elif e.node.kind == LiteralNode:
                    let pos = tr.sys.baseArray.len
                    let v = tr.sys.newConstrainedVariable()
                    v.setDomain(@[int(e.node.value)])
                    circuitPositions.add(pos)
                else:
                    raise newException(ValueError, "fzn_circuit: unsupported expression node kind " & $e.node.kind)
        let n = circuitPositions.len
        var hasZero = false
        var hasN = false
        for pos in circuitPositions:
            let dom = tr.sys.baseArray.domain[pos]
            for v in dom:
                if v == 0: hasZero = true
                if v == n: hasN = true
        let valueOffset = if hasZero and not hasN: 0 else: 1
        if valueOffset == 0:
            stderr.writeLine(&"[FZN] Circuit with {n} nodes uses 0-based indexing")
        tr.sys.addConstraint(circuit[int](circuitPositions, valueOffset))

    of "fzn_subcircuit":
        let exprs = tr.resolveExprArray(con.args[0])
        let (allRefs, positions) = isAllRefs(exprs)
        var subcircuitPositions: seq[int]
        if allRefs:
            subcircuitPositions = positions
        else:
            for e in exprs:
                if e.node.kind == RefNode:
                    subcircuitPositions.add(e.node.position)
                elif e.node.kind == LiteralNode:
                    let pos = tr.sys.baseArray.len
                    let v = tr.sys.newConstrainedVariable()
                    v.setDomain(@[int(e.node.value)])
                    subcircuitPositions.add(pos)
                else:
                    raise newException(ValueError, "fzn_subcircuit: unsupported expression node kind " & $e.node.kind)
        let nSub = subcircuitPositions.len
        var hasZeroSub = false
        var hasNSub = false
        for pos in subcircuitPositions:
            let dom = tr.sys.baseArray.domain[pos]
            for v in dom:
                if v == 0: hasZeroSub = true
                if v == nSub: hasNSub = true
        let valueOffsetSub = if hasZeroSub and not hasNSub: 0 else: 1
        tr.sys.addConstraint(subcircuit[int](subcircuitPositions, valueOffsetSub))
        tr.sys.addConstraint(allDifferent[int](subcircuitPositions))

    of "fzn_connected":
        # fzn_connected(from, to, ns, es)
        # from, to: constant int arrays (1-based node indices for edge endpoints)
        # ns: var bool array (node activity)
        # es: var bool array (edge activity)
        let fromArr = tr.resolveIntArray(con.args[0])
        let toArr = tr.resolveIntArray(con.args[1])
        let nsExprs = tr.resolveExprArray(con.args[2])
        let esExprs = tr.resolveExprArray(con.args[3])

        # Extract node positions
        var nodePositions: seq[int]
        for e in nsExprs:
            if e.node.kind == RefNode:
                nodePositions.add(e.node.position)
            elif e.node.kind == LiteralNode:
                let pos = tr.sys.baseArray.len
                let v = tr.sys.newConstrainedVariable()
                v.setDomain(@[int(e.node.value)])
                nodePositions.add(pos)
            else:
                raise newException(ValueError, "fzn_connected: unsupported ns expression node kind " & $e.node.kind)

        # Extract edge positions
        var edgePositions: seq[int]
        for e in esExprs:
            if e.node.kind == RefNode:
                edgePositions.add(e.node.position)
            elif e.node.kind == LiteralNode:
                let pos = tr.sys.baseArray.len
                let v = tr.sys.newConstrainedVariable()
                v.setDomain(@[int(e.node.value)])
                edgePositions.add(pos)
            else:
                raise newException(ValueError, "fzn_connected: unsupported es expression node kind " & $e.node.kind)

        # Convert from/to from 1-based MiniZinc to 0-based node indices
        var from0 = newSeq[int](fromArr.len)
        var to0 = newSeq[int](toArr.len)
        for i in 0..<fromArr.len:
            from0[i] = fromArr[i] - 1
            to0[i] = toArr[i] - 1

        tr.sys.addConstraint(connected[int](nodePositions, edgePositions, from0, to0))

    of "fzn_regular":
        # regular(x, Q, S, d, q0, F)
        let exprs = tr.resolveExprArray(con.args[0])
        let nStates = tr.resolveIntArg(con.args[1])
        let nSymbols = tr.resolveIntArg(con.args[2])
        let transFlat = tr.resolveIntArray(con.args[3])
        let q0 = tr.resolveIntArg(con.args[4])
        # F is a set of final states
        let fArg = con.args[5]
        var finalStates: seq[int]
        case fArg.kind
        of FznSetLit:
            finalStates = fArg.setElems
        of FznRange:
            for i in fArg.lo..fArg.hi:
                finalStates.add(i)
        of FznArrayLit:
            for e in fArg.elems:
                finalStates.add(tr.resolveIntArg(e))
        else:
            finalStates = tr.resolveIntArray(fArg)

        # Build 2D transition table from flat array
        var transition = newSeq[seq[int]](nStates)
        for i in 0..<nStates:
            transition[i] = newSeq[int](nSymbols)
            for j in 0..<nSymbols:
                transition[i][j] = transFlat[i * nSymbols + j]

        tr.sys.addConstraint(regular[int](exprs, nStates, 1, nSymbols, transition, q0, finalStates))

    of "fzn_table_int":
        # table_int(x, t) where t is flat array of tuples
        let exprs = tr.resolveExprArray(con.args[0])
        let flatTable = tr.resolveIntArray(con.args[1])
        let arity = exprs.len
        let nTuples = flatTable.len div arity
        var tuples = newSeq[seq[int]](nTuples)
        for i in 0..<nTuples:
            tuples[i] = flatTable[i * arity ..< (i + 1) * arity]

        # Extract defines_var hint: identify which column is the dependent variable
        var definesVarCol = -1
        if con.hasAnnotation("defines_var"):
            let ann = con.getAnnotation("defines_var")
            if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                let defName = ann.args[0].ident
                if defName in tr.varPositions:
                    let defPos = tr.varPositions[defName]
                    let (allRefsCheck, positionsCheck) = isAllRefs(exprs)
                    if allRefsCheck:
                        for col in 0..<arity:
                            if positionsCheck[col] == defPos:
                                definesVarCol = col
                                break

        # Pre-filter: detect singleton-domain columns (constants) and filter tuples
        # to matching rows, then project out constant columns. This is critical for
        # tables like preferences_data where a user_id column is fixed per constraint.
        var singletonCols: PackedSet[int]  # column indices with singleton domains
        var singletonVals: Table[int, int] # col -> constant value for each singleton column
        let (allRefs, positions) = isAllRefs(exprs)
        if allRefs:
            for col in 0..<arity:
                let pos = positions[col]
                if tr.sys.baseArray.domain[pos].len == 1:
                    singletonCols.incl(col)
                    singletonVals[col] = tr.sys.baseArray.domain[pos][0]

        if singletonCols.len > 0 and singletonCols.len < arity:
            # Filter tuples to only those matching all singleton column values
            var filtered: seq[seq[int]]
            for t in tuples:
                var matches = true
                for col in singletonCols.items:
                    if t[col] != singletonVals[col]:
                        matches = false
                        break
                if matches:
                    # Project out singleton columns
                    var projected = newSeq[int](arity - singletonCols.len)
                    var j = 0
                    for col in 0..<arity:
                        if col notin singletonCols:
                            projected[j] = t[col]
                            inc j
                    filtered.add(projected)

            # Build reduced position array (exclude singleton columns)
            var reducedPositions: seq[int]
            # Remap definesVarCol to account for projected-out columns
            var reducedDefinesVarCol = -1
            var reducedIdx = 0
            for col in 0..<arity:
                if col notin singletonCols:
                    reducedPositions.add(positions[col])
                    if col == definesVarCol:
                        reducedDefinesVarCol = reducedIdx
                    inc reducedIdx

            if filtered.len > 0:
                # Try functional dependency: if col0 values are unique, dependent cols become channels
                if not tr.tryTableFunctionalDep(reducedPositions, filtered, reducedDefinesVarCol):
                    if not tr.tryTableComplementConversion(reducedPositions, filtered):
                        tr.sys.addConstraint(tableIn[int](reducedPositions, filtered))
            else:
                stderr.writeLine("[FznTranslator] WARNING: table constraint has 0 matching tuples after singleton filtering — infeasible")
        elif allRefs:
            # Try functional dependency on the original table
            if not tr.tryTableFunctionalDep(positions, tuples, definesVarCol):
                if not tr.tryTableComplementConversion(positions, tuples):
                    tr.sys.addConstraint(tableIn[int](positions, tuples))
        else:
            # Some expressions are not simple variable references (e.g., defined vars
            # with linear expressions, or constants). Materialize them:
            # - Constants: filter tuples and project out the column
            # - Simple refs: use position directly
            # - Complex expressions: create auxiliary position with equality constraint
            var constCols: PackedSet[int]
            var constVals: Table[int, int]
            for col in 0..<arity:
                if exprs[col].node.kind == LiteralNode:
                    constCols.incl(col)
                    constVals[col] = exprs[col].node.value

            # Filter tuples by constant columns
            var filteredTuples: seq[seq[int]]
            for t in tuples:
                var matches = true
                for col in constCols.items:
                    if t[col] != constVals[col]:
                        matches = false
                        break
                if matches:
                    filteredTuples.add(t)

            if filteredTuples.len == 0:
                stderr.writeLine("[FznTranslator] WARNING: table constraint has 0 matching tuples after constant filtering — infeasible")
            else:
                # Build positions for non-constant columns, materializing complex expressions
                var tablePositions: seq[int]
                var projectCols: seq[int]  # original column indices to keep
                for col in 0..<arity:
                    if col in constCols:
                        continue
                    projectCols.add(col)
                    let expr = exprs[col]
                    if expr.node.kind == RefNode:
                        tablePositions.add(expr.node.position)
                    else:
                        # Create auxiliary position constrained to equal this expression
                        let auxPos = tr.sys.baseArray.len
                        let auxVar = tr.sys.newConstrainedVariable()
                        # Domain: unique values in this column from filtered tuples
                        var colVals: seq[int]
                        var seen: HashSet[int]
                        for t in filteredTuples:
                            if t[col] notin seen:
                                seen.incl(t[col])
                                colVals.add(t[col])
                        colVals.sort()
                        auxVar.setDomain(colVals)
                        tr.sys.baseArray.channelPositions.incl(auxPos)
                        # Constrain: auxPos == expression
                        let auxExpr = tr.getExpr(auxPos)
                        tr.sys.addConstraint(auxExpr == expr)
                        tablePositions.add(auxPos)

                # Project out constant columns from tuples
                var projectedTuples: seq[seq[int]]
                for t in filteredTuples:
                    var projected = newSeq[int](projectCols.len)
                    for j, col in projectCols:
                        projected[j] = t[col]
                    projectedTuples.add(projected)

                # Remap definesVarCol through constant-column projection
                var projectedDefinesVarCol = -1
                if definesVarCol >= 0:
                    for j, col in projectCols:
                        if col == definesVarCol:
                            projectedDefinesVarCol = j
                            break

                if tablePositions.len > 0 and projectedTuples.len > 0:
                    if not tr.tryTableFunctionalDep(tablePositions, projectedTuples, projectedDefinesVarCol):
                        if not tr.tryTableComplementConversion(tablePositions, projectedTuples):
                            tr.sys.addConstraint(tableIn[int](tablePositions, projectedTuples))

    of "fzn_global_cardinality":
        # global_cardinality(x, cover, counts)
        let exprs = tr.resolveExprArray(con.args[0])
        let cover = tr.resolveIntArray(con.args[1])
        var constantCounts = true
        var counts: seq[int]
        try:
            counts = tr.resolveIntArray(con.args[2])
        except KeyError:
            constantCounts = false

        if constantCounts:
            tr.sys.addConstraint(globalCardinality[int](exprs, cover, counts))
        else:
            let countExprs = tr.resolveExprArray(con.args[2])

            # Check 1: All count expressions have singleton domains → use as constants
            var allSingleton = true
            var inferredCounts = newSeq[int](countExprs.len)
            for i, ce in countExprs:
                if ce.node.kind == RefNode:
                    let dom = tr.sys.baseArray.domain[ce.node.position]
                    if dom.len == 1:
                        inferredCounts[i] = dom[0]
                    else:
                        allSingleton = false; break
                else:
                    allSingleton = false; break

            if allSingleton:
                tr.sys.addConstraint(globalCardinality[int](exprs, cover, inferredCounts))
            else:
                # Check 2: All count exprs reference the same position + closed GCC
                var allSamePos = true
                var countPos = -1
                for ce in countExprs:
                    if ce.node.kind == RefNode:
                        if countPos == -1: countPos = ce.node.position
                        elif ce.node.position != countPos: allSamePos = false; break
                    else: allSamePos = false; break

                var closed = false
                if allSamePos and countPos >= 0:
                    let coverSet = cover.toHashSet()
                    closed = true
                    for xExpr in exprs:
                        if xExpr.node.kind == RefNode:
                            for v in tr.sys.baseArray.domain[xExpr.node.position]:
                                if v notin coverSet: closed = false; break
                        else: closed = false
                        if not closed: break

                if allSamePos and closed and exprs.len mod cover.len == 0:
                    let target = exprs.len div cover.len
                    var targets = newSeq[int](cover.len)
                    for i in 0..<cover.len: targets[i] = target
                    tr.sys.addConstraint(globalCardinality[int](exprs, cover, targets))
                    tr.sys.baseArray.domain[countPos] = @[target]
                else:
                    tr.decomposeWithIndicators(exprs, cover, countExprs)

    of "fzn_global_cardinality_closed":
        # global_cardinality_closed(x, cover, counts)
        # Same as open variant but domains are restricted to cover set
        let exprs = tr.resolveExprArray(con.args[0])
        let cover = tr.resolveIntArray(con.args[1])
        let coverSet = cover.toHashSet()
        # Restrict domains to cover set
        for e in exprs:
            if e.node.kind == RefNode:
                let pos = e.node.position
                tr.sys.baseArray.domain[pos] = tr.sys.baseArray.domain[pos].filterIt(it in coverSet)
        var constantCounts = true
        var counts: seq[int]
        try:
            counts = tr.resolveIntArray(con.args[2])
        except KeyError:
            constantCounts = false
        if constantCounts:
            tr.sys.addConstraint(globalCardinality[int](exprs, cover, counts))
        else:
            let countExprs = tr.resolveExprArray(con.args[2])
            var allSingleton = true
            var inferredCounts = newSeq[int](countExprs.len)
            for i, ce in countExprs:
                if ce.node.kind == RefNode:
                    let dom = tr.sys.baseArray.domain[ce.node.position]
                    if dom.len == 1:
                        inferredCounts[i] = dom[0]
                    else:
                        allSingleton = false; break
                else:
                    allSingleton = false; break
            if allSingleton:
                tr.sys.addConstraint(globalCardinality[int](exprs, cover, inferredCounts))
            else:
                tr.decomposeWithIndicators(exprs, cover, countExprs)

    of "fzn_global_cardinality_low_up_closed":
        # global_cardinality_low_up_closed(x, cover, lbound, ubound)
        # Same as open variant but domains are restricted to cover set
        let exprs = tr.resolveExprArray(con.args[0])
        let cover = tr.resolveIntArray(con.args[1])
        let lbound = tr.resolveIntArray(con.args[2])
        let ubound = tr.resolveIntArray(con.args[3])
        let n = exprs.len
        let coverSet = cover.toHashSet()
        # Restrict domains to cover set
        for e in exprs:
            if e.node.kind == RefNode:
                let pos = e.node.position
                tr.sys.baseArray.domain[pos] = tr.sys.baseArray.domain[pos].filterIt(it in coverSet)
        # Pigeon-hole tightening: derive effective bounds from total item count
        # If n items must be distributed across cover.len slots with bounds [lb, ub],
        # then each slot i must have at least n - sum(ub[j] for j != i) items
        # and at most n - sum(lb[j] for j != i) items.
        let sumLbound = lbound.foldl(a + b, 0)
        let sumUbound = ubound.foldl(a + b, 0)
        var effectiveLbound = newSeq[int](cover.len)
        var effectiveUbound = newSeq[int](cover.len)
        for i in 0..<cover.len:
            effectiveLbound[i] = max(lbound[i], n - (sumUbound - ubound[i]))
            effectiveUbound[i] = min(ubound[i], n - (sumLbound - lbound[i]))
        # Same cardinality logic as open variant, using tightened bounds
        for i in 0..<cover.len:
            if effectiveLbound[i] > 0:
                tr.sys.addConstraint(atLeast[int](exprs, cover[i], effectiveLbound[i]))
            if effectiveUbound[i] < n:
                tr.sys.addConstraint(atMost[int](exprs, cover[i], effectiveUbound[i]))

    of "fzn_global_cardinality_low_up":
        # global_cardinality_low_up(x, cover, lbound, ubound)
        # For each i: lbound[i] <= count(x, cover[i]) <= ubound[i]
        # Skip trivial bounds; emit atLeast/atMost for non-trivial ones.
        # Note: open variant — items can take values outside cover set,
        # so pigeon-hole lower bound tightening does NOT apply (items can
        # escape to uncovered values). Upper bound tightening is still valid.
        let exprs = tr.resolveExprArray(con.args[0])
        let cover = tr.resolveIntArray(con.args[1])
        let lbound = tr.resolveIntArray(con.args[2])
        let ubound = tr.resolveIntArray(con.args[3])
        let n = exprs.len
        # Upper bound tightening: count[i] <= n - sum(lbound[j] for j != i)
        let sumLbound = lbound.foldl(a + b, 0)
        for i in 0..<cover.len:
            if lbound[i] > 0:
                tr.sys.addConstraint(atLeast[int](exprs, cover[i], lbound[i]))
            let effectiveUbound = min(ubound[i], n - (sumLbound - lbound[i]))
            if effectiveUbound < n:
                tr.sys.addConstraint(atMost[int](exprs, cover[i], effectiveUbound))

    of "fzn_count_eq":
        # count_eq(x, y, c) means count(x, y) == c
        # x is array of var int, y is the value to count, c is var int (the count)
        let arrayExprs = tr.resolveExprArray(con.args[0])
        let countValue = tr.resolveIntArg(con.args[1])
        let countExpr = tr.resolveExprArg(con.args[2])
        # Extract positions
        var arrayPos: seq[int]
        for e in arrayExprs:
            if e.node.kind == RefNode:
                arrayPos.add(e.node.position)
            else:
                raise newException(ValueError, "fzn_count_eq requires simple variable references in array")
        if countExpr.node.kind == RefNode:
            tr.sys.addConstraint(countEq[int](arrayPos, countValue, countExpr.node.position))
        else:
            raise newException(ValueError, "fzn_count_eq requires a variable for the count argument")

    of "fzn_count_eq_reif":
        # Reified form - not yet implemented
        stderr.writeLine("[FZN] Warning: fzn_count_eq_reif not implemented, constraint ignored")

    of "fzn_at_least_int":
        # at_least(n, x, v) means at least n occurrences of v in x
        let n = tr.resolveIntArg(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let v = tr.resolveIntArg(con.args[2])
        tr.sys.addConstraint(atLeast[int](exprs, v, n))

    of "fzn_at_most_int":
        let n = tr.resolveIntArg(con.args[0])
        let exprs = tr.resolveExprArray(con.args[1])
        let v = tr.resolveIntArg(con.args[2])
        tr.sys.addConstraint(atMost[int](exprs, v, n))

    of "fzn_increasing_int":
        let exprs = tr.resolveExprArray(con.args[0])
        tr.sys.addConstraint(increasing[int](exprs))

    of "fzn_decreasing_int":
        let exprs = tr.resolveExprArray(con.args[0])
        tr.sys.addConstraint(decreasing[int](exprs))

    of "fzn_lex_lesseq_int", "fzn_lex_lesseq_bool":
        let leftExprs = tr.resolveExprArray(con.args[0])
        let rightExprs = tr.resolveExprArray(con.args[1])
        tr.sys.addConstraint(lexLe[int](leftExprs, rightExprs))

    of "fzn_lex_less_int", "fzn_lex_less_bool":
        let leftExprs = tr.resolveExprArray(con.args[0])
        let rightExprs = tr.resolveExprArray(con.args[1])
        tr.sys.addConstraint(lexLt[int](leftExprs, rightExprs))

    of "fzn_all_different_except_0", "fzn_alldifferent_except_0":
        let exprs = tr.resolveExprArray(con.args[0])
        # Filter out constant 0 expressions — they are exempt from uniqueness
        var filteredExprs: seq[AlgebraicExpression[int]]
        for e in exprs:
            if e.node.kind == LiteralNode and e.node.value == 0:
                continue
            filteredExprs.add(e)
        let (allRefs, positions) = isAllRefs(filteredExprs)
        if allRefs:
            tr.sys.addConstraint(allDifferentExcept0[int](positions))
        else:
            tr.sys.addConstraint(allDifferentExcept0[int](filteredExprs))

    of "set_in":
        # set_in(x, S) means x must be in set S
        let xArg = con.args[0]
        let sArg = con.args[1]
        let sInfo = tr.resolveSetArg(sArg)
        if sInfo.isConst:
            # S is a constant set — restrict x's domain (already handled by FlatZinc domain)
            if xArg.kind == FznIdent and xArg.ident in tr.varPositions:
                let pos = tr.varPositions[xArg.ident]
                let currentDom = tr.sys.baseArray.domain[pos]
                var newDom: seq[int]
                for v in currentDom:
                    if v in sInfo.constVals:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < currentDom.len:
                    tr.sys.baseArray.setDomain(pos, newDom)
        else:
            # S is a set variable
            let info = sInfo.varInfo
            if xArg.kind == FznIntLit or (xArg.kind == FznIdent and xArg.ident in tr.paramValues):
                # x is a constant literal: fix S.bools[x - lo] to 1
                let xVal = tr.resolveIntArg(xArg)
                let bpos = getSetBoolPosition(info, xVal)
                if bpos >= 0:
                    tr.sys.baseArray.setDomain(bpos, @[1])
            elif xArg.kind == FznIdent and xArg.ident in tr.varPositions:
                # x is a variable, S is a set variable: S.bools[x - lo] == 1
                # Restrict x's domain to S's universe
                let xPos = tr.varPositions[xArg.ident]
                let currentDom = tr.sys.baseArray.domain[xPos]
                var newDom: seq[int]
                for v in currentDom:
                    if v >= info.lo and v <= info.hi:
                        newDom.add(v)
                if newDom.len > 0 and newDom.len < currentDom.len:
                    tr.sys.baseArray.setDomain(xPos, newDom)
                # Channel binding: membership = element(x - lo, S.bools)
                # Then constraint: membership == 1
                # This ensures proper cascade propagation through channel-dep.
                let membershipVar = tr.sys.newConstrainedVariable()
                tr.sys.baseArray.setDomain(membershipVar.offset, @[0, 1])
                let xExpr = tr.getExpr(xPos)
                let indexExpr = xExpr - info.lo
                var arrayElems: seq[ArrayElement[int]]
                for bpos in info.positions:
                    arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: bpos))
                tr.sys.baseArray.addChannelBinding(membershipVar.offset, indexExpr, arrayElems)
                let membershipExpr = tr.getExpr(membershipVar.offset)
                let oneExpr = newAlgebraicExpression[int](
                    positions = initPackedSet[int](),
                    node = ExpressionNode[int](kind: LiteralNode, value: 1),
                    linear = true)
                tr.sys.addConstraint(membershipExpr == oneExpr)

    of "set_card":
        # set_card(S, c) means |S| == c
        let sArg = con.args[0]
        let cArg = con.args[1]
        let sInfo = tr.resolveSetArg(sArg)
        if sInfo.isConst:
            # S is a constant set — c must equal |S|
            let cardVal = sInfo.constVals.len
            if cArg.kind == FznIdent and cArg.ident in tr.varPositions:
                let cPos = tr.varPositions[cArg.ident]
                tr.sys.baseArray.setDomain(cPos, @[cardVal])
        else:
            # S is a set variable — sum(S.bools) == c
            let info = sInfo.varInfo
            if info.positions.len == 0:
                # Empty universe set — cardinality must be 0
                if cArg.kind == FznIdent and cArg.ident in tr.varPositions:
                    tr.sys.baseArray.setDomain(tr.varPositions[cArg.ident], @[0])
            else:
                var boolExprs = newSeq[AlgebraicExpression[int]](info.positions.len)
                for i, bpos in info.positions:
                    boolExprs[i] = tr.getExpr(bpos)
                let sumExpr = sum(boolExprs)
                let cExpr = tr.resolveExprArg(cArg)
                tr.sys.addConstraint(sumExpr == cExpr)

    of "set_union":
        # set_union(A, B, C) means C = A ∪ B
        # For each element e in universe: C.bools[e-lo] = max(A.bools[e-lo], B.bools[e-lo])
        # Note: unions with defines_var(C) are detected as channels and get hard channel
        # bindings in buildSetUnionChannelBindings; this soft constraint path handles
        # non-channel unions only.
        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])
        let cInfo = tr.resolveSetArg(con.args[2])
        if cInfo.isConst:
            discard  # Constant result — no constraint needed
        else:
            let cVar = cInfo.varInfo
            for idx in 0..<cVar.positions.len:
                let elem = cVar.lo + idx
                let cBoolPos = cVar.positions[idx]
                let aExpr = constSetExpr(aInfo, tr, elem)
                let bExpr = constSetExpr(bInfo, tr, elem)
                let cExpr = tr.getExpr(cBoolPos)
                tr.sys.addConstraint(cExpr == binaryMax(aExpr, bExpr))

    of "set_intersect":
        # set_intersect(A, B, C) means C = A ∩ B
        # For each element e: C.bools[e-lo] = min(A.bools[e-lo], B.bools[e-lo])
        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])
        let cInfo = tr.resolveSetArg(con.args[2])
        if cInfo.isConst:
            discard
        else:
            let cVar = cInfo.varInfo
            for idx in 0..<cVar.positions.len:
                let elem = cVar.lo + idx
                let cBoolPos = cVar.positions[idx]
                let aExpr = constSetExpr(aInfo, tr, elem)
                let bExpr = constSetExpr(bInfo, tr, elem)
                let cExpr = tr.getExpr(cBoolPos)
                tr.sys.addConstraint(cExpr == binaryMin(aExpr, bExpr))

    of "set_in_reif":
        # set_in_reif(x, S, b) means b ↔ (x ∈ S)
        let xArg = con.args[0]
        let sArg = con.args[1]
        let bArg = con.args[2]
        let sInfo = tr.resolveSetArg(sArg)
        if not sInfo.isConst and xArg.kind == FznIdent and xArg.ident in tr.setVarBoolPositions:
            # Both x and S are set variables — skip (not expected in practice)
            discard
        elif not sInfo.isConst:
            # S is a set variable, x is int/bool
            let info = sInfo.varInfo
            if xArg.kind == FznIntLit or (xArg.kind == FznIdent and xArg.ident in tr.paramValues):
                # x is a constant: b = S.bools[x - lo] (identity channel)
                let xVal = tr.resolveIntArg(xArg)
                let sbpos = getSetBoolPosition(info, xVal)
                if sbpos >= 0:
                    if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
                        let bPos = tr.varPositions[bArg.ident]
                        let zeroExpr = newAlgebraicExpression[int](
                            positions = initPackedSet[int](),
                            node = ExpressionNode[int](kind: LiteralNode, value: 0),
                            linear = true)
                        tr.sys.baseArray.addChannelBinding(bPos, zeroExpr,
                            @[ArrayElement[int](isConstant: false, variablePosition: sbpos)])
                else:
                    # x outside universe — b must be 0
                    if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
                        tr.sys.baseArray.setDomain(tr.varPositions[bArg.ident], @[0])
            elif xArg.kind == FznIdent and (xArg.ident in tr.varPositions or xArg.ident in tr.definedVarExprs):
                # x is a variable (or defined var): b = element(x - lo, S.bools)
                let xExpr = if xArg.ident in tr.varPositions:
                    tr.getExpr(tr.varPositions[xArg.ident])
                else:
                    tr.definedVarExprs[xArg.ident]
                let xDom = if xArg.ident in tr.varPositions:
                    tr.sys.baseArray.domain[tr.varPositions[xArg.ident]]
                else:
                    tr.lookupVarDomain(xArg.ident)
                var arrayElems: seq[ArrayElement[int]]
                # Build array covering x's domain range (out-of-universe values map to 0)
                let arrLo = xDom[0]
                let arrHi = xDom[^1]
                for v in arrLo..arrHi:
                    let bpos = getSetBoolPosition(info, v)
                    if bpos >= 0:
                        arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: bpos))
                    else:
                        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
                if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
                    let bPos = tr.varPositions[bArg.ident]
                    let adjIndexExpr = xExpr - arrLo
                    tr.sys.baseArray.addChannelBinding(bPos, adjIndexExpr, arrayElems)
        else:
            # S is a constant set — b ↔ (x ∈ S) via domain lookup table
            let setAsHashSet = sInfo.constVals
            if xArg.kind == FznIdent and xArg.ident in tr.varPositions:
                let xPos = tr.varPositions[xArg.ident]
                let xExpr = tr.getExpr(xPos)
                let domain = tr.sys.baseArray.domain[xPos]
                if domain.len > 0:
                    let lo = domain[0]
                    let indexExpr = xExpr - lo
                    var arrayElems: seq[ArrayElement[int]]
                    for v in domain:
                        arrayElems.add(ArrayElement[int](isConstant: true,
                                constantValue: if v in setAsHashSet: 1 else: 0))
                    if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
                        let bPos = tr.varPositions[bArg.ident]
                        tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)
            elif xArg.kind == FznIdent and xArg.ident in tr.definedVarExprs:
                # x is a defined var — use its defining expression and declared domain
                let xExpr = tr.definedVarExprs[xArg.ident]
                let domain = tr.lookupVarDomain(xArg.ident)
                if domain.len > 0:
                    let lo = domain[0]
                    let hi = domain[^1]
                    if hi - lo + 1 <= 100_000:
                        let indexExpr = xExpr - lo
                        var arrayElems: seq[ArrayElement[int]]
                        for v in lo..hi:
                            arrayElems.add(ArrayElement[int](isConstant: true,
                                    constantValue: if v in setAsHashSet: 1 else: 0))
                        if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
                            let bPos = tr.varPositions[bArg.ident]
                            tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

    of "array_var_set_element":
        # array_var_set_element(idx, [S1, S2, ...], R) means R = array[idx]
        # For each element e in R's universe: R.bools[e-lo] = element(idx, [S1.bools[e-lo], S2.bools[e-lo], ...])
        let idxArg = con.args[0]
        let arrArg = con.args[1]
        let rArg = con.args[2]

        # Resolve the result set variable
        let rInfo = tr.resolveSetArg(rArg)
        if rInfo.isConst:
            discard  # Result is constant — skip
        else:
            let rVar = rInfo.varInfo

            # Resolve the array of set variables/constants
            var setElems: seq[SetArrayElement]
            case arrArg.kind
            of FznIdent:
                if arrArg.ident in tr.setArrayDecompositions:
                    setElems = tr.setArrayDecompositions[arrArg.ident]
                elif arrArg.ident in tr.setArrayValues:
                    let vals = tr.setArrayValues[arrArg.ident]
                    for sv in vals:
                        setElems.add(SetArrayElement(isConstant: true, constantValues: sv))
                else:
                    discard  # Unknown array
            of FznArrayLit:
                for e in arrArg.elems:
                    let si = tr.resolveSetArg(e)
                    if si.isConst:
                        setElems.add(SetArrayElement(isConstant: true, constantValues: toSeq(si.constVals)))
                    else:
                        setElems.add(SetArrayElement(isConstant: false, varName: e.ident))
            else:
                discard

            if setElems.len > 0:
                # Resolve index expression (FZN element is 1-indexed)
                let idxExpr = tr.resolveExprArg(idxArg)
                let indexExpr = idxExpr - 1  # Convert to 0-based

                # For each boolean position in R's universe
                for idx in 0..<rVar.positions.len:
                    let elem = rVar.lo + idx
                    let rBoolPos = rVar.positions[idx]

                    # Build array elements: for each set in the array, get the boolean for this element
                    var arrayElems: seq[ArrayElement[int]]
                    for se in setElems:
                        if se.isConstant:
                            arrayElems.add(ArrayElement[int](isConstant: true,
                                    constantValue: if elem in se.constantValues: 1 else: 0))
                        else:
                            if se.varName in tr.setVarBoolPositions:
                                let svi = tr.setVarBoolPositions[se.varName]
                                let bpos = getSetBoolPosition(svi, elem)
                                if bpos >= 0:
                                    arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: bpos))
                                else:
                                    arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
                            else:
                                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))

                    # R.bools[elem] = element(idx - 1, [array of bools for this element])
                    tr.sys.baseArray.addChannelBinding(rBoolPos, indexExpr, arrayElems)

    of "array_set_element":
        # array_set_element(idx, [S1, S2, ...], R) means R = array[idx]
        # Simpler version of array_var_set_element: all sets in the array are constants.
        # For each element e in R's universe: R.bools[e-lo] = element(idx-1, [e in S1, e in S2, ...])
        let idxArg = con.args[0]
        let arrArg = con.args[1]
        let rArg = con.args[2]

        let rInfo = tr.resolveSetArg(rArg)
        if not rInfo.isConst:
            let rVar = rInfo.varInfo

            # Resolve the array of constant sets
            var constSets: seq[seq[int]]
            case arrArg.kind
            of FznIdent:
                if arrArg.ident in tr.setArrayValues:
                    constSets = tr.setArrayValues[arrArg.ident]
            of FznArrayLit:
                for e in arrArg.elems:
                    case e.kind
                    of FznSetLit, FznRange:
                        constSets.add(extractSetValues(e))
                    of FznIdent:
                        if e.ident in tr.setParamValues:
                            constSets.add(tr.setParamValues[e.ident])
                        else:
                            constSets.add(@[])
                    else:
                        constSets.add(@[])
            else:
                discard

            if constSets.len > 0:
                # Convert to HashSets for O(1) membership tests
                var setHashSets: seq[HashSet[int]]
                for s in constSets:
                    setHashSets.add(toHashSet(s))

                let idxExpr = tr.resolveExprArg(idxArg)
                let indexExpr = idxExpr - 1  # FZN 1-based → 0-based

                for idx in 0..<rVar.positions.len:
                    let elem = rVar.lo + idx
                    let rBoolPos = rVar.positions[idx]

                    var arrayElems: seq[ArrayElement[int]]
                    for hs in setHashSets:
                        arrayElems.add(ArrayElement[int](isConstant: true,
                                constantValue: if elem in hs: 1 else: 0))

                    tr.sys.baseArray.addChannelBinding(rBoolPos, indexExpr, arrayElems)

    of "set_diff":
        # set_diff(A, B, C) means C = A \ B
        # C.bools[i] = min(A.bools[i], 1 - B.bools[i])
        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])
        let cInfo = tr.resolveSetArg(con.args[2])
        if cInfo.isConst:
            discard
        else:
            let cVar = cInfo.varInfo
            for idx in 0..<cVar.positions.len:
                let elem = cVar.lo + idx
                let cBoolPos = cVar.positions[idx]
                let aExpr = constSetExpr(aInfo, tr, elem)
                let bVal = constSetExpr(bInfo, tr, elem)
                let oneExpr = newAlgebraicExpression[int](
                    positions = initPackedSet[int](),
                    node = ExpressionNode[int](kind: LiteralNode, value: 1),
                    linear = true)
                let cExpr = tr.getExpr(cBoolPos)
                tr.sys.addConstraint(cExpr == binaryMin(aExpr, oneExpr - bVal))

    of "set_subset":
        # set_subset(A, B) means A ⊆ B
        # For each element: A.bools[i] <= B.bools[i]
        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])
        if aInfo.isConst and not bInfo.isConst:
            # Every constant element of A must be in B
            let bVar = bInfo.varInfo
            for elem in aInfo.constVals:
                let bpos = getSetBoolPosition(bVar, elem)
                if bpos >= 0:
                    tr.sys.baseArray.setDomain(bpos, @[1])
        elif not aInfo.isConst and bInfo.isConst:
            # Every element of A must be in constant B
            let aVar = aInfo.varInfo
            for idx in 0..<aVar.positions.len:
                let elem = aVar.lo + idx
                if elem notin bInfo.constVals:
                    tr.sys.baseArray.setDomain(aVar.positions[idx], @[0])
        elif not aInfo.isConst and not bInfo.isConst:
            # A.bools[i] <= B.bools[i] for all i in shared universe
            let aVar = aInfo.varInfo
            let bVar = bInfo.varInfo
            let lo = max(aVar.lo, bVar.lo)
            let hi = min(aVar.hi, bVar.hi)
            for elem in lo..hi:
                let aPos = getSetBoolPosition(aVar, elem)
                let bPos = getSetBoolPosition(bVar, elem)
                if aPos >= 0 and bPos >= 0:
                    tr.sys.addConstraint(tr.getExpr(aPos) <= tr.getExpr(bPos))
            # Elements in A outside B's universe must be 0
            for idx in 0..<aVar.positions.len:
                let elem = aVar.lo + idx
                if elem < bVar.lo or elem > bVar.hi:
                    tr.sys.baseArray.setDomain(aVar.positions[idx], @[0])

    of "set_eq":
        # set_eq(A, B) means A = B (all booleans equal)
        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])
        if aInfo.isConst and not bInfo.isConst:
            # Fix B's booleans to match constant A
            let bVar = bInfo.varInfo
            let constSet = aInfo.constVals
            for idx in 0..<bVar.positions.len:
                let elem = bVar.lo + idx
                if elem in constSet:
                    tr.sys.baseArray.setDomain(bVar.positions[idx], @[1])
                else:
                    tr.sys.baseArray.setDomain(bVar.positions[idx], @[0])
        elif not aInfo.isConst and bInfo.isConst:
            let aVar = aInfo.varInfo
            let constSet = bInfo.constVals
            for idx in 0..<aVar.positions.len:
                let elem = aVar.lo + idx
                if elem in constSet:
                    tr.sys.baseArray.setDomain(aVar.positions[idx], @[1])
                else:
                    tr.sys.baseArray.setDomain(aVar.positions[idx], @[0])
        elif not aInfo.isConst and not bInfo.isConst:
            let aVar = aInfo.varInfo
            let bVar = bInfo.varInfo
            let lo = min(aVar.lo, bVar.lo)
            let hi = max(aVar.hi, bVar.hi)
            for elem in lo..hi:
                let aPos = getSetBoolPosition(aVar, elem)
                let bPos = getSetBoolPosition(bVar, elem)
                if aPos >= 0 and bPos >= 0:
                    tr.sys.addConstraint(tr.getExpr(aPos) == tr.getExpr(bPos))
                elif aPos >= 0:
                    tr.sys.baseArray.setDomain(aPos, @[0])
                elif bPos >= 0:
                    tr.sys.baseArray.setDomain(bPos, @[0])

    of "set_ne":
        # set_ne(A, B) means A ≠ B — at least one boolean differs
        # sum(|A[i] - B[i]|) >= 1 (exact for booleans: |a-b| = a+b - 2*min(a,b))
        let aInfo = tr.resolveSetArg(con.args[0])
        let bInfo = tr.resolveSetArg(con.args[1])
        if not aInfo.isConst and not bInfo.isConst:
            let aVar = aInfo.varInfo
            let bVar = bInfo.varInfo
            let lo = min(aVar.lo, bVar.lo)
            let hi = max(aVar.hi, bVar.hi)
            var diffExprs: seq[AlgebraicExpression[int]]
            for elem in lo..hi:
                let aExpr = constSetExpr(aInfo, tr, elem)
                let bExpr = constSetExpr(bInfo, tr, elem)
                diffExprs.add(aExpr + bExpr - 2 * binaryMin(aExpr, bExpr))
            if diffExprs.len > 0:
                tr.sys.addConstraint(sum(diffExprs) >= 1)

    of "fzn_bin_packing_load":
        # bin_packing_load(load, bin, w): load[b] = sum(w[i] where bin[i] == b)
        let loadArg = con.args[0]
        let binArg = con.args[1]
        let weights = tr.resolveIntArray(con.args[2])

        # Separate variable and constant bin assignments
        var constBinIndices: seq[int]  # indices into weights for constant bin assignments
        var constBinValues: seq[int]
        var varPositions: seq[int]
        var varWeights: seq[int]
        let binExprs = tr.resolveExprArray(binArg)
        for i, e in binExprs:
            if e.node.kind == LiteralNode:
                constBinIndices.add(i)
                constBinValues.add(int(e.node.value))
            elif e.node.kind == RefNode:
                varPositions.add(e.node.position)
                varWeights.add(weights[i])
            else:
                varPositions.add(e.positions.toSeq[0])
                varWeights.add(weights[i])

        # Resolve load positions (will become channels)
        var loadPositions: seq[int]
        let loadExprs = tr.resolveExprArray(loadArg)
        for e in loadExprs:
            if e.node.kind == RefNode:
                loadPositions.add(e.node.position)
            else:
                loadPositions.add(e.positions.toSeq[0])

        # Derive loadBase from bin variable domains (minimum possible bin value)
        # FlatZinc normalizes arrays to 1-based, so loadBase is typically 1,
        # but we derive it to be robust against non-standard indexing.
        var loadBase = high(int)
        for pos in varPositions:
            let dom = tr.sys.baseArray.domain[pos]
            if dom.len > 0:
                loadBase = min(loadBase, min(dom))
        for v in constBinValues:
            loadBase = min(loadBase, v)
        if loadBase == high(int):
            loadBase = 1  # fallback for empty domains

        # For each load position: create WeightedCountEq channel
        for b in 0..<loadPositions.len:
            let binValue = b + loadBase
            let loadPos = loadPositions[b]

            # Compute constant offset from fixed bin assignments
            var constOffset = 0
            for ci in 0..<constBinIndices.len:
                if constBinValues[ci] == binValue:
                    constOffset += weights[constBinIndices[ci]]

            tr.sys.baseArray.addWeightedCountEqChannelBinding(
                loadPos, binValue, varPositions, varWeights, constOffset)

        # Add sum(load) = sum(w) as constraint for domain reduction
        let totalWeight = weights.foldl(a + b, 0)
        let loadSp = scalarProduct[int](newSeqWith(loadPositions.len, 1), loadExprs)
        tr.sys.addConstraint(loadSp == totalWeight)

        stderr.writeLine(&"[FZN] bin_packing_load: {loadPositions.len} loads, {binExprs.len} items ({constBinValues.len} const) -> {loadPositions.len} weighted count channels")

    of "fzn_bin_packing":
        # bin_packing(c, bin, w): for each bin b, sum(w[i] where bin[i]==b) <= c
        let capacity = tr.resolveIntArg(con.args[0])
        let binExprs = tr.resolveExprArray(con.args[1])
        let weights = tr.resolveIntArray(con.args[2])

        # Separate variable and constant bin assignments
        var varPositions: seq[int]
        var varWeights: seq[int]
        var constBinValues: seq[int]   # bin value for each constant assignment
        var constWeights: seq[int]     # weight for each constant assignment
        for i, e in binExprs:
            if e.node.kind == LiteralNode:
                constBinValues.add(int(e.node.value))
                constWeights.add(weights[i])
            elif e.node.kind == RefNode:
                varPositions.add(e.node.position)
                varWeights.add(weights[i])
            else:
                varPositions.add(e.positions.toSeq[0])
                varWeights.add(weights[i])

        # Determine range of bin values from variable domains and constant values
        var binLo = high(int)
        var binHi = low(int)
        for pos in varPositions:
            let dom = tr.sys.baseArray.domain[pos]
            if dom.len > 0:
                binLo = min(binLo, min(dom))
                binHi = max(binHi, max(dom))
        for v in constBinValues:
            binLo = min(binLo, v)
            binHi = max(binHi, v)

        let totalWeight = weights.foldl(a + b, 0)
        var allUnit = true
        for w in weights:
            if w != 1: allUnit = false; break

        # For each possible bin value, create auxiliary load variable + channel + capacity constraint
        var nChannels = 0
        for b in binLo..binHi:
            let loadPos = tr.sys.baseArray.len
            discard tr.sys.newConstrainedVariable()
            tr.sys.baseArray.domain[loadPos] = toSeq(0..min(totalWeight, capacity))

            # Compute constant offset from fixed bin assignments
            var constOffset = 0
            for ci in 0..<constBinValues.len:
                if constBinValues[ci] == b:
                    constOffset += constWeights[ci]

            if allUnit:
                # Unit weights: use cheaper CountEq channel
                tr.sys.baseArray.addCountEqChannelBinding(
                    loadPos, b, varPositions, constOffset)
            else:
                tr.sys.baseArray.addWeightedCountEqChannelBinding(
                    loadPos, b, varPositions, varWeights, constOffset)

            let loadExpr = tr.getExpr(loadPos)
            tr.sys.addConstraint(loadExpr <= capacity)
            inc nChannels

        stderr.writeLine(&"[FZN] bin_packing: {nChannels} bins (cap={capacity}), {binExprs.len} items ({constBinValues.len} const) -> {nChannels} " &
            (if allUnit: "count" else: "weighted count") & " channels")

    else:
        # Unknown constraint - warn and skip
        stderr.writeLine(&"[FZN] Warning: unsupported constraint '{con.name}' (normalized: '{name}'), skipping")

proc translateSolve(tr: var FznTranslator) =
    ## Handles the solve directive.
    case tr.model.solve.kind
    of Minimize, Maximize:
        if tr.model.solve.objective != nil:
            case tr.model.solve.objective.kind
            of FznIdent:
                let objName = tr.model.solve.objective.ident
                if objName == tr.weightedSameValueObjName:
                    # Weighted same-value objective — handled separately via WeightedSameValueExpression
                    tr.objectivePos = ObjPosWeightedSV
                elif objName in tr.varPositions:
                    tr.objectivePos = tr.varPositions[objName]
                    # Extract domain bounds from the variable declaration for the optimizer
                    for decl in tr.model.variables:
                        if not decl.isArray and decl.name == objName:
                            if decl.varType.kind == FznIntRange:
                                tr.objectiveLoBound = decl.varType.lo
                                tr.objectiveHiBound = decl.varType.hi
                            break
                elif objName in tr.definedVarExprs:
                    # Objective was eliminated as a defined variable — use its defining expression directly.
                    # This avoids an intermediate position + binary-penalty linking constraint,
                    # which would hide objective gradient from compound moves (ejection chains).
                    tr.objectiveDefExpr = tr.definedVarExprs[objName]
                    tr.objectivePos = ObjPosDefinedExpr
                else:
                    raise newException(KeyError, &"Unknown objective variable '{objName}'")
            else:
                raise newException(ValueError, "Objective must be a variable identifier")
    of Satisfy:
        tr.objectivePos = ObjPosNone

proc extractSearchAnnotationVars(tr: var FznTranslator) =
    ## Extracts variable names from solve :: int_search / seq_search annotations.
    ## Populates tr.annotatedSearchVarNames with all variable names that are
    ## explicitly listed as search variables by the model's solve annotation.

    proc extractFromAnnotation(tr: var FznTranslator, ann: FznAnnotation) =
        ## Recursively extract variable names from a single search annotation.
        case ann.name
        of "int_search", "bool_search":
            # int_search(array, varsel, valsel, strategy)
            # First arg is the array of search variables
            if ann.args.len >= 1:
                let arrayArg = ann.args[0]
                case arrayArg.kind
                of FznIdent:
                    # Named array reference — resolve to element variable names
                    let arrayName = arrayArg.ident
                    # Look up in model declarations
                    for decl in tr.model.variables:
                        if decl.isArray and decl.name == arrayName and decl.value != nil and
                           decl.value.kind == FznArrayLit:
                            for elem in decl.value.elems:
                                if elem.kind == FznIdent:
                                    tr.annotatedSearchVarNames.incl(elem.ident)
                            break
                of FznArrayLit:
                    # Inline array literal
                    for elem in arrayArg.elems:
                        if elem.kind == FznIdent:
                            tr.annotatedSearchVarNames.incl(elem.ident)
                else:
                    discard
        of "seq_search":
            # seq_search([ann1, ann2, ...]) — recurse into each sub-annotation
            if ann.args.len >= 1 and ann.args[0].kind == FznArrayLit:
                for elem in ann.args[0].elems:
                    if elem.kind == FznAnnotationExpr:
                        tr.extractFromAnnotation(FznAnnotation(
                            name: elem.annName, args: elem.annArgs))
        else:
            discard  # Unknown annotation type — ignore

    for ann in tr.model.solve.annotations:
        tr.extractFromAnnotation(ann)
        if tr.annotatedSearchVarNames.len > 0:
            tr.hasSearchAnnotation = true

    if tr.hasSearchAnnotation:
        stderr.writeLine("[FZN] Solve annotation: " & $tr.annotatedSearchVarNames.len &
            " annotated search variables")

proc detectOrphanSearchVariables(tr: var FznTranslator) =
    ## Before translateVariables: detect non-annotated search variables ("orphans") and
    ## add them to equalityCopyAliases + definedVarNames so they don't get system positions.
    ##
    ## Orphan variables KEEP their system positions (needed by constraints that reference
    ## them, like at_least/at_most and reification channels). But they're marked as
    ## channel positions (not searched) and get element channel bindings that copy the
    ## annotated variable's value. This ensures:
    ## 1. Constraints on orphan positions see the same values as annotated positions
    ## 2. Channel-dep penalty maps trace through orphan positions correctly
    ## 3. Reification channels on orphan positions propagate correctly
    if not tr.hasSearchAnnotation:
        return

    # Build set of bool2int output variable names from model constraints.
    # bool2intSourceMap isn't populated yet (detectNandRedundancy runs later),
    # so we scan constraints directly.
    var bool2intOutputs: HashSet[string]
    for con in tr.model.constraints:
        if stripSolverPrefix(con.name) == "bool2int" and con.args.len >= 2 and
           con.args[1].kind == FznIdent:
            bool2intOutputs.incl(con.args[1].ident)

    # Identify orphan search variables: not in annotation, not channels, not defined
    var orphanVarNames: seq[string]
    for decl in tr.model.variables:
        if decl.isArray: continue
        if not decl.isVar: continue  # skip parameters
        let vn = decl.name
        if vn in tr.annotatedSearchVarNames: continue
        if vn in tr.channelVarNames: continue
        if vn in tr.definedVarNames: continue
        if vn in bool2intOutputs: continue  # bool2int output — not an orphan
        case decl.varType.kind
        of FznBool:
            continue
        else:
            discard
        orphanVarNames.add(vn)

    if orphanVarNames.len == 0:
        return

    stderr.writeLine("[FZN] Warning: " & $orphanVarNames.len &
        " non-annotated search variables detected (not in solve :: int_search)")

    let orphanSet = toHashSet(orphanVarNames)
    let annotatedSet = tr.annotatedSearchVarNames

    # Reconstruct variable sequences from overlapping window arrays.
    var successors: Table[string, string]
    var predecessors: Table[string, string]
    var hasMixedArray = false

    for decl in tr.model.variables:
        if not decl.isArray or decl.value == nil or decl.value.kind != FznArrayLit:
            continue
        var hasOrphan, hasAnnotated = false
        var elems: seq[string]
        for elem in decl.value.elems:
            if elem.kind == FznIdent:
                elems.add(elem.ident)
                if elem.ident in orphanSet: hasOrphan = true
                if elem.ident in annotatedSet: hasAnnotated = true
            else:
                elems.add("")
        if hasOrphan and hasAnnotated:
            hasMixedArray = true
        if hasOrphan or hasAnnotated:
            for i in 0..<elems.len - 1:
                let a = elems[i]
                let b = elems[i + 1]
                if a == "" or b == "": continue
                if a notin successors:
                    successors[a] = b
                if b notin predecessors:
                    predecessors[b] = a

    if not hasMixedArray:
        stderr.writeLine("[FZN] No overlapping arrays found between orphan and annotated variables")
        return

    # Find an annotated variable that is preceded by an orphan variable.
    var boundaryAnnotated = ""
    var boundaryOrphan = ""
    for vn in annotatedSet:
        if vn in predecessors and predecessors[vn] in orphanSet:
            boundaryAnnotated = vn
            boundaryOrphan = predecessors[vn]
            break

    if boundaryAnnotated == "":
        stderr.writeLine("[FZN] Could not find orphan→annotated boundary in window arrays")
        return

    # Walk backward from boundary orphan to reconstruct orphan sequence
    var orphanSeq: seq[string]
    var cur = boundaryOrphan
    var visitedOrphans: HashSet[string]
    while cur in orphanSet and cur notin visitedOrphans:
        visitedOrphans.incl(cur)
        orphanSeq.add(cur)
        if cur in predecessors and predecessors[cur] in orphanSet:
            cur = predecessors[cur]
        else:
            break
    var orphanForward: seq[string]
    for i in countdown(orphanSeq.len - 1, 0):
        orphanForward.add(orphanSeq[i])

    # Build complete annotated sequence
    var fullAnnotatedSeq: seq[string]
    cur = boundaryAnnotated
    var visited: HashSet[string]
    while cur in annotatedSet and cur notin visited:
        visited.incl(cur)
        fullAnnotatedSeq.add(cur)
        if cur in successors: cur = successors[cur]
        else: break
    var prefixAnnotated: seq[string]
    visited.clear()
    if boundaryAnnotated in predecessors:
        cur = predecessors[boundaryAnnotated]
        while cur in annotatedSet and cur notin visited:
            visited.incl(cur)
            prefixAnnotated.add(cur)
            if cur in predecessors: cur = predecessors[cur]
            else: break
    var completeAnnotatedSeq: seq[string]
    for i in countdown(prefixAnnotated.len - 1, 0):
        completeAnnotatedSeq.add(prefixAnnotated[i])
    for vn in fullAnnotatedSeq:
        completeAnnotatedSeq.add(vn)

    if orphanForward.len != completeAnnotatedSeq.len:
        stderr.writeLine("[FZN] Orphan sequence length (" & $orphanForward.len &
            ") != annotated sequence length (" & $completeAnnotatedSeq.len &
            ") — cannot infer mapping, skipping")
        return

    # Store the mapping for later: after translateVariables, we create equality
    # constraints to link orphan positions to annotated positions.
    tr.orphanToAnnotatedMap = newSeq[(string, string)]()
    for i in 0..<orphanForward.len:
        let orphanName = orphanForward[i]
        let annotatedName = completeAnnotatedSeq[i]
        if orphanName != annotatedName:
            tr.orphanToAnnotatedMap.add((orphanName, annotatedName))

    if tr.orphanToAnnotatedMap.len > 0:
        stderr.writeLine("[FZN] Detected " & $tr.orphanToAnnotatedMap.len &
            " orphan→annotated variable mappings (will generate equality constraints)")

proc buildOrphanEqualityConstraints(tr: var FznTranslator) =
    ## After translateVariables: generate equality constraints linking orphan
    ## positions to annotated positions. These provide penalty signals during
    ## search to keep the two sets synchronized.
    if tr.orphanToAnnotatedMap.len == 0:
        return

    var nEqualities = 0
    var nSkippedDisjoint = 0
    for (orphanName, annotatedName) in tr.orphanToAnnotatedMap:
        if orphanName notin tr.varPositions or annotatedName notin tr.varPositions:
            continue
        let orphanPos = tr.varPositions[orphanName]
        let annotatedPos = tr.varPositions[annotatedName]
        # Check domain compatibility: skip if domains are completely disjoint,
        # as an unsatisfiable equality constraint would pollute penalty maps.
        let orphanDom = tr.sys.baseArray.domain[orphanPos]
        let annotatedDom = tr.sys.baseArray.domain[annotatedPos]
        let annotatedSet = annotatedDom.toHashSet()
        var hasOverlap = false
        for v in orphanDom:
            if v in annotatedSet:
                hasOverlap = true
                break
        if not hasOverlap:
            inc nSkippedDisjoint
            continue
        tr.sys.addConstraint(tr.getExpr(orphanPos) == tr.getExpr(annotatedPos))
        inc nEqualities

    if nSkippedDisjoint > 0:
        stderr.writeLine("[FZN] Warning: skipped " & $nSkippedDisjoint &
            " orphan equality constraints due to disjoint domains")
    if nEqualities > 0:
        stderr.writeLine("[FZN] Generated " & $nEqualities &
            " equality constraints linking orphan to annotated search variables")

