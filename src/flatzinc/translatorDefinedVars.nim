## Included from translator.nim -- not a standalone module.

proc resolveVarArrayElems(tr: FznTranslator, arg: FznExpr): seq[FznExpr] =
    ## Resolves a variable array argument to its elements, from inline literal or named declaration.
    if arg.kind == FznArrayLit:
        return arg.elems
    elif arg.kind == FznIdent:
        for decl in tr.model.variables:
            if decl.isArray and decl.name == arg.ident and decl.value != nil and decl.value.kind == FznArrayLit:
                return decl.value.elems
    return @[]

proc collectDefinedVars(tr: var FznTranslator) =
    ## First pass: identify variables defined by int_lin_eq constraints with defines_var annotations.
    ## These variables will be replaced by their defining expressions instead of being created as positions.
    var definedVarNames: Table[string, bool]
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name == "int_lin_eq" and con.hasAnnotation("defines_var"):
            # Find the defines_var annotation
            var ann: FznAnnotation
            for a in con.annotations:
                if a.name == "defines_var":
                    ann = a
                    break
            if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                let definedName = ann.args[0].ident
                # Check: the defined var must be one of the variables in the constraint,
                # and its coefficient must be 1 or -1 for exact integer arithmetic
                let coeffs = tr.resolveIntArray(con.args[0])
                let varElems = tr.resolveVarArrayElems(con.args[1])
                for vi, v in varElems:
                    if v.kind == FznIdent and v.ident == definedName and (coeffs[vi] == 1 or coeffs[vi] == -1):
                        definedVarNames[definedName] = true
                        tr.definingConstraints.incl(ci)
                        break
    # Third loop: identify int_abs, int_max, int_min, int_times with defines_var annotations
    # int_min/int_max become channel variables (like array_int_minimum/maximum) to avoid
    # deep expression tree inlining that creates exponentially large DAGs.
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name in ["int_abs", "int_max", "int_min", "int_times"] and con.hasAnnotation("defines_var"):
            let ann = con.getAnnotation("defines_var")
            if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                let definedName = ann.args[0].ident
                # int_abs(a, b) :: defines_var(b) → b is args[1]
                # int_max(a, b, c) :: defines_var(c) → c is args[2]
                # int_min(a, b, c) :: defines_var(c) → c is args[2]
                # int_times(a, b, c) :: defines_var(c) → c is args[2]
                let expectedIdx = if name == "int_abs": 1 else: 2
                if con.args[expectedIdx].kind == FznIdent and
                     con.args[expectedIdx].ident == definedName:
                    if name in ["int_min", "int_max"]:
                        # Make int_min/int_max into channel variables to avoid deep expression DAGs
                        let isMin = name == "int_min"
                        tr.channelVarNames.incl(definedName)
                        tr.definingConstraints.incl(ci)
                        tr.minMaxChannelDefs.add((ci: ci, varName: definedName, isMin: isMin))
                    else:
                        definedVarNames[definedName] = true
                        tr.definingConstraints.incl(ci)
        # int_div(a, b, c) :: defines_var(c) → expression channel variable (c = a div b)
        # int_mod(a, b, c) :: defines_var(c) → expression channel variable (c = a mod b)
        # int_plus(a, b, c) :: defines_var(c) → expression channel variable (c = a + b)
        elif name in ["int_div", "int_mod", "int_plus"] and con.hasAnnotation("defines_var"):
            let ann = con.getAnnotation("defines_var")
            if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                let definedName = ann.args[0].ident
                if con.args[2].kind == FznIdent and con.args[2].ident == definedName:
                    tr.channelVarNames.incl(definedName)
                    tr.definingConstraints.incl(ci)
                    tr.expressionChannelDefs.add((ci: ci, varName: definedName))
        # array_int_minimum(m, array) :: defines_var(m) → channel variable (not searched)
        # array_int_maximum(m, array) :: defines_var(m) → channel variable (not searched)
        elif name in ["array_int_minimum", "array_int_maximum"] and con.hasAnnotation("defines_var"):
            let ann = con.getAnnotation("defines_var")
            if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                let definedName = ann.args[0].ident
                if con.args[0].kind == FznIdent and con.args[0].ident == definedName:
                    let isMin = name == "array_int_minimum"
                    tr.channelVarNames.incl(definedName)
                    tr.definingConstraints.incl(ci)
                    tr.minMaxChannelDefs.add((ci: ci, varName: definedName, isMin: isMin))

    # Refine int_min/int_max channel decisions: only keep as channels when inputs
    # reference other channels (risk of exponential DAG growth from chained inlining).
    # Simple binary min/max (e.g., max(abs(x-y), abs(a-b))) can be safely inlined
    # as defined var expressions, giving the solver direct gradient through penalty maps.
    block:
        var refined: seq[tuple[ci: int, varName: string, isMin: bool]]
        for def in tr.minMaxChannelDefs:
            let con = tr.model.constraints[def.ci]
            let cname = stripSolverPrefix(con.name)
            var inputsRefChannel = false
            if cname in ["int_min", "int_max"]:
                for argIdx in 0..1:
                    let arg = con.args[argIdx]
                    if arg.kind == FznIdent and arg.ident in tr.channelVarNames:
                        inputsRefChannel = true
                        break
            else:
                # array_int_minimum/maximum — variable-length arrays, keep as channels
                inputsRefChannel = true
            if inputsRefChannel:
                refined.add(def)
            else:
                # Safe to inline as defined var expression
                tr.channelVarNames.excl(def.varName)
                definedVarNames[def.varName] = true
        tr.minMaxChannelDefs = refined

    # Detect int_times(a, b, c) WITHOUT defines_var where c can be treated as defined.
    # MiniZinc sometimes doesn't annotate cube variables (x^2 * x = x^3) with defines_var
    # even though the result is fully determined. These can have enormous domains (54M+).
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_times": continue
        if con.hasAnnotation("defines_var"): continue  # already handled above
        if con.args.len < 3: continue
        # int_times(a, b, c): c = a * b
        let cArg = con.args[2]
        if cArg.kind != FznIdent: continue
        let cName = cArg.ident
        if cName in definedVarNames or cName in tr.channelVarNames: continue
        # Check that a and b are resolvable (constants, positioned vars, or defined vars)
        var resolvable = true
        for idx in 0..1:
            let arg = con.args[idx]
            if arg.kind == FznIdent:
                let id = arg.ident
                if id notin tr.paramValues and id notin definedVarNames and
                     id notin tr.channelVarNames:
                    # It's a free variable — that's ok, it will get a position
                    discard
            elif arg.kind != FznIntLit:
                resolvable = false
        if resolvable:
            definedVarNames[cName] = true
            tr.definingConstraints.incl(ci)

    # Store the set of defined variable names for use in translateVariables
    for name in definedVarNames.keys:
        tr.definedVarNames.incl(name)

    # Second loop: identify element constraints with defines_var annotations
    # These define channel variables that should be computed, not searched
    # Also deduplicate: when multiple constant-array element constraints share the same
    # index variable and array content, only the first becomes a channel; duplicates
    # become defined-variable aliases (eliminated, no position allocated).
    type ElementKey = tuple[indexVar: string, arrayHash: Hash, arrayLen: int]
    var elementChannelMap: Table[ElementKey, string]  # key -> first channel var name
    var elementArrayCache: Table[string, seq[int]]  # channel var name -> resolved array (for verification)
    var nElementAliases = 0
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name in ["array_var_int_element", "array_var_int_element_nonshifted",
                                "array_int_element", "array_int_element_nonshifted",
                                "array_var_bool_element", "array_var_bool_element_nonshifted",
                                "array_bool_element"] and
             con.hasAnnotation("defines_var"):
            # Extract the defined variable name from the 3rd argument
            if con.args[2].kind == FznIdent:
                let definedName = con.args[2].ident
                let ann = con.getAnnotation("defines_var")
                if ann.args.len > 0 and ann.args[0].kind == FznIdent and
                     ann.args[0].ident == definedName:
                    # Try to deduplicate constant-array element constraints
                    var deduplicated = false
                    if name in ["array_int_element", "array_int_element_nonshifted",
                                            "array_bool_element"] and
                         con.args[0].kind == FznIdent:
                        let indexVar = con.args[0].ident
                        try:
                            let constArray = tr.resolveIntArray(con.args[1])
                            let key: ElementKey = (indexVar, hash(constArray), constArray.len)
                            if key in elementChannelMap:
                                # Verify content match (hash collision guard)
                                let originalName = elementChannelMap[key]
                                if elementArrayCache[originalName] == constArray:
                                    # Duplicate! Make this a defined-var alias instead of a channel
                                    tr.elementChannelAliases[definedName] = originalName
                                    tr.definedVarNames.incl(definedName)
                                    tr.definingConstraints.incl(ci)
                                    deduplicated = true
                                    nElementAliases += 1
                            else:
                                elementChannelMap[key] = definedName
                                elementArrayCache[definedName] = constArray
                        except KeyError:
                            discard  # array resolution failed, skip dedup

                    if not deduplicated:
                        tr.channelVarNames.incl(definedName)
                        tr.channelConstraints[ci] = definedName
                        # DO NOT add to definedVarNames (channel vars need positions)
                        tr.definingConstraints.incl(ci)  # Channel binding replaces this constraint
    if nElementAliases > 0:
        stderr.writeLine(&"[FZN] Deduplicated {nElementAliases} element channels (shared index+array)")

    # Dead element channel elimination: detect element channel variables that
    # are not referenced by any constraint other than their own defining constraint.
    # These are "dead" channels (e.g., stock lookups when symmetry breaking is disabled)
    # and can be eliminated.
    block:
        # Collect variable references per constraint (excluding only the channel's own
        # defining constraint, not all defining constraints — other defining constraints
        # like the objective's int_lin_eq may reference channels that must be kept alive).
        # Build a set of all variable references from non-defining constraints,
        # PLUS references from defining constraints that define OTHER variables.
        # For each element channel, it's "dead" only if no constraint other than its
        # own defining constraint references it.

        # First: build per-constraint reference sets for defining constraints
        var definingRefs: Table[int, HashSet[string]]
        for ci in tr.definingConstraints:
            let con = tr.model.constraints[ci]
            var refs = initHashSet[string]()
            for arg in con.args:
                if arg.kind == FznIdent:
                    refs.incl(arg.ident)
                elif arg.kind == FznArrayLit:
                    for elem in arg.elems:
                        if elem.kind == FznIdent:
                            refs.incl(elem.ident)
            definingRefs[ci] = refs

        # Collect all variable references from non-defining constraints
        var referencedVars = initHashSet[string]()
        for ci, con in tr.model.constraints:
            if ci in tr.definingConstraints:
                continue
            for arg in con.args:
                if arg.kind == FznIdent:
                    referencedVars.incl(arg.ident)
                elif arg.kind == FznArrayLit:
                    for elem in arg.elems:
                        if elem.kind == FznIdent:
                            referencedVars.incl(elem.ident)
            # Also check annotation args (some constraints reference vars in annotations)
            for ann in con.annotations:
                for annArg in ann.args:
                    if annArg.kind == FznIdent:
                        referencedVars.incl(annArg.ident)
        # Also check array variable declarations (vars referenced as array elements)
        for decl in tr.model.variables:
            if decl.value != nil and decl.value.kind == FznArrayLit:
                for elem in decl.value.elems:
                    if elem.kind == FznIdent:
                        referencedVars.incl(elem.ident)

        # Build reverse alias map: original channel name → set of alias names
        var aliasesOf = initTable[string, seq[string]]()
        for aliasName, originalName in tr.elementChannelAliases:
            if originalName notin aliasesOf:
                aliasesOf[originalName] = @[]
            aliasesOf[originalName].add(aliasName)

        # Check each element channel: if neither it nor any alias is referenced, eliminate it
        # A channel is referenced if:
        #   1. It appears in a non-defining constraint, OR
        #   2. It appears in a defining constraint OTHER than its own
        var nDeadChannels = 0
        var deadCIs: seq[int] = @[]
        for ci, chanName in tr.channelConstraints:
            var isReferenced = chanName in referencedVars
            if not isReferenced:
                # Check aliases
                if chanName in aliasesOf:
                    for aliasName in aliasesOf[chanName]:
                        if aliasName in referencedVars:
                            isReferenced = true
                            break
            if not isReferenced:
                # Check if any OTHER defining constraint references this channel
                for defCi, refs in definingRefs:
                    if defCi == ci:
                        continue  # skip own defining constraint
                    if chanName in refs:
                        isReferenced = true
                        break
                    if chanName in aliasesOf:
                        for aliasName in aliasesOf[chanName]:
                            if aliasName in refs:
                                isReferenced = true
                                break
                    if isReferenced:
                        break
            if not isReferenced:
                # Dead channel: convert to defined var (no position needed)
                tr.channelVarNames.excl(chanName)
                tr.definedVarNames.incl(chanName)
                deadCIs.add(ci)
                nDeadChannels += 1
        for ci in deadCIs:
            tr.channelConstraints.del(ci)
        if nDeadChannels > 0:
            stderr.writeLine(&"[FZN] Eliminated {nDeadChannels} dead element channels (unreferenced)")

    # Rescue defined vars that appear in var-indexed arrays.
    # These need positions for element constraint channel bindings, so convert
    # them from defined vars (expression-only) to channel vars with positions.
    block:
        var rescueNames = initHashSet[string]()
        for ci, con in tr.model.constraints:
            let name = stripSolverPrefix(con.name)
            if name notin ["array_var_int_element", "array_var_int_element_nonshifted",
                                        "array_var_bool_element", "array_var_bool_element_nonshifted"]:
                continue
            let elems = tr.resolveVarArrayElems(con.args[1])
            for elem in elems:
                if elem.kind == FznIdent and elem.ident in tr.definedVarNames:
                    rescueNames.incl(elem.ident)

        if rescueNames.len > 0:
            # Find defining constraints for each rescued var
            for ci, con in tr.model.constraints:
                if ci notin tr.definingConstraints: continue
                if con.hasAnnotation("defines_var"):
                    let ann = con.getAnnotation("defines_var")
                    if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                        let definedName = ann.args[0].ident
                        if definedName in rescueNames:
                            tr.rescuedChannelDefs.add((ci: ci, varName: definedName))
                else:
                    # Handle int_times without defines_var (detected by collectDefinedVars)
                    let name = stripSolverPrefix(con.name)
                    if name == "int_times" and con.args.len >= 3 and
                         con.args[2].kind == FznIdent:
                        let cName = con.args[2].ident
                        if cName in rescueNames:
                            tr.rescuedChannelDefs.add((ci: ci, varName: cName))

            # Move from definedVarNames to channelVarNames
            for name in rescueNames:
                tr.definedVarNames.excl(name)
                tr.channelVarNames.incl(name)
            stderr.writeLine(&"[FZN] Rescued {rescueNames.len} defined vars as channels (from var-indexed arrays)")

proc tryBuildDefinedExpression(tr: var FznTranslator, ci: int): bool =
    ## Tries to build the AlgebraicExpression for one defining constraint.
    ## Returns true if successful, false if a dependency is not yet available.
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)

    # Handle int_times without defines_var (detected by collectDefinedVars)
    if name == "int_times" and not con.hasAnnotation("defines_var"):
        if con.args.len < 3 or con.args[2].kind != FznIdent: return true
        let definedName = con.args[2].ident
        if definedName notin tr.definedVarNames: return true
        if definedName in tr.definedVarExprs: return true
        let a = con.args[0]
        let b = con.args[1]
        for operand in [a, b]:
            if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
                 operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
                 operand.ident notin tr.paramValues:
                return false  # dependency not yet built
        tr.definedVarExprs[definedName] = tr.resolveExprArg(a) * tr.resolveExprArg(b)
        return true

    # Only process defining constraints with defines_var
    if name notin ["int_lin_eq", "int_abs", "int_max", "int_min", "int_times",
                                    "array_int_minimum", "array_int_maximum"] or
         not con.hasAnnotation("defines_var"):
        return true  # not our concern, treat as done
    var ann: FznAnnotation
    for a in con.annotations:
        if a.name == "defines_var":
            ann = a
            break
    let definedName = ann.args[0].ident
    # Min/max channel vars get positions and channel bindings, not expressions
    if definedName in tr.channelVarNames:
        return true
    if definedName in tr.definedVarExprs:
        return true  # already built
    # WeightedSameValue objective is handled separately
    if definedName == tr.weightedSameValueObjName:
        return true

    # Handle int_abs, int_max, int_min
    if name == "int_abs":
        # int_abs(a, b) :: defines_var(b) → b = abs(a)
        let a = con.args[0]
        if a.kind == FznIdent and a.ident in tr.definedVarNames and
             a.ident notin tr.definedVarExprs and a.ident notin tr.varPositions and
             a.ident notin tr.paramValues:
            return false  # dependency not yet built
        tr.definedVarExprs[definedName] = abs(tr.resolveExprArg(a))
        return true

    if name == "int_max":
        # int_max(a, b, c) :: defines_var(c) → c = max(a, b)
        let a = con.args[0]
        let b = con.args[1]
        for operand in [a, b]:
            if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
                 operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
                 operand.ident notin tr.paramValues:
                return false
        tr.definedVarExprs[definedName] = binaryMax(tr.resolveExprArg(a), tr.resolveExprArg(b))
        return true

    if name == "int_min":
        # int_min(a, b, c) :: defines_var(c) → c = min(a, b)
        let a = con.args[0]
        let b = con.args[1]
        for operand in [a, b]:
            if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
                 operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
                 operand.ident notin tr.paramValues:
                return false
        tr.definedVarExprs[definedName] = binaryMin(tr.resolveExprArg(a), tr.resolveExprArg(b))
        return true

    if name == "int_times":
        # int_times(a, b, c) :: defines_var(c) → c = a * b
        let a = con.args[0]
        let b = con.args[1]
        for operand in [a, b]:
            if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
                 operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
                 operand.ident notin tr.paramValues:
                return false
        tr.definedVarExprs[definedName] = tr.resolveExprArg(a) * tr.resolveExprArg(b)
        return true

    let coeffs = tr.resolveIntArray(con.args[0])
    let rhs = tr.resolveIntArg(con.args[2])
    let varElems = tr.resolveVarArrayElems(con.args[1])

    if varElems.len == 0:
        return true  # can't process, skip

    # Find the defined variable's position in the constraint
    var definedIdx = -1
    for vi, v in varElems:
        if v.kind == FznIdent and v.ident == definedName:
            definedIdx = vi
            break

    if definedIdx < 0:
        return true  # can't process, skip

    # Check if all dependencies are available before building
    for vi, v in varElems:
        if vi == definedIdx:
            continue
        if v.kind == FznIdent and v.ident in tr.definedVarNames and
             v.ident notin tr.definedVarExprs and v.ident notin tr.varPositions and
             v.ident notin tr.paramValues:
            return false  # dependency not yet built

    let defCoeff = coeffs[definedIdx]
    # Constraint: defCoeff * defined + sum(other_coeffs * other_vars) = rhs
    # defined = (rhs - sum(other_coeffs * other_vars)) / defCoeff
    # For defCoeff = 1: defined = rhs - sum(other_coeffs * other_vars)
    # For defCoeff = -1: defined = sum(other_coeffs * other_vars) - rhs

    # Build expression: start with the constant term (rhs / defCoeff)
    var expr: AlgebraicExpression[int]
    let sign = if defCoeff == 1: -1 else: 1  # negate other coefficients

    var first = true
    for vi, v in varElems:
        if vi == definedIdx:
            continue
        let otherExpr = tr.resolveExprArg(v)
        let scaledCoeff = sign * coeffs[vi]
        let term = scaledCoeff * otherExpr
        if first:
            expr = term
            first = false
        else:
            expr = expr + term

    # Add constant term: sign * (-rhs) = rhs/defCoeff for the constant part
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

    if expr.isNil:
        raise newException(ValueError, &"Failed to build expression for defined variable '{definedName}'")
    tr.definedVarExprs[definedName] = expr
    return true

proc detectImplicitMaxChannels(tr: var FznTranslator) =
    ## Detects array_int_maximum/minimum constraints WITHOUT defines_var that can be treated
    ## as channel variables. This handles cases like the Unison model where le[v] = max(use_cycles)
    ## is emitted without a defines_var annotation.
    ##
    ## Eligibility criteria for variable m in `array_int_maximum(m, arr)`:
    ##   1. m is not already in definedVarNames or channelVarNames or paramValues
    ##   2. m appears as LHS (args[0]) in exactly one array_int_maximum/minimum constraint
    ##   3. m does not appear as an input in any other constraint

    let targetNames = ["array_int_maximum", "array_int_minimum"]

    # Step 1: collect all candidate LHS variables from array_int_max/min without defines_var
    # and count how many times each appears as LHS
    var lhsCount: Table[string, int]     # varName -> # times it is LHS of array_int_max/min
    var lhsCi: Table[string, int]        # varName -> constraint index of (single) LHS occurrence
    var lhsIsMin: Table[string, bool]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name notin targetNames: continue
        if con.hasAnnotation("defines_var"): continue
        if con.args.len < 2: continue
        if con.args[0].kind != FznIdent: continue
        let mName = con.args[0].ident
        lhsCount[mName] = lhsCount.getOrDefault(mName, 0) + 1
        lhsCi[mName] = ci
        lhsIsMin[mName] = (name == "array_int_minimum")

    if lhsCount.len == 0:
        return

    # Step 2: filter candidates and register eligible ones as min/max channels.
    # A variable is eligible if it is defined by exactly one array_int_max/min constraint
    # and is not already defined/channeled elsewhere. It is fine for m to appear as an
    # input to other constraints (cumulative, nooverlap, etc.) — that is normal use.
    var nDetected = 0
    for mName, count in lhsCount:
        if count != 1: continue  # ambiguous: multiple max/min constraints define this var
        if mName in tr.definedVarNames: continue
        if mName in tr.channelVarNames: continue
        if mName in tr.paramValues: continue
        let ci = lhsCi[mName]
        let isMin = lhsIsMin[mName]
        tr.channelVarNames.incl(mName)
        tr.definingConstraints.incl(ci)
        tr.minMaxChannelDefs.add((ci: ci, varName: mName, isMin: isMin))
        inc nDetected

    if nDetected > 0:
        stderr.writeLine(&"[FZN] Detected {nDetected} implicit min/max channel variables (array_int_max/min without defines_var)")

proc buildDefinedExpressions(tr: var FznTranslator) =
    ## Second pass: build AlgebraicExpressions for defined variables using the positions
    ## of non-defined variables that are already created.
    ## Uses multiple passes to handle dependencies between defined variables.
    var remaining: seq[int]
    for ci in tr.definingConstraints.items:
        remaining.add(ci)

    var maxPasses = remaining.len + 1
    while remaining.len > 0 and maxPasses > 0:
        var nextRemaining: seq[int]
        for ci in remaining:
            if not tr.tryBuildDefinedExpression(ci):
                nextRemaining.add(ci)
        if nextRemaining.len == remaining.len:
            # No progress - break to avoid infinite loop
            for ci in nextRemaining:
                discard tr.tryBuildDefinedExpression(ci)  # will raise on error
            break
        remaining = nextRemaining
        dec maxPasses
