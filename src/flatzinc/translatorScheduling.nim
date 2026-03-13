## Included from translator.nim -- not a standalone module.

proc extractLinLeReifTerm(tr: FznTranslator, reifCi: int):
    tuple[ok: bool, term: DisjunctiveClauseTerm] =
    ## Extract coefficients, variable names, and RHS from int_lin_le_reif constraint.
    let reifCon = tr.model.constraints[reifCi]
    let coeffs = try: tr.resolveIntArray(reifCon.args[0]) except ValueError, KeyError: return
    let rhs = try: tr.resolveIntArg(reifCon.args[2]) except ValueError, KeyError: return
    let varArr = reifCon.args[1]
    var varNames: seq[string]
    case varArr.kind
    of FznArrayLit:
        for e in varArr.elems:
            if e.kind == FznIdent:
                varNames.add(e.ident)
            else:
                return
    of FznIdent:
        if varArr.ident in tr.arrayElementNames:
            varNames = tr.arrayElementNames[varArr.ident]
        else:
            return
    else: return
    if varNames.len != coeffs.len: return
    result = (ok: true, term: DisjunctiveClauseTerm(coeffs: coeffs, varNames: varNames, rhs: rhs))

proc detectDisjunctivePairs(tr: var FznTranslator) =
    ## Detects disjunctive pair patterns:
    ##   int_lin_le_reif(coeffs1, vars1, rhs1, b1) :: defines_var(b1)
    ##   int_lin_le_reif(coeffs2, vars2, rhs2, b2) :: defines_var(b2)
    ##   bool_clause([b1, b2], [])
    ## Where b1, b2 are bool variables only used in this one clause.
    ## Replaces all 3 constraints + 2 bool variables with:
    ##   min(max(0, expr1), max(0, expr2)) == 0
    ## where expr_i = scalar_product(coeffs_i, vars_i) - rhs_i.
    ##
    ## Also detects generalized disjunctive clauses:
    ##   Pattern A: bool_clause([b1, b2, b3], []) — 3 literals from int_lin_le_reif
    ##   Pattern B: bool_clause([a, d], []) where d = array_bool_and([b, c]) and a,b,c from int_lin_le_reif
    ##   Pattern C: bool_clause([d1, d2, ...], []) where all di = array_bool_and(inputs from int_lin_le_reif)

    # Step 1: Build mapping from result var name → constraint index for
    # all int_lin_le_reif with defines_var annotation
    var linLeReifDefines: Table[string, int]  # result var name → constraint index
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le_reif": continue
        if con.args.len < 4: continue
        if not con.hasAnnotation("defines_var"): continue
        let resultArg = con.args[3]
        if resultArg.kind != FznIdent: continue
        linLeReifDefines[resultArg.ident] = ci

    if linLeReifDefines.len == 0: return

    # Step 1b: Build mapping from result var name → (constraint index, input var names)
    # for all array_bool_and with defines_var annotation
    var arrayBoolAndDefines: Table[string, tuple[ci: int, inputs: seq[string]]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_and": continue
        if con.args.len < 2: continue
        if not con.hasAnnotation("defines_var"): continue
        let resultArg = con.args[1]
        if resultArg.kind != FznIdent: continue
        var inputs: seq[string]
        let inputArr = con.args[0]
        if inputArr.kind != FznArrayLit: continue
        var allIdents = true
        for elem in inputArr.elems:
            if elem.kind != FznIdent:
                allIdents = false
                break
            inputs.add(elem.ident)
        if allIdents and inputs.len > 0:
            arrayBoolAndDefines[resultArg.ident] = (ci: ci, inputs: inputs)

    # Step 2: Count references to each bool var in non-defining constraints.
    # Count references in bool_clause, array_bool_and/array_bool_or, bool2int, bool_not, bool_clause_reif.
    var varRefCount: Table[string, int]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        case name
        of "bool_clause":
            if con.args.len < 2: continue
            for argIdx in 0..1:
                let arr = con.args[argIdx]
                if arr.kind != FznArrayLit: continue
                for elem in arr.elems:
                    if elem.kind == FznIdent:
                        varRefCount.mgetOrPut(elem.ident, 0) += 1
        of "array_bool_and", "array_bool_or":
            if con.args.len < 1: continue
            let inputArr = con.args[0]
            if inputArr.kind != FznArrayLit: continue
            for elem in inputArr.elems:
                if elem.kind == FznIdent:
                    varRefCount.mgetOrPut(elem.ident, 0) += 1
        of "bool2int":
            # bool2int(boolVar, intVar) — boolVar is referenced
            if con.args.len >= 1 and con.args[0].kind == FznIdent:
                varRefCount.mgetOrPut(con.args[0].ident, 0) += 1
        of "bool_not":
            # bool_not(a, b) — both a and b are referenced
            for argIdx in 0..1:
                if con.args.len > argIdx and con.args[argIdx].kind == FznIdent:
                    varRefCount.mgetOrPut(con.args[argIdx].ident, 0) += 1
        of "bool_clause_reif":
            if con.args.len < 3: continue
            for argIdx in 0..1:
                let arr = con.args[argIdx]
                if arr.kind != FznArrayLit: continue
                for elem in arr.elems:
                    if elem.kind == FznIdent:
                        varRefCount.mgetOrPut(elem.ident, 0) += 1
            if con.args[2].kind == FznIdent:
                varRefCount.mgetOrPut(con.args[2].ident, 0) += 1
        else: discard

    # Step 3: Scan bool_clause constraints for disjunctive patterns.
    # A bool var from int_lin_le_reif with refcount=1 can be fully consumed.
    # A bool var with refcount=2 can still be consumed if BOTH its references
    # are in bool_clause constraints we'll consume (shared var between Pattern A and B).
    # For shared vars, we don't eliminate the var or its defining constraint — it becomes
    # a channel — but we still emit the algebraic constraint using the underlying vars.
    var nPairConsumed = 0
    var nTautological = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len != 0: continue

        if posArg.elems.len == 2:
            # Original 2-literal pattern: bool_clause([b1, b2], [])
            let b1 = posArg.elems[0]
            let b2 = posArg.elems[1]
            if b1.kind != FznIdent or b2.kind != FznIdent: continue
            # Check both are defined by int_lin_le_reif
            if b1.ident notin linLeReifDefines or b2.ident notin linLeReifDefines: continue
            # Check both are only used in this one clause
            if varRefCount.getOrDefault(b1.ident) != 1 or varRefCount.getOrDefault(b2.ident) != 1: continue

            let (ok1, term1) = tr.extractLinLeReifTerm(linLeReifDefines[b1.ident])
            let (ok2, term2) = tr.extractLinLeReifTerm(linLeReifDefines[b2.ident])
            if not ok1 or not ok2: continue

            # Check for tautological pair: the two linear expressions are negations of each other.
            # E.g., x-y <= 0 OR y-x <= 0 is always true for integers.
            var isTautology = false
            if term1.varNames.len == term2.varNames.len:
                # Check pattern 1: same coefficients, reversed variables
                var sameCoeffs = true
                var varsReversed = true
                for k in 0..<term1.coeffs.len:
                    if term2.coeffs[k] != term1.coeffs[k]:
                        sameCoeffs = false
                        break
                for k in 0..<term1.varNames.len:
                    if term2.varNames[k] != term1.varNames[term1.varNames.len - 1 - k]:
                        varsReversed = false
                        break
                if sameCoeffs and varsReversed and term1.rhs + term2.rhs >= 0:
                    isTautology = true

                # Check pattern 2: negated coefficients, same variables
                if not isTautology:
                    var negCoeffs = true
                    var sameVars = true
                    for k in 0..<term1.coeffs.len:
                        if term2.coeffs[k] != -term1.coeffs[k]:
                            negCoeffs = false
                            break
                    for k in 0..<term1.varNames.len:
                        if term2.varNames[k] != term1.varNames[k]:
                            sameVars = false
                            break
                    if negCoeffs and sameVars and term1.rhs + term2.rhs >= 0:
                        isTautology = true

            # Consume all 3 constraints and both bool variables
            tr.definingConstraints.incl(ci)
            tr.definingConstraints.incl(linLeReifDefines[b1.ident])
            tr.definingConstraints.incl(linLeReifDefines[b2.ident])
            tr.definedVarNames.incl(b1.ident)
            tr.definedVarNames.incl(b2.ident)

            if isTautology:
                nTautological += 1
                nPairConsumed += 3
                continue

            tr.disjunctivePairs.add((
                coeffs1: term1.coeffs, varNames1: term1.varNames, rhs1: term1.rhs,
                coeffs2: term2.coeffs, varNames2: term2.varNames, rhs2: term2.rhs))
            nPairConsumed += 3

        elif posArg.elems.len == 3:
            # Pattern A: bool_clause([b1, b2, b3], []) — 3 literals from int_lin_le_reif
            var allIdent = true
            for e in posArg.elems:
                if e.kind != FznIdent:
                    allIdent = false
                    break
            if not allIdent: continue
            let b1 = posArg.elems[0].ident
            let b2 = posArg.elems[1].ident
            let b3 = posArg.elems[2].ident
            # Check all three are defined by int_lin_le_reif
            if b1 notin linLeReifDefines or b2 notin linLeReifDefines or b3 notin linLeReifDefines: continue
            # Allow refcount <= 2: vars with refcount=2 are shared between Pattern A and B
            # and will be consumed by both. Don't eliminate shared vars (they become channels).
            if varRefCount.getOrDefault(b1) > 2 or varRefCount.getOrDefault(b2) > 2 or varRefCount.getOrDefault(b3) > 2: continue

            let (ok1, term1) = tr.extractLinLeReifTerm(linLeReifDefines[b1])
            let (ok2, term2) = tr.extractLinLeReifTerm(linLeReifDefines[b2])
            let (ok3, term3) = tr.extractLinLeReifTerm(linLeReifDefines[b3])
            if not ok1 or not ok2 or not ok3: continue

            # Consume the bool_clause and int_lin_le_reif constraints.
            # For shared vars (refcount=2), keep the defining constraint and var alive.
            tr.definingConstraints.incl(ci)
            for bIdent in [b1, b2, b3]:
                if varRefCount.getOrDefault(bIdent) == 1:
                    tr.definingConstraints.incl(linLeReifDefines[bIdent])
                    tr.definedVarNames.incl(bIdent)

            tr.disjunctiveClauses.add(DisjunctiveClause(
                disjuncts: @[@[term1], @[term2], @[term3]]))

    if nTautological > 0:
        stderr.writeLine(&"[FZN] Skipped {nTautological} tautological disjunctive pairs")
    if tr.disjunctivePairs.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.disjunctivePairs.len} disjunctive pairs, " &
                                          &"{nPairConsumed} constraints consumed, " &
                                          &"{tr.disjunctivePairs.len * 2} bool variables eliminated")

    # Step 4: Scan bool_clause for Pattern B: bool_clause([a, d], [])
    # where a is from int_lin_le_reif and d is from array_bool_and([b, c, ...])
    # with all inputs from int_lin_le_reif
    var nPatternB = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len != 0: continue
        if posArg.elems.len != 2: continue
        let e0 = posArg.elems[0]
        let e1 = posArg.elems[1]
        if e0.kind != FznIdent or e1.kind != FznIdent: continue

        # Try both orderings: (a=reif, d=and) or (d=and, a=reif)
        var reifIdent, andIdent: string
        if e0.ident in linLeReifDefines and e1.ident in arrayBoolAndDefines:
            reifIdent = e0.ident
            andIdent = e1.ident
        elif e1.ident in linLeReifDefines and e0.ident in arrayBoolAndDefines:
            reifIdent = e1.ident
            andIdent = e0.ident
        else:
            continue

        # Allow refcount <= 2 for reif var (may be shared with Pattern A clause)
        if varRefCount.getOrDefault(reifIdent) > 2: continue
        if varRefCount.getOrDefault(andIdent) != 1: continue

        let andInfo = arrayBoolAndDefines[andIdent]
        # Check all inputs of array_bool_and are from int_lin_le_reif with refcount 1
        var allInputsValid = true
        for inp in andInfo.inputs:
            if inp notin linLeReifDefines or varRefCount.getOrDefault(inp) != 1:
                allInputsValid = false
                break
        if not allInputsValid: continue

        # Extract terms
        let (okA, termA) = tr.extractLinLeReifTerm(linLeReifDefines[reifIdent])
        if not okA: continue
        var conjTerms: seq[DisjunctiveClauseTerm]
        var allOk = true
        for inp in andInfo.inputs:
            let (okInp, termInp) = tr.extractLinLeReifTerm(linLeReifDefines[inp])
            if not okInp:
                allOk = false
                break
            conjTerms.add(termInp)
        if not allOk: continue

        # Consume: 1 bool_clause + 1 array_bool_and + int_lin_le_reif constraints
        tr.definingConstraints.incl(ci)            # bool_clause
        tr.definingConstraints.incl(andInfo.ci)    # array_bool_and
        tr.definedVarNames.incl(andIdent)
        # For reif var: only consume if refcount=1 (not shared with Pattern A)
        if varRefCount.getOrDefault(reifIdent) == 1:
            tr.definingConstraints.incl(linLeReifDefines[reifIdent])
            tr.definedVarNames.incl(reifIdent)
        for inp in andInfo.inputs:
            tr.definingConstraints.incl(linLeReifDefines[inp])
            tr.definedVarNames.incl(inp)

        tr.disjunctiveClauses.add(DisjunctiveClause(
            disjuncts: @[@[termA], conjTerms]))
        nPatternB += 1

    # Step 5: Scan bool_clause for Pattern C: bool_clause([d1, d2, ...], [])
    # where ALL positive literals are from array_bool_and, each with inputs from int_lin_le_reif.
    # This handles double-track FIFO patterns: each disjunct is a conjunction of linear inequalities.
    var nPatternC = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len != 0: continue
        if posArg.elems.len < 2: continue

        # Check ALL positive literals are array_bool_and with int_lin_le_reif inputs
        var allAndReif = true
        var disjuncts: seq[seq[DisjunctiveClauseTerm]]
        var allBoolVars: seq[string]  # Track all bool vars to consume
        for elem in posArg.elems:
            if elem.kind != FznIdent:
                allAndReif = false; break
            let ident = elem.ident
            if ident notin arrayBoolAndDefines:
                allAndReif = false; break
            if varRefCount.getOrDefault(ident) != 1:
                allAndReif = false; break
            let andInfo = arrayBoolAndDefines[ident]
            var terms: seq[DisjunctiveClauseTerm]
            var inputsOk = true
            for inp in andInfo.inputs:
                if inp notin linLeReifDefines or varRefCount.getOrDefault(inp) != 1:
                    inputsOk = false; break
                let (ok, term) = tr.extractLinLeReifTerm(linLeReifDefines[inp])
                if not ok:
                    inputsOk = false; break
                terms.add(term)
            if not inputsOk:
                allAndReif = false; break
            disjuncts.add(terms)
            allBoolVars.add(ident)
            for inp in andInfo.inputs:
                allBoolVars.add(inp)
        if not allAndReif or disjuncts.len < 2: continue

        # Consume bool_clause + all array_bool_and + all int_lin_le_reif constraints and bool vars
        tr.definingConstraints.incl(ci)
        for elem in posArg.elems:
            let andInfo = arrayBoolAndDefines[elem.ident]
            tr.definingConstraints.incl(andInfo.ci)
            tr.definedVarNames.incl(elem.ident)
            for inp in andInfo.inputs:
                tr.definingConstraints.incl(linLeReifDefines[inp])
                tr.definedVarNames.incl(inp)

        tr.disjunctiveClauses.add(DisjunctiveClause(disjuncts: disjuncts))
        nPatternC += 1

    if tr.disjunctiveClauses.len > 0:
        let nPatternA = tr.disjunctiveClauses.len - nPatternB - nPatternC
        stderr.writeLine(&"[FZN] Detected {tr.disjunctiveClauses.len} generalized disjunctive clauses " &
                                          &"({nPatternA} 3-way, {nPatternB} AND-of-reif, {nPatternC} AND-vs-AND)")


proc referencesIdent(expr: FznExpr, name: string): bool =
    ## Check if a FznExpr tree references a given identifier name.
    case expr.kind
    of FznIdent: return expr.ident == name
    of FznArrayLit:
        for e in expr.elems:
            if referencesIdent(e, name): return true
    else: discard
    return false

proc detectSmallDomainProducts(tr: var FznTranslator) =
    ## Detects int_times(a, b, prod) :: defines_var(prod) where one operand has
    ## a small domain (≤8 values), and ALL non-defining references to prod are in
    ## int_lin_le constraints. Decomposes into DisjunctiveClause with |smallDomain|
    ## disjuncts (case-splitting on each value of the small operand).
    ## Also emits synthetic relaxation constraints for bounds propagation.
    const MaxSmallDomainSize = 8

    # Step 1: Find all int_times defining constraints with a small-domain operand
    type ProductInfo = tuple[timesCi: int, smallVar, largeVar, prodVar: string, smallDomain: seq[int]]
    var products: seq[ProductInfo]

    for ci in tr.definingConstraints.items:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_times": continue
        if con.args.len < 3: continue
        if con.args[2].kind != FznIdent: continue
        let prodName = con.args[2].ident
        if prodName notin tr.definedVarNames: continue
        if prodName in tr.channelVarNames: continue  # defensive
        for (si, li) in [(0, 1), (1, 0)]:
            let sArg = con.args[si]
            let lArg = con.args[li]
            if sArg.kind != FznIdent or lArg.kind != FznIdent: continue
            let dom = tr.lookupVarDomain(sArg.ident)
            if dom.len >= 2 and dom.len <= MaxSmallDomainSize:
                products.add((timesCi: ci, smallVar: sArg.ident,
                              largeVar: lArg.ident, prodVar: prodName, smallDomain: dom))
                break

    if products.len == 0: return

    # Step 2: For each product, find ALL non-defining constraints referencing it
    var consumedLinLe = initPackedSet[int]()
    var nDecomposed = 0
    var nLinLeConsumed = 0
    for product in products:
        var linLeCIs: seq[int]
        var allLinLe = true
        for ci, con in tr.model.constraints:
            if ci in tr.definingConstraints: continue
            if ci in consumedLinLe: continue
            var refsProd = false
            for arg in con.args:
                if referencesIdent(arg, product.prodVar):
                    refsProd = true; break
            if not refsProd: continue
            let cname = stripSolverPrefix(con.name)
            if cname != "int_lin_le":
                allLinLe = false; break
            linLeCIs.add(ci)
        if not allLinLe or linLeCIs.len == 0: continue

        # Step 3: Build DisjunctiveClause with |smallDomain| disjuncts
        var disjuncts: seq[seq[DisjunctiveClauseTerm]]

        for k in product.smallDomain:
            var terms: seq[DisjunctiveClauseTerm]
            # B[i] == k: encoded as two inequality terms (smallVar <= k AND smallVar >= k)
            terms.add(DisjunctiveClauseTerm(coeffs: @[1], varNames: @[product.smallVar], rhs: k))
            terms.add(DisjunctiveClauseTerm(coeffs: @[-1], varNames: @[product.smallVar], rhs: -k))

            for lci in linLeCIs:
                let con = tr.model.constraints[lci]
                let coeffs = tr.resolveIntArray(con.args[0])
                let rhs = tr.resolveIntArg(con.args[2])
                var varNames: seq[string]
                let varArr = con.args[1]
                var varExtractOk = true
                if varArr.kind == FznArrayLit:
                    for elem in varArr.elems:
                        if elem.kind != FznIdent:
                            varExtractOk = false
                            break
                        varNames.add(elem.ident)
                elif varArr.kind == FznIdent and varArr.ident in tr.arrayElementNames:
                    varNames = tr.arrayElementNames[varArr.ident]
                else:
                    varExtractOk = false
                if not varExtractOk: continue

                # Substitute prod = k * largeVar
                var newCoeffs: seq[int]
                var newVarNames: seq[string]
                var largeCoeff = 0
                var prodCoeff = 0
                for vi in 0..<coeffs.len:
                    if varNames[vi] == product.prodVar:
                        prodCoeff = coeffs[vi]
                        largeCoeff += coeffs[vi] * k
                    elif varNames[vi] == product.largeVar:
                        largeCoeff += coeffs[vi]
                    else:
                        newCoeffs.add(coeffs[vi])
                        newVarNames.add(varNames[vi])
                if largeCoeff != 0:
                    newCoeffs.add(largeCoeff)
                    newVarNames.add(product.largeVar)
                terms.add(DisjunctiveClauseTerm(coeffs: newCoeffs, varNames: newVarNames, rhs: rhs))

                # Synthetic relaxation: for positive prodCoeff (upper-bound on product),
                # dropping prod >= 0 is a valid relaxation.
                # Emit once per int_lin_le (relaxation is the same for all k values);
                # k == smallDomain[0] serves as a "first iteration" guard.
                if k == product.smallDomain[0] and prodCoeff > 0:
                    var synCoeffs: seq[int]
                    var synVarNames: seq[string]
                    for vi in 0..<coeffs.len:
                        if varNames[vi] != product.prodVar:
                            synCoeffs.add(coeffs[vi])
                            synVarNames.add(varNames[vi])
                    if synCoeffs.len > 0:
                        tr.syntheticRelaxations.add(DisjunctiveClauseTerm(
                            coeffs: synCoeffs, varNames: synVarNames, rhs: rhs))

            disjuncts.add(terms)

        for lci in linLeCIs:
            tr.definingConstraints.incl(lci)
            consumedLinLe.incl(lci)
        tr.disjunctiveClauses.add(DisjunctiveClause(disjuncts: disjuncts))
        nDecomposed += 1
        nLinLeConsumed += linLeCIs.len

    if nDecomposed > 0:
        stderr.writeLine(&"[FZN] Decomposed {nDecomposed} small-domain products " &
                          &"({nLinLeConsumed} int_lin_le consumed)")


proc detectDisjunctiveResources(tr: var FznTranslator) =
    ## Detects disjunctive resource groups among disjunctive pairs and replaces
    ## them with cumulative(limit=1) constraints.
    ## A disjunctive resource is a complete subgraph (clique) of pairwise
    ## disjunctive constraints where all tasks on the same resource have
    ## consistent durations.
    if tr.disjunctivePairs.len == 0:
        return

    # Step 1: Extract 2-variable disjunctive pairs with [1,-1]/[-1,1] coefficients
    # These represent: either (a - b <= -durA) or (b - a <= -durB),
    # meaning tasks don't overlap on the same resource.
    type PairInfo = object
        pairIdx: int
        posA, posB: string  # Variable names (posA < posB for canonical ordering)
        durA, durB: int     # Duration of A (when A before B), duration of B (when B before A)

    var validPairs: seq[PairInfo]
    for idx, pair in tr.disjunctivePairs:
        # Only handle simple 2-variable pairs
        if pair.varNames1.len != 2 or pair.varNames2.len != 2:
            continue
        # Check coefficient pattern: [1,-1] or [-1,1]
        var varA1, varB1, varA2, varB2: string
        var durFromDisj1, durFromDisj2: int

        # Disjunct 1: coeffs1·vars1 <= rhs1
        if pair.coeffs1 == @[1, -1]:
            # a - b <= rhs1 → a + (-rhs1) <= b → if a before b, a needs duration -rhs1
            varA1 = pair.varNames1[0]
            varB1 = pair.varNames1[1]
            durFromDisj1 = -pair.rhs1  # duration of A in "A before B" interpretation
        elif pair.coeffs1 == @[-1, 1]:
            # -a + b <= rhs1 → b - a <= rhs1 → b + (-rhs1) <= a → if b before a, b needs duration -rhs1
            varA1 = pair.varNames1[1]
            varB1 = pair.varNames1[0]
            durFromDisj1 = -pair.rhs1
        else:
            continue

        # Disjunct 2: coeffs2·vars2 <= rhs2
        if pair.coeffs2 == @[1, -1]:
            varA2 = pair.varNames2[0]
            varB2 = pair.varNames2[1]
            durFromDisj2 = -pair.rhs2
        elif pair.coeffs2 == @[-1, 1]:
            varA2 = pair.varNames2[1]
            varB2 = pair.varNames2[0]
            durFromDisj2 = -pair.rhs2
        else:
            continue

        # The two disjuncts should involve the same pair of variables
        # but in opposite directions:
        # disjunct 1: A + durA <= B (A before B)
        # disjunct 2: B + durB <= A (B before A)
        if varA1 == varA2 and varB1 == varB2:
            # Same direction — not a proper disjunctive pair for our purposes
            # Actually this means: (A+dur1<=B) or (A+dur2<=B) — skip
            continue
        elif varA1 == varB2 and varB1 == varA2:
            # disjunct1: A1+dur1<=B1, disjunct2: A2+dur2<=B2 where A1=B2, B1=A2
            # So: A+durA<=B or B+durB<=A — correct pattern
            validPairs.add(PairInfo(
                pairIdx: idx,
                posA: varA1, posB: varB1,
                durA: durFromDisj1, durB: durFromDisj2))
        else:
            continue

    if validPairs.len == 0:
        return

    # Step 2: Build adjacency and validate duration consistency
    # Each position (variable name) should have a consistent duration across all pairs.
    # Variables with inconsistent durations are excluded; remaining consistent pairs are kept.
    var varDuration: Table[string, int]  # var → its duration
    var inconsistentVars: HashSet[string]

    # First pass: detect duration inconsistencies
    for pi in validPairs:
        if pi.posA in varDuration:
            if varDuration[pi.posA] != pi.durA:
                inconsistentVars.incl(pi.posA)
        else:
            varDuration[pi.posA] = pi.durA
        if pi.posB in varDuration:
            if varDuration[pi.posB] != pi.durB:
                inconsistentVars.incl(pi.posB)
        else:
            varDuration[pi.posB] = pi.durB

    # Second pass: build adjacency from consistent pairs only
    var adjacency: Table[string, Table[string, int]]  # var → {partner → pairIdx}
    for pi in validPairs:
        if pi.posA in inconsistentVars or pi.posB in inconsistentVars:
            continue
        if pi.posA notin adjacency:
            adjacency[pi.posA] = initTable[string, int]()
        adjacency[pi.posA][pi.posB] = pi.pairIdx

        if pi.posB notin adjacency:
            adjacency[pi.posB] = initTable[string, int]()
        adjacency[pi.posB][pi.posA] = pi.pairIdx

    if adjacency.len == 0:
        return

    # Step 3: Find cliques by greedy detection
    var assigned: HashSet[string]  # Variables already assigned to a resource group
    type ResourceGroup = object
        members: seq[string]
        pairIndices: seq[int]

    var groups: seq[ResourceGroup]

    # Sort variables by degree (highest first) for better clique detection
    var varsByDegree: seq[(int, string)]
    for v, partners in adjacency:
        varsByDegree.add((partners.len, v))
    varsByDegree.sort(proc(a, b: (int, string)): int = -cmp(a[0], b[0]))

    for (_, startVar) in varsByDegree:
        if startVar in assigned:
            continue

        # Try to build a clique starting from startVar
        var clique = @[startVar]
        # Candidates: all partners of startVar not yet assigned
        var candidates: seq[string]
        for partner in adjacency[startVar].keys:
            if partner notin assigned:
                candidates.add(partner)

        # Greedily add candidates that are connected to all current clique members
        for candidate in candidates:
            var connectedToAll = true
            for member in clique:
                if member == candidate:
                    connectedToAll = false
                    break
                if candidate notin adjacency.getOrDefault(member):
                    connectedToAll = false
                    break
            if connectedToAll:
                clique.add(candidate)

        if clique.len < 2:
            continue

        # Verify it's a complete subgraph and collect pair indices
        var pairIndices: seq[int]
        var isComplete = true
        for i in 0..<clique.len:
            for j in (i+1)..<clique.len:
                if clique[j] notin adjacency.getOrDefault(clique[i]):
                    isComplete = false
                    break
                pairIndices.add(adjacency[clique[i]][clique[j]])
            if not isComplete:
                break

        if not isComplete:
            continue

        for member in clique:
            assigned.incl(member)
        groups.add(ResourceGroup(members: clique, pairIndices: pairIndices))

    if groups.len == 0:
        return

    # Step 4: Mark consumed pairs and create cumulative constraints
    var totalConsumed = 0
    var totalTasks = 0

    for group in groups:
        for pidx in group.pairIndices:
            tr.consumedDisjunctivePairs.incl(pidx)
            inc totalConsumed

        totalTasks += group.members.len

        # Collect positions and durations for cumulative constraint
        # We store var names here; positions will be resolved during constraint emission
        # (after translateVariables has run)
        var memberNames = group.members
        var durations: seq[int]
        for m in memberNames:
            durations.add(varDuration[m])

        # Store for later emission (positions aren't resolved yet)
        tr.disjunctiveResourceGroups.add((varNames: memberNames, durations: durations))

    stderr.writeLine(&"[FZN] Detected {groups.len} disjunctive resource groups ({totalTasks} tasks total), " &
                                      &"{totalConsumed} pairs consumed -> {groups.len} cumulative constraints")


proc detectNoOverlapPatterns(tr: var FznTranslator) =
    ## Detects 6-literal bool_clause patterns encoding 3D box non-overlap:
    ##   bool_clause([b1,b2,b3,b4,b5,b6], [])
    ## where each bi is defined by int_le_reif, and the 6 comparisons form
    ## 3 pairs (one per dimension) checking separation between a variable
    ## pipe leg box and a fixed obstacle box.
    ##
    ## Chain: bool_clause → int_le_reif → int_lin_eq → int_min/int_max → node endpoints
    ##
    ## Replaces 7 constraints (1 bool_clause + 6 int_le_reif) + chain intermediates
    ## with a single NoOverlapFixedBox constraint.

    # Step 1: Build reverse indices
    # Note: leReifDefs only includes unconsumed int_le_reif constraints,
    # but linEqDefs and minMaxDefs include ALL constraints (even already consumed ones)
    # because we need them for tracing the chain through defined variables and channels.
    var leReifDefs: Table[string, int]   # bool var name → int_le_reif constraint index
    var linEqDefs: Table[string, int]    # defined var name → int_lin_eq constraint index
    var minMaxDefs: Table[string, int]   # channel var name → int_min/int_max constraint index

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        let defVar = ann.args[0].ident
        case name
        of "int_le_reif":
            # Only include unconsumed int_le_reif
            if ci notin tr.definingConstraints and con.args.len >= 3 and con.args[2].kind == FznIdent:
                leReifDefs[defVar] = ci
        of "int_lin_eq":
            linEqDefs[defVar] = ci
        of "int_min", "int_max":
            minMaxDefs[defVar] = ci
        else: discard

    if leReifDefs.len == 0: return

    type
        LegTrace = object
            ## Result of tracing a leg variable chain
            epA: NoOverlapEndpoint  # first endpoint of min/max
            epB: NoOverlapEndpoint  # second endpoint of min/max
            isMin: bool             # true for int_min (leg lower), false for int_max (leg upper)
            offset: int             # offset from int_lin_eq (typically -radius or +radius)
            innerVar: string        # the int_min/int_max output variable
            linEqCi: int            # constraint index of int_lin_eq
            minMaxCi: int           # constraint index of int_min/int_max

    proc traceLeg(tr: FznTranslator, legVarName: string): tuple[ok: bool, trace: LegTrace] =
        ## Trace a leg variable: legVar → int_lin_eq → int_min/int_max → endpoints
        if legVarName notin linEqDefs:
            return (false, LegTrace())

        let linCi = linEqDefs[legVarName]
        let linCon = tr.model.constraints[linCi]

        # Parse int_lin_eq(coeffs, vars, rhs)
        let coeffsArg = linCon.args[0]
        let varsArg = linCon.args[1]
        let rhsArg = linCon.args[2]

        var coeffs: seq[int]
        try:
            coeffs = tr.resolveIntArray(coeffsArg)
        except ValueError, KeyError:
            return (false, LegTrace())

        var rhs: int
        try:
            rhs = tr.resolveIntArg(rhsArg)
        except ValueError, KeyError:
            return (false, LegTrace())

        # Resolve variable names
        var varNames: seq[string]
        case varsArg.kind
        of FznArrayLit:
            for e in varsArg.elems:
                if e.kind == FznIdent:
                    varNames.add(e.ident)
                else:
                    return (false, LegTrace())
        of FznIdent:
            if varsArg.ident in tr.arrayElementNames:
                varNames = tr.arrayElementNames[varsArg.ident]
            else:
                return (false, LegTrace())
        else:
            return (false, LegTrace())

        if varNames.len != coeffs.len or varNames.len != 2:
            return (false, LegTrace())

        # Find which var is the leg var and which is the inner (min/max output)
        var innerIdx = -1
        var legIdx = -1
        for i in 0..<2:
            if varNames[i] == legVarName:
                legIdx = i
            else:
                innerIdx = i
        if innerIdx < 0 or legIdx < 0:
            return (false, LegTrace())

        let innerVarName = varNames[innerIdx]
        let legCoeff = coeffs[legIdx]
        let innerCoeff = coeffs[innerIdx]

        # Expect coeffs like [1, -1]: legCoeff*legVar + innerCoeff*innerVar = rhs
        # => legVar = (rhs - innerCoeff*innerVar) / legCoeff
        # For [1,-1],[legVar,innerVar],rhs: legVar - innerVar = rhs => legVar = innerVar + rhs
        # Only accept the standard form: legCoeff=1, innerCoeff=-1 or legCoeff=-1, innerCoeff=1
        if not ((legCoeff == 1 and innerCoeff == -1) or (legCoeff == -1 and innerCoeff == 1)):
            return (false, LegTrace())

        # legCoeff=1, innerCoeff=-1: leg - inner = rhs → leg = inner + rhs → offset = rhs
        # legCoeff=-1, innerCoeff=1: -leg + inner = rhs → leg = inner - rhs → offset = -rhs
        let offset = if legCoeff == 1: rhs else: -rhs

        # Trace inner to int_min/int_max
        if innerVarName notin minMaxDefs:
            return (false, LegTrace())

        let mmCi = minMaxDefs[innerVarName]
        let mmCon = tr.model.constraints[mmCi]
        let mmName = stripSolverPrefix(mmCon.name)
        let isMin = (mmName == "int_min")

        # Parse int_min/int_max(a, b, output)
        if mmCon.args.len < 3:
            return (false, LegTrace())

        let aArg = mmCon.args[0]
        let bArg = mmCon.args[1]

        proc makeEndpoint(arg: FznExpr): NoOverlapEndpoint =
            if arg.kind == FznIntLit:
                return NoOverlapEndpoint(isFixed: true, fixedValue: arg.intVal)
            elif arg.kind == FznIdent:
                if arg.ident in tr.paramValues:
                    return NoOverlapEndpoint(isFixed: true, fixedValue: tr.paramValues[arg.ident])
                else:
                    return NoOverlapEndpoint(isFixed: false, varName: arg.ident)
            return NoOverlapEndpoint(isFixed: true, fixedValue: 0)  # fallback

        result = (true, LegTrace(
            epA: makeEndpoint(aArg),
            epB: makeEndpoint(bArg),
            isMin: isMin,
            offset: offset,
            innerVar: innerVarName,
            linEqCi: linCi,
            minMaxCi: mmCi,
        ))

    # Step 2: Count references to each bool var in non-defining constraints
    # Track which bool_clause constraints each bool appears in, so we can check
    # if ALL its references are covered by NoOverlap patterns.
    var boolVarRefClauses: Table[string, seq[int]]  # bool var → list of bool_clause constraint indices
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        for argIdx in 0..1:
            let arr = con.args[argIdx]
            if arr.kind != FznArrayLit: continue
            for elem in arr.elems:
                if elem.kind == FznIdent:
                    boolVarRefClauses.mgetOrPut(elem.ident, @[]).add(ci)

    # Step 3: Scan 6-literal bool_clause constraints
    var nConsumed = 0
    var nSixLit = 0
    var nFailPair = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 6 or negArg.elems.len != 0: continue
        nSixLit += 1

        # All 6 literals must be defined by int_le_reif
        var lits: array[6, string]
        var allLeReif = true
        for i in 0..5:
            if posArg.elems[i].kind != FznIdent:
                allLeReif = false
                break
            lits[i] = posArg.elems[i].ident
            if lits[i] notin leReifDefs:
                allLeReif = false
                break
        if not allLeReif: continue

        # (allExclusive check deferred to two-pass consumption below)

        # For each lit, extract the int_le_reif args: (a, b, boolVar)
        # One of a/b is a constant (box bound), the other is a defined leg var
        type LeReifInfo = object
            constVal: int
            legVarName: string
            constIsArg0: bool  # true: int_le_reif(const, legVar, b), false: int_le_reif(legVar, const, b)
            leReifCi: int

        var infos: array[6, LeReifInfo]
        var allValid = true
        for i in 0..5:
            let leReifCi = leReifDefs[lits[i]]
            let leReifCon = tr.model.constraints[leReifCi]
            let a0 = leReifCon.args[0]
            let a1 = leReifCon.args[1]
            let a0IsConst = a0.kind == FznIntLit or (a0.kind == FznIdent and a0.ident in tr.paramValues)
            let a1IsConst = a1.kind == FznIntLit or (a1.kind == FznIdent and a1.ident in tr.paramValues)

            if a0IsConst and not a1IsConst and a1.kind == FznIdent:
                let cv = if a0.kind == FznIntLit: a0.intVal else: tr.paramValues[a0.ident]
                infos[i] = LeReifInfo(constVal: cv, legVarName: a1.ident, constIsArg0: true, leReifCi: leReifCi)
            elif not a0IsConst and a1IsConst and a0.kind == FznIdent:
                let cv = if a1.kind == FznIntLit: a1.intVal else: tr.paramValues[a1.ident]
                infos[i] = LeReifInfo(constVal: cv, legVarName: a0.ident, constIsArg0: false, leReifCi: leReifCi)
            else:
                allValid = false
                break
        if not allValid: continue

        # Trace each leg variable
        var traces: array[6, LegTrace]
        var tracesOk = true
        for i in 0..5:
            let (ok, trace) = traceLeg(tr, infos[i].legVarName)
            if not ok:
                tracesOk = false
                break
            traces[i] = trace
        if not tracesOk: continue

        # Group into 3 pairs by dimension.
        # Each pair should have one isMin (leg lower) and one !isMin (leg upper)
        # with the same endpoint variables (epA, epB).
        # NOTE: The 6 items are NOT necessarily in consecutive dimension pairs —
        # we must match by endpoint signature.
        var pattern: NoOverlapPattern
        var pairOk = true
        var radius = 0

        # Build endpoint key for matching
        proc endpointKey(ep: NoOverlapEndpoint): string =
            if ep.isFixed: "F" & $ep.fixedValue
            else: "V" & ep.varName

        # Match traces into pairs by (epA_key, epB_key)
        type DimPair = object
            minIdx, maxIdx: int
        var pairs: seq[DimPair]
        var used: array[6, bool]

        for i in 0..5:
            if used[i]: continue
            let keyA = endpointKey(traces[i].epA)
            let keyB = endpointKey(traces[i].epB)
            var found = false
            for j in (i+1)..5:
                if used[j]: continue
                if endpointKey(traces[j].epA) == keyA and endpointKey(traces[j].epB) == keyB:
                    # Found matching pair — verify one isMin and one isMax
                    if traces[i].isMin == traces[j].isMin:
                        continue  # both min or both max — not a valid pair
                    if traces[i].isMin:
                        pairs.add(DimPair(minIdx: i, maxIdx: j))
                    else:
                        pairs.add(DimPair(minIdx: j, maxIdx: i))
                    used[i] = true
                    used[j] = true
                    found = true
                    break
            if not found:
                pairOk = false
                break

        if pairs.len != 3:
            pairOk = false

        if pairOk:
            for d in 0..2:
                let tMin = traces[pairs[d].minIdx]
                let tMax = traces[pairs[d].maxIdx]

                # Verify consistent radius: offset should be -radius for min, +radius for max
                let r = tMax.offset
                if tMin.offset != -r:
                    pairOk = false
                    break
                if d == 0:
                    radius = r
                elif r != radius:
                    pairOk = false
                    break

                pattern.nodeA[d] = tMin.epA
                pattern.nodeB[d] = tMin.epB

                # Extract box bounds from int_le_reif constants.
                # The 6 separation conditions form 3 pairs (one per dimension):
                #   b_upper: int_le_reif(boxUpper, legLower, b) → b = (boxUpper <= legLower) → separated above
                #   b_lower: int_le_reif(legUpper, boxLower, b) → b = (legUpper <= boxLower) → separated below
                # So for the min trace (legLower): constIsArg0=true → constVal is boxUpper
                # For the max trace (legUpper): constIsArg0=false → constVal is boxLower
                let infoMin = infos[pairs[d].minIdx]
                let infoMax = infos[pairs[d].maxIdx]

                var gotLower = false
                var gotUpper = false

                if infoMin.constIsArg0:
                    # int_le_reif(C, legLower, b) → b = (C <= legLower) → boxUpper = C
                    pattern.boxUpper[d] = infoMin.constVal
                    gotUpper = true
                else:
                    # int_le_reif(legLower, C, b) → b = (legLower <= C) → boxLower = C
                    pattern.boxLower[d] = infoMin.constVal
                    gotLower = true

                if infoMax.constIsArg0:
                    # int_le_reif(C, legUpper, b) → b = (C <= legUpper) → boxUpper = C
                    pattern.boxUpper[d] = infoMax.constVal
                    gotUpper = true
                else:
                    # int_le_reif(legUpper, C, b) → b = (legUpper <= C) → boxLower = C
                    pattern.boxLower[d] = infoMax.constVal
                    gotLower = true

                if not gotLower or not gotUpper:
                    pairOk = false
                    break

        if not pairOk:
            nFailPair += 1
            continue

        pattern.radius = radius

        # Always consume the bool_clause itself
        pattern.consumedConstraints.add(ci)
        # Store the bool var names and their int_le_reif indices for two-pass consumption
        for i in 0..5:
            pattern.consumedBoolVars.add(lits[i])

        # Mark the bool_clause as consumed
        tr.definingConstraints.incl(ci)

        tr.noOverlapPatterns.add(pattern)
        nConsumed += 1

    if nSixLit > 0 and nFailPair > 0:
        stderr.writeLine(&"[FZN] NoOverlap: {nSixLit} 6-lit clauses, {tr.noOverlapPatterns.len} matched, " &
                                          &"{nFailPair} unmatched (pair mismatch)")

    # Two-pass consumption: now that ALL patterns are detected, check each bool var.
    # A bool can be consumed if ALL bool_clause constraints referencing it are NoOverlap patterns
    # (i.e., all their constraint indices are in definingConstraints).
    var nBoolsConsumed = 0
    var nLeReifConsumed = 0
    var consumedBools: HashSet[string]
    for pattern in tr.noOverlapPatterns:
        for boolVar in pattern.consumedBoolVars:
            if boolVar in consumedBools: continue
            # Check if ALL clauses referencing this bool are consumed (= became NoOverlap patterns)
            let refs = boolVarRefClauses.getOrDefault(boolVar, @[])
            var allCovered = true
            for clauseCi in refs:
                if clauseCi notin tr.definingConstraints:
                    allCovered = false
                    break
            if allCovered and refs.len > 0:
                consumedBools.incl(boolVar)
                tr.definedVarNames.incl(boolVar)
                nBoolsConsumed += 1
                # Also consume its defining int_le_reif constraint
                if boolVar in leReifDefs:
                    let leReifCi = leReifDefs[boolVar]
                    if leReifCi notin tr.definingConstraints:
                        tr.definingConstraints.incl(leReifCi)
                        nLeReifConsumed += 1

    nConsumed += nLeReifConsumed
    if tr.noOverlapPatterns.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.noOverlapPatterns.len} NoOverlap patterns, " &
                                          &"{nConsumed} constraints consumed, {nBoolsConsumed} bools eliminated, " &
                                          &"{nLeReifConsumed} int_le_reif consumed")


proc detectDfaGeostPattern(tr: var FznTranslator) =
    ## Detects multiple fzn_regular constraints over the same variable array
    ## (tiling pattern) and converts them to a single geost constraint.
    ## Each regular constraint encodes one tile's valid placements as a DFA.

    # Step 1: Find all fzn_regular constraints, verify they share the same array
    var regularIndices: seq[int]
    var boardArrayArg: FznExpr = nil

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "fzn_regular":
            continue
        if con.args.len < 6:
            continue

        let arrayArg = con.args[0]
        if boardArrayArg == nil:
            boardArrayArg = arrayArg
        else:
            # Verify same array reference
            if arrayArg.kind != boardArrayArg.kind:
                return
            case arrayArg.kind
            of FznIdent:
                if arrayArg.ident != boardArrayArg.ident:
                    return
            of FznArrayLit:
                # Array literals - check same elements
                if arrayArg.elems.len != boardArrayArg.elems.len:
                    return
                for i in 0..<arrayArg.elems.len:
                    if arrayArg.elems[i].kind != boardArrayArg.elems[i].kind:
                        return
                    if arrayArg.elems[i].kind == FznIdent and
                          arrayArg.elems[i].ident != boardArrayArg.elems[i].ident:
                        return
            else:
                return
        regularIndices.add(ci)

    if regularIndices.len < 2:
        return

    # Determine board array name
    var boardArrayName = ""
    if boardArrayArg.kind == FznIdent:
        boardArrayName = boardArrayArg.ident
    else:
        # Inline array literal - find which declared array matches
        for decl in tr.model.variables:
            if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
                if decl.value.elems.len == boardArrayArg.elems.len:
                    var match = true
                    for i in 0..<decl.value.elems.len:
                        if decl.value.elems[i].kind == FznIdent and
                              boardArrayArg.elems[i].kind == FznIdent and
                              decl.value.elems[i].ident != boardArrayArg.elems[i].ident:
                            match = false
                            break
                    if match:
                        boardArrayName = decl.name
                        break
        if boardArrayName == "":
            return

    # Step 2: Determine board size and sentinel positions from the model
    # Find board array declaration to get size
    var boardSize = 0
    var boardArrayDecl: FznVarDecl
    for decl in tr.model.variables:
        if decl.isArray and decl.name == boardArrayName:
            boardArrayDecl = decl
            if decl.value != nil and decl.value.kind == FznArrayLit:
                boardSize = decl.value.elems.len
            else:
                boardSize = decl.arraySize
            break
    if boardSize == 0:
        return

    # Find sentinel positions: look for int_eq constraints that fix board vars to a constant
    # Pattern: int_eq(board_element, constant) where constant is ntiles+1
    var sentinelPositions = initPackedSet[int]()
    var sentinelBoardIndices: seq[int]
    var sentinelValue = -1

    # Build a set of board element variable names for quick lookup
    var boardElemNames: seq[string]
    var boardElemNameSet: sets.HashSet[string] = initHashSet[string]()
    if boardArrayDecl.value != nil and boardArrayDecl.value.kind == FznArrayLit:
        for e in boardArrayDecl.value.elems:
            if e.kind == FznIdent:
                boardElemNames.add(e.ident)
                boardElemNameSet.incl(e.ident)
            else:
                boardElemNames.add("")

    # Map board element names to their 0-based index in the board array
    var elemToIdx: Table[string, int] = initTable[string, int]()
    for i, name in boardElemNames:
        if name != "":
            elemToIdx[name] = i

    # Scan for int_eq constraints setting board vars to constants
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "int_eq" and con.args.len >= 2:
            # int_eq(var, const) or int_eq(const, var)
            var varName = ""
            var constVal = -1
            if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit:
                varName = con.args[0].ident
                constVal = con.args[1].intVal
            elif con.args[1].kind == FznIdent and con.args[0].kind == FznIntLit:
                varName = con.args[1].ident
                constVal = con.args[0].intVal
            if varName in boardElemNameSet and constVal >= 0:
                let idx = elemToIdx[varName]
                sentinelBoardIndices.add(idx)
                sentinelPositions.incl(idx)
                if sentinelValue < 0:
                    sentinelValue = constVal
                # Mark this constraint as consumed
                tr.definingConstraints.incl(ci)

    # Also check: the board array may contain literal integers (already sentinel)
    if boardArrayDecl.value != nil and boardArrayDecl.value.kind == FznArrayLit:
        for i, e in boardArrayDecl.value.elems:
            if e.kind == FznIntLit:
                sentinelBoardIndices.add(i)
                sentinelPositions.incl(i)
                if sentinelValue < 0:
                    sentinelValue = e.intVal

    # Scan for int_ne constraints on board vars (these will be auto-satisfied by geost)
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name == "int_ne" and con.args.len >= 2:
            var varName = ""
            if con.args[0].kind == FznIdent and con.args[0].ident in boardElemNameSet:
                varName = con.args[0].ident
            elif con.args[1].kind == FznIdent and con.args[1].ident in boardElemNameSet:
                varName = con.args[1].ident
            if varName != "":
                tr.definingConstraints.incl(ci)

    let ntiles = regularIndices.len
    if sentinelValue < 0:
        sentinelValue = ntiles + 1

    # Step 3: For each regular constraint, extract placements
    var allPlacements: seq[seq[seq[int]]]
    var tileValues: seq[int]

    for ri, ci in regularIndices:
        let con = tr.model.constraints[ci]
        let nStates = tr.resolveIntArg(con.args[1])
        let nSymbols = tr.resolveIntArg(con.args[2])
        let transFlat = tr.resolveIntArray(con.args[3])
        let q0 = tr.resolveIntArg(con.args[4])
        var finalStates: seq[int]
        let fArg = con.args[5]
        case fArg.kind
        of FznSetLit:
            finalStates = fArg.setElems
        of FznRange:
            for s in fArg.lo..fArg.hi:
                finalStates.add(s)
        of FznArrayLit:
            for e in fArg.elems:
                finalStates.add(tr.resolveIntArg(e))
        else:
            finalStates = tr.resolveIntArray(fArg)

        # Build 2D transition table
        var transition = newSeq[seq[int]](nStates)
        for s in 0..<nStates:
            transition[s] = newSeq[int](nSymbols)
            for j in 0..<nSymbols:
                transition[s][j] = transFlat[s * nSymbols + j]

        # Identify which input is the tile
        let tileInputIdx = identifyTileInput(transition, nStates, nSymbols)
        if tileInputIdx < 0:
            stderr.writeLine(&"[FZN] Geost: cannot identify tile input for regular constraint {ci}, aborting")
            return

        let tileValue = tileInputIdx + 1  # 1-indexed tile value

        let placements = extractPlacementsFromDfa(
            nStates, nSymbols, transition, q0, finalStates,
            tileInputIdx, boardSize, sentinelPositions
        )

        if placements.len == 0:
            stderr.writeLine(&"[FZN] Geost: tile {tileValue} has no valid placements, aborting")
            return

        allPlacements.add(placements)
        tileValues.add(tileValue)

        # Mark this regular constraint as consumed
        tr.definingConstraints.incl(ci)

    # Step 4: Store the conversion
    tr.geostConversion = GeostConversion(
        boardArrayName: boardArrayName,
        allPlacements: allPlacements,
        tileValues: tileValues,
        sentinelBoardIndices: sentinelBoardIndices,
        sentinelValue: sentinelValue,
    )

    stderr.writeLine(&"[FZN] Detected DFA-to-geost pattern: {ntiles} tiles, {boardSize} board cells")
    for t in 0..<ntiles:
        stderr.writeLine(&"[FZN]   Tile {tileValues[t]}: {allPlacements[t].len} placements, {allPlacements[t][0].len} cells")

proc detectConditionalNoOverlapPairs(tr: var FznTranslator) =
    ## Detects conditional no-overlap pair patterns from room-conflict constraints:
    ##
    ## Patient-patient (3+2 or 3+1 bool_clause):
    ##   int_lin_ne_reif([1,-1], [room_A, room_B], 0, B_ne) :: defines_var(B_ne)
    ##   int_lin_le_reif([-1,1], [adm_A, adm_B], -stay_B, B_le1) :: defines_var(B_le1)
    ##   int_lin_le_reif([-1,1], [adm_B, adm_A], -stay_A, B_le2) :: defines_var(B_le2)
    ##   bool_clause([B_le1, B_le2, B_ne], [sel_A, sel_B])  -- both optional
    ##   bool_clause([B_le1, B_le2, B_ne], [sel_A])          -- B is mandatory
    ##
    ## Occupant-patient (2+1 bool_clause):
    ##   int_ne_reif(room_A, occ_room, B_ne) :: defines_var(B_ne)
    ##   int_le_reif(occ_end, adm_A, B_le) :: defines_var(B_le)
    ##   bool_clause([B_ne, B_le], [sel_A])

    type
        ConditionalNoOverlapInfo = object
            startAName, startBName: string
            durationA, durationB: int
            resourceAName, resourceBName: string  # "" if fixed
            resourceAFixed, resourceBFixed: int
            condAName, condBName: string          # "" if always true
            consumedCIs: seq[int]                 # constraint indices to consume
            consumedVars: seq[string]             # intermediate bool vars to eliminate

    # Step 1: Index reification constraints with defines_var
    type ReifInfo = object
        ci: int
        constraintType: string  # "int_lin_ne_reif", "int_lin_le_reif", "int_ne_reif", "int_le_reif"
        varNames: seq[string]
        coeffs: seq[int]
        rhs: int

    var reifByOutputVar: Table[string, ReifInfo]  # output bool var -> info

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if not con.hasAnnotation("defines_var"): continue
        let name = stripSolverPrefix(con.name)
        if name notin ["int_lin_ne_reif", "int_lin_le_reif", "int_ne_reif", "int_le_reif"]: continue

        var info: ReifInfo
        info.ci = ci
        info.constraintType = name

        case name
        of "int_lin_ne_reif":
            # int_lin_ne_reif(coeffs, vars, rhs, result_bool)
            if con.args.len < 4 or con.args[3].kind != FznIdent: continue
            try:
                info.coeffs = tr.resolveIntArray(con.args[0])
                let varExprs = tr.resolveVarArrayElems(con.args[1])
                info.varNames = newSeq[string](varExprs.len)
                for i, e in varExprs:
                    if e.kind != FznIdent: continue
                    info.varNames[i] = e.ident
                info.rhs = tr.resolveIntArg(con.args[2])
            except KeyError, ValueError: continue
            reifByOutputVar[con.args[3].ident] = info

        of "int_lin_le_reif":
            # int_lin_le_reif(coeffs, vars, rhs, result_bool)
            if con.args.len < 4 or con.args[3].kind != FznIdent: continue
            try:
                info.coeffs = tr.resolveIntArray(con.args[0])
                let varExprs = tr.resolveVarArrayElems(con.args[1])
                info.varNames = newSeq[string](varExprs.len)
                for i, e in varExprs:
                    if e.kind != FznIdent: continue
                    info.varNames[i] = e.ident
                info.rhs = tr.resolveIntArg(con.args[2])
            except KeyError, ValueError: continue
            reifByOutputVar[con.args[3].ident] = info

        of "int_ne_reif":
            # int_ne_reif(var, val, result_bool) or int_ne_reif(val, var, result_bool)
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            info.varNames = @[]
            info.coeffs = @[]
            # Extract var and constant
            if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit:
                info.varNames = @[con.args[0].ident]
                info.rhs = con.args[1].intVal
            elif con.args[0].kind == FznIntLit and con.args[1].kind == FznIdent:
                info.varNames = @[con.args[1].ident]
                info.rhs = con.args[0].intVal
            else: continue
            reifByOutputVar[con.args[2].ident] = info

        of "int_le_reif":
            # int_le_reif(a, b, result_bool) — a <= b
            if con.args.len < 3 or con.args[2].kind != FznIdent: continue
            # We need: const <= var (meaning var >= const, i.e., admission >= occ_end)
            if con.args[0].kind == FznIntLit and con.args[1].kind == FznIdent:
                info.varNames = @[con.args[1].ident]
                info.rhs = con.args[0].intVal  # the constant (occ_end)
            elif con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit:
                info.varNames = @[con.args[0].ident]
                info.rhs = con.args[1].intVal
            else: continue
            reifByOutputVar[con.args[2].ident] = info

        else: discard

    if reifByOutputVar.len == 0: return

    # Step 2: Scan bool_clause constraints for the no-overlap patterns
    var nPatientPatient = 0
    var detected: seq[ConditionalNoOverlapInfo]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue

        # Extract positive and negative literals
        var posLits, negLits: seq[string]
        if con.args[0].kind == FznArrayLit:
            for e in con.args[0].elems:
                if e.kind == FznIdent: posLits.add(e.ident)
        if con.args[1].kind == FznArrayLit:
            for e in con.args[1].elems:
                if e.kind == FznIdent: negLits.add(e.ident)

        # Pattern A: 3 positive, 1-2 negative (patient-patient no-overlap)
        # bool_clause([B_le1, B_le2, B_ne], [sel_A, sel_B]) or [sel_A]
        if posLits.len == 3 and negLits.len in {1, 2}:
            # Find which positive lits are lin_le_reif and which is lin_ne_reif
            var leReifs: seq[ReifInfo]
            var neReif: ReifInfo
            var hasNe = false
            var allFound = true

            for lit in posLits:
                if lit notin reifByOutputVar:
                    allFound = false
                    break
                let info = reifByOutputVar[lit]
                if info.constraintType == "int_lin_le_reif":
                    leReifs.add(info)
                elif info.constraintType == "int_lin_ne_reif":
                    neReif = info
                    hasNe = true
                else:
                    allFound = false
                    break

            if allFound and hasNe and leReifs.len == 2:
                # Validate structure:
                # neReif: [1,-1], [roomA, roomB], 0 → roomA != roomB
                # leReif1: [-1,1], [admA, admB], -stayB → admA >= admB + stayB
                # leReif2: [-1,1], [admB, admA], -stayA → admB >= admA + stayA
                if neReif.coeffs == @[1, -1] and neReif.rhs == 0 and neReif.varNames.len == 2 and
                      leReifs[0].coeffs == @[-1, 1] and leReifs[0].varNames.len == 2 and
                      leReifs[1].coeffs == @[-1, 1] and leReifs[1].varNames.len == 2:
                    let roomAName = neReif.varNames[0]
                    let roomBName = neReif.varNames[1]

                    # Extract admission vars and durations from le_reifs
                    # leReif: [-1,1]*[x,y] <= -d means y - x <= -d, i.e., x >= y + d
                    # So if leReif1 has vars [admA, admB] and rhs -stayB: admA >= admB + stayB
                    #    leReif2 has vars [admB, admA] and rhs -stayA: admB >= admA + stayA
                    let admA1 = leReifs[0].varNames[0]  # admA (the one that must be >= other + dur)
                    let admB1 = leReifs[0].varNames[1]
                    let durB = -leReifs[0].rhs  # stayB
                    let admB2 = leReifs[1].varNames[0]
                    let admA2 = leReifs[1].varNames[1]
                    let durA = -leReifs[1].rhs  # stayA

                    # Verify consistency: the two le_reifs should involve the same admission pairs
                    if admA1 == admA2 and admB1 == admB2 and durA > 0 and durB > 0:
                        var info: ConditionalNoOverlapInfo
                        info.startAName = admA1
                        info.startBName = admB1
                        info.durationA = durA
                        info.durationB = durB
                        info.resourceAName = roomAName
                        info.resourceBName = roomBName
                        info.resourceAFixed = -1
                        info.resourceBFixed = -1

                        # Condition vars from negative literals (selection vars)
                        if negLits.len >= 1:
                            info.condAName = negLits[0]
                        if negLits.len >= 2:
                            info.condBName = negLits[1]

                        info.consumedCIs = @[ci, neReif.ci, leReifs[0].ci, leReifs[1].ci]
                        info.consumedVars = @[]
                        for lit in posLits:
                            info.consumedVars.add(lit)

                        detected.add(info)
                        nPatientPatient += 1

        # Pattern B: 2 positive, 1 negative (occupant-patient no-overlap)
        # Skipped: patient duration is unknown at detection time and these
        # are handled adequately as boolean constraints.

    if detected.len == 0: return

    # Step 3: Consume detected patterns
    for info in detected:
        for ci in info.consumedCIs:
            tr.definingConstraints.incl(ci)
        for v in info.consumedVars:
            tr.definedVarNames.incl(v)

    # Store for later constraint creation (after translateVariables)
    for info in detected:
        tr.conditionalNoOverlapInfos.add((
            startAName: info.startAName, startBName: info.startBName,
            durationA: info.durationA, durationB: info.durationB,
            resourceAName: info.resourceAName, resourceBName: info.resourceBName,
            resourceAFixed: info.resourceAFixed, resourceBFixed: info.resourceBFixed,
            condAName: info.condAName, condBName: info.condBName,
            consumedCIs: info.consumedCIs, consumedVars: info.consumedVars))

    stderr.writeLine(&"[FZN] Detected {nPatientPatient} patient-patient conditional no-overlap pairs")


proc detectConditionalCumulativePattern(tr: var FznTranslator) =
    ## Detects the room_admission encoding pattern:
    ##   array_var_int_element(room[p], [ra[1,p]..ra[n,p]], result) :: defines_var(result)
    ##   int_eq_reif(result, admission[p], B) :: defines_var(B)
    ##   fzn_cumulative([fixed..., ra[r,1]..ra[r,n]], durations, heights, limit) for each room r
    ##
    ## Replaces with ConditionalCumulative constraints where tasks are active
    ## only when room[p] == r AND selection[p] == true.

    type
        ElementInfo = object
            ci: int
            indexVarName: string      # room[p]
            arrayVarNames: seq[string] # [ra[1,p], ra[2,p], ...]
            resultVarName: string      # element output (channel), "" if constant result
            resultConstVal: int        # constant result value (when resultVarName == "")

    # Pre-build array name -> element names and constant values from model variable declarations
    # (arrayElementNames is populated later in translateVariables, so we build a local one)
    var localArrayElements: Table[string, seq[string]]
    var localArrayConstVals: Table[string, seq[int]]  # parallel: const value when name is ""
    for decl in tr.model.variables:
        if decl.value != nil and decl.value.kind == FznArrayLit:
            var elemNames: seq[string]
            var constVals: seq[int]
            for e in decl.value.elems:
                if e.kind == FznIdent:
                    elemNames.add(e.ident)
                    constVals.add(0)
                elif e.kind == FznIntLit:
                    elemNames.add("")
                    constVals.add(e.intVal)
                else:
                    elemNames.add("")
                    constVals.add(0)
            localArrayElements[decl.name] = elemNames
            localArrayConstVals[decl.name] = constVals

    template resolveArrayNames(arrArg: FznExpr): seq[string] =
        block:
            var res: seq[string]
            if arrArg.kind == FznIdent:
                if arrArg.ident in localArrayElements:
                    res = localArrayElements[arrArg.ident]
                elif arrArg.ident in tr.arrayElementNames:
                    res = tr.arrayElementNames[arrArg.ident]
            elif arrArg.kind == FznArrayLit:
                for elem in arrArg.elems:
                    if elem.kind == FznIdent:
                        res.add(elem.ident)
                    else:
                        res.add("")
            res

    # Step 1: Find element constraints with ra var arrays
    # Scan ALL constraints, not just channelConstraints — some element constraints have
    # constant results (mandatory patients with fixed admission days) and no defines_var.
    var elementInfos: seq[ElementInfo]
    var elementByResult: Table[string, int]

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent: continue
        # Result can be variable (FznIdent) or constant (FznIntLit)
        let hasVarResult = con.args[2].kind == FznIdent
        let hasConstResult = con.args[2].kind == FznIntLit
        if not hasVarResult and not hasConstResult: continue

        let arrayVarNames = resolveArrayNames(con.args[1])
        if arrayVarNames.len == 0: continue

        # All array elements must be variables (not constants, not already defined/channel)
        var allVars = true
        for vn in arrayVarNames:
            if vn == "" or vn in tr.definedVarNames or vn in tr.channelVarNames:
                allVars = false
                break
        if not allVars: continue

        if hasVarResult:
            elementByResult[con.args[2].ident] = elementInfos.len
            elementInfos.add(ElementInfo(
                ci: ci,
                indexVarName: con.args[0].ident,
                arrayVarNames: arrayVarNames,
                resultVarName: con.args[2].ident,
                resultConstVal: 0
            ))
        else:
            # Constant result: mandatory patient with fixed admission day
            elementInfos.add(ElementInfo(
                ci: ci,
                indexVarName: con.args[0].ident,
                arrayVarNames: arrayVarNames,
                resultVarName: "",
                resultConstVal: con.args[2].intVal
            ))

    if elementInfos.len == 0: return

    # Step 2: Find int_eq_reif(result, admission, B) for each element result
    # NOTE: scan ALL constraints including definingConstraints (reif channels consumed them)
    type EqReifInfo = object
        admissionVarName: string
        selectionVarName: string  # filled in step 3

    var eqReifByResult: Table[string, EqReifInfo]

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent or con.args[2].kind != FznIdent:
            continue
        let resultName = con.args[0].ident
        if resultName notin elementByResult: continue
        eqReifByResult[resultName] = EqReifInfo(
            admissionVarName: con.args[1].ident,
            selectionVarName: ""
        )

    if eqReifByResult.len == 0: return

    # Step 3: Find bool_clause linking selection to eq_reif bool vars
    # Pattern: bool_clause([B], [sel]) where B is the eq_reif bool output
    # Build set of eq_reif bool var names for quick lookup
    var eqReifBoolVars: Table[string, string]  # boolVarName -> resultVarName
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        if con.args[0].ident in eqReifByResult:
            eqReifBoolVars[con.args[2].ident] = con.args[0].ident

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        var posLits, negLits: seq[string]
        if con.args[0].kind == FznArrayLit:
            for e in con.args[0].elems:
                if e.kind == FznIdent: posLits.add(e.ident)
        if con.args[1].kind == FznArrayLit:
            for e in con.args[1].elems:
                if e.kind == FznIdent: negLits.add(e.ident)
        if posLits.len == 1 and negLits.len == 1:
            if posLits[0] in eqReifBoolVars:
                let resultName = eqReifBoolVars[posLits[0]]
                if resultName in eqReifByResult:
                    eqReifByResult[resultName].selectionVarName = negLits[0]

    # Step 4: Find cumulative constraints with ra vars as start times
    # Build ra_var -> (elementIdx, roomIdx) lookup
    var allRaVarNames = initHashSet[string]()
    var raVarToElementRoom: Table[string, tuple[elemIdx, roomIdx: int]]
    for ei, einfo in elementInfos:
        for ri, vn in einfo.arrayVarNames:
            allRaVarNames.incl(vn)
            raVarToElementRoom[vn] = (ei, ri)

    type ConditionalCumulativeInfo = object
        fixedTasks: seq[tuple[start, duration, height: int]]
        conditionalTasks: seq[tuple[admissionVarName, selectionVarName, roomVarName: string,
                                                                  duration, height, roomValue, fixedAdmission: int]]
        limit: int
        cumulativeCi: int
        consumedRaVarNames: seq[string]

    var conditionalCumulatives: seq[ConditionalCumulativeInfo]

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name notin ["fzn_cumulative", "fzn_cumulatives"]: continue
        if ci in tr.definingConstraints: continue

        # Resolve start array names and const values
        let startArg = con.args[0]
        var startNames: seq[string]
        var startConstVals: seq[int]  # parallel: const value when name is ""
        if startArg.kind == FznIdent:
            if startArg.ident in localArrayElements:
                startNames = localArrayElements[startArg.ident]
                startConstVals = localArrayConstVals[startArg.ident]
            elif startArg.ident in tr.arrayElementNames:
                startNames = tr.arrayElementNames[startArg.ident]
                startConstVals = newSeq[int](startNames.len)
            else: continue
        elif startArg.kind == FznArrayLit:
            for e in startArg.elems:
                if e.kind == FznIdent:
                    startNames.add(e.ident)
                    startConstVals.add(0)
                elif e.kind == FznIntLit:
                    startNames.add("")
                    startConstVals.add(e.intVal)
                else:
                    startNames.add("")
                    startConstVals.add(0)
        else: continue

        if startNames.len == 0: continue

        # Check if this cumulative has ra vars
        var raCount = 0
        for sn in startNames:
            if sn in allRaVarNames: raCount += 1
        if raCount == 0: continue

        var durations, heights: seq[int]
        var limit: int
        try:
            durations = tr.resolveIntArray(con.args[1])
            heights = tr.resolveIntArray(con.args[2])
            limit = tr.resolveIntArg(con.args[3])
        except KeyError, ValueError: continue
        if durations.len != startNames.len or heights.len != startNames.len: continue

        var ccinfo: ConditionalCumulativeInfo
        ccinfo.limit = limit
        ccinfo.cumulativeCi = ci
        var allMatched = true
        var roomValue = -1

        for i, sn in startNames:
            if sn in tr.paramValues:
                ccinfo.fixedTasks.add((tr.paramValues[sn], durations[i], heights[i]))
            elif sn == "":
                # Inline constant in the start array
                ccinfo.fixedTasks.add((startConstVals[i], durations[i], heights[i]))
            elif sn in allRaVarNames:
                let (elemIdx, roomIdx) = raVarToElementRoom[sn]
                if roomValue < 0:
                    roomValue = roomIdx
                elif roomIdx != roomValue:
                    allMatched = false
                    break
                let einfo = elementInfos[elemIdx]
                if einfo.resultVarName == "":
                    # Constant-result element: mandatory patient with fixed admission day
                    # This is a conditional task (depends on room assignment) but admission is fixed
                    ccinfo.conditionalTasks.add((
                        admissionVarName: "",  # signals fixed admission
                        selectionVarName: "",  # always active (mandatory)
                        roomVarName: einfo.indexVarName,
                        duration: durations[i],
                        height: heights[i],
                        roomValue: roomIdx + 1,  # FZN 1-based
                        fixedAdmission: einfo.resultConstVal
                    ))
                elif einfo.resultVarName in eqReifByResult:
                    # Optional patient: element(room[p], ra_array, result), eq_reif(result, admission, B)
                    let eqInfo = eqReifByResult[einfo.resultVarName]
                    ccinfo.conditionalTasks.add((
                        admissionVarName: eqInfo.admissionVarName,
                        selectionVarName: eqInfo.selectionVarName,
                        roomVarName: einfo.indexVarName,
                        duration: durations[i],
                        height: heights[i],
                        roomValue: roomIdx + 1,  # FZN 1-based
                        fixedAdmission: -1
                    ))
                else:
                    # Mandatory patient: element(room[p], ra_array, admission[p]) directly
                    # The element result IS the admission var; no selection condition needed
                    ccinfo.conditionalTasks.add((
                        admissionVarName: einfo.resultVarName,
                        selectionVarName: "",  # always active (mandatory)
                        roomVarName: einfo.indexVarName,
                        duration: durations[i],
                        height: heights[i],
                        roomValue: roomIdx + 1,
                        fixedAdmission: -1
                    ))
                ccinfo.consumedRaVarNames.add(sn)
            else:
                # Non-ra variable start time - can't convert
                allMatched = false
                break

        if not allMatched or roomValue < 0: continue
        conditionalCumulatives.add(ccinfo)

    if conditionalCumulatives.len == 0: return

    # Step 5: Consume cumulative constraints and mark ra vars as non-searchable
    for ccinfo in conditionalCumulatives:
        tr.definingConstraints.incl(ccinfo.cumulativeCi)

    # Mark ra vars as channel vars so they're not searched (but still get positions)
    var nRaChanneled = 0
    var consumedRaSet = initHashSet[string]()
    for ccinfo in conditionalCumulatives:
        for raName in ccinfo.consumedRaVarNames:
            consumedRaSet.incl(raName)
            if raName notin tr.channelVarNames and raName notin tr.definedVarNames:
                tr.channelVarNames.incl(raName)
                nRaChanneled += 1

    # Also mark ra vars from constant-result elements (mandatory patients with fixed admission)
    for ei, einfo in elementInfos:
        if einfo.resultVarName == "":
            for vn in einfo.arrayVarNames:
                consumedRaSet.incl(vn)
                if vn notin tr.channelVarNames and vn notin tr.definedVarNames:
                    tr.channelVarNames.incl(vn)
                    nRaChanneled += 1

    # Also remove element channel constraints whose arrays reference consumed ra vars.
    # These channels are dead (cumulative replaced by conditional cumulative)
    # and would waste time propagating.
    var elementsToRemove: seq[int]
    for ci, chanVar in tr.channelConstraints:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        let arrayNames = resolveArrayNames(con.args[1])
        var hasRa = false
        for vn in arrayNames:
            if vn in consumedRaSet:
                hasRa = true
                break
        if hasRa:
            elementsToRemove.add(ci)
            if chanVar in eqReifByResult:
                # Intermediate result: eq_reif links it to admission. Safe to eliminate.
                tr.channelVarNames.excl(chanVar)
                tr.definedVarNames.incl(chanVar)
            else:
                # Mandatory patient: admission var IS the element result.
                # Remove channel status so it becomes a search position.
                # The element constraint in the main constraint set ensures consistency.
                tr.channelVarNames.excl(chanVar)

    for ci in elementsToRemove:
        tr.channelConstraints.del(ci)

    # Also consume constant-result element constraints (mandatory patients)
    for ei, einfo in elementInfos:
        if einfo.resultVarName == "":
            tr.definingConstraints.incl(einfo.ci)

    stderr.writeLine(&"[FZN] Marked {nRaChanneled} ra vars as channels, removed {elementsToRemove.len} dead element channels for conditional cumulative")

    # Store for later constraint creation
    for ccinfo in conditionalCumulatives:
        var condTaskTuples: seq[tuple[admissionVarName, selectionVarName, roomVarName: string,
                                                                      duration, height, roomValue, fixedAdmission: int]]
        for ct in ccinfo.conditionalTasks:
            condTaskTuples.add(ct)
        var fixedTaskTuples: seq[tuple[start, duration, height: int]]
        for ft in ccinfo.fixedTasks:
            fixedTaskTuples.add(ft)
        tr.conditionalCumulativeInfos.add((
            fixedTasks: fixedTaskTuples,
            conditionalTasks: condTaskTuples,
            limit: ccinfo.limit,
            cumulativeCi: ccinfo.cumulativeCi,
            consumedElementCIs: newSeq[int](),
            consumedEqReifCIs: newSeq[int](),
            consumedBoolClauseCIs: newSeq[int](),
            consumedRaVarNames: ccinfo.consumedRaVarNames,
            consumedBoolVarNames: newSeq[string]()))

    stderr.writeLine(&"[FZN] Detected {conditionalCumulatives.len} conditional cumulative constraints (replacing regular cumulatives)")


proc detectConditionalDayCapacityPattern(tr: var FznTranslator) =
    ## Detects the H3/H4 surgeon/OT capacity encoding pattern:
    ##   int_lin_le(coeffs, [D_1, ..., D_n], capacity)
    ## where each D_i is:
    ##   bool2int(C_i, D_i) :: defines_var(D_i)
    ##   array_bool_and([sel[p], B_day, (B_ot)?], C_i) :: defines_var(C_i)
    ##   int_eq_reif(admission[p], day, B_day) :: defines_var(B_day)
    ##   int_eq_reif(ot[p], otVal, B_ot) :: defines_var(B_ot)  [H4 only]
    ##
    ## Replaces with ConditionalDayCapacity constraints.

    # Step 1: Build lookup tables from FZN constraints
    # bool2int: outputVar -> inputVar
    var bool2intInput: Table[string, string]
    # array_bool_and: outputVar -> seq of input vars
    var boolAndInputs: Table[string, seq[string]]
    # int_eq_reif: outputVar -> (sourceVar, value)
    var eqReifSource: Table[string, tuple[sourceVar: string, value: int]]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name == "bool2int" and con.annotations.len > 0:
            # bool2int(B, I) :: defines_var(I)
            if con.args[0].kind == FznIdent and con.args[1].kind == FznIdent:
                bool2intInput[con.args[1].ident] = con.args[0].ident
        elif name == "array_bool_and" and con.annotations.len > 0:
            # array_bool_and([...], R) :: defines_var(R)
            if con.args[0].kind == FznArrayLit and con.args[1].kind == FznIdent:
                var inputs: seq[string]
                for elem in con.args[0].elems:
                    if elem.kind == FznIdent:
                        inputs.add(elem.ident)
                    elif elem.kind == FznBoolLit:
                        if not elem.boolVal:
                            inputs = @[]  # false literal => always false, skip
                            break
                        # true literal: skip (doesn't affect AND result)
                    else:
                        inputs = @[]
                        break
                if inputs.len >= 1:
                    boolAndInputs[con.args[1].ident] = inputs
        elif name == "int_eq_reif" and con.annotations.len > 0:
            # int_eq_reif(X, val, B) :: defines_var(B)
            if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit and
                  con.args[2].kind == FznIdent:
                eqReifSource[con.args[2].ident] = (con.args[0].ident, con.args[1].intVal)

    # Also scan definingConstraints for eq_reif that were already consumed by reif channel detection
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name == "int_eq_reif" and con.args[0].kind == FznIdent and
              con.args[1].kind == FznIntLit and con.args[2].kind == FznIdent:
            if con.args[2].ident notin eqReifSource:
                eqReifSource[con.args[2].ident] = (con.args[0].ident, con.args[1].intVal)
        if name == "bool2int" and con.args[0].kind == FznIdent and con.args[1].kind == FznIdent:
            if con.args[1].ident notin bool2intInput:
                bool2intInput[con.args[1].ident] = con.args[0].ident
        if name == "array_bool_and" and con.args[0].kind == FznArrayLit and con.args[1].kind == FznIdent:
            if con.args[1].ident notin boolAndInputs:
                var inputs: seq[string]
                for elem in con.args[0].elems:
                    if elem.kind == FznIdent:
                        inputs.add(elem.ident)
                    elif elem.kind == FznBoolLit:
                        if not elem.boolVal:
                            inputs = @[]
                            break
                    else:
                        inputs = @[]
                        break
                if inputs.len >= 1:
                    boolAndInputs[con.args[1].ident] = inputs

    # Step 2: Find int_lin_le constraints with many bool2int variables
    # Identify the selection and admission arrays
    var selectionVarNames: HashSet[string]
    var admissionVarNames: HashSet[string]
    var otVarNames: HashSet[string]

    # Look at output arrays to identify variable roles
    for v in tr.model.variables:
        if v.isArray and v.value != nil and v.value.kind == FznArrayLit:
            if v.name.startsWith("selection"):
                for elem in v.value.elems:
                    if elem.kind == FznIdent:
                        selectionVarNames.incl(elem.ident)
            elif v.name.startsWith("admission"):
                for elem in v.value.elems:
                    if elem.kind == FznIdent:
                        admissionVarNames.incl(elem.ident)
            elif v.name == "ot" or v.name.startsWith("ot_"):
                for elem in v.value.elems:
                    if elem.kind == FznIdent:
                        otVarNames.incl(elem.ident)

    # Step 3: Trace each candidate int_lin_le
    type
        TaskInfo = object
            weight: int
            admissionVarName: string
            selectionVarName: string
            extraCondVarName: string  # "" if none
            extraCondVal: int
            day: int
            isMandatory: bool

    type
        PerDayConstraint = object
            ci: int
            day: int
            capacity: int
            tasks: seq[TaskInfo]
            consumedVarNames: seq[string]

    var nDetected = 0
    var perDayConstraints: seq[PerDayConstraint]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le": continue

        if con.args[2].kind != FznIntLit:
            continue

        # Resolve coefficient and variable arrays (can be inline FznArrayLit or named FznIdent)
        var coeffs: seq[FznExpr]
        var vars: seq[FznExpr]
        if con.args[0].kind == FznArrayLit:
            coeffs = con.args[0].elems
        elif con.args[0].kind == FznIdent:
            # Resolve named parameter array
            if con.args[0].ident in tr.arrayValues:
                for v in tr.arrayValues[con.args[0].ident]:
                    coeffs.add(FznExpr(kind: FznIntLit, intVal: v))
            else:
                continue
        else:
            continue

        if con.args[1].kind == FznArrayLit:
            vars = con.args[1].elems
        elif con.args[1].kind == FznIdent:
            # Resolve named variable array
            for v in tr.model.variables:
                if v.isArray and v.name == con.args[1].ident and v.value != nil and v.value.kind == FznArrayLit:
                    vars = v.value.elems
                    break
            if vars.len == 0:
                continue
        else:
            continue

        let rhs = con.args[2].intVal

        if coeffs.len != vars.len or coeffs.len < 10:
            continue

        let isFirstCandidate = perDayConstraints.len == 0 and nDetected == 0

        var tasks: seq[TaskInfo]
        var allValid = true
        var commonDay = -1
        var consumedVarNames: seq[string]

        for idx in 0..<vars.len:
            if vars[idx].kind != FznIdent or coeffs[idx].kind != FznIntLit:
                allValid = false
                break

            let dVarName = vars[idx].ident
            let weight = coeffs[idx].intVal

            if dVarName notin bool2intInput:
                allValid = false
                break
            let cVarName = bool2intInput[dVarName]

            var selVar = ""
            var day = -1
            var admVar = ""
            var extraSource = ""
            var extraVal = -1
            var mandatory = false

            if cVarName in boolAndInputs:
                # Normal case: bool2int input is an array_bool_and output
                let andInputs = boolAndInputs[cVarName]

                if andInputs.len < 1 or andInputs.len > 3:
                    allValid = false
                    break

                for inp in andInputs:
                    if inp in selectionVarNames:
                        selVar = inp
                    elif inp in eqReifSource:
                        let (srcVar, val) = eqReifSource[inp]
                        if srcVar in admissionVarNames:
                            admVar = srcVar
                            day = val
                        elif srcVar in otVarNames:
                            extraSource = srcVar
                            extraVal = val
                        else:
                            allValid = false
                            break
                    else:
                        allValid = false
                        break
            elif cVarName in eqReifSource:
                # Mandatory patient case: bool2int input is directly eq_reif output
                # (selection=true was constant-folded away, no AND needed)
                let (srcVar, val) = eqReifSource[cVarName]
                if srcVar in admissionVarNames:
                    admVar = srcVar
                    day = val
                    selVar = ""
                    mandatory = true
                else:
                    allValid = false
            else:
                allValid = false

            if not allValid: break
            if admVar == "" or day < 0:
                allValid = false
                break

            if commonDay < 0:
                commonDay = day
            elif commonDay != day:
                allValid = false
                break

            tasks.add(TaskInfo(
                weight: weight,
                admissionVarName: admVar,
                selectionVarName: selVar,
                extraCondVarName: extraSource,
                extraCondVal: extraVal,
                day: day,
                isMandatory: mandatory))
            consumedVarNames.add(dVarName)
            consumedVarNames.add(cVarName)

        if not allValid or tasks.len == 0:
            continue

        perDayConstraints.add(PerDayConstraint(
            ci: ci, day: commonDay, capacity: rhs, tasks: tasks,
            consumedVarNames: consumedVarNames))

    # Group by task signature (same patients, same conditions, different days)
    # Signature = sorted list of (admissionVar, selectionVar, extraCondVarName, extraCondVal, weight)
    var groups: Table[string, seq[int]]  # signature -> indices into perDayConstraints

    for i, pdc in perDayConstraints:
        var sig = ""
        for t in pdc.tasks:
            sig.add(t.admissionVarName & ":" & t.selectionVarName & ":" &
                            t.extraCondVarName & ":" & $t.extraCondVal & ":" & $t.weight & ";")
        groups.mgetOrPut(sig, @[]).add(i)

    # Build ConditionalDayCapacity constraints from groups
    for sig, indices in groups:
        var maxDay = 0
        for i in indices:
            if perDayConstraints[i].day > maxDay:
                maxDay = perDayConstraints[i].day

        # Build capacity array: default to max int (unconstrained) for days not mentioned
        var capacities = newSeq[int](maxDay + 1)
        for d in 0..maxDay:
            capacities[d] = high(int32).int  # unconstrained by default

        var consumedCIs: seq[int]
        var consumedVarNames: seq[string]

        for i in indices:
            let pdc = perDayConstraints[i]
            if pdc.day <= maxDay:
                capacities[pdc.day] = pdc.capacity
            consumedCIs.add(pdc.ci)
            for vn in pdc.consumedVarNames:
                consumedVarNames.add(vn)

        # Build task list from the first constraint (all have same structure)
        let firstPdc = perDayConstraints[indices[0]]
        var taskInfos: seq[tuple[weight: int, admissionVarName, selectionVarName: string,
                                                            extraCondVarName: string, extraCondVal: int,
                                                            isMandatory: bool]]
        for t in firstPdc.tasks:
            taskInfos.add((weight: t.weight,
                                            admissionVarName: t.admissionVarName,
                                            selectionVarName: t.selectionVarName,
                                            extraCondVarName: t.extraCondVarName,
                                            extraCondVal: t.extraCondVal,
                                            isMandatory: t.isMandatory))

        # Mark consumed
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)
        for vn in consumedVarNames:
            if vn notin tr.channelVarNames and vn notin tr.definedVarNames:
                tr.definedVarNames.incl(vn)

        tr.conditionalDayCapacityInfos.add((
            tasks: taskInfos,
            capacities: capacities,
            maxDay: maxDay,
            consumedCIs: consumedCIs,
            consumedVarNames: consumedVarNames))

        nDetected += indices.len

    stderr.writeLine(&"[FZN] Detected {nDetected} int_lin_le → {tr.conditionalDayCapacityInfos.len} ConditionalDayCapacity constraints")


proc detectRedundantOrderings(tr: var FznTranslator) =
    ## Detects transitively redundant ordering constraints.
    ## Handles weighted edges: int_lin_le([-1,1], [a,b], -d) means b >= a + d (edge a→b weight d).
    ## Edge u→v weight w is redundant if there exists a path u→...→v with total weight >= w.
    type OrderEdge = object
        constraintIdx: int
        fromVar, toVar: string
        weight: int  # a + weight <= b

    var edges: seq[OrderEdge]
    var nameToId: Table[string, int]
    var idToName: seq[string]
    var nextId = 0

    proc getId(name: string): int =
        if name in nameToId:
            return nameToId[name]
        result = nextId
        nameToId[name] = nextId
        idToName.add(name)
        inc nextId

    # Collect ordering edges from int_lin_le with 2 variables
    # Patterns:
    #   [1,-1], [a,b], rhs  →  a - b <= rhs  →  a + (-rhs) <= b  →  edge a→b weight -rhs
    #   [-1,1], [a,b], rhs  →  -a + b <= rhs  →  b + (-rhs) <= a  →  edge b→a weight -rhs
    #   [c,-c], [a,b], rhs (c>0)  →  c(a-b) <= rhs  →  a - b <= rhs/c  →  edge a→b weight -rhs/c
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        if con.name != "int_lin_le":
            continue
        # Resolve coefficients
        var coeffs: seq[int]
        try:
            coeffs = tr.resolveIntArray(con.args[0])
        except CatchableError:
            continue
        if coeffs.len != 2:
            continue
        # Need one positive and one negative coefficient of same magnitude
        if not ((coeffs[0] > 0 and coeffs[1] < 0 and coeffs[0] == -coeffs[1]) or
                        (coeffs[0] < 0 and coeffs[1] > 0 and -coeffs[0] == coeffs[1])):
            continue
        # Resolve RHS
        var rhs: int
        try:
            rhs = tr.resolveIntArg(con.args[2])
        except CatchableError:
            continue
        # Compute weight: for coeffs [c,-c] with c>0: edge a→b weight -rhs/c
        let c = abs(coeffs[0])
        if c > 1 and rhs mod c != 0:
            continue  # Non-integer weight, skip
        let scaledRhs = rhs div c
        # Resolve variable names
        let varNames = tr.resolveVarNames(con.args[1])
        if varNames.len != 2:
            continue
        # Skip if either variable is defined (will be replaced by expression)
        if varNames[0] in tr.definedVarNames or varNames[1] in tr.definedVarNames:
            continue
        # Determine edge direction based on coefficient signs
        var fromVar, toVar: string
        if coeffs[0] > 0:
            # [+c, -c]: a - b <= rhs/c → a + (-rhs/c) <= b → edge a→b
            fromVar = varNames[0]
            toVar = varNames[1]
        else:
            # [-c, +c]: b - a <= rhs/c → b + (-rhs/c) <= a → edge b→a
            fromVar = varNames[1]
            toVar = varNames[0]
        let weight = -scaledRhs  # from + weight <= to
        discard getId(fromVar)
        discard getId(toVar)
        edges.add(OrderEdge(constraintIdx: ci, fromVar: fromVar, toVar: toVar, weight: weight))

    if edges.len == 0:
        return

    let n = nextId

    # Build adjacency: node → {successor → max weight}
    var succ = newSeq[Table[int, int]](n)
    for i in 0..<n:
        succ[i] = initTable[int, int]()
    # Map (from, to, weight) to constraint indices
    var edgeConstraints: Table[(int, int, int), seq[int]]
    for e in edges:
        let fromId = nameToId[e.fromVar]
        let toId = nameToId[e.toVar]
        # Keep max weight for adjacency
        if toId in succ[fromId]:
            succ[fromId][toId] = max(succ[fromId][toId], e.weight)
        else:
            succ[fromId][toId] = e.weight
        let key = (fromId, toId, e.weight)
        if key notin edgeConstraints:
            edgeConstraints[key] = @[]
        edgeConstraints[key].add(e.constraintIdx)

    # Compute in-degree for topological sort (Kahn's algorithm)
    var inDeg = newSeq[int](n)
    for i in 0..<n:
        for j in succ[i].keys:
            inDeg[j] += 1

    var queue: seq[int]
    for i in 0..<n:
        if inDeg[i] == 0:
            queue.add(i)

    var topoOrder: seq[int]
    var qi = 0
    while qi < queue.len:
        let u = queue[qi]
        inc qi
        topoOrder.add(u)
        for v in succ[u].keys:
            inDeg[v] -= 1
            if inDeg[v] == 0:
                queue.add(v)

    if topoOrder.len != n:
        # Graph has cycles — can't do transitive reduction, skip
        return

    # Compute longest-path distances bottom-up (reverse topological order)
    # dist[u][v] = longest path weight from u to v
    const NoPath = low(int) div 2  # Safe sentinel that won't overflow when added to a weight
    var dist = newSeq[Table[int, int]](n)
    for i in 0..<n:
        dist[i] = initTable[int, int]()

    for i in countdown(topoOrder.len - 1, 0):
        let u = topoOrder[i]
        for v, w in succ[u]:
            # Direct edge u→v
            dist[u][v] = max(dist[u].getOrDefault(v, NoPath), w)
            # Transitive: u→v→...→target
            for target, d in dist[v]:
                dist[u][target] = max(dist[u].getOrDefault(target, NoPath), w + d)

    # Mark redundant edges: edge u→v weight w is redundant if
    # there exists an intermediate node x (x≠v) with succ[u][x] + dist[x][v] >= w
    var redundantCount = 0
    for e in edges:
        let fromId = nameToId[e.fromVar]
        let toId = nameToId[e.toVar]
        var isRedundant = false
        # Check if any other neighbor provides a path with >= weight
        for x, wx in succ[fromId]:
            if x == toId:
                continue
            let pathWeight = wx + dist[x].getOrDefault(toId, NoPath)
            if pathWeight >= e.weight:
                isRedundant = true
                break
        # Also: if multiple constraints exist for the same (from, to) pair,
        # keep only the one with the largest weight
        if not isRedundant:
            let maxWeight = succ[fromId][toId]  # This is the max weight for this edge
            if e.weight < maxWeight:
                isRedundant = true  # A stronger constraint exists for this edge
        if isRedundant:
            tr.redundantOrderings.incl(e.constraintIdx)
            inc redundantCount

    if redundantCount > 0:
        stderr.writeLine(&"[FZN] Ordering reduction: {edges.len} -> {edges.len - redundantCount} constraints ({redundantCount} redundant)")

proc estimateRangeImpl(tr: FznTranslator, node: ExpressionNode[int],
                                              cache: var Table[pointer, (int, int)]): (int, int) =
    ## Conservative interval arithmetic to estimate the range of an expression.
    ## Returns (min, max) values the expression can take.
    ## Uses memoization cache to avoid exponential re-traversal of shared DAG nodes.
    let key = cast[pointer](node)
    if key in cache:
        return cache[key]
    var result: (int, int)
    case node.kind
    of LiteralNode:
        result = (node.value, node.value)
    of RefNode:
        let dom = tr.sys.baseArray.domain[node.position]
        if dom.len > 0:
            result = (dom[0], dom[^1])
        else:
            result = (low(int), high(int))
    of UnaryOpNode:
        let (cMin, cMax) = tr.estimateRangeImpl(node.target, cache)
        case node.unaryOp
        of Negation:
            result = (-cMax, -cMin)
        of AbsoluteValue:
            if cMin >= 0: result = (cMin, cMax)
            elif cMax <= 0: result = (-cMax, -cMin)
            else: result = (0, max(-cMin, cMax))
    of BinaryOpNode:
        let (lMin, lMax) = tr.estimateRangeImpl(node.left, cache)
        let (rMin, rMax) = tr.estimateRangeImpl(node.right, cache)
        case node.binaryOp
        of Addition:
            result = (lMin + rMin, lMax + rMax)
        of Subtraction:
            result = (lMin - rMax, lMax - rMin)
        of Multiplication:
            let products = [lMin*rMin, lMin*rMax, lMax*rMin, lMax*rMax]
            result = (min(products), max(products))
        of Maximum:
            result = (max(lMin, rMin), max(lMax, rMax))
        of Minimum:
            result = (min(lMin, rMin), min(lMax, rMax))
    cache[key] = result
    return result

proc estimateRange(tr: FznTranslator, node: ExpressionNode[int]): (int, int) =
    var cache = initTable[pointer, (int, int)]()
    tr.estimateRangeImpl(node, cache)


proc pruneZeroCapacityDays(tr: var FznTranslator) =
    ## Prune admission domains by detecting zero-capacity day constraints.
    ##
    ## Pattern: int_lin_le(coeffs, bool_vars, 0) where each bool_var is a
    ## channel encoding "selection[p] AND admission[p]==d" (surgeon capacity)
    ## or "selection[p] AND admission[p]==d AND ot[p]==o" (OT capacity).
    ##
    ## When capacity=0, no patient can be admitted on that day (for surgeon)
    ## or on that day+OT combo. For surgeon zero days, we directly prune
    ## the admission domain. For OT, we only prune if ALL OTs are zero on that day.

    # Step 1: Build defines_var map for chain tracing
    var definerOf: Table[string, int]  # varName → constraint index
    for ci, con in tr.model.constraints:
        if con.hasAnnotation("defines_var"):
            let ann = con.getAnnotation("defines_var")
            if ann.args.len > 0 and ann.args[0].kind == FznIdent:
                definerOf[ann.args[0].ident] = ci

    # Step 2: Find zero-capacity int_lin_le constraints and trace to find day values
    type CapInfo = object
        day: int
        isOtConstrained: bool  # true = OT-specific, false = surgeon (all OTs)

    var zeroCaps: seq[CapInfo]

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le":
            continue
        if con.args.len < 3:
            continue

        # Check RHS <= 0
        let rhsArg = con.args[2]
        if rhsArg.kind != FznIntLit or rhsArg.intVal > 0:
            continue

        # Check all coefficients are positive
        let coeffArg = con.args[0]
        if coeffArg.kind != FznArrayLit:
            continue
        var allPositive = true
        for elem in coeffArg.elems:
            if elem.kind != FznIntLit or elem.intVal <= 0:
                allPositive = false
                break
        if not allPositive:
            continue

        # Need many variables (capacity constraint spans all patients)
        let varsArg = con.args[1]
        if varsArg.kind != FznArrayLit or varsArg.elems.len < 5:
            continue

        # Trace first variable back: bool2int → array_bool_and → int_eq_reif
        let firstVar = varsArg.elems[0]
        if firstVar.kind != FznIdent or firstVar.ident notin definerOf:
            continue
        let b2iCon = tr.model.constraints[definerOf[firstVar.ident]]
        if stripSolverPrefix(b2iCon.name) != "bool2int" or b2iCon.args.len < 2:
            continue
        let boolVar = b2iCon.args[0]
        if boolVar.kind != FznIdent or boolVar.ident notin definerOf:
            continue
        let andCon = tr.model.constraints[definerOf[boolVar.ident]]
        if stripSolverPrefix(andCon.name) != "array_bool_and" or andCon.args.len < 2:
            continue
        let andInputs = andCon.args[0]
        if andInputs.kind != FznArrayLit:
            continue

        # Determine constraint type by AND input count:
        # 2 inputs = surgeon (sel + adm==d), 3 inputs = OT (sel + adm==d + ot==o)
        let isOtConstrained = andInputs.elems.len >= 3

        # Find int_eq_reif among the AND inputs to extract the day value
        var foundDay = -1
        for inp in andInputs.elems:
            if inp.kind != FznIdent or inp.ident notin definerOf:
                continue
            let eqCon = tr.model.constraints[definerOf[inp.ident]]
            if stripSolverPrefix(eqCon.name) != "int_eq_reif" or eqCon.args.len < 3:
                continue
            # int_eq_reif(var, constant, result) — we want the constant (day value)
            if eqCon.args[1].kind == FznIntLit:
                # Verify the first arg is an admission variable (has a non-tiny domain)
                let varArg = eqCon.args[0]
                if varArg.kind == FznIdent and varArg.ident in tr.varPositions:
                    let pos = tr.varPositions[varArg.ident]
                    let dom = tr.sys.baseArray.domain[pos]
                    if dom.len > 2:  # admission-like domain, not a boolean
                        foundDay = eqCon.args[1].intVal
                        break

        if foundDay >= 0:
            zeroCaps.add(CapInfo(day: foundDay, isOtConstrained: isOtConstrained))

    if zeroCaps.len == 0:
        return

    # Step 3: Determine which days to prune
    # Surgeon zero days (isOtConstrained=false) → directly prune
    # OT zero days (isOtConstrained=true) → only prune if ALL OT slots for that day are zero
    var surgeonZeroDays: PackedSet[int]
    var otZeroDayCount: Table[int, int]  # day → count of zero-capacity OT slots
    var otTotalPerDay: Table[int, int]   # day → total OT constraints for that day

    for cap in zeroCaps:
        if not cap.isOtConstrained:
            surgeonZeroDays.incl(cap.day)
        else:
            discard otZeroDayCount.mgetOrPut(cap.day, 0)
            otZeroDayCount[cap.day] += 1

    # Count total OT constraints per day from ALL int_lin_le (not just zero ones)
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_le":
            continue
        if con.args.len < 3:
            continue
        let varsArg = con.args[1]
        if varsArg.kind != FznArrayLit or varsArg.elems.len < 5:
            continue
        # Quick trace to check if this is an OT constraint
        let firstVar = varsArg.elems[0]
        if firstVar.kind != FznIdent or firstVar.ident notin definerOf:
            continue
        let b2iCon = tr.model.constraints[definerOf[firstVar.ident]]
        if stripSolverPrefix(b2iCon.name) != "bool2int" or b2iCon.args.len < 2:
            continue
        let boolVar = b2iCon.args[0]
        if boolVar.kind != FznIdent or boolVar.ident notin definerOf:
            continue
        let andCon = tr.model.constraints[definerOf[boolVar.ident]]
        if stripSolverPrefix(andCon.name) != "array_bool_and" or andCon.args.len < 2:
            continue
        let andInputs = andCon.args[0]
        if andInputs.kind != FznArrayLit or andInputs.elems.len < 3:
            continue
        # This is an OT constraint — find its day
        for inp in andInputs.elems:
            if inp.kind != FznIdent or inp.ident notin definerOf:
                continue
            let eqCon = tr.model.constraints[definerOf[inp.ident]]
            if stripSolverPrefix(eqCon.name) != "int_eq_reif" or eqCon.args.len < 3:
                continue
            if eqCon.args[1].kind == FznIntLit:
                let varArg = eqCon.args[0]
                if varArg.kind == FznIdent and varArg.ident in tr.varPositions:
                    let pos = tr.varPositions[varArg.ident]
                    let dom = tr.sys.baseArray.domain[pos]
                    if dom.len > 2:
                        let day = eqCon.args[1].intVal
                        discard otTotalPerDay.mgetOrPut(day, 0)
                        otTotalPerDay[day] += 1
                        break

    # Days where ALL OTs have zero capacity
    var otFullyZeroDays: PackedSet[int]
    for day, zeroCount in otZeroDayCount:
        if day in otTotalPerDay and zeroCount >= otTotalPerDay[day]:
            otFullyZeroDays.incl(day)

    let pruneDays = surgeonZeroDays + otFullyZeroDays
    if pruneDays.len == 0:
        return

    # Step 4: Prune admission variable domains
    if "admission" notin tr.arrayPositions:
        return

    let admPositions = tr.arrayPositions["admission"]
    var totalPruned = 0
    for pos in admPositions:
        if pos < 0: continue  # constant placeholder
        var domain = tr.sys.baseArray.domain[pos]
        var newDomain: seq[int]
        for v in domain:
            if v notin pruneDays:
                newDomain.add(v)
        if newDomain.len < domain.len:
            totalPruned += domain.len - newDomain.len
            tr.sys.baseArray.domain[pos] = newDomain

    var dayList: seq[int]
    for d in pruneDays.items:
        dayList.add(d)
    dayList.sort()
    stderr.writeLine(&"[FZN] Zero-capacity day pruning: removed {totalPruned} values from {admPositions.len} admission vars (zero days: {dayList})")


proc detectDormantPositions(tr: var FznTranslator) =
    ## Detects don't-care (dormant) positions in diffnK constraints.
    ## When a box's sizes are all case-analysis channels that equal zero for most
    ## selector values, the corresponding position variables are irrelevant
    ## (dormant) whenever the selector doesn't match. This dramatically reduces
    ## the effective search space for problems like products-and-shelves.

    # Build reverse map: channel position → (selectorPos, activeValue)
    # Only for single-source case-analysis channels where exactly one selector value
    # produces a non-zero result.
    var channelToSelector: Table[int, tuple[selectorPos: int, activeValue: int]]

    for def in tr.caseAnalysisDefs:
        if def.sourceVarNames.len != 1: continue
        if def.targetVarName notin tr.varPositions: continue
        let channelPos = tr.varPositions[def.targetVarName]
        let srcName = def.sourceVarNames[0]
        if srcName notin tr.varPositions: continue
        let selectorPos = tr.varPositions[srcName]

        # Find which selector values produce non-zero outputs
        var nonZeroIndices: seq[int]
        for i, v in def.lookupTable:
            if v != 0:
                nonZeroIndices.add(i)
        # Dormancy only works if exactly one selector value produces non-zero
        if nonZeroIndices.len != 1: continue
        let activeValue = nonZeroIndices[0] + def.domainOffsets[0]
        channelToSelector[channelPos] = (selectorPos: selectorPos, activeValue: activeValue)

    if channelToSelector.len == 0: return

    # Scan diffnK constraints for boxes where all size dimensions are controlled channels
    var nDormant = 0
    var dormantPositions: PackedSet[int]  # avoid duplicates
    for cons in tr.sys.baseArray.constraints:
        if cons.stateType != DiffnKType: continue
        let dk = cons.diffnKState
        for boxI in 0..<dk.n:
            var allSizeChannel = true
            var selectorPos = -1
            var activeValue = -1
            var consistent = true

            for d in 0..<dk.k:
                let sizeExpr = dk.sizeExprs[boxI][d]
                # Size expression must reference exactly one position
                if sizeExpr.positions.len != 1:
                    allSizeChannel = false
                    break
                var sizePos = -1
                for p in sizeExpr.positions.items:
                    sizePos = p
                    break
                # That position must be a known channel with selector info
                if sizePos notin channelToSelector:
                    allSizeChannel = false
                    break
                let info = channelToSelector[sizePos]
                if d == 0:
                    selectorPos = info.selectorPos
                    activeValue = info.activeValue
                elif info.selectorPos != selectorPos or info.activeValue != activeValue:
                    consistent = false
                    break

            if not allSizeChannel or not consistent or selectorPos < 0:
                continue

            # All k size dimensions are channels controlled by the same selector.
            # Mark the k position expressions as dormant.
            for d in 0..<dk.k:
                let posExpr = dk.posExprs[boxI][d]
                if posExpr.positions.len != 1: continue
                var posPos = -1
                for p in posExpr.positions.items:
                    posPos = p
                    break
                # Only mark non-channel, non-fixed search positions
                if posPos in tr.sys.baseArray.channelPositions: continue
                if posPos in tr.sys.baseArray.fixedPositions: continue
                if posPos in dormantPositions: continue
                dormantPositions.incl(posPos)
                let bi = tr.sys.baseArray.dormancyBindings.len
                tr.sys.baseArray.dormancyBindings.add(
                    (dormantPos: posPos, selectorPos: selectorPos, activeValue: activeValue))
                tr.sys.baseArray.dormancyAtSelector.mgetOrPut(selectorPos, @[]).add(bi)
                nDormant += 1

    if nDormant > 0:
        stderr.writeLine(&"[FZN] Detected {nDormant} dormant positions (diffnK don't-care placements)")


proc detectMultiResourceNoOverlapPairs*(tr: var FznTranslator) =
    ## Detects groups of bool_clause([], [a, b, c]) where:
    ##   - c is an overlap variable (channel or search var)
    ##   - a, b are assignment boolean variables
    ## Multiple clauses sharing the same c variable are grouped into a single
    ## MultiResourceNoOverlapConstraint.
    ##
    ## Pattern: for each resource r: NOT(assign[i,r] AND assign[j,r] AND overlap[i,j])
    ## Encoded as: bool_clause([], [assign[i,r], assign[j,r], overlap[i,j]])
    ##
    ## Grouping by overlap variable consolidates ~21 clauses per pair into 1 constraint.

    # Step 1: Collect all bool_clause([], [a, b, c]) with exactly 3 negative literals
    type ClauseInfo = object
        ci: int
        neg0, neg1, neg2: string  # the three negative literal variable names

    var threeNegClauses: seq[ClauseInfo]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 0 or negArg.elems.len != 3: continue
        let n0 = negArg.elems[0]
        let n1 = negArg.elems[1]
        let n2 = negArg.elems[2]
        if n0.kind != FznIdent or n1.kind != FznIdent or n2.kind != FznIdent: continue
        threeNegClauses.add(ClauseInfo(ci: ci, neg0: n0.ident, neg1: n1.ident, neg2: n2.ident))

    if threeNegClauses.len == 0: return

    # Step 2: Group by the third variable (overlap variable)
    # The third variable is the shared overlap variable. It can be a search variable,
    # an overlap channel, or any bool variable that appears in the third position
    # of multiple 3-negative-literal clauses.
    # Group: overlapVar → seq[(assignA, assignB, constraintIdx)]
    var groups: Table[string, seq[(string, string, int)]]
    for info in threeNegClauses:
        let overlapVar = info.neg2
        # First two are assign variables
        groups.mgetOrPut(overlapVar, @[]).add((info.neg0, info.neg1, info.ci))

    if groups.len == 0: return

    # Step 3: For each group with multiple clauses, create a MultiResourceNoOverlap info
    var totalClauses = 0
    for overlapVar, clauses in groups:
        if clauses.len < 2: continue  # not worth grouping single clauses

        var assignPairNames: seq[(string, string)]
        var consumedCIs: seq[int]
        for (a, b, ci) in clauses:
            assignPairNames.add((a, b))
            consumedCIs.add(ci)

        tr.multiResourceNoOverlapInfos.add((
            overlapVarName: overlapVar,
            assignPairNames: assignPairNames,
            consumedCIs: consumedCIs))

        # Consume the individual bool_clause constraints
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)
        totalClauses += consumedCIs.len

    if tr.multiResourceNoOverlapInfos.len > 0:
        stderr.writeLine(&"[FZN] Detected {tr.multiResourceNoOverlapInfos.len} multi-resource no-overlap pairs " &
                                          &"(from {totalClauses} bool_clause constraints)")

