## Included from translator.nim -- not a standalone module.
## Shared helper procs used across multiple translator sub-modules.

# --- Domain lookup infrastructure (moved from translatorChannels.nim) ---

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

# --- FZN-level alias canonicalization ---

proc canonicalizeFznVarAliases*(tr: var FznTranslator) =
    ## Resolves FZN-level variable aliases (`var X = Y;`) by substituting canonical
    ## names everywhere in the model. The MZN flattener emits these aliases when CSE
    ## merges parallel definitions of the same value (e.g., two `defines_var` element
    ## constraints that compute the same logical value via different routes).
    ##
    ## Without this canonicalization, downstream passes would create separate positions
    ## for each aliased name and lose the implicit equality the alias is asserting,
    ## breaking the model. After this pass, no constraint or array decl references the
    ## alias name; the alias-side defining constraints (if any) are demoted to regular
    ## constraints so they enforce their underlying equation against the canonical's
    ## position.

    # Step 1: Build alias parent map from `var X = Y;` (FznIdent value) decls.
    var aliasOf = initTable[string, string]()
    for decl in tr.model.variables:
        if decl.isArray: continue
        if decl.value != nil and decl.value.kind == FznIdent:
            aliasOf[decl.name] = decl.value.ident

    if aliasOf.len == 0:
        return

    # Step 2: Path-compressing chain resolution (cycle-safe). Returns the canonical
    # name at the end of the alias chain.
    proc canonical(name: string): string =
        var cur = name
        var depth = 0
        while cur in aliasOf and depth < 64:
            let next = aliasOf[cur]
            if next == cur: break
            cur = next
            inc depth
        return cur

    # Step 3: In-place substitution helper. FznExpr is a ref object so we can mutate.
    proc substituteExpr(e: FznExpr) =
        if e.isNil: return
        case e.kind
        of FznIdent:
            let canon = canonical(e.ident)
            if canon != e.ident:
                e.ident = canon
        of FznArrayLit:
            for elem in e.elems:
                substituteExpr(elem)
        of FznAnnotationExpr:
            for elem in e.annArgs:
                substituteExpr(elem)
        else:
            discard

    # Step 4: Substitute aliased identifiers in all constraint args and annotations.
    for ci in 0..<tr.model.constraints.len:
        for arg in tr.model.constraints[ci].args:
            substituteExpr(arg)
        for ann in tr.model.constraints[ci].annotations:
            for annArg in ann.args:
                substituteExpr(annArg)

    # Step 5: Substitute in variable array declarations
    # (e.g., `array of var: A = [a, b, X_INTRODUCED_21_, ...]`).
    for di in 0..<tr.model.variables.len:
        if tr.model.variables[di].isArray and
             tr.model.variables[di].value != nil:
            substituteExpr(tr.model.variables[di].value)
        # Also walk annotation args on variable decls (rare but possible)
        for ann in tr.model.variables[di].annotations:
            for annArg in ann.args:
                substituteExpr(annArg)

    # Step 6: Substitute in solve directive (objective var + search annotations).
    if tr.model.solve.objective != nil:
        substituteExpr(tr.model.solve.objective)
    for ann in tr.model.solve.annotations:
        for annArg in ann.args:
            substituteExpr(annArg)

    # Step 7: After substitution, multiple constraints may now declare
    # `defines_var(canonical)` for the same canonical name. The MZN flattener emits
    # these parallel defining constraints to assert that two computation routes
    # produce the same value, and aliases their results. Pick the FIRST encountered
    # as the canonical channel definer; demote the rest to regular constraints by
    # stripping their `defines_var` annotation. The demoted constraints remain in
    # the model and are enforced as regular constraints against their input vars,
    # ensuring the implicit equality the alias was asserting is actually checked
    # by the search.
    var firstDefiner = initTable[string, int]()
    var nDemoted = 0
    for ci in 0..<tr.model.constraints.len:
        if not tr.model.constraints[ci].hasAnnotation("defines_var"): continue
        var defName = ""
        for ann in tr.model.constraints[ci].annotations:
            if ann.name == "defines_var" and ann.args.len > 0 and
                 ann.args[0].kind == FznIdent:
                defName = ann.args[0].ident
                break
        if defName == "": continue
        if defName notin firstDefiner:
            firstDefiner[defName] = ci
        else:
            # Demote: remove the defines_var annotation in place.
            var newAnns: seq[FznAnnotation]
            for ann in tr.model.constraints[ci].annotations:
                if ann.name != "defines_var":
                    newAnns.add(ann)
            tr.model.constraints[ci].annotations = newAnns
            inc nDemoted
    # Step 8: Save the chain-resolved alias map for translateVariables and the output
    # formatter to use when looking up positions for aliased names.
    for aliasName in aliasOf.keys:
        let canon = canonical(aliasName)
        if canon != aliasName:
            tr.fznVarAliases[aliasName] = canon

    stderr.writeLine(&"[FZN] Canonicalized {tr.fznVarAliases.len} FZN variable aliases ({nDemoted} redundant parallel defining constraints demoted)")

# --- Variable name extraction ---

func containsIdent*(expr: FznExpr, name: string): bool =
    ## Recursively checks whether a FznExpr tree contains a FznIdent with the given name.
    if expr.isNil: return false
    case expr.kind
    of FznIdent:
        return expr.ident == name
    of FznArrayLit:
        for e in expr.elems:
            if e.containsIdent(name): return true
    of FznAnnotationExpr:
        for e in expr.annArgs:
            if e.containsIdent(name): return true
    else:
        discard

proc extractVarNames*(tr: FznTranslator, arrExpr: FznExpr): seq[string] =
    ## Extracts variable names from an array expression.
    ## If arrExpr is an FznArrayLit, extracts .ident from each element (all must be FznIdent).
    ## If arrExpr is an FznIdent referencing a known array, returns the element names.
    ## Returns empty seq if extraction fails.
    case arrExpr.kind
    of FznArrayLit:
        result = newSeq[string](arrExpr.elems.len)
        for i, e in arrExpr.elems:
            if e.kind != FznIdent:
                return @[]
            result[i] = e.ident
    of FznIdent:
        if arrExpr.ident in tr.arrayElementNames:
            return tr.arrayElementNames[arrExpr.ident]
        return @[]
    else:
        return @[]

# --- Expression resolution ---

proc resolveVarOrExpr*(tr: FznTranslator, name: string): AlgebraicExpression[int] =
    ## Resolves a variable name to its AlgebraicExpression.
    ## Checks definedVarExprs first (defined variables), then varPositions (search variables).
    ## Raises KeyError if the name is not found in either.
    if name in tr.definedVarExprs:
        return tr.definedVarExprs[name]
    elif name in tr.varPositions:
        return tr.getExpr(tr.varPositions[name])
    else:
        raise newException(KeyError, &"Unknown variable '{name}' — not in varPositions or definedVarExprs")

# --- Domain bounds helpers ---

proc lookupTightenedDomain*(tr: var FznTranslator, varName: string): seq[int] =
    ## Look up a variable's domain, preferring the presolve-tightened domain
    ## (`tr.presolveDomains`) over the raw FZN declaration.
    if varName in tr.presolveDomains:
        return tr.presolveDomains[varName]
    return tr.lookupVarDomain(varName)

proc getDomainBounds*(tr: var FznTranslator, varName: string):
    tuple[domain: seq[int], lo: int, hi: int] =
    ## Looks up a variable's domain and returns (domain, lo, hi).
    ## Returns empty domain if not found. Domain must be sorted.
    let domain = tr.lookupVarDomain(varName)
    if domain.len == 0:
        return (@[], 0, 0)
    return (domain, domain[0], domain[^1])

proc getTightenedBounds*(tr: var FznTranslator, varName: string):
    tuple[domain: seq[int], lo: int, hi: int] =
    ## Same as getDomainBounds but consults presolve-tightened domains first.
    let domain = tr.lookupTightenedDomain(varName)
    if domain.len == 0:
        return (@[], 0, 0)
    return (domain, domain[0], domain[^1])

proc getActualDomainBounds*(tr: var FznTranslator, expr: AlgebraicExpression[int],
                            identName: string):
    tuple[domain: seq[int], lo: int, hi: int] =
    ## Resolves the actual domain for an expression (accounting for aliasing) and returns bounds.
    ## Returns empty domain if not found.
    let domain = tr.resolveActualDomain(expr, identName)
    if domain.len == 0:
        return (@[], 0, 0)
    return (domain, domain[0], domain[^1])

# --- Lookup table construction ---

proc buildConstLookupTable*(lo, hi: int, f: proc(v: int): int): seq[ArrayElement[int]] =
    ## Builds a constant lookup table of ArrayElement[int] for values lo..hi using f(v).
    result = newSeq[ArrayElement[int]](hi - lo + 1)
    for v in lo..hi:
        result[v - lo] = ArrayElement[int](isConstant: true, constantValue: f(v))

proc buildConstLookupTable2D*(loX, hiX, loY, hiY: int,
                               f: proc(vx, vy: int): int): seq[ArrayElement[int]] =
    ## Builds a constant 2D lookup table (row-major: x outer, y inner) using f(vx, vy).
    let rangeX = hiX - loX + 1
    let rangeY = hiY - loY + 1
    result = newSeq[ArrayElement[int]](rangeX * rangeY)
    for vx in loX..hiX:
        for vy in loY..hiY:
            let idx = (vx - loX) * rangeY + (vy - loY)
            result[idx] = ArrayElement[int](isConstant: true, constantValue: f(vx, vy))

proc make2DIndex*(exprA, exprB: AlgebraicExpression[int],
                  loA, loB, rangeB: int): AlgebraicExpression[int] =
    ## Builds a 2D index expression: (exprA - loA) * rangeB + (exprB - loB).
    (exprA - loA) * rangeB + (exprB - loB)

# --- Sparse clamp index for reified comparison channels ---

proc constLitExpr*(value: int): AlgebraicExpression[int] {.inline.} =
    ## Builds a constant literal AlgebraicExpression with no positions.
    newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: value),
        linear = true)

proc buildSignClampIndex*(diffExpr: AlgebraicExpression[int]): AlgebraicExpression[int] =
    ## Builds a 3-valued sign-clamp index from a difference expression:
    ##   index = clamp(diffExpr, -1, 1) + 1   ∈  {0, 1, 2}
    ##     0 when diffExpr < 0   (LT)
    ##     1 when diffExpr == 0  (EQ)
    ##     2 when diffExpr > 0   (GT)
    ## Used for sparse 3-entry channels for reified comparisons (int_eq_reif,
    ## int_ne_reif, int_le_reif, int_lt_reif, int_lin_eq_reif) when the source
    ## domain is too large for a dense lookup table. The index is non-linear
    ## (uses Maximum/Minimum) but the underlying eval is cheap.
    binaryMin(binaryMax(diffExpr, constLitExpr(-1)), constLitExpr(1)) + 1

# --- Bool clause helpers ---

proc extractBoolClauseLiterals*(con: FznConstraint):
    tuple[ok: bool, posElems: seq[FznExpr], negElems: seq[FznExpr]] =
    ## Extracts positive and negative literal arrays from a bool_clause constraint.
    ## Returns (ok=false, ...) if args aren't both FznArrayLit.
    result.ok = false
    if con.args.len < 2: return
    if con.args[0].kind != FznArrayLit or con.args[1].kind != FznArrayLit: return
    result = (ok: true, posElems: con.args[0].elems, negElems: con.args[1].elems)

# --- Subset-sum reachability (used by bin_packing_load presolve, linear-sum
#     reachable-values presolve, and anywhere we need the set of achievable
#     values of Σ cᵢ·xᵢ where each xᵢ has a small discrete domain). ---

proc computeReachableSums*(termDomains: seq[seq[int]], limit: int): HashSet[int] =
    ## Return the set of all achievable values of the sum `Σᵢ t[i]` where each
    ## `t[i]` independently ranges over the values in `termDomains[i]`.
    ## Aborts (returning an empty set) if the set of reachable sums exceeds `limit`
    ## at any point — callers should treat an empty return as "skip tightening".
    ## Empty `termDomains[i]` (no choices) contributes 0 for convenience so the
    ## helper can't be poisoned by degenerate inputs.
    result = initHashSet[int]()
    result.incl(0)
    for vals in termDomains:
        if vals.len == 0: continue
        # Dedup the offsets so we don't blow up when the same value appears twice.
        var distinctVals: seq[int]
        var seen = initHashSet[int]()
        for v in vals:
            if v notin seen:
                seen.incl(v)
                distinctVals.add(v)
        if distinctVals.len == 1 and distinctVals[0] == 0:
            continue  # term is forced to zero, no branching
        var nextSums = initHashSet[int](result.len * distinctVals.len)
        for s in result:
            for v in distinctVals:
                nextSums.incl(s + v)
                if nextSums.len > limit:
                    return initHashSet[int]()
        result = nextSums

proc reachableWeightedSums*(weights: seq[int], limit: int): HashSet[int] =
    ## Convenience wrapper for Σ wᵢ·bᵢ where each bᵢ ∈ {0,1} (i.e. the classic
    ## subset-sum set), used by bin_packing_load.
    var termDoms = newSeq[seq[int]](weights.len)
    for i, w in weights:
        termDoms[i] = @[0, w]
    return computeReachableSums(termDoms, limit)

# --- Logging ---

template logBuilt*(label: string, count: int, tr: FznTranslator) =
    ## Logs the number of items built with the standard [FZN] prefix.
    if count > 0:
        stderr.writeLine(&"[FZN] Built {count} {label} (total channels: {tr.sys.baseArray.channelBindings.len})")
