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

proc getDomainBounds*(tr: var FznTranslator, varName: string):
    tuple[domain: seq[int], lo: int, hi: int] =
    ## Looks up a variable's domain and returns (domain, lo, hi).
    ## Returns empty domain if not found. Domain must be sorted.
    let domain = tr.lookupVarDomain(varName)
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

# --- Bool clause helpers ---

proc extractBoolClauseLiterals*(con: FznConstraint):
    tuple[ok: bool, posElems: seq[FznExpr], negElems: seq[FznExpr]] =
    ## Extracts positive and negative literal arrays from a bool_clause constraint.
    ## Returns (ok=false, ...) if args aren't both FznArrayLit.
    result.ok = false
    if con.args.len < 2: return
    if con.args[0].kind != FznArrayLit or con.args[1].kind != FznArrayLit: return
    result = (ok: true, posElems: con.args[0].elems, negElems: con.args[1].elems)

# --- Logging ---

template logBuilt*(label: string, count: int, tr: FznTranslator) =
    ## Logs the number of items built with the standard [FZN] prefix.
    if count > 0:
        stderr.writeLine(&"[FZN] Built {count} {label} (total channels: {tr.sys.baseArray.channelBindings.len})")
