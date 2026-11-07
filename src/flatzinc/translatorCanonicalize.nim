## Included from translator.nim -- not a standalone module.
## Pre-translation canonicalization passes that rewrite the FZN constraint list
## into more uniform shapes BEFORE any pattern detection or presolve runs.
##
## These rewrites are general (apply to any FZN model) — they don't depend on
## semantic information, just on the shape of the linear reification.

func crFloorDiv(a, b: int): int {.inline.} =
    ## floor(a / b) for b != 0
    if b > 0:
        if a >= 0: a div b else: -((-a + b - 1) div b)
    else:
        # b < 0: floor(a / b) = -ceil(a / -b) = -((a + (-b) - 1) div (-b))
        let nb = -b
        if a >= 0: -((a + nb - 1) div nb)
        else: (-a) div nb

func crCeilDiv(a, b: int): int {.inline.} =
    ## ceil(a / b) for b != 0
    if b > 0:
        if a >= 0: (a + b - 1) div b else: -((-a) div b)
    else:
        let nb = -b
        if a >= 0: -(a div nb)
        else: ((-a) + nb - 1) div nb

proc cnClassifySingleTerm(tr: FznTranslator, coeffsArg, varsArg: FznExpr,
                          rhsVal: int): tuple[ok: bool, theVar: FznExpr,
                                               coeff: int, adjRhs: int] =
    ## If `sum(coeffs[i] * vars[i])` reduces to `coeff * theVar + offset` with
    ## exactly one true variable (others being parameters / int literals),
    ## return (true, theVar, coeff, rhsVal - offset). Otherwise (false, ...).
    result.ok = false
    let coeffs = try: tr.resolveIntArray(coeffsArg)
                 except ValueError, KeyError: return
    let varElems = tr.resolveVarArrayElems(varsArg)
    if coeffs.len != varElems.len or coeffs.len == 0: return
    var nVars = 0
    var coeff = 0
    var theVar: FznExpr
    var constOffset = 0
    for i in 0..<coeffs.len:
        let v = varElems[i]
        case v.kind
        of FznIntLit:
            constOffset += coeffs[i] * v.intVal
        of FznBoolLit:
            constOffset += coeffs[i] * (if v.boolVal: 1 else: 0)
        of FznIdent:
            if v.ident in tr.paramValues:
                constOffset += coeffs[i] * tr.paramValues[v.ident]
            else:
                inc nVars
                if nVars > 1: return
                theVar = v
                coeff = coeffs[i]
        else:
            return
    if nVars != 1 or coeff == 0: return
    result = (ok: true, theVar: theVar, coeff: coeff,
              adjRhs: rhsVal - constOffset)

proc canonicalizeLinearReifs(tr: var FznTranslator) =
    ## Fold single-variable `int_lin_{eq,ne,le}_reif` into the corresponding
    ## primitive `int_{eq,ne,le}_reif`. Multi-variable linear reifs are left
    ## alone. Constants and parameters in the variable array are absorbed
    ## into the right-hand side. Coefficients other than ±1 are handled too:
    ##
    ##   int_lin_eq_reif([c],[x],k,b)  with c|k → int_eq_reif(x, k/c, b)
    ##   int_lin_ne_reif([c],[x],k,b)  with c|k → int_ne_reif(x, k/c, b)
    ##   int_lin_le_reif([c],[x],k,b), c > 0    → int_le_reif(x, floor(k/c), b)
    ##   int_lin_le_reif([c],[x],k,b), c < 0    → int_le_reif(intLit(ceil(k/c)), x, b)
    ##
    ## Cases where eq-coefficient does not divide the rhs are left alone — the
    ## existing presolve catches the resulting domain pruning. Annotations
    ## (including `defines_var`) are preserved on the rewritten constraint so
    ## downstream defining-var detection still finds it.
    var nFolded = 0
    var nEq = 0
    var nNe = 0
    var nLe = 0
    for ci in 0..<tr.model.constraints.len:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif" and name != "int_lin_ne_reif" and
           name != "int_lin_le_reif": continue
        if con.args.len < 4: continue
        # rhs must be a constant — if it's a var the FZN spec doesn't allow it
        # for the standard reified primitives anyway
        let rhsVal = try: tr.resolveIntArg(con.args[2])
                     except ValueError, KeyError: continue
        let info = tr.cnClassifySingleTerm(con.args[0], con.args[1], rhsVal)
        if not info.ok: continue
        # The bool result must be a real var (FznIdent) — keep BoolLit cases
        # alone so the existing tautology handling in core.nim runs.
        if con.args[3].kind != FznIdent and con.args[3].kind != FznBoolLit: continue

        case name
        of "int_lin_eq_reif":
            if info.adjRhs mod info.coeff != 0:
                # No integer solution → b forced to 0. Leave to presolve.
                continue
            let v = info.adjRhs div info.coeff
            tr.model.constraints[ci].name = "int_eq_reif"
            tr.model.constraints[ci].args = @[
                info.theVar,
                FznExpr(kind: FznIntLit, intVal: v),
                con.args[3]
            ]
            inc nEq; inc nFolded
        of "int_lin_ne_reif":
            if info.adjRhs mod info.coeff != 0:
                # No integer solution → ne always true → b forced to 1.
                # Leave to presolve.
                continue
            let v = info.adjRhs div info.coeff
            tr.model.constraints[ci].name = "int_ne_reif"
            tr.model.constraints[ci].args = @[
                info.theVar,
                FznExpr(kind: FznIntLit, intVal: v),
                con.args[3]
            ]
            inc nNe; inc nFolded
        of "int_lin_le_reif":
            if info.coeff > 0:
                # c > 0:  c*x ≤ k  ⟺  x ≤ floor(k/c)
                let bound = crFloorDiv(info.adjRhs, info.coeff)
                tr.model.constraints[ci].name = "int_le_reif"
                tr.model.constraints[ci].args = @[
                    info.theVar,
                    FznExpr(kind: FznIntLit, intVal: bound),
                    con.args[3]
                ]
            else:
                # c < 0:  c*x ≤ k  ⟺  x ≥ ceil(k/c)  ⟺  ceil(k/c) ≤ x
                let bound = crCeilDiv(info.adjRhs, info.coeff)
                tr.model.constraints[ci].name = "int_le_reif"
                tr.model.constraints[ci].args = @[
                    FznExpr(kind: FznIntLit, intVal: bound),
                    info.theVar,
                    con.args[3]
                ]
            inc nLe; inc nFolded
        else: discard
    if nFolded > 0:
        stderr.writeLine(&"[FZN] Canonicalized {nFolded} single-term linear reifs → primitive reifs (eq={nEq} ne={nNe} le={nLe})")


proc splitImplicationConjunctions(tr: var FznTranslator) =
    ## Rewrite the implication  cond -> (c1 /\ ... /\ ck), i.e.
    ##   bool_clause([cond', A], [])  or  bool_clause([A], [cond])
    ## with A <-> array_bool_and(c1..ck) used only there, into k implications
    ## cond -> cj (appended; the original clause is consumed). Sound, and exposes
    ## cond -> (target == value) to the case-analysis detector, e.g.
    ##   demand_end_job[d] = j  ->  (produced[j] >= total /\ demand_end[d] = end[j]).
    ## Conservative: only two-literal clauses whose condition is an eq/ne
    ## reification of a variable against a constant, and only clauses no earlier
    ## detector consumed (AND structure matters to the disjunctive-clause and
    ## conditional-source detectors). Runs late, so it appends instead of
    ## re-indexing the constraint list.
    if existsEnv("CRUSHER_NO_SPLIT"): return
    var useCount: CountTable[string]
    for con in tr.model.constraints:
        for arg in con.args:
            if arg.kind == FznIdent: useCount.inc(arg.ident)
            elif arg.kind == FznArrayLit:
                for e in arg.elems:
                    if e.kind == FznIdent: useCount.inc(e.ident)
    for decl in tr.model.variables:
        if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
            for e in decl.value.elems:
                if e.kind == FznIdent: useCount.inc(e.ident)
    var andDef: Table[string, int]
    var condReif: HashSet[string]     # outputs of int_eq_reif / int_ne_reif(var, const)
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if not con.hasAnnotation("defines_var"): continue
        if name == "array_bool_and" and con.args.len >= 2 and con.args[1].kind == FznIdent:
            andDef[con.args[1].ident] = ci
        elif name in ["int_eq_reif", "int_ne_reif"] and con.args.len >= 3 and
             con.args[0].kind == FznIdent and con.args[2].kind == FznIdent:
            let isConst = con.args[1].kind == FznIntLit or
                          (con.args[1].kind == FznIdent and con.args[1].ident in tr.paramValues)
            if isConst: condReif.incl(con.args[2].ident)
    if andDef.len == 0: return

    var usedAnd: HashSet[string]
    var added: seq[FznConstraint]
    var nSplit = 0
    let nOrig = tr.model.constraints.len
    for ci in 0 ..< nOrig:
        if ci in tr.definingConstraints: continue
        let con = tr.model.constraints[ci]
        if stripSolverPrefix(con.name) != "bool_clause" or con.args.len < 2: continue
        if con.args[0].kind != FznArrayLit or con.args[1].kind != FznArrayLit: continue
        let pos = con.args[0].elems
        let neg = con.args[1].elems
        if pos.len + neg.len != 2: continue
        var a, cond = ""
        var condIsNeg = false
        for e in pos:
            if e.kind != FznIdent: continue
            if e.ident in andDef and a == "": a = e.ident
            elif e.ident in condReif: cond = e.ident
        for e in neg:
            if e.kind == FznIdent and e.ident in condReif:
                cond = e.ident
                condIsNeg = true
        if a == "" or cond == "" or a in usedAnd: continue
        if useCount.getOrDefault(a) != 2: continue
        let andCI = andDef[a]
        if andCI in tr.definingConstraints: continue
        let lits = tr.resolveVarArrayElems(tr.model.constraints[andCI].args[0])
        var ok = lits.len >= 2
        for l in lits:
            if l.kind != FznIdent: ok = false
        if not ok: continue
        let condExpr = FznExpr(kind: FznIdent, ident: cond)
        for l in lits:
            let posElems = if condIsNeg: @[l] else: @[l, condExpr]
            let negElems = if condIsNeg: @[condExpr] else: newSeq[FznExpr]()
            added.add(FznConstraint(name: con.name,
                args: @[FznExpr(kind: FznArrayLit, elems: posElems),
                        FznExpr(kind: FznArrayLit, elems: negElems)],
                annotations: con.annotations))
        usedAnd.incl(a)
        tr.definingConstraints.incl(ci)   # original clause replaced by the split ones
        inc nSplit
    if nSplit == 0: return
    for c in added: tr.model.constraints.add(c)
    stderr.writeLine("[FZN] Split " & $nSplit & " implication conjunctions into " &
                     $added.len & " clauses")


proc eliminateDeadDefinitions(tr: var FznTranslator) =
    ## Consume `defines_var(b)` constraints whose output is read by no other live
    ## constraint and is not output / the objective (fixpoint: chains of dead
    ## reifications die together). Earlier detectors that consume a constraint
    ## often leave the reifications feeding it behind; translated, those become
    ## junk search variables with constraints the search keeps "repairing".
    var keep: HashSet[string]
    for decl in tr.model.variables:
        if decl.hasAnnotation("output_var"): keep.incl(decl.name)
        if decl.isArray and decl.hasAnnotation("output_array") and decl.value != nil and
           decl.value.kind == FznArrayLit:
            for e in decl.value.elems:
                if e.kind == FznIdent: keep.incl(e.ident)
    if tr.model.solve.objective != nil and tr.model.solve.objective.kind == FznIdent:
        keep.incl(tr.model.solve.objective.ident)
    for v in tr.annotatedSearchVarNames: keep.incl(v)
    # Array declarations referenced by name count as uses of their elements
    var arrElems: Table[string, seq[string]]
    for decl in tr.model.variables:
        if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
            var names: seq[string]
            for e in decl.value.elems:
                if e.kind == FznIdent: names.add(e.ident)
            arrElems[decl.name] = names
    # Dropping a definition is sound only when it is total: every assignment of
    # its inputs has a matching value of b. Reifications are (b is a free bool);
    # functional int definitions are only when b's declared domain is unbounded
    # (`var 0..5: b = x + y` restricts x + y). Partial ones (int_div, element)
    # are never dropped.
    var declType: Table[string, FznTypeKind]
    for decl in tr.model.variables:
        if decl.isVar and not decl.isArray: declType[decl.name] = decl.varType.kind
    var declIdx: Table[string, int]
    for i, decl in tr.model.variables:
        if decl.isVar and not decl.isArray: declIdx[decl.name] = i
    proc isTotalDefinition(tr: FznTranslator, declType: Table[string, FznTypeKind],
                           declIdx: Table[string, int], con: FznConstraint, b: string): bool =
        let name = stripSolverPrefix(con.name)
        let kind = declType.getOrDefault(b, FznIntSet)
        let lastIsB = con.args.len > 0 and con.args[^1].kind == FznIdent and
                      con.args[^1].ident == b
        if name.endsWith("_reif") or name in ["array_bool_and", "array_bool_or", "bool_xor"]:
            return kind == FznBool and lastIsB
        if name == "bool_not":
            return kind == FznBool
        if name == "bool2int":
            if not lastIsB: return false
            if kind == FznInt: return true
            if kind == FznIntRange:
                let t = tr.model.variables[declIdx[b]].varType
                return t.lo <= 0 and t.hi >= 1
            return false
        if name == "int_lin_eq":
            # b's coefficient must be +-1 (2*b = x forces x even)
            if kind != FznInt or con.args.len < 2: return false
            let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: return false
            let elems = tr.resolveVarArrayElems(con.args[1])
            if coeffs.len != elems.len: return false
            var nB = 0
            for i, e in elems:
                if e.kind == FznIdent and e.ident == b:
                    inc nB
                    if abs(coeffs[i]) != 1: return false
            return nB == 1
        if name in ["int_plus", "int_times", "int_max", "int_min",
                    "int_abs", "array_int_maximum", "array_int_minimum"]:
            return kind == FznInt
        false

    var total = 0
    for round in 0..<10:
        var uses: CountTable[string]
        for ci, con in tr.model.constraints:
            if ci in tr.definingConstraints: continue
            for arg in con.args:
                if arg.kind == FznIdent:
                    uses.inc(arg.ident)
                    if arg.ident in arrElems:
                        for n in arrElems[arg.ident]: uses.inc(n)
                elif arg.kind == FznArrayLit:
                    for e in arg.elems:
                        if e.kind == FznIdent: uses.inc(e.ident)
        var removed = 0
        for ci, con in tr.model.constraints:
            if ci in tr.definingConstraints: continue
            if not con.hasAnnotation("defines_var"): continue
            let ann = con.getAnnotation("defines_var")
            if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
            let b = ann.args[0].ident
            if b in keep: continue
            if not isTotalDefinition(tr, declType, declIdx, con, b): continue
            # its own definition is its only use
            if uses.getOrDefault(b, 0) <= 1:
                tr.definingConstraints.incl(ci)
                inc removed
        total += removed
        if removed == 0: break
    if total > 0:
        stderr.writeLine("[FZN] Eliminated " & $total & " dead definitions")

proc aliasFixedEqualities(tr: var FznTranslator) =
    ## Presolve can fix the boolean of `int_eq_reif(x, y, b)` to true (e.g. the
    ## other literal of `bool_clause([ua == 0, b])` became false), leaving a plain
    ## equality between two variables that MiniZinc could not alias. Translated
    ## as a constraint, x stays a search variable that the search must keep
    ## "repairing" toward y; as an alias (`var x = y;`, resolved by
    ## canonicalizeFznVarAliases) x simply IS y (e.g. y is an element channel).
    ##
    ## Sound only if the alias does not drop a restriction: the canonical side's
    ## domain must be contained in the alias side's domain (the alias's own
    ## domain is not enforced after substitution). Also handles plain
    ## `int_eq(x, y)`. The equality constraint is consumed.
    var declIdx: Table[string, int]
    for i, decl in tr.model.variables:
        if not decl.isArray: declIdx[decl.name] = i

    proc boolFixedTrue(tr: FznTranslator, e: FznExpr): bool =
        case e.kind
        of FznBoolLit: e.boolVal
        of FznIntLit: e.intVal == 1
        of FznIdent:
            if e.ident in tr.paramValues: tr.paramValues[e.ident] == 1
            elif e.ident in tr.presolveDomains:
                let d {.cursor.} = tr.presolveDomains[e.ident]
                d.len == 1 and d[0] == 1
            else: false
        else: false

    # Domain as (bounded, sorted values) — unbounded `var int` is (false, @[]).
    proc domOf(tr: FznTranslator, declIdx: Table[string, int], name: string): (bool, seq[int]) =
        if name in tr.presolveDomains: return (true, tr.presolveDomains[name])
        if name notin declIdx: return (false, @[])
        let decl {.cursor.} = tr.model.variables[declIdx[name]]
        case decl.varType.kind
        of FznIntRange:
            if decl.varType.hi - decl.varType.lo > 1_000_000: return (false, @[])
            return (true, toSeq(decl.varType.lo..decl.varType.hi))
        of FznIntSet: return (true, decl.varType.values.sorted())
        of FznBool: return (true, @[0, 1])
        else: return (false, @[])

    proc contains(outer, inner: (bool, seq[int])): bool =
        ## inner ⊆ outer
        if not outer[0]: return true
        if not inner[0]: return false
        let s = outer[1].toPackedSet()
        for v in inner[1]:
            if v notin s: return false
        true

    var definedByCon: HashSet[string]
    for ci in 0 ..< tr.model.constraints.len:
        if ci in tr.definingConstraints: continue
        for ann in tr.model.constraints[ci].annotations:
            if ann.name == "defines_var" and ann.args.len > 0 and ann.args[0].kind == FznIdent:
                definedByCon.incl(ann.args[0].ident)
    var touched: HashSet[string]   # one alias decision per variable per pass
    var nAliased = 0
    for ci in 0 ..< tr.model.constraints.len:
        if ci in tr.definingConstraints: continue
        let con {.cursor.} = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        var isEq = false
        if name == "int_eq" and con.args.len >= 2:
            isEq = true
        elif name == "int_eq_reif" and con.args.len >= 3 and tr.boolFixedTrue(con.args[2]):
            isEq = true
        if not isEq: continue
        let a = con.args[0]
        let b = con.args[1]
        if a.kind != FznIdent or b.kind != FznIdent: continue
        let x = a.ident
        let y = b.ident
        if x == y: continue
        if x notin declIdx or y notin declIdx: continue
        if x in touched or y in touched: continue
        let dx = tr.model.variables[declIdx[x]]
        let dy = tr.model.variables[declIdx[y]]
        if not dx.isVar or not dy.isVar: continue
        if dx.value != nil or dy.value != nil: continue
        if dx.varType.kind notin {FznIntRange, FznIntSet, FznInt} or
           dy.varType.kind notin {FznIntRange, FznIntSet, FznInt}: continue
        let domX = tr.domOf(declIdx, x)
        let domY = tr.domOf(declIdx, y)
        # The alias side must be a free variable (no defining constraint):
        # aliasing a defined variable would demote its definition and reshape
        # the defined-variable structure later detectors rely on.
        var aliasName, canonName: string
        let yDefined = y in definedByCon
        let xDefined = x in definedByCon
        if not xDefined and contains(domX, domY):
            aliasName = x; canonName = y
        elif not yDefined and contains(domY, domX):
            aliasName = y; canonName = x
        else:
            continue
        tr.model.variables[declIdx[aliasName]].value = FznExpr(kind: FznIdent, ident: canonName)
        tr.definingConstraints.incl(ci)
        touched.incl(x)
        touched.incl(y)
        inc nAliased
    if nAliased > 0:
        stderr.writeLine(&"[FZN] Aliased {nAliased} presolve-fixed variable equalities")
