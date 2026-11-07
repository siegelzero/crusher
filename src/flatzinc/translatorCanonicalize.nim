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
