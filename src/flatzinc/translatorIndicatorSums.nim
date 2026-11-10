## Indicator-sum grouping (FZN-level rewrite, runs before collectDefinedVars).
##
## MiniZinc flattens sums like `sum(w, a)(c[w,a] * y[w] * (i = x[w] + a))` into
## one term per (w, a):
##
##     r = int_eq_reif(x, v)        b = bool2int(r)
##     p = int_times(c, b)  or  p = int_times(G, b) with G = alpha*y + beta
##     L = ... + e*p + ...          (int_lin_eq :: defines_var(L))
##
## All terms over the same (x, y) are one function of (x, y): a constant table
## lookup. This pass replaces each such group by a single element channel
##
##     I = n*(y - ylo) + (x - lo) + 1          (int_lin_eq :: defines_var(I))
##     C = array_int_element(I, T)             (:: defines_var(C))
##
## and rewrites L's equation over the C's. On nside this turns 113k product
## channels and 48k reified indicators into 24k table channels. The original
## r/b/p constraints are left in place (exact equivalences), so any other use
## of them is unaffected; unused ones are removed by dead-definition passes.

proc groupIndicatorSums(tr: var FznTranslator) =
    const MaxTableSize = 65536
    # defines_var index: var name -> constraint index
    var defOf: Table[string, int]
    for ci in 0 ..< tr.model.constraints.len:
        let con {.cursor.} = tr.model.constraints[ci]
        if not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len > 0 and ann.args[0].kind == FznIdent:
            defOf[ann.args[0].ident] = ci

    proc isVarIdent(tr: FznTranslator, e: FznExpr): bool =
        e.kind == FznIdent and e.ident notin tr.paramValues

    proc constOf(tr: FznTranslator, e: FznExpr): (bool, int) =
        if e.kind == FznIntLit: return (true, e.intVal)
        if e.kind == FznIdent and e.ident in tr.paramValues: return (true, tr.paramValues[e.ident])
        (false, 0)

    # Indicator: b = bool2int(r), r = int_eq_reif(x, v) -> (ok, x, v)
    proc indicatorOf(tr: FznTranslator, defOf: Table[string, int], name: string): (bool, string, int) =
        if name notin defOf: return (false, "", 0)
        let bcon {.cursor.} = tr.model.constraints[defOf[name]]
        if stripSolverPrefix(bcon.name) != "bool2int" or bcon.args.len != 2: return (false, "", 0)
        if bcon.args[1].kind != FznIdent or bcon.args[1].ident != name: return (false, "", 0)
        if bcon.args[0].kind != FznIdent: return (false, "", 0)
        let rName = bcon.args[0].ident
        if rName notin defOf: return (false, "", 0)
        let rcon {.cursor.} = tr.model.constraints[defOf[rName]]
        if stripSolverPrefix(rcon.name) != "int_eq_reif" or rcon.args.len != 3: return (false, "", 0)
        if rcon.args[2].kind != FznIdent or rcon.args[2].ident != rName: return (false, "", 0)
        let (c0, v0) = tr.constOf(rcon.args[0])
        let (c1, v1) = tr.constOf(rcon.args[1])
        if tr.isVarIdent(rcon.args[0]) and c1: return (true, rcon.args[0].ident, v1)
        if tr.isVarIdent(rcon.args[1]) and c0: return (true, rcon.args[1].ident, v0)
        (false, "", 0)

    type Term = object
        x, y: string          # y == "" -> no multiplier variable
        v: int                # indicator value: [x == v]
        alpha, beta: int      # multiplier = alpha*y + beta (alpha = 0 when y == "")
        e: int                # coefficient in the sum

    # Multiplier G = alpha*y + beta from a 2-variable int_lin_eq definition,
    # or a plain variable y (alpha = 1).
    proc multiplierOf(tr: FznTranslator, defOf: Table[string, int], name: string): (bool, string, int, int) =
        if name in defOf:
            let gcon {.cursor.} = tr.model.constraints[defOf[name]]
            if stripSolverPrefix(gcon.name) == "int_lin_eq":
                let cs = try: tr.resolveIntArray(gcon.args[0]) except CatchableError: @[]
                let vs = tr.resolveVarArrayElems(gcon.args[1])
                if cs.len == 2 and vs.len == 2:
                    let (rok, rhs) = tr.constOf(gcon.args[2])
                    if rok:
                        for gi in 0..1:
                            let yi = 1 - gi
                            if vs[gi].kind == FznIdent and vs[gi].ident == name and
                                 (cs[gi] == 1 or cs[gi] == -1) and tr.isVarIdent(vs[yi]):
                                # cG*G + cy*y = rhs -> G = cG*rhs - cG*cy*y
                                return (true, vs[yi].ident, -cs[gi] * cs[yi], cs[gi] * rhs)
            return (false, "", 0, 0)
        (true, name, 1, 0)

    var nRewritten, nGroups, nTerms = 0
    var newVars: seq[FznVarDecl]
    var newCons: seq[FznConstraint]
    var domCache: Table[string, (bool, int, int)]
    proc boundsOf(tr: var FznTranslator, domCache: var Table[string, (bool, int, int)], name: string): (bool, int, int) =
        if name in domCache: return domCache[name]
        # Declared domain: the table must cover every value a position can take
        let d = tr.lookupVarDomain(name)
        result = if d.len == 0: (false, 0, 0) else: (true, min(d), max(d))
        domCache[name] = result

    let nCons = tr.model.constraints.len
    for ci in 0 ..< nCons:
        let con {.cursor.} = tr.model.constraints[ci]
        if stripSolverPrefix(con.name) != "int_lin_eq": continue
        if not con.hasAnnotation("defines_var"): continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        let defName = ann.args[0].ident
        let coefs = try: tr.resolveIntArray(con.args[0]) except CatchableError: continue
        let vars = tr.resolveVarArrayElems(con.args[1])
        if coefs.len != vars.len or vars.len < 4: continue

        var terms: seq[Term]
        var keep: seq[int]   # indices of terms left as they are
        for k, ve in vars:
            if ve.kind != FznIdent or ve.ident == defName or ve.ident in tr.paramValues:
                keep.add k; continue
            let name = ve.ident
            # Bare indicator
            let (bok, bx, bv) = tr.indicatorOf(defOf, name)
            if bok:
                terms.add Term(x: bx, y: "", v: bv, alpha: 0, beta: 1, e: coefs[k])
                continue
            # Product with an indicator
            var matched = false
            if name in defOf:
                let pcon {.cursor.} = tr.model.constraints[defOf[name]]
                if stripSolverPrefix(pcon.name) == "int_times" and pcon.args.len == 3 and
                     pcon.args[2].kind == FznIdent and pcon.args[2].ident == name:
                    for side in 0..1:
                        let ind = pcon.args[side]
                        let other = pcon.args[1 - side]
                        if ind.kind != FznIdent: continue
                        let (iok, ix, iv) = tr.indicatorOf(defOf, ind.ident)
                        if not iok: continue
                        let (cok, cval) = tr.constOf(other)
                        if cok:
                            terms.add Term(x: ix, y: "", v: iv, alpha: 0, beta: cval, e: coefs[k])
                            matched = true
                        elif tr.isVarIdent(other):
                            let (mok, my, ma, mb) = tr.multiplierOf(defOf, other.ident)
                            if mok and my != ix:
                                terms.add Term(x: ix, y: my, v: iv, alpha: ma, beta: mb, e: coefs[k])
                                matched = true
                        if matched: break
            if not matched: keep.add k

        if terms.len < 4: continue
        # Group by (x, y)
        var groups: Table[(string, string), seq[int]]
        var order: seq[(string, string)]
        for ti, t in terms:
            let key = (t.x, t.y)
            if key notin groups:
                groups[key] = @[]
                order.add key
            groups[key].add ti
        # Worth it only when groups merge terms on average
        if terms.len < 2 * order.len: continue

        var okAll = true
        type GroupPlan = object
            x, y: string
            lo, n, ylo, m: int
            table: seq[int]
        var plans: seq[GroupPlan]
        for key in order:
            let (x, y) = key
            let (xok, lo, hi) = tr.boundsOf(domCache, x)
            if not xok: okAll = false; break
            var ylo, yhi = 0
            if y != "":
                let (yok, a, b) = tr.boundsOf(domCache, y)
                if not yok: okAll = false; break
                ylo = a; yhi = b
            let n = hi - lo + 1
            let m = yhi - ylo + 1
            if n <= 0 or m <= 0 or n * m > MaxTableSize: okAll = false; break
            var table = newSeq[int](n * m)
            for ti in groups[key]:
                let t = terms[ti]
                if t.v < lo or t.v > hi: continue   # indicator can never fire
                for yi in 0..<m:
                    let yv = ylo + yi
                    let mult = (if y == "": t.beta else: t.alpha * yv + t.beta)
                    table[yi * n + (t.v - lo)] += t.e * mult
            plans.add GroupPlan(x: x, y: y, lo: lo, n: n, ylo: ylo, m: m, table: table)
        if not okAll: continue

        # Emit the channels and the rewritten equation
        var newCoefs: seq[FznExpr]
        var newVarsArr: seq[FznExpr]
        for p in plans:
            let base = "X_CRUSHER_INDSUM_" & $(nGroups)
            let iName = base & "_I"
            let cName = base & "_C"
            inc nGroups
            let tMin = min(p.table)
            let tMax = max(p.table)
            newVars.add FznVarDecl(name: iName, varType: FznType(kind: FznIntRange, lo: 1, hi: p.n * p.m),
                                   isVar: true, annotations: @[FznAnnotation(name: "var_is_introduced"),
                                                               FznAnnotation(name: "is_defined_var")])
            newVars.add FznVarDecl(name: cName, varType: FznType(kind: FznIntRange, lo: tMin, hi: tMax),
                                   isVar: true, annotations: @[FznAnnotation(name: "var_is_introduced"),
                                                               FznAnnotation(name: "is_defined_var")])
            # I = n*y + x - (n*ylo + lo - 1)
            var ic, iv: seq[FznExpr]
            if p.y != "":
                ic.add FznExpr(kind: FznIntLit, intVal: p.n); iv.add FznExpr(kind: FznIdent, ident: p.y)
            ic.add FznExpr(kind: FznIntLit, intVal: 1); iv.add FznExpr(kind: FznIdent, ident: p.x)
            ic.add FznExpr(kind: FznIntLit, intVal: -1); iv.add FznExpr(kind: FznIdent, ident: iName)
            let rhs = (if p.y != "": p.n * p.ylo else: 0) + p.lo - 1
            newCons.add FznConstraint(name: "int_lin_eq",
                args: @[FznExpr(kind: FznArrayLit, elems: ic), FznExpr(kind: FznArrayLit, elems: iv),
                        FznExpr(kind: FznIntLit, intVal: rhs)],
                annotations: @[FznAnnotation(name: "defines_var", args: @[FznExpr(kind: FznIdent, ident: iName)])])
            var tElems: seq[FznExpr]
            for tv in p.table: tElems.add FznExpr(kind: FznIntLit, intVal: tv)
            newCons.add FznConstraint(name: "array_int_element",
                args: @[FznExpr(kind: FznIdent, ident: iName), FznExpr(kind: FznArrayLit, elems: tElems),
                        FznExpr(kind: FznIdent, ident: cName)],
                annotations: @[FznAnnotation(name: "defines_var", args: @[FznExpr(kind: FznIdent, ident: cName)])])
            newCoefs.add FznExpr(kind: FznIntLit, intVal: 1)
            newVarsArr.add FznExpr(kind: FznIdent, ident: cName)
        for k in keep:
            newCoefs.add FznExpr(kind: FznIntLit, intVal: coefs[k])
            newVarsArr.add vars[k]
        tr.model.constraints[ci].args[0] = FznExpr(kind: FznArrayLit, elems: newCoefs)
        tr.model.constraints[ci].args[1] = FznExpr(kind: FznArrayLit, elems: newVarsArr)
        inc nRewritten
        nTerms += terms.len

    if nRewritten == 0: return
    for d in newVars:
        tr.model.variables.add d
        if tr.varDomainIndex.len > 0:
            tr.varDomainIndex[d.name] = tr.model.variables.len - 1
    for c in newCons:
        tr.model.constraints.add c
    stderr.writeLine(&"[FZN] Indicator sums: {nTerms} terms in {nRewritten} equations grouped into {nGroups} table channels")

    # The product / bool2int / reif chains behind the grouped terms are now
    # usually unread. Drop them here, before definitions and channels are
    # collected (later dead-definition passes see them already registered):
    # each dead definition becomes a consumed no-op and its variable
    # declaration is removed. Only total definitions are dropped.
    var keep: HashSet[string]
    var arrElems: Table[string, seq[string]]   # named var arrays: uses count per reference
    for decl in tr.model.variables:
        if decl.hasAnnotation("output_var"): keep.incl(decl.name)
        if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
            var names: seq[string]
            for e in decl.value.elems:
                if e.kind == FznIdent: names.add e.ident
            arrElems[decl.name] = names
            if decl.hasAnnotation("output_array"):
                for n in names: keep.incl n
        if decl.value != nil and decl.value.kind == FznIdent: keep.incl(decl.value.ident)
    if tr.model.solve.objective != nil and tr.model.solve.objective.kind == FznIdent:
        keep.incl(tr.model.solve.objective.ident)
    for v in tr.annotatedSearchVarNames: keep.incl(v)
    var uses: CountTable[string]
    proc countUses(uses: var CountTable[string], arrElems: Table[string, seq[string]],
                   con: FznConstraint, delta: int) =
        for arg in con.args:
            if arg.kind == FznIdent:
                uses.inc(arg.ident, delta)
                if arg.ident in arrElems:
                    for n in arrElems[arg.ident]: uses.inc(n, delta)
            elif arg.kind == FznArrayLit:
                for e in arg.elems:
                    if e.kind == FznIdent: uses.inc(e.ident, delta)
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        countUses(uses, arrElems, con, 1)
    var declType: Table[string, FznTypeKind]
    var declIdx: Table[string, int]
    for i, decl in tr.model.variables:
        if decl.isVar and not decl.isArray:
            declType[decl.name] = decl.varType.kind
            declIdx[decl.name] = i
    var deadVars: HashSet[string]
    var work: seq[string]
    for name in defOf.keys: work.add name
    var nDead = 0
    while work.len > 0:
        let b = work.pop()
        if b in deadVars or b in keep or b notin defOf: continue
        let ci = defOf[b]
        if uses.getOrDefault(b, 0) > 1: continue
        if ci in tr.definingConstraints: continue
        let con = tr.model.constraints[ci]
        if stripSolverPrefix(con.name) notin ["int_times", "bool2int", "int_eq_reif", "int_lin_eq"]: continue
        if not isTotalDefinition(tr, declType, declIdx, con, b): continue
        deadVars.incl b
        countUses(uses, arrElems, con, -1)
        tr.model.constraints[ci] = FznConstraint(name: "bool_eq",
            args: @[FznExpr(kind: FznBoolLit, boolVal: true), FznExpr(kind: FznBoolLit, boolVal: true)])
        tr.definingConstraints.incl(ci)
        inc nDead
        for arg in con.args:
            if arg.kind == FznIdent:
                work.add arg.ident
                if arg.ident in arrElems:
                    for n in arrElems[arg.ident]: work.add n
            elif arg.kind == FznArrayLit:
                for e in arg.elems:
                    if e.kind == FznIdent: work.add e.ident
    if nDead > 0:
        var vars: seq[FznVarDecl]
        for d in tr.model.variables:
            if d.isArray:
                # An array holding a dead element is unreferenced (a reference
                # would have counted as a use of the element): drop it too.
                var hasDead = false
                if d.name in arrElems and not d.hasAnnotation("output_array"):
                    for n in arrElems[d.name]:
                        if n in deadVars: hasDead = true; break
                if not hasDead: vars.add d
            elif d.name notin deadVars: vars.add d
        tr.model.variables = vars
        tr.varDomainIndex.clear()
        tr.buildVarDomainIndex()
        stderr.writeLine(&"[FZN] Indicator sums: dropped {nDead} dead product/indicator definitions")
