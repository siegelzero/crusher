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

    # Pass 1: match the indicator terms of every int_lin_eq definition.
    type EqInfo = object
        ci: int
        defName: string
        coefs: seq[int]
        vars: seq[FznExpr]
        keep: seq[int]
        terms: seq[Term]
    var eqs: seq[EqInfo]
    var eqOf: Table[string, int]   # defined var -> index in eqs
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
        if coefs.len != vars.len or vars.len < 2: continue

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

        # Kept: equations worth grouping, and pure indicator sums (only the
        # defined variable left over) that a profile max may absorb.
        let pureSum = keep.len == 1 and vars[keep[0]].kind == FznIdent and
                      vars[keep[0]].ident == defName and abs(coefs[keep[0]]) == 1
        if terms.len < 4 and not pureSum: continue
        eqOf[defName] = eqs.len
        eqs.add EqInfo(ci: ci, defName: defName, coefs: coefs, vars: vars, keep: keep, terms: terms)

    # Pass 2: peak-load profiles. array_int_maximum(M, [L_1..L_n]) over pure
    # indicator sums used nowhere else becomes one profile max channel: a
    # source move then updates the few slots it touches instead of n sums.
    var consumedEq: PackedSet[int]
    var profileDead: HashSet[string]
    var profileMaxCis: seq[int]
    block profiles:
        var candL: HashSet[string]
        for e in eqs:
            if e.keep.len == 1 and e.vars[e.keep[0]].kind == FznIdent and
               e.vars[e.keep[0]].ident == e.defName and abs(e.coefs[e.keep[0]]) == 1:
                candL.incl e.defName
        if candL.len == 0: break profiles
        if tr.varDomainIndex.len == 0: tr.buildVarDomainIndex()
        var outNames: HashSet[string]
        var arrOf: Table[string, seq[string]]
        for decl in tr.model.variables:
            if decl.hasAnnotation("output_var"): outNames.incl decl.name
            if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
                var names: seq[string]
                for el in decl.value.elems:
                    if el.kind == FznIdent: names.add el.ident
                if decl.hasAnnotation("output_array"):
                    for n in names: outNames.incl n
                arrOf[decl.name] = names
            if decl.value != nil and decl.value.kind == FznIdent: outNames.incl decl.value.ident
        # References to candidates (their own definition counts one)
        var refs: CountTable[string]
        for ci in 0 ..< tr.model.constraints.len:
            for arg in tr.model.constraints[ci].args:
                if arg.kind == FznIdent:
                    if arg.ident in candL: refs.inc arg.ident
                    elif arg.ident in arrOf:
                        for n in arrOf[arg.ident]:
                            if n in candL: refs.inc n
                elif arg.kind == FznArrayLit:
                    for el in arg.elems:
                        if el.kind == FznIdent and el.ident in candL: refs.inc el.ident
        proc declCovers(tr: FznTranslator, name: string, lo, hi: int): bool =
            ## The declared domain is no constraint on values in lo..hi.
            let idx = tr.varDomainIndex.getOrDefault(name, -1)
            if idx < 0: return false
            let vt = tr.model.variables[idx].varType
            case vt.kind
            of FznInt: true
            of FznIntRange: vt.lo <= lo and hi <= vt.hi
            else: false
        for ci in 0 ..< nCons:
            let con {.cursor.} = tr.model.constraints[ci]
            if stripSolverPrefix(con.name) != "array_int_maximum" or con.args.len != 2: continue
            if con.args[0].kind != FznIdent: continue
            let mName = con.args[0].ident
            if not con.hasAnnotation("defines_var"): continue
            let mann = con.getAnnotation("defines_var")
            if mann.args.len == 0 or mann.args[0].kind != FznIdent or mann.args[0].ident != mName: continue
            if mName in tr.annotatedSearchVarNames: continue
            let elems = tr.resolveVarArrayElems(con.args[1])
            if elems.len == 0: continue
            var ok = true
            var seenL: HashSet[string]
            for el in elems:
                if el.kind != FznIdent or el.ident notin candL or el.ident in outNames or
                   el.ident in seenL or refs.getOrDefault(el.ident, 0) != 2 or
                   el.ident in tr.annotatedSearchVarNames:
                    ok = false; break
                seenL.incl el.ident
                # Sources must be plain variables: then a move of one changes
                # only its own groups (what the cached evaluation relies on)
                for t in eqs[eqOf[el.ident]].terms:
                    if t.x in defOf or (t.y != "" and t.y in defOf): ok = false; break
                if not ok: break
            if not ok: continue
            # Contributions per group (x, y): (v, slot, A, B) with
            # L_slot += [x == v] * (A*y + B). From cL*L + Σ e*term = rhs (cL = ±1):
            # L = cL*rhs - cL*Σ e*(alpha*y + beta)*[x == v].
            var gIdx: Table[(string, string), int]
            var gx, gy: seq[string]
            var gEntries: seq[seq[(int, int, int, int)]]
            var slotBase = newSeq[int](elems.len)
            for s, el in elems:
                let e {.cursor.} = eqs[eqOf[el.ident]]
                let cL = e.coefs[e.keep[0]]
                let (rok, rhs) = tr.constOf(tr.model.constraints[e.ci].args[2])
                if not rok: ok = false; break
                slotBase[s] = cL * rhs
                for t in e.terms:
                    let key = (t.x, t.y)
                    var g = gIdx.getOrDefault(key, -1)
                    if g < 0:
                        g = gx.len
                        gIdx[key] = g
                        gx.add t.x
                        gy.add t.y
                        gEntries.add @[]
                    gEntries[g].add (t.v, s, -cL * t.e * t.alpha, -cL * t.e * t.beta)
            if not ok: continue
            var natLo = slotBase
            var natHi = slotBase
            var def = ProfileMaxDef(maxVarName: mName, slotBase: slotBase)
            def.valStart.add 0
            for g in 0 ..< gx.len:
                let (xok, xlo, xhi) = tr.boundsOf(domCache, gx[g])
                if not xok: ok = false; break
                var ylo, yhi = 0
                if gy[g] != "":
                    let (yok, a, b) = tr.boundsOf(domCache, gy[g])
                    if not yok: ok = false; break
                    ylo = a
                    yhi = b
                var ents: seq[(int, int, int, int)]
                for en in gEntries[g]:
                    if en[0] >= xlo and en[0] <= xhi: ents.add en   # others never fire
                ents.sort()
                var agg: seq[(int, int, int, int)]
                for en in ents:
                    if agg.len > 0 and agg[^1][0] == en[0] and agg[^1][1] == en[1]:
                        agg[^1][2] += en[2]
                        agg[^1][3] += en[3]
                    else:
                        agg.add en
                if agg.len == 0: continue
                # Natural range per slot: over x in xlo..xhi (0 where no entry)
                # and the y range (contributions are linear in y)
                var perSlot: Table[int, (int, int, int)]   # slot -> (#values, min, max)
                for en in agg:
                    let c0 = en[2] * ylo + en[3]
                    let c1 = en[2] * yhi + en[3]
                    let cur = perSlot.getOrDefault(en[1], (0, high(int), low(int)))
                    perSlot[en[1]] = (cur[0] + 1, min(cur[1], min(c0, c1)), max(cur[2], max(c0, c1)))
                for s, st in perSlot:
                    var lo2 = st[1]
                    var hi2 = st[2]
                    if st[0] < xhi - xlo + 1:
                        lo2 = min(lo2, 0)
                        hi2 = max(hi2, 0)
                    natLo[s] += lo2
                    natHi[s] += hi2
                let vlo = agg[0][0]
                let vhi = agg[^1][0]
                def.groupX.add gx[g]
                def.groupY.add gy[g]
                def.groupLo.add vlo
                def.groupN.add vhi - vlo + 1
                def.groupStart.add def.valStart.len - 1
                var ai = 0
                for v in vlo .. vhi:
                    while ai < agg.len and agg[ai][0] == v:
                        def.contribSlot.add int32(agg[ai][1])
                        def.contribA.add agg[ai][2]
                        def.contribB.add agg[ai][3]
                        inc ai
                    def.valStart.add def.contribSlot.len
            if not ok: continue
            # Dropping the sums' declared domains must not drop constraints
            for s, el in elems:
                if not tr.declCovers(el.ident, natLo[s], natHi[s]): ok = false; break
            if not ok: continue
            # M's declared bounds stay as constraints on the channel (a
            # declared peak cap, nside's 0..max(perterb)*days, is binding);
            # a declared set with holes is not handled
            block:
                let idx = tr.varDomainIndex.getOrDefault(mName, -1)
                if idx < 0 or tr.model.variables[idx].varType.kind notin {FznInt, FznIntRange}: continue
            def.natLo = max(natLo)
            def.natHi = max(natHi)
            stderr.writeLine(&"[FZN] Profile max {mName}: {elems.len} slots, {def.groupX.len} groups, " &
                             &"{def.contribSlot.len} contributions")
            tr.profileMaxDefs.add def
            tr.channelVarNames.incl mName
            profileMaxCis.add ci
            for el in elems:
                consumedEq.incl eqOf[el.ident]
                profileDead.incl el.ident
    for def in tr.profileMaxDefs:
        # M is now a native channel, not a defined variable
        let idx = tr.varDomainIndex.getOrDefault(def.maxVarName, -1)
        if idx >= 0:
            tr.model.variables[idx].annotations.keepItIf(it.name != "is_defined_var")
    for ci in profileMaxCis:
        tr.model.constraints[ci] = FznConstraint(name: "bool_eq",
            args: @[FznExpr(kind: FznBoolLit, boolVal: true), FznExpr(kind: FznBoolLit, boolVal: true)])
        tr.definingConstraints.incl(ci)
    for ei in consumedEq.items:
        let ci = eqs[ei].ci
        tr.model.constraints[ci] = FznConstraint(name: "bool_eq",
            args: @[FznExpr(kind: FznBoolLit, boolVal: true), FznExpr(kind: FznBoolLit, boolVal: true)])
        tr.definingConstraints.incl(ci)

    # Pass 3: table channels for the remaining equations
    for ei in 0 ..< eqs.len:
        if ei in consumedEq: continue
        let ci = eqs[ei].ci
        let coefs {.cursor.} = eqs[ei].coefs
        let vars {.cursor.} = eqs[ei].vars
        let keep {.cursor.} = eqs[ei].keep
        let terms {.cursor.} = eqs[ei].terms
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
            # The table is a named constant array: as a literal it costs one
            # FznExpr per entry (nside 2000_500: 120k tables of ~1000 entries).
            let tName = base & "_T"
            tr.arrayValues[tName] = p.table
            newCons.add FznConstraint(name: "array_int_element",
                args: @[FznExpr(kind: FznIdent, ident: iName), FznExpr(kind: FznIdent, ident: tName),
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

    if nRewritten == 0 and profileDead.len == 0: return
    for d in newVars.mitems:
        if tr.varDomainIndex.len > 0:
            tr.varDomainIndex[d.name] = tr.model.variables.len
        tr.model.variables.add move(d)
    for c in newCons.mitems:
        tr.model.constraints.add move(c)
    if nRewritten > 0:
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
    for ci in 0 ..< tr.model.constraints.len:
        if ci in tr.definingConstraints: continue
        countUses(uses, arrElems, tr.model.constraints[ci], 1)
    var declType: Table[string, FznTypeKind]
    var declIdx: Table[string, int]
    for i in 0 ..< tr.model.variables.len:
        let decl {.cursor.} = tr.model.variables[i]
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
        if stripSolverPrefix(tr.model.constraints[ci].name) notin
             ["int_times", "bool2int", "int_eq_reif", "int_lin_eq"]: continue
        if not isTotalDefinition(tr, declType, declIdx, tr.model.constraints[ci], b): continue
        deadVars.incl b
        countUses(uses, arrElems, tr.model.constraints[ci], -1)
        let con = move(tr.model.constraints[ci])
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
    for n in profileDead: deadVars.incl n
    if nDead > 0 or profileDead.len > 0:
        var vars: seq[FznVarDecl]
        for d in tr.model.variables.mitems:
            if d.isArray:
                # An array holding a dead element is unreferenced (a reference
                # would have counted as a use of the element): drop it too.
                var hasDead = false
                if d.name in arrElems and not d.hasAnnotation("output_array"):
                    for n in arrElems[d.name]:
                        if n in deadVars: hasDead = true; break
                if not hasDead: vars.add move(d)
            elif d.name notin deadVars: vars.add move(d)
        tr.model.variables = vars
        tr.varDomainIndex.clear()
        tr.buildVarDomainIndex()
        stderr.writeLine(&"[FZN] Indicator sums: dropped {nDead} dead product/indicator definitions")
