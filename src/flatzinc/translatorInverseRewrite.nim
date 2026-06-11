## Included from translator.nim -- not a standalone module.
##
## Post-inverse-detection rewrites. Both passes run after
## detectInverseChannelPatterns (suppression state final) and before the main
## constraint translation loop.
##
## 1. dropImpliedInverseCircuits: a crusher_circuit over the CHANNEL side of an
##    inverse channel pattern is implied — the channel side is definitionally
##    the inverse of the forward vars, and the inverse of a Hamiltonian circuit
##    is a Hamiltonian circuit — whenever the forward side is itself
##    circuit-enforced (by a surviving crusher_circuit or a CircuitTimeProp
##    instance). The implied circuit only duplicates penalty gradient on
##    channel positions and pays channel-dep evaluation cost on every move.
##
## 2. rewriteInverseChannelIndexedElements: element constraints indexed by a
##    channel-side variable, X[A_k] = t_k (e.g. vehicle[pred[k]] = vehicle[k]
##    in VRP models), are rewritten onto the forward side. Since A_k = r iff
##    f_r = k, the group {X[A_k] = t_k : k in K} is equivalent to, per forward
##    var f_r:  f_r in K -> X[r] = t[f_r], expressible as a plain element
##    constraint element(f_r, W_r, X[r]) where W_r[k] = t_k for k in K and
##    W_r[k] = X[r] (self, trivially satisfied) elsewhere. This moves the
##    constraints from channel-index positions (expensive cascade evaluation,
##    poor search guidance) onto search positions with dense penalty maps.
##    Rewrites already implied by an existing forward-side element constraint
##    (same index var, same array, target X[r]) are dropped entirely.


proc inverseChannelPatternIsBuildable(tr: FznTranslator, pi: int): bool =
    ## Mirrors the validity checks of buildInverseChannelBindings: the pattern
    ## must survive suppression and have consecutive result values so the
    ## channel group will actually be built later.
    if pi in tr.suppressedInversePatterns: return false
    let pattern = tr.inverseChannelPatterns[pi]
    if pattern.arrayName notin tr.arrayPositions: return false
    let sortedResults = pattern.resultValues.sorted()
    if sortedResults.len == 0: return false
    for i in 1..<sortedResults.len:
        if sortedResults[i] != sortedResults[i-1] + 1: return false
    for vn in pattern.indexVarNames:
        if vn notin tr.varPositions: return false
    return true


proc dropImpliedInverseCircuits(tr: var FznTranslator) =
    if tr.inverseChannelPatterns.len == 0: return

    # Circuit constraints by (named) array argument
    var circuitByArray: Table[string, seq[int]]
    for ci, con in tr.model.constraints:
        if stripSolverPrefix(con.name) notin ["crusher_circuit", "fzn_circuit"]: continue
        if con.args.len < 1 or con.args[0].kind != FznIdent: continue
        circuitByArray.mgetOrPut(con.args[0].ident, @[]).add(ci)
    if circuitByArray.len == 0: return

    # Circuits consumed by circuit-time detection still enforce Hamiltonicity
    # (the CircuitTimeProp instance carries the circuit penalty).
    var ctEnforced = initPackedSet[int]()
    for cand in tr.circuitTimeCandidates:
        ctEnforced.incl(cand.circuitCI)

    for pi in 0..<tr.inverseChannelPatterns.len:
        if not tr.inverseChannelPatternIsBuildable(pi): continue
        let pattern = tr.inverseChannelPatterns[pi]
        if pattern.arrayName notin circuitByArray: continue

        # Find a circuit-enforced forward-side array: its variable elements
        # must be exactly the pattern's index vars.
        let idxSet = pattern.indexVarNames.toHashSet()
        var fwdEnforced = false
        for arrName, cis in circuitByArray:
            if arrName == pattern.arrayName: continue
            if arrName notin tr.arrayElementNames: continue
            var varNames: HashSet[string]
            for en in tr.arrayElementNames[arrName]:
                if en.len > 0 and en in tr.varPositions and
                   tr.sys.baseArray.domain[tr.varPositions[en]].len > 1:
                    varNames.incl(en)
            if varNames != idxSet: continue
            for ci in cis:
                if ci notin tr.definingConstraints or ci in ctEnforced:
                    fwdEnforced = true
                    break
            if fwdEnforced: break
        if not fwdEnforced: continue

        for ci in circuitByArray[pattern.arrayName]:
            if ci in tr.definingConstraints: continue
            tr.definingConstraints.incl(ci)
            stderr.writeLine("[FZN] Dropped circuit on channelized inverse array '" &
                             pattern.arrayName & "' (implied by forward-side circuit)")


proc rewriteInverseChannelIndexedElements(tr: var FznTranslator) =
    if tr.inverseChannelPatterns.len == 0: return

    # Map channel-side element name -> (pattern index, 1-based slot k)
    var chanElemOwner: Table[string, (int, int)]
    for pi in 0..<tr.inverseChannelPatterns.len:
        if not tr.inverseChannelPatternIsBuildable(pi): continue
        let arrName = tr.inverseChannelPatterns[pi].arrayName
        if arrName notin tr.arrayElementNames: continue
        for k0, en in tr.arrayElementNames[arrName]:
            if en.len > 0 and en in tr.varPositions and
               tr.sys.baseArray.domain[tr.varPositions[en]].len > 1:
                chanElemOwner[en] = (pi, k0 + 1)
    if chanElemOwner.len == 0: return

    # Collect rewritable element constraints grouped by (pattern, lookup array)
    type InvElemOrig = object
        ci: int
        k: int              # 1-based channel slot
        target: FznExpr
    var groups: Table[(int, string), seq[InvElemOrig]]
    var groupArrayArg: Table[(int, string), FznExpr]
    # All surviving var-element constraints, for subsumption lookups:
    # (indexVarName, arrayKey) -> targets
    var existingElems: Table[(string, string), seq[FznExpr]]

    proc arrayKeyOf(arg: FznExpr): string =
        case arg.kind
        of FznIdent:
            return arg.ident
        of FznArrayLit:
            for e in arg.elems:
                case e.kind
                of FznIdent: result.add(e.ident & ",")
                of FznIntLit: result.add($e.intVal & ",")
                else: return ""
        else:
            return ""

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
        if con.hasAnnotation("defines_var"): continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent: continue
        if con.args[2].kind notin {FznIdent, FznIntLit}: continue
        let key = arrayKeyOf(con.args[1])
        if key == "": continue
        existingElems.mgetOrPut((con.args[0].ident, key), @[]).add(con.args[2])
        if con.args[0].ident notin chanElemOwner: continue
        let (pi, k) = chanElemOwner[con.args[0].ident]
        groups.mgetOrPut((pi, key), @[]).add(InvElemOrig(ci: ci, k: k, target: con.args[2]))
        if (pi, key) notin groupArrayArg:
            groupArrayArg[(pi, key)] = con.args[1]

    if groups.len == 0: return

    proc sameExpr(a, b: FznExpr): bool =
        if a.kind != b.kind: return false
        case a.kind
        of FznIdent: a.ident == b.ident
        of FznIntLit: a.intVal == b.intVal
        else: false

    var nConsumed = 0
    var nEmitted = 0
    var nSubsumed = 0
    for piKey, origs in groups.pairs:
        let (pi, key) = piKey
        let pattern = tr.inverseChannelPatterns[pi]
        let nSlots = tr.arrayPositions[pattern.arrayName].len
        let arrArg = groupArrayArg[piKey]

        # Resolve the lookup array X as raw expressions (idents / literals)
        var xExprs: seq[FznExpr]
        case arrArg.kind
        of FznArrayLit:
            xExprs = arrArg.elems
        of FznIdent:
            xExprs = tr.presolveResolveVarElems(arrArg)
        else:
            continue
        if xExprs.len == 0: continue
        var xShapeOk = true
        for e in xExprs:
            if e.kind notin {FznIdent, FznIntLit}:
                xShapeOk = false
                break
        if not xShapeOk: continue

        # Targets per constrained slot k; bail on conflicting duplicates
        var targetByK: Table[int, FznExpr]
        var groupOk = true
        for o in origs:
            if o.k in targetByK:
                if not sameExpr(targetByK[o.k], o.target):
                    groupOk = false
                    break
            else:
                targetByK[o.k] = o.target
        if not groupOk: continue

        # Forward vars sorted by their result value r; every r must index X
        var fwdPairs: seq[(int, string)]
        for ii in 0..<pattern.resultValues.len:
            fwdPairs.add((pattern.resultValues[ii], pattern.indexVarNames[ii]))
        fwdPairs.sort(proc(a, b: (int, string)): int = cmp(a[0], b[0]))
        for (r, fName) in fwdPairs:
            if r < 1 or r > xExprs.len or fName notin tr.varPositions:
                groupOk = false
                break
        if not groupOk: continue

        # Pre-resolve the rewritten W-slot entries; bail if any target or X
        # entry cannot be resolved to a position/constant.
        var emitSpecs: seq[tuple[fPos: int, target: FznExpr]]
        var allResolved = true
        for (r, fName) in fwdPairs:
            let fPos = tr.varPositions[fName]
            # Vacuous when the forward var can never point into a constrained slot
            var reachable = false
            for v in tr.sys.baseArray.domain[fPos]:
                if v in targetByK:
                    reachable = true
                    break
            if not reachable: continue
            let selfTarget = xExprs[r-1]
            # Subsumption: an existing element over the same array with the
            # same index var and target X[r] implies the rewritten constraint
            # (it pins X[f_r] = X[r] for every value of f_r, not just k in K).
            var subsumed = false
            if (fName, key) in existingElems:
                for t in existingElems[(fName, key)]:
                    if sameExpr(t, selfTarget):
                        subsumed = true
                        break
            if subsumed:
                inc nSubsumed
                continue
            # Tautology: when the lookup array X is the forward array itself
            # (mutual-inverse consistency elements F[A_k] = k), the rewritten
            # form reads "f_r = k -> f_r = k". The runtime would disable these
            # as zero-gradient anyway; skip emitting them.
            if selfTarget.kind == FznIdent and selfTarget.ident == fName:
                var allIdentity = true
                for k, t in targetByK:
                    if not (t.kind == FznIntLit and t.intVal == k):
                        allIdentity = false
                        break
                if allIdentity:
                    inc nSubsumed
                    continue
            if selfTarget.kind == FznIdent and selfTarget.ident notin tr.varPositions and
               selfTarget.ident notin tr.paramValues:
                allResolved = false
                break
            emitSpecs.add((fPos: fPos, target: selfTarget))
        if not allResolved: continue
        for o in origs:
            let t = o.target
            if t.kind == FznIdent and t.ident notin tr.varPositions and
               t.ident notin tr.paramValues:
                allResolved = false
                break
        if not allResolved: continue

        proc toArrayElement(tr: FznTranslator, e: FznExpr): ArrayElement[int] =
            case e.kind
            of FznIntLit:
                ArrayElement[int](isConstant: true, constantValue: e.intVal)
            of FznIdent:
                if e.ident in tr.varPositions:
                    ArrayElement[int](isConstant: false, variablePosition: tr.varPositions[e.ident])
                else:
                    ArrayElement[int](isConstant: true, constantValue: tr.paramValues[e.ident])
            else:
                ArrayElement[int](isConstant: true, constantValue: 0)

        # Emit the rewritten forward-side elements
        for spec in emitSpecs:
            if spec.target.kind == FznIdent and spec.target.ident in tr.varPositions:
                # Position-based element: raw 1-based index values land on a
                # length nSlots+1 array padded with a self-target at slot 0.
                var w = newSeq[ArrayElement[int]](nSlots + 1)
                w[0] = tr.toArrayElement(spec.target)
                for k in 1..nSlots:
                    let entry = if k in targetByK: targetByK[k] else: spec.target
                    w[k] = tr.toArrayElement(entry)
                tr.sys.addConstraint(element(
                    tr.getExpr(spec.fPos), w,
                    tr.getExpr(tr.varPositions[spec.target.ident])))
            else:
                # Constant target: expression-based element with 0-based index
                var arrayExprs = newSeq[AlgebraicExpression[int]](nSlots)
                for k in 1..nSlots:
                    let entry = if k in targetByK: targetByK[k] else: spec.target
                    arrayExprs[k-1] = tr.resolveExprArg(entry)
                tr.sys.addConstraint(elementExpr(
                    tr.getExpr(spec.fPos) - 1, arrayExprs, tr.resolveExprArg(spec.target)))
            inc nEmitted

        # Consume the originals
        for o in origs:
            tr.definingConstraints.incl(o.ci)
            inc nConsumed

    if nConsumed > 0:
        stderr.writeLine("[FZN] Inverse-indexed element rewrite: " & $nConsumed &
                         " channel-index elements -> " & $nEmitted &
                         " forward-side elements (" & $nSubsumed &
                         " implied by existing constraints)")
