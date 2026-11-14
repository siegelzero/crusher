## Included from translator.nim -- not a standalone module.
## Local existential projection.
##
## A group Y of small-domain search variables whose whole influence is a few
## local constraints C (directly, or through element/expression channels D
## computed from them) can be projected out: for every combination of the
## other values C and D read (the interface X), enumerate Y and keep the least
## penalty and a Y achieving it. C is replaced by one graduated constraint on a
## channel cost(X) = min_Y pen(C), and every y in Y becomes a channel
## y = witness_y(X). The projection is exact: X admits a zero-cost Y iff it
## extends to a solution of C, and the witness is such a Y.
##
## Multiple constant multiplication: per adder a, the shifts ka[a], kai[a,l]
## and kai[a,r] only enter ka*ca = kai_l*cai_l + kai_r*cai_r and two sign
## side conditions. Local search had to change a shift together with every
## change of a constant or an operand index; after projection the adders cost
## only "is ca[a] a shift-add of these two operands".

const
    ProjMaxYDomain = 64          # candidate search variables: domain size
    ProjMaxClusterCons = 12      # constraints influenced by one cluster
    ProjMaxConsArity = 24        # positions of one influenced constraint
    ProjMaxDerived = 24          # channels computed from one cluster
    ProjMaxInterface = 5         # interface columns
    ProjMaxXProduct = 50_000     # interface value combinations
    ProjMaxYProduct = 4096       # projected value combinations
    ProjMaxClusterWork = 4_000_000  # X × Y combinations of one cluster
    ProjMaxTotalWork = 40_000_000   # over all clusters
    ProjMaxRankRange = 100_000   # value range of a rank lookup

proc projValueSet(tr: FznTranslator, pos: int, elemBind, exprBind: Table[int, int],
                  depth: int = 0): seq[int] =
    ## Every value position pos can take: its domain for a search position, the
    ## union of reachable entries for an element channel, the image of the input
    ## domains for an expression channel. Empty when unknown or too large.
    template arr: untyped = tr.sys.baseArray
    if pos notin arr.channelPositions:
        return arr.domain[pos].sorted()
    if depth > 3: return @[]
    var vals: HashSet[int]
    if pos in elemBind:
        let b = arr.channelBindings[elemBind[pos]]
        # Reachable indices: image of the index expression over its inputs.
        var idxs: seq[int]
        let ips = toSeq(b.indexExpression.positions.items)
        var idxVals: seq[seq[int]]
        var prod = 1
        for p in ips:
            let vs = tr.projValueSet(p, elemBind, exprBind, depth + 1)
            if vs.len == 0: return @[]
            idxVals.add(vs)
            prod *= vs.len
            if prod > 4096: break
        if prod <= 4096:
            var asg = initTable[int, int]()
            var seen: HashSet[int]
            var ctr = newSeq[int](ips.len)
            while true:
                for i, p in ips: asg[p] = idxVals[i][ctr[i]]
                let v = b.indexExpression.evaluate(asg)
                if v notin seen:
                    seen.incl(v)
                    idxs.add(v)
                var k = 0
                while k < ips.len:
                    inc ctr[k]
                    if ctr[k] < idxVals[k].len: break
                    ctr[k] = 0
                    inc k
                if k == ips.len: break
        else:
            idxs = toSeq(0..<b.arrayElements.len)
        for i in idxs:
            if i < 0 or i >= b.arrayElements.len: continue
            let e = b.arrayElements[i]
            if e.isConstant:
                vals.incl(e.constantValue)
            else:
                let vs = tr.projValueSet(e.variablePosition, elemBind, exprBind, depth + 1)
                if vs.len == 0: return @[]
                for v in vs: vals.incl(v + e.offset)
            if vals.len > 4096: return @[]
    elif pos in exprBind:
        let b = arr.expressionChannelBindings[exprBind[pos]]
        let ips = toSeq(b.expression.positions.items)
        var inVals: seq[seq[int]]
        var prod = 1
        for p in ips:
            let vs = tr.projValueSet(p, elemBind, exprBind, depth + 1)
            if vs.len == 0: return @[]
            inVals.add(vs)
            prod *= vs.len
            if prod > 4096: return @[]
        var asg = initTable[int, int]()
        var ctr = newSeq[int](ips.len)
        while true:
            for i, p in ips: asg[p] = inVals[i][ctr[i]]
            vals.incl(b.expression.evaluate(asg))
            var k = 0
            while k < ips.len:
                inc ctr[k]
                if ctr[k] < inVals[k].len: break
                ctr[k] = 0
                inc k
            if k == ips.len: break
    else:
        return @[]
    result = toSeq(vals.items)
    result.sort()

proc projExact(c: StatefulConstraint[int]): bool =
    ## Constraint kinds whose stateless penalty (evaluateConstraint) is exact.
    ## Others are left alone (a cumulative with a variable limit, for one,
    ## would be evaluated against its constant field).
    case c.stateType
    of AlgebraicType, RelationalType: true
    of BooleanType:
        let bc = c.booleanState
        if bc.isUnary: projExact(bc.targetConstraint)
        else: projExact(bc.leftConstraint) and projExact(bc.rightConstraint)
    else: false

proc projPenalty(c: StatefulConstraint[int], asg: seq[int]): int =
    if c.stateType == RelationalType:
        let rc = c.relationalState
        let l = evaluateExpression(rc.leftExpr, asg)
        let r = evaluateExpression(rc.rightExpr, asg)
        if rc.graduated and rc.relation == EqualTo: abs(l - r)
        else: rc.relation.penalty(l, r)
    else:
        evaluateConstraint(c, asg)

proc projChannelInputs(arr: ConstrainedArray[int], p: int,
                       elemBind, exprBind: Table[int, int]): seq[int] =
    if p in elemBind:
        let b = arr.channelBindings[elemBind[p]]
        for q in b.indexExpression.positions.items: result.add(q)
        for e in b.arrayElements:
            if not e.isConstant: result.add(e.variablePosition)
    elif p in exprBind:
        for q in arr.expressionChannelBindings[exprBind[p]].expression.positions.items:
            result.add(q)

proc projClusterShape(arr: ConstrainedArray[int], ys: seq[int],
                      derivedOf, consOf: Table[int, seq[int]],
                      elemBind, exprBind: Table[int, int], opaque, constPos: PackedSet[int]):
        tuple[y, d, x: PackedSet[int], inner, cons: seq[int]] =
    ## Projected set, derived channels, interface and influenced constraints of
    ## the cluster formed by candidates ys. Interface channels computed from
    ## other interface values only (MCM: ca[a] != 0 reifications) move to
    ## `inner`, in evaluation order: they are recomputed, not enumerated.
    for y in ys:
        result.y.incl(y)
        for d in derivedOf[y]: result.d.incl(d)
        for ci in consOf[y]:
            if ci notin result.cons: result.cons.add(ci)
    result.cons.sort()
    var reads: seq[int]
    for ci in result.cons:
        for p in arr.constraints[ci].positions.items: reads.add(p)
    for d in result.d.items:
        if d in elemBind:
            let b = arr.channelBindings[elemBind[d]]
            for p in b.indexExpression.positions.items: reads.add(p)
            for e in b.arrayElements:
                if not e.isConstant: reads.add(e.variablePosition)
        else:
            for p in arr.expressionChannelBindings[exprBind[d]].expression.positions.items:
                reads.add(p)
    for p in reads:
        if p notin result.y and p notin result.d: result.x.incl(p)
    var changed = true
    while changed:
        changed = false
        for p in toSeq(result.x.items):
            if p in constPos:
                result.x.excl(p)
                result.inner.add(p)
                changed = true
                continue
            if p notin arr.channelPositions or p in opaque: continue
            if p notin elemBind and p notin exprBind: continue
            let ins = projChannelInputs(arr, p, elemBind, exprBind)
            var ok = true
            for q in ins:
                if q == p or (q notin result.x and q notin result.inner): ok = false
            if not ok: continue
            # Keep its inputs as interface (they may be read only through p).
            for q in ins: result.x.incl(q)
            result.x.excl(p)
            result.inner.add(p)
            changed = true
    # Evaluation order: an inner channel after the inner channels it reads.
    var ordered: seq[int]
    var done: PackedSet[int]
    proc visit(p: int, inner: seq[int], done: var PackedSet[int], ordered: var seq[int]) =
        if p in done: return
        done.incl(p)
        for q in projChannelInputs(arr, p, elemBind, exprBind):
            if q in inner: visit(q, inner, done, ordered)
        ordered.add(p)
    for p in result.inner: visit(p, result.inner, done, ordered)
    result.inner = ordered

proc projectLocalExistentials(tr: var FznTranslator) =
    template arr: untyped = tr.sys.baseArray
    let n = tr.sys.baseArray.len
    if n == 0: return
    if tr.objectivePos == ObjPosWeightedSV or tr.objectivePos == ObjPosBinaryPairwiseSum:
        return
    var objPositions: PackedSet[int]
    if tr.objectivePos >= 0: objPositions.incl(tr.objectivePos)
    if tr.objectivePos == ObjPosDefinedExpr and not tr.objectiveDefExpr.isNil:
        for p in tr.objectiveDefExpr.positions.items: objPositions.incl(p)

    # Channel kinds and readers.
    var elemBind, exprBind: Table[int, int]
    var chanReaders = newSeq[seq[int]](n)
    block:
        for bi, b in arr.channelBindings:
            elemBind[b.channelPosition] = bi
            for p in b.indexExpression.positions.items:
                chanReaders[p].add(b.channelPosition)
            for e in b.arrayElements:
                if not e.isConstant and b.channelPosition notin chanReaders[e.variablePosition]:
                    chanReaders[e.variablePosition].add(b.channelPosition)
        for bi, b in arr.expressionChannelBindings:
            exprBind[b.channelPosition] = bi
            for p in b.expression.positions.items:
                chanReaders[p].add(b.channelPosition)
    # Positions read by any other channel kind or grouping structure: values
    # there feed computations this pass cannot evaluate.
    var opaque: PackedSet[int]
    block:
        for p in arr.minMaxChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.countEqChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.weightedCountEqChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.conditionalCountEqChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.argmaxChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.crossingCountMaxChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.profileMaxChannelsAtPosition.keys: opaque.incl(p)
        for p in arr.inverseChannelsAtPosition.keys: opaque.incl(p)
        for g in arr.inverseChannelGroups:
            for p in g.inversePositions: opaque.incl(p)
        for g in arr.inverseGroups:
            for p in g.positions: opaque.incl(p)
        for g in arr.partitionGroups:
            for p in g.searchPositions: opaque.incl(p)
        for d in arr.dormancyBindings:
            opaque.incl(d.dormantPos)
            opaque.incl(d.selectorPos)
        for p in arr.channelPositions.items:
            if p notin elemBind and p notin exprBind: opaque.incl(p)

    # Channels without any binding whose domain is one value (a reification
    # presolve decided, MCM: cansh[a] == 0) hold that value: constants here.
    var constPos: PackedSet[int]
    block:
        var bound: PackedSet[int]
        for b in arr.minMaxChannelBindings: bound.incl(b.channelPosition)
        for b in arr.countEqChannelBindings: bound.incl(b.channelPosition)
        for b in arr.weightedCountEqChannelBindings: bound.incl(b.channelPosition)
        for b in arr.conditionalCountEqChannelBindings: bound.incl(b.channelPosition)
        for b in arr.argmaxChannelBindings: bound.incl(b.channelPosition)
        for b in arr.crossingCountMaxChannelBindings: bound.incl(b.channelPosition)
        for b in arr.profileMaxChannelBindings: bound.incl(b.channelPosition)
        for g in arr.inverseChannelGroups:
            for p in g.inversePositions: bound.incl(p)
        for p in arr.channelPositions.items:
            if p notin elemBind and p notin exprBind and p notin bound and
                    arr.domain[p].len == 1:
                constPos.incl(p)

    var consAt = newSeq[seq[int]](n)
    for ci, c in tr.sys.baseArray.constraints:
        for p in c.positions.items:
            consAt[p].add(ci)

    # Candidates: each with its derived channels and influenced constraints.
    var derivedOf = initTable[int, seq[int]]()
    var consOf = initTable[int, seq[int]]()
    for y in 0..<n:
        if y in arr.channelPositions or y in arr.fixedPositions: continue
        let dl = arr.domain[y].len
        if dl < 2 or dl > ProjMaxYDomain: continue
        if y in opaque or y in objPositions: continue
        var derived: seq[int]
        var seen: PackedSet[int]
        seen.incl(y)
        var stack = @[y]
        var ok = true
        while stack.len > 0 and ok:
            let p = stack.pop()
            for c in chanReaders[p]:
                if c in seen: continue
                if c in opaque or c in objPositions or derived.len >= ProjMaxDerived:
                    ok = false
                    break
                seen.incl(c)
                derived.add(c)
                stack.add(c)
        if not ok: continue
        var cons: seq[int]
        for p in seen.items:
            for ci in consAt[p]:
                if ci notin cons: cons.add(ci)
        if cons.len == 0 or cons.len > ProjMaxClusterCons: continue
        for ci in cons:
            if tr.sys.baseArray.constraints[ci].positions.card > ProjMaxConsArity or
                    not projExact(tr.sys.baseArray.constraints[ci]):
                ok = false
                break
        if not ok: continue
        derivedOf[y] = derived
        consOf[y] = cons

    if consOf.len == 0: return

    # Clusters: candidates sharing an influenced constraint, merged only while
    # the merged cluster keeps a small interface. (MCM: an operand index shares
    # the adder's sum with the shifts, but merging it would pull every constant
    # it can select into the interface; it stays a search variable.)
    var ysSorted = toSeq(consOf.keys)
    ysSorted.sort()
    var clusterOf = initTable[int, int]()
    var members: seq[seq[int]]
    for y in ysSorted:
        clusterOf[y] = members.len
        members.add(@[y])
    var owners = initTable[int, seq[int]]()
    for y in ysSorted:
        for ci in consOf[y]:
            owners.mgetOrPut(ci, @[]).add(y)
    var ownedCons = toSeq(owners.keys)
    ownedCons.sort()
    for ci in ownedCons:
        let os = owners[ci]
        for i in 0..<os.len:
            for j in (i + 1)..<os.len:
                let a = clusterOf[os[i]]
                let b = clusterOf[os[j]]
                if a == b: continue
                let merged = members[a] & members[b]
                let sh = projClusterShape(arr, merged, derivedOf, consOf, elemBind, exprBind, opaque, constPos)
                if sh.cons.len > ProjMaxClusterCons or sh.d.card > ProjMaxDerived or
                        sh.x.card > ProjMaxInterface:
                    continue
                for y in members[b]: clusterOf[y] = a
                members[a] = merged
                members[b] = @[]

    var removeCons: PackedSet[int]
    var takenY, takenX, takenD: PackedSet[int]
    var totalWork = 0
    var nClusters, nProjected, nRemoved = 0
    for ci0 in 0..<members.len:
        if members[ci0].len == 0: continue
        var ys = members[ci0]
        ys.sort()
        let sh = projClusterShape(arr, ys, derivedOf, consOf, elemBind, exprBind, opaque, constPos)
        let ySet = sh.y
        let dSet = sh.d
        let xSet = sh.x
        let cons = sh.cons
        var bad = cons.len > ProjMaxClusterCons or dSet.card > ProjMaxDerived
        # Accepted clusters must not overlap: none removes a constraint another
        # projected, derives what another reads, or reads what another projects.
        for ci in cons:
            if ci in removeCons: bad = true
        for d in dSet.items:
            if d in takenD or d in takenY or d in takenX: bad = true
        for y in ySet.items:
            if y in takenX or y in takenD: bad = true
        for x in xSet.items:
            if x in takenY or x in takenD: bad = true
        # One variable gains little (a tabu move already tries all its values
        # against the current interface); the point is changing several
        # together. With no interface the cluster is a whole component.
        if bad or ys.len < 2 or xSet.len == 0 or xSet.len > ProjMaxInterface: continue
        let xs = toSeq(xSet.items)
        var xVals: seq[seq[int]]
        var xProd = 1
        for x in xs:
            let vs = tr.projValueSet(x, elemBind, exprBind)
            if vs.len == 0 or vs[^1] - vs[0] >= ProjMaxRankRange:
                bad = true
                break
            xVals.add(vs)
            xProd *= vs.len
            if xProd > ProjMaxXProduct:
                bad = true
                break
        if bad: continue
        var yProd = 1
        for y in ys:
            yProd *= arr.domain[y].len
            if yProd > ProjMaxYProduct:
                bad = true
                break
        if bad or xProd * yProd > ProjMaxClusterWork or totalWork + xProd * yProd > ProjMaxTotalWork:
            continue

        # Derived channels in dependency order.
        var order: seq[int]
        block:
            var done: PackedSet[int]
            proc visit(d: int, dSet: PackedSet[int], done: var PackedSet[int],
                       order: var seq[int], arr: ConstrainedArray[int]) =
                if d in done: return
                done.incl(d)
                var ins: seq[int]
                if d in elemBind:
                    let b = arr.channelBindings[elemBind[d]]
                    for p in b.indexExpression.positions.items: ins.add(p)
                    for e in b.arrayElements:
                        if not e.isConstant: ins.add(e.variablePosition)
                else:
                    for p in arr.expressionChannelBindings[exprBind[d]].expression.positions.items:
                        ins.add(p)
                for p in ins:
                    if p in dSet: visit(p, dSet, done, order, arr)
                order.add(d)
            for d in dSet.items: visit(d, dSet, done, order, arr)

        # Enumerate.
        var asg = newSeq[int](n)
        var yVals: seq[seq[int]]
        for y in ys: yVals.add(arr.domain[y])
        let nKeys = xProd
        var costs = newSeq[int](nKeys)
        var witness = newSeq[seq[int]](ys.len)
        for i in 0..<ys.len: witness[i] = newSeq[int](nKeys)
        var xc = newSeq[int](xs.len)
        var key = 0
        var unsupported = false
        while true:
            for i, x in xs: asg[x] = xVals[i][xc[i]]
            var xValid = true
            for p in sh.inner:
                if p in constPos:
                    asg[p] = arr.domain[p][0]
                elif p in elemBind:
                    let b = arr.channelBindings[elemBind[p]]
                    let idx = b.evalIndex(asg)
                    if idx < 0 or idx >= b.arrayElements.len:
                        xValid = false
                        break
                    let e = b.arrayElements[idx]
                    asg[p] = if e.isConstant: e.constantValue
                             else: asg[e.variablePosition] + e.offset
                else:
                    asg[p] = arr.expressionChannelBindings[exprBind[p]].evalExpr(asg)
            var best = high(int)
            var bestY = newSeq[int](ys.len)
            var yc = newSeq[int](ys.len)
            while xValid:
                for i, y in ys: asg[y] = yVals[i][yc[i]]
                var valid = true
                for d in order:
                    if d in elemBind:
                        let b = arr.channelBindings[elemBind[d]]
                        let idx = b.evalIndex(asg)
                        if idx < 0 or idx >= b.arrayElements.len:
                            valid = false
                            break
                        let e = b.arrayElements[idx]
                        asg[d] = if e.isConstant: e.constantValue
                                 else: asg[e.variablePosition] + e.offset
                    else:
                        asg[d] = arr.expressionChannelBindings[exprBind[d]].evalExpr(asg)
                if valid:
                    var pen = 0
                    for ci in cons:
                        var p = projPenalty(arr.constraints[ci], asg)
                        if p < 0:
                            unsupported = true
                            break
                        pen += p
                        if pen >= best: break
                    if unsupported: break
                    if pen < best:
                        best = pen
                        for i in 0..<ys.len: bestY[i] = asg[ys[i]]
                        if best == 0: break
                var k = 0
                while k < ys.len:
                    inc yc[k]
                    if yc[k] < yVals[k].len: break
                    yc[k] = 0
                    inc k
                if k == ys.len: break
            if unsupported: break
            if best == high(int):
                # No Y gives every derived channel a defined value.
                best = 1
                for i in 0..<ys.len: bestY[i] = yVals[i][0]
            costs[key] = best
            for i in 0..<ys.len: witness[i][key] = bestY[i]
            inc key
            # Advance X, last column fastest (matches the key below).
            var k = xs.len - 1
            while k >= 0:
                inc xc[k]
                if xc[k] < xVals[k].len: break
                xc[k] = 0
                dec k
            if k < 0: break
        if unsupported: continue
        totalWork += xProd * yProd
        inc nClusters

        # Key over value ranks of the interface columns.
        var keyExpr: AlgebraicExpression[int] = nil
        for i, x in xs:
            let vs = xVals[i]
            var rankExpr: AlgebraicExpression[int]
            if vs[^1] - vs[0] + 1 == vs.len:
                rankExpr = tr.getExpr(x) - vs[0]
            else:
                let rp = tr.sys.baseArray.len
                discard tr.sys.newConstrainedVariable()
                tr.sys.baseArray.setDomain(rp, toSeq(0..<vs.len))
                var elems = newSeq[ArrayElement[int]](vs[^1] - vs[0] + 1)
                for j in 0..<elems.len:
                    elems[j] = ArrayElement[int](isConstant: true, constantValue: 0)
                for r, v in vs:
                    elems[v - vs[0]] = ArrayElement[int](isConstant: true, constantValue: r)
                tr.sys.baseArray.addChannelBinding(rp, tr.getExpr(x) - vs[0], elems)
                rankExpr = tr.getExpr(rp)
            keyExpr = if keyExpr.isNil: rankExpr else: keyExpr * vs.len + rankExpr

        let cp = tr.sys.baseArray.len
        discard tr.sys.newConstrainedVariable()
        var costDom = costs.deduplicate()
        costDom.sort()
        tr.sys.baseArray.setDomain(cp, costDom)
        var costElems = newSeq[ArrayElement[int]](nKeys)
        for j in 0..<nKeys:
            costElems[j] = ArrayElement[int](isConstant: true, constantValue: costs[j])
        tr.sys.baseArray.addChannelBinding(cp, keyExpr, costElems)
        tr.sys.addConstraint(tr.getExpr(cp) <= 0)
        for i, y in ys:
            var wElems = newSeq[ArrayElement[int]](nKeys)
            for j in 0..<nKeys:
                wElems[j] = ArrayElement[int](isConstant: true, constantValue: witness[i][j])
            tr.sys.baseArray.addChannelBinding(y, keyExpr, wElems)
        for ci in cons: removeCons.incl(ci)
        for y in ySet.items: takenY.incl(y)
        for x in xSet.items: takenX.incl(x)
        for d in dSet.items: takenD.incl(d)
        nProjected += ys.len
        nRemoved += cons.len

    if removeCons.len > 0:
        var kept: seq[StatefulConstraint[int]]
        for ci, c in tr.sys.baseArray.constraints:
            if ci notin removeCons: kept.add(c)
        tr.sys.baseArray.constraints = kept
        tr.sys.baseArray.reducedDomain = @[]
        stderr.writeLine(&"[FZN] Local projection: {nClusters} clusters, {nProjected} search variables " &
                         &"projected out of {nRemoved} constraints")
