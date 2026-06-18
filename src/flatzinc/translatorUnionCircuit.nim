## Included from translator.nim -- not a standalone module.
##
## Detects MiniZinc's `union_circuit(x, y)` decomposition and rewrites it to the
## matching-level form. The decomposition (e.g. the perfect-1-factorization model
## p1f) lowers to:
##
##   c[i] selected by  array_var_int_element(idx_i, [x_i, y_i], c_i)   (2-way pick)
##   crusher_circuit([c_0, .., c_{n-1}])
##
## with x and y the two matchings (already fixed-point-free involutions). The
## circuit over the derived `c` puts the whole penalty on channel variables, which
## local search handles poorly. Since x and y are involutions, `union_circuit`
## holds iff the graph {i—x[i]} ∪ {i—y[i]} is a single cycle — so the constraint
## is replaced by `unionCycle(x, y)` directly on the matchings, dropping the
## selectors and the channel circuit. An `involution` penalty is also posted on
## each matching row (the inverse groups only supply moves; without a posted
## penalty the search drifts off the involution manifold).


proc detectUnionCircuits(tr: var FznTranslator) =
    # Index every 2-element selector element by the variable it defines:
    #   array_var_int_element(idx, A, c) with A = [x, y].
    # NB: do NOT skip constraints already in definingConstraints — the selector
    # elements carry `defines_var(c_i)`, so they are marked consumed (channelized)
    # before this pass. We only read their structure to recover the matchings.
    var selectorByResult: Table[string, tuple[idxName, arrName: string]]
    for ci, con in tr.model.constraints:
        if stripSolverPrefix(con.name) notin ["array_var_int_element", "array_var_int_element_nonshifted"]:
            continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent: continue           # index selector var
        if con.args[1].kind != FznIdent: continue           # named array
        if con.args[2].kind != FznIdent: continue           # result (channel) var
        let arrName = con.args[1].ident
        if arrName notin tr.arrayElementNames: continue
        if tr.arrayElementNames[arrName].len != 2: continue  # exactly [x_i, y_i]
        selectorByResult[con.args[2].ident] = (idxName: con.args[0].ident, arrName: arrName)
    if selectorByResult.len == 0: return

    var distinctRows: HashSet[string]
    var rowsToPost: seq[seq[int]]
    var nDetected = 0

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue           # circuit must be live
        if stripSolverPrefix(con.name) notin ["crusher_circuit", "fzn_circuit"]: continue
        if con.args.len < 1 or con.args[0].kind != FznIdent: continue
        let cArr = con.args[0].ident
        if cArr notin tr.arrayElementNames: continue
        let cElems = tr.arrayElementNames[cArr]              # [c_0 .. c_{n-1}], node order
        let n = cElems.len
        if n < 3: continue

        # Every c_i must be the result of a 2-way selector over [x_i, y_i].
        var xNames = newSeq[string](n)
        var yNames = newSeq[string](n)
        var ok = true
        for i, cn in cElems:
            if cn notin selectorByResult: ok = false; break
            let pair = tr.arrayElementNames[selectorByResult[cn].arrName]
            if pair.len != 2 or pair[0] notin tr.varPositions or pair[1] notin tr.varPositions:
                ok = false; break
            xNames[i] = pair[0]
            yNames[i] = pair[1]
        if not ok: continue

        var xPos = newSeq[int](n)
        var yPos = newSeq[int](n)
        for i in 0..<n:
            xPos[i] = tr.varPositions[xNames[i]]
            yPos[i] = tr.varPositions[yNames[i]]

        # Replace the channel circuit with a matching-level union-cycle constraint.
        tr.sys.addConstraint(unionCycle[int](xPos, yPos))
        tr.definingConstraints.incl(ci)
        nDetected += 1

        for row in [xPos, yPos]:
            let key = $row
            if key notin distinctRows:
                distinctRows.incl(key)
                rowsToPost.add(row)

    if nDetected == 0: return

    # Post an involution penalty on each matching row (x[x[i]] = i), so cost 0 is
    # a genuine involution rather than the inverse-group moves' invariant alone.
    for row in rowsToPost:
        tr.sys.addConstraint(involution[int](row))

    stderr.writeLine("[FZN] Detected " & $nDetected &
                     " union_circuit pattern(s) -> unionCycle on matchings (" &
                     $rowsToPost.len & " involution penalties posted)")
