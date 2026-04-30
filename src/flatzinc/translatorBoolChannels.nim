## Included from translator.nim -- not a standalone module.
## Boolean channel detection: AND, equivalence, clause-iff, OR, gated, overlap, XOR, forward-backward.

proc detectBoolAndChannels*(tr: var FznTranslator) =
    ## Detects bool_clause([b], [c1, ..., cn]) where:
    ##   - b is a plain var bool appearing as positive literal in EXACTLY ONE bool_clause
    ##   - all ci are already channel variables (in channelVarNames)
    ##   - n >= 1
    ## These encode b = AND(c1, ..., cn). The constraint is consumed; b becomes a channel.
    ##
    ## In graph-clear: encodes var_i[e,t] = (var_l[e]<=t) AND (var_u[e]>=t) AND (var_t[i]!=t) AND (var_t[j]!=t)
    ## Requires: detectReifChannels() must have run first (to populate channelVarNames).

    # Pass 1: count how many bool_clause constraints have each var as sole positive literal
    var posLiteralCount = initTable[string, int]()
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        if posArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1: continue  # must have exactly 1 positive literal
        let posElem = posArg.elems[0]
        if posElem.kind != FznIdent: continue
        let bName = posElem.ident
        posLiteralCount[bName] = posLiteralCount.getOrDefault(bName, 0) + 1

    # Pass 2: for constraints where the positive literal appears exactly once and
    # all negative literals are channel variables, detect the AND pattern
    var detected = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue

        let posArg = con.args[0]
        if posArg.kind != FznArrayLit or posArg.elems.len != 1: continue
        let posElem = posArg.elems[0]
        if posElem.kind != FznIdent: continue
        let bName = posElem.ident

        # b must appear as positive literal in exactly one bool_clause
        if posLiteralCount.getOrDefault(bName, 0) != 1: continue

        # b must not already be a channel or defined var
        if bName in tr.channelVarNames: continue
        if bName in tr.definedVarNames: continue

        # Gather negative literals — all must be channel variables
        let negArg = con.args[1]
        if negArg.kind != FznArrayLit: continue
        if negArg.elems.len < 2: continue  # need at least 2 conditions;
            # trivial AND(x)=x consumes bool_clause constraints needed by
            # case-analysis for complete visit-time channel patterns

        var condNames: seq[string]
        var allChannels = true
        for elem in negArg.elems:
            if elem.kind != FznIdent or elem.ident notin tr.channelVarNames:
                allChannels = false
                break
            condNames.add(elem.ident)
        if not allChannels: continue

        # All checks passed: b = AND(c1, ..., cn)
        tr.boolAndChannelDefs.add((ci: ci, resultVar: bName, condVars: condNames))
        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool AND channels (b = AND(ci) from bool_clause)")

proc detectBoolEquivalenceChannels*(tr: var FznTranslator) =
    ## Detects mutual bool_clause implications that establish equivalence between
    ## boolean variables. For bool_clause([A],[B]) + bool_clause([B],[A]), we have
    ## A↔B. If one of them is already a channel, the other becomes an alias channel.
    ##
    ## Uses union-find for transitive closure: A↔B, B↔C → A↔B↔C.
    ## Must run after detectBoolAndChannels() so channelVarNames includes AND channels.

    # Step 1: Scan non-consumed bool_clause([X],[Y]) (1 pos, 1 neg) to build implication edges
    type ImplEdge = object
        fromVar, toVar: string
        ci: int

    var forwardImpls = initTable[string, seq[ImplEdge]]()  # from → edges (from→to means "to implies from")

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1 or negArg.elems.len != 1: continue
        let posLit = posArg.elems[0]
        let negLit = negArg.elems[0]
        if posLit.kind != FznIdent or negLit.kind != FznIdent: continue
        # bool_clause([A],[B]) means B → A (if B is true then A is true)
        let a = posLit.ident
        let b = negLit.ident
        # Skip if either is a constant parameter
        if a in tr.paramValues or b in tr.paramValues: continue
        # Skip if either is already consumed by value-support
        if a in tr.valueSupportConsumedBools or b in tr.valueSupportConsumedBools: continue
        forwardImpls.mgetOrPut(b, @[]).add(ImplEdge(fromVar: b, toVar: a, ci: ci))

    # Step 2: Find mutual pairs (A→B and B→A both exist)
    type MutualPair = object
        varA, varB: string
        ciAB, ciBA: int  # constraint indices for A→B and B→A

    var mutualPairs: seq[MutualPair]
    var usedCIs: PackedSet[int]

    for bVar, edges in forwardImpls:
        for edge in edges:
            let aVar = edge.toVar
            # Check if there's a reverse edge: aVar → bVar (i.e., aVar in forwardImpls keys with target bVar)
            if aVar in forwardImpls:
                for revEdge in forwardImpls[aVar]:
                    if revEdge.toVar == bVar and edge.ci notin usedCIs and revEdge.ci notin usedCIs:
                        mutualPairs.add(MutualPair(varA: aVar, varB: bVar,
                                                   ciAB: revEdge.ci, ciBA: edge.ci))
                        usedCIs.incl(edge.ci)
                        usedCIs.incl(revEdge.ci)
                        break

    if mutualPairs.len == 0: return

    # Step 3: Union-find for transitive closure
    var parent = initTable[string, string]()

    proc find(x: string): string =
        var cur = x
        while cur in parent and parent[cur] != cur:
            cur = parent[cur]
        # Path compression
        var compress = x
        while compress in parent and parent[compress] != cur:
            let next = parent[compress]
            parent[compress] = cur
            compress = next
        result = cur

    proc union(a, b: string) =
        let ra = find(a)
        let rb = find(b)
        if ra != rb:
            parent[ra] = rb

    for pair in mutualPairs:
        if pair.varA notin parent: parent[pair.varA] = pair.varA
        if pair.varB notin parent: parent[pair.varB] = pair.varB
        union(pair.varA, pair.varB)

    # Step 4: Group into equivalence classes
    var classes = initTable[string, seq[string]]()
    for v in parent.keys:
        let root = find(v)
        classes.mgetOrPut(root, @[]).add(v)

    # Step 5: For each class, find if any member is already a channel.
    # If so, all non-channel members become alias channels.
    var detected = 0
    # Build map from pair to consumed CIs for lookup
    var pairCIs = initTable[(string, string), seq[int]]()
    for pair in mutualPairs:
        pairCIs[(pair.varA, pair.varB)] = @[pair.ciAB, pair.ciBA]
        pairCIs[(pair.varB, pair.varA)] = @[pair.ciAB, pair.ciBA]

    # Build per-variable map to all pair CIs involving that variable (for chain consumption)
    var varPairCIs = initTable[string, seq[int]]()
    for pair in mutualPairs:
        varPairCIs.mgetOrPut(pair.varA, @[]).add(pair.ciAB)
        varPairCIs.mgetOrPut(pair.varA, @[]).add(pair.ciBA)
        varPairCIs.mgetOrPut(pair.varB, @[]).add(pair.ciAB)
        varPairCIs.mgetOrPut(pair.varB, @[]).add(pair.ciBA)

    for root, members in classes:
        # Find canonical (channel) member
        var canonical = ""
        for m in members:
            if m in tr.channelVarNames:
                canonical = m
                break
        if canonical == "":
            continue  # No channel in this class — skip

        for m in members:
            if m == canonical: continue
            if m in tr.channelVarNames: continue
            if m in tr.definedVarNames: continue
            # Find the CIs connecting m to canonical (may be indirect through chain).
            # Direct pair: consume just the pair's CIs.
            # Indirect chain: consume all pair CIs involving m to avoid redundant constraints.
            var consumedCIs: seq[int]
            if (m, canonical) in pairCIs:
                consumedCIs = pairCIs[(m, canonical)]
            elif m in varPairCIs:
                consumedCIs = varPairCIs[m]
            if consumedCIs.len == 0: continue

            tr.boolEquivAliasDefs.add((aliasVar: m, canonicalVar: canonical,
                                       consumedCIs: consumedCIs))
            tr.channelVarNames.incl(m)
            for ci in consumedCIs:
                tr.definingConstraints.incl(ci)
            inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool equivalence alias channels")

proc detectBoolClauseIffChannels*(tr: var FznTranslator) =
    ## Detects bool_clause([b],[c]) + bool_clause(pos, [b]) where c is a channel
    ## defined by bool_clause_reif(pos, neg, c), and the clause literals match c's
    ## defining clause. This establishes b ↔ c.
    ##
    ## Pattern in FlatZinc:
    ##   bool_clause_reif([x1,...,xn], [y1,...,ym], c)  :: defines_var(c)   -- c ↔ (∨xi ∨ ∨¬yj)
    ##   bool_clause([b], [c])                                              -- c → b
    ##   bool_clause([x1,...,xn], [b, y1,...,ym])                          -- b → (∨xi ∨ ∨¬yj)
    ##
    ## Proof: c → b (clause 1), b → (∨xi ∨ ∨¬yj) ↔ c (clause 2 + c defn), so b ↔ c.
    ## Must run after detectReifChannels() so bool_clause_reif channels are known.

    # Step 1: Build a map from channel var name → (posLitNames, negLitNames)
    # for channels defined by bool_clause_reif
    var reifChannelLits: Table[string, tuple[posLits, negLits: HashSet[string]]]

    for ci in tr.boolClauseReifChannelDefs:
        let con = tr.model.constraints[ci]
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let cName = con.args[2].ident
        var posLits, negLits: HashSet[string]
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind == FznArrayLit:
            for elem in posArg.elems:
                if elem.kind == FznIdent: posLits.incl(elem.ident)
        if negArg.kind == FznArrayLit:
            for elem in negArg.elems:
                if elem.kind == FznIdent: negLits.incl(elem.ident)
        reifChannelLits[cName] = (posLits: posLits, negLits: negLits)

    if reifChannelLits.len == 0: return

    # Step 2: Index bool_clause constraints by negative literal (sole variable in neg position)
    # For bool_clause([b], [c]): index by c → (b, ci)
    # For bool_clause([x1,...], [b, ...]): index by b → (posLits, otherNegs, ci)
    type
        SimpleImpl = object
            posVar: string  # b in bool_clause([b],[c])
            ci: int
        MultiClause = object
            posLits: HashSet[string]
            negLits: HashSet[string]  # other negs excluding the key variable
            ci: int

    var simpleByNeg = initTable[string, seq[SimpleImpl]]()  # c → [(b, ci)]
    var multiByNeg = initTable[string, seq[MultiClause]]()   # b → [(posLits, otherNegs, ci)]

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue

        if posArg.elems.len == 1 and negArg.elems.len == 1:
            # bool_clause([b],[c]) — simple implication c → b
            if posArg.elems[0].kind == FznIdent and negArg.elems[0].kind == FznIdent:
                simpleByNeg.mgetOrPut(negArg.elems[0].ident, @[]).add(
                    SimpleImpl(posVar: posArg.elems[0].ident, ci: ci))
        elif negArg.elems.len >= 1:
            # bool_clause(pos, neg) where neg has at least 1 element
            # Index by each neg literal as potential target variable
            var posLits: HashSet[string]
            var allIdent = true
            for elem in posArg.elems:
                if elem.kind != FznIdent:
                    allIdent = false
                    break
                posLits.incl(elem.ident)
            if not allIdent: continue

            var negNames: seq[string]
            allIdent = true
            for elem in negArg.elems:
                if elem.kind != FznIdent:
                    allIdent = false
                    break
                negNames.add(elem.ident)
            if not allIdent: continue

            for i, nName in negNames:
                var otherNegs: HashSet[string]
                for j, nn in negNames:
                    if j != i: otherNegs.incl(nn)
                multiByNeg.mgetOrPut(nName, @[]).add(
                    MultiClause(posLits: posLits, negLits: otherNegs, ci: ci))

    # Step 3: Match patterns. For each simple implication c → b where c is a reif channel:
    # Look for a multi-literal clause b → (∨pos ∨ ∨¬otherNegs) that matches c's definition.
    var detected = 0
    for cName, simples in simpleByNeg:
        if cName notin reifChannelLits: continue
        let cDef = reifChannelLits[cName]

        for simpl in simples:
            let bName = simpl.posVar
            if bName in tr.channelVarNames: continue
            if bName in tr.definedVarNames: continue
            if bName in tr.paramValues: continue
            if bName in tr.valueSupportConsumedBools: continue

            # Look for matching multi-literal clause with b as negative literal
            if bName notin multiByNeg: continue

            for multi in multiByNeg[bName]:
                # Check: posLits match c's posLits, and otherNegs match c's negLits
                if multi.posLits == cDef.posLits and multi.negLits == cDef.negLits:
                    # Match! b ↔ c
                    tr.boolEquivAliasDefs.add((aliasVar: bName, canonicalVar: cName,
                                               consumedCIs: @[simpl.ci, multi.ci]))
                    tr.channelVarNames.incl(bName)
                    tr.definingConstraints.incl(simpl.ci)
                    tr.definingConstraints.incl(multi.ci)
                    inc detected
                    break  # Found match for this b, move on

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool clause iff channels (b ↔ reif via two clauses)")

proc detectBoolOrChannels*(tr: var FznTranslator) =
    ## Detects boolean OR channels: b = c ∨ prev where c and prev are channels.
    ##
    ## Pattern in FlatZinc (from if-then-else on booleans):
    ##   bool_clause([b], [c])                           -- c → b
    ##   bool_eq_reif(b, prev, eq)  :: defines_var(eq)   -- eq ↔ (b = prev)
    ##   bool_clause([eq, c1, ..., cn], [])               -- eq ∨ c1 ∨ ... ∨ cn
    ##
    ## Where c is a channel defined by bool_clause_reif([c1,...,cn], [], c)
    ## meaning c ↔ (c1 ∨ ... ∨ cn).
    ##
    ## Proof: when c=1, b=1 (from clause 1). When c=0, all ci=0,
    ## so from clause 3: eq=1, meaning b=prev. So b = c ∨ prev.
    ##
    ## More generally: c ↔ (∨ci ∨ ∨¬negj), and the forcing clause is
    ## [eq, c1, ..., cn, neg1, ..., negm] / [] where ci are the pos literals
    ## and negj appear as positives (since ¬(¬negj) = negj).
    ## Wait, actually negj in bool_clause_reif are negated, so in the forcing
    ## clause they should NOT appear. Let me handle both empty-neg and general cases.
    ##
    ## Must run after detectBoolClauseIffChannels() and detectReifChannels().
    ## Runs in fixpoint loop to cascade through temporal chains.

    # Step 1: Build map from channel var → defining clause literals (same as iff detection)
    var reifChannelLits: Table[string, tuple[posLits: HashSet[string], negLits: HashSet[string]]]

    for ci in tr.boolClauseReifChannelDefs:
        let con = tr.model.constraints[ci]
        if con.args.len < 3 or con.args[2].kind != FznIdent: continue
        let cName = con.args[2].ident
        var posLits, negLits: HashSet[string]
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind == FznArrayLit:
            for elem in posArg.elems:
                if elem.kind == FznIdent: posLits.incl(elem.ident)
        if negArg.kind == FznArrayLit:
            for elem in negArg.elems:
                if elem.kind == FznIdent: negLits.incl(elem.ident)
        reifChannelLits[cName] = (posLits: posLits, negLits: negLits)

    # Also include array_bool_or channels: c = OR(c1, ..., cn)
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_or": continue
        if con.args.len < 2 or con.args[1].kind != FznIdent: continue
        let cName = con.args[1].ident
        let elems = tr.resolveVarArrayElems(con.args[0])
        var posLits: HashSet[string]
        for elem in elems:
            if elem.kind == FznIdent: posLits.incl(elem.ident)
        reifChannelLits[cName] = (posLits: posLits, negLits: initHashSet[string]())

    if reifChannelLits.len == 0: return

    # Step 2: Build index of simple implications: c → b from bool_clause([b],[c])
    var implByChannel = initTable[string, seq[tuple[bVar: string, ci: int]]]()
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1 or negArg.elems.len != 1: continue
        if posArg.elems[0].kind != FznIdent or negArg.elems[0].kind != FznIdent: continue
        let bName = posArg.elems[0].ident
        let cName = negArg.elems[0].ident
        if cName in tr.channelVarNames:
            implByChannel.mgetOrPut(cName, @[]).add((bVar: bName, ci: ci))

    # Step 3: Build index of bool_eq_reif(b, prev, eq) :: defines_var(eq)
    # Note: these constraints are already consumed by detectReifChannels (they define eq as
    # a channel). We scan ALL constraints here — we don't consume them, just use the info.
    # Maps b → [(prev, eq, ci)]
    var boolEqReifByFirst = initTable[string, seq[tuple[prevVar, eqVar: string, ci: int]]]()
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "bool_eq_reif": continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent or con.args[2].kind != FznIdent: continue
        let bName = con.args[0].ident
        let prevName = con.args[1].ident
        let eqName = con.args[2].ident
        boolEqReifByFirst.mgetOrPut(bName, @[]).add((prevVar: prevName, eqVar: eqName, ci: ci))

    # Step 4: Build index of forcing clauses: bool_clause([eq, ...], [])
    # Maps eq var → [(allPosLits, ci)]
    var forcingByEq = initTable[string, seq[tuple[otherLits: HashSet[string], ci: int]]]()
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len != 0: continue  # Must have empty negative literals
        if posArg.elems.len < 2: continue   # Need at least eq + one other
        var posNames: seq[string]
        var allIdent = true
        for elem in posArg.elems:
            if elem.kind != FznIdent:
                allIdent = false
                break
            posNames.add(elem.ident)
        if not allIdent: continue
        # Index by each element as potential eq variable
        for i, eqCandidate in posNames:
            var others: HashSet[string]
            for j, name in posNames:
                if j != i: others.incl(name)
            forcingByEq.mgetOrPut(eqCandidate, @[]).add((otherLits: others, ci: ci))

    # Step 5: Match the three-constraint pattern
    var detected = 0
    for cName, impls in implByChannel:
        if cName notin reifChannelLits: continue
        let cDef = reifChannelLits[cName]
        # Only handle case where c's reif has empty negLits (most common)
        if cDef.negLits.len > 0: continue

        for impl in impls:
            let bName = impl.bVar
            if bName in tr.channelVarNames: continue
            if bName in tr.definedVarNames: continue
            if bName in tr.paramValues: continue
            if bName in tr.valueSupportConsumedBools: continue

            # Look for bool_eq_reif(b, prev, eq)
            if bName notin boolEqReifByFirst: continue

            for eqDef in boolEqReifByFirst[bName]:
                let prevName = eqDef.prevVar
                let eqName = eqDef.eqVar

                # prev must be a channel variable (or will become one via fixpoint)
                if prevName notin tr.channelVarNames: continue

                # Look for forcing clause: bool_clause([eq, c1, ..., cn], [])
                if eqName notin forcingByEq: continue

                for forcing in forcingByEq[eqName]:
                    # The other literals in the forcing clause should match c's pos literals
                    if forcing.otherLits == cDef.posLits:
                        # Match! b = c ∨ prev
                        tr.boolOrChannelDefs.add((
                            targetVar: bName,
                            condChannel: cName,
                            prevChannel: prevName,
                            consumedCIs: @[impl.ci, forcing.ci]))
                        tr.channelVarNames.incl(bName)
                        tr.definingConstraints.incl(impl.ci)
                        tr.definingConstraints.incl(forcing.ci)
                        # Note: we do NOT consume the bool_eq_reif constraint — it defines
                        # eq which may be used in other reif chains. But eq's channel was
                        # already built by detectReifChannels. We just don't need it for b.
                        inc detected
                        break  # Found match
                if bName in tr.channelVarNames: break  # Already matched

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool OR channels (b = c ∨ prev from if-then-else)")

proc detectBoolGatedVariableChannels*(tr: var FznTranslator) =
    ## Detects patterns where a variable is conditionally assigned either a variable
    ## value or a constant, gated by a boolean channel condition:
    ##   x = if cond then y else constant
    ##
    ## Pattern in FlatZinc (via bool_clause implications):
    ##   int_eq_reif(x, y, B_eq)   :: defines_var(B_eq)  -- B_eq ↔ (x == y)
    ##   bool_clause([B_eq], [cond])                       -- cond → x == y
    ##   plus: default value when ¬cond is derivable from target domain + other implications
    ##
    ## The condition variable must be a boolean channel. The target must not already
    ## be a channel or defined. One branch has a variable value, the other a constant.
    ##
    ## Must run after detectConditionalImplicationChannels() and detectBoolEquivalenceChannels().

    # Step 1: Build eq_reif reverse map: output bool var → (sourceVar, testVal)
    # Scan ALL int_eq_reif constraints (not just reifChannelDefs) because
    # some eq_reif outputs end up as definedVars rather than channels, but
    # the semantic relationship (b ↔ x == val) is still needed for matching.
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        eqReifMap[con.args[2].ident] = (sourceVar: con.args[0].ident, testVal: con.args[1])

    # Step 1b: Extend eqReifMap with bool equivalence aliases
    for def in tr.boolEquivAliasDefs:
        if def.canonicalVar in eqReifMap and def.aliasVar notin eqReifMap:
            eqReifMap[def.aliasVar] = eqReifMap[def.canonicalVar]

    # Step 2: Scan non-consumed bool_clause([A],[B1,...,Bn]) where:
    #   A is eq_reif output with variable testVal → implies cond → target == varValue
    #   B1..Bn are boolean channels (the conditions forming a conjunction)
    #   For multi-neg: look up known AND channel for the conjunction
    type GatedEntry = object
        boolClauseCI: int
        condChannel: string     # the boolean condition (single channel or AND channel)
        valVar: string          # the variable value (from eq_reif testVal)
        eqReifBool: string      # the eq_reif output bool (positive literal)

    # Build reverse map: sorted condVars → AND channel resultVar
    var andChannelByInputs = initTable[seq[string], string]()
    for def in tr.boolAndChannelDefs:
        var sortedConds = def.condVars.sorted()
        andChannelByInputs[sortedConds] = def.resultVar
    # Also include array_bool_and channels
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_and": continue
        if con.args.len < 2 or con.args[1].kind != FznIdent: continue
        let resultVar = con.args[1].ident
        let arrArg = con.args[0]
        if arrArg.kind != FznArrayLit: continue
        var condVars: seq[string]
        var allIdent = true
        for elem in arrArg.elems:
            if elem.kind != FznIdent:
                allIdent = false
                break
            condVars.add(elem.ident)
        if not allIdent: continue
        var sortedConds = condVars.sorted()
        andChannelByInputs[sortedConds] = resultVar

    var entriesByTarget = initTable[string, seq[GatedEntry]]()

    # Scan ALL bool_clause constraints including consumed ones. Earlier passes
    # (e.g. N-literal disjunctive clause detection) may consume clauses that are
    # part of the gated pattern. The semantic checks below prevent false matches,
    # and if gated detection succeeds, the disjunctive constraint becomes tautological.
    for ci, con in tr.model.constraints:
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1: continue  # exactly 1 positive literal
        if negArg.elems.len < 1: continue   # at least 1 negative literal
        let posLit = posArg.elems[0]
        if posLit.kind != FznIdent: continue

        # posLit must be an eq_reif output
        if posLit.ident notin eqReifMap: continue
        let eqInfo = eqReifMap[posLit.ident]
        let targetVar = eqInfo.sourceVar

        # testVal must be a variable (not constant)
        if eqInfo.testVal.kind != FznIdent: continue
        let valVarName = eqInfo.testVal.ident
        if valVarName in tr.paramValues: continue

        # Skip if target is already channel or defined
        if targetVar in tr.channelVarNames or targetVar in tr.definedVarNames: continue

        # Determine the effective condition channel
        # The condition can be a channel OR a boolean search variable
        var condChannel = ""
        if negArg.elems.len == 1:
            # Single negative literal: must be a boolean variable (channel or search)
            let negLit = negArg.elems[0]
            if negLit.kind != FznIdent: continue
            let negId = negLit.ident
            if negId in tr.paramValues or negId in tr.definedVarNames: continue
            # Verify boolean domain
            if negId notin tr.channelVarNames:
                let negDomain = tr.lookupVarDomain(negId)
                if negDomain != @[0, 1]: continue
            condChannel = negId
        else:
            # Multi-negative: all must be channels, AND their conjunction must be a known channel
            var negVars: seq[string]
            var allChannels = true
            for elem in negArg.elems:
                if elem.kind != FznIdent or elem.ident notin tr.channelVarNames:
                    allChannels = false
                    break
                negVars.add(elem.ident)
            if not allChannels: continue
            var sortedNegs = negVars.sorted()
            if sortedNegs in andChannelByInputs:
                condChannel = andChannelByInputs[sortedNegs]
            else:
                continue  # no known AND channel for this conjunction

        entriesByTarget.mgetOrPut(targetVar, @[]).add(GatedEntry(
            boolClauseCI: ci,
            condChannel: condChannel,
            valVar: valVarName,
            eqReifBool: posLit.ident))

    if entriesByTarget.len == 0: return

    # Step 2b: Build equivalence map for boolean channels.
    # A bool AND channel with a single condition (AND([c]) = c) is equivalent to c.
    # An equivalence alias is also equivalent. Used to match default clauses.
    var boolEquivSet = initTable[string, HashSet[string]]()  # any member → set of all equivalents
    for def in tr.boolAndChannelDefs:
        if def.condVars.len == 1:
            let src = def.condVars[0]
            if src notin boolEquivSet:
                boolEquivSet[src] = [src].toHashSet()
            boolEquivSet[src].incl(def.resultVar)
            # Also index by resultVar so lookups from either direction work
            boolEquivSet[def.resultVar] = boolEquivSet[src]
    for def in tr.boolEquivAliasDefs:
        # Merge into existing set or create new one
        var equivs: HashSet[string]
        if def.canonicalVar in boolEquivSet:
            equivs = boolEquivSet[def.canonicalVar]
        elif def.aliasVar in boolEquivSet:
            equivs = boolEquivSet[def.aliasVar]
        else:
            equivs = initHashSet[string]()
        equivs.incl(def.canonicalVar)
        equivs.incl(def.aliasVar)
        # Point all members to the merged set
        for m in equivs:
            boolEquivSet[m] = equivs

    # Step 3: Pre-build lookup table for default-value bool_clause constraints.
    # Pattern: bool_clause([litA, litB], []) with 2 positive, 0 negative literals.
    # Index by each positive literal for O(1) lookup per target.
    # Include consumed constraints: even if another detection pass (e.g. N-literal
    # disjunctive clause) consumed the clause, the semantic relationship still holds.
    type DefaultClauseEntry = object
        ci: int
        litA, litB: string  # the two positive literals
    var defaultClausesByLit = initTable[string, seq[DefaultClauseEntry]]()
    for ci, con in tr.model.constraints:
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 2 or negArg.elems.len != 0: continue
        if posArg.elems[0].kind != FznIdent or posArg.elems[1].kind != FznIdent: continue
        let litA = posArg.elems[0].ident
        let litB = posArg.elems[1].ident
        let entry = DefaultClauseEntry(ci: ci, litA: litA, litB: litB)
        defaultClausesByLit.mgetOrPut(litA, @[]).add(entry)
        defaultClausesByLit.mgetOrPut(litB, @[]).add(entry)

    # Step 4: For each target with exactly 1 entry (binary condition):
    # Check if target has binary domain {constant, ?} and can derive default constant
    var detected = 0
    for targetVar, entries in entriesByTarget:
        if targetVar in tr.channelVarNames: continue  # may have been channelized in this loop
        if entries.len != 1: continue  # only binary case for now

        let entry = entries[0]
        let condDomain = tr.lookupVarDomain(entry.condChannel)
        if condDomain != @[0, 1]: continue  # condition must be boolean

        let targetDomain = tr.lookupVarDomain(targetVar)
        if targetDomain.len < 2: continue

        # We need the default value when cond=0 (condition is false).
        # The implication says: cond=1 → target = valVar
        # When cond=0, target must take a constant value.
        # Look for bool_clause([B_eq_const, cond], []) meaning ¬cond → target==const
        var defaultConstant = int.low
        var defaultCI = -1

        let condEquivs = if entry.condChannel in boolEquivSet:
            boolEquivSet[entry.condChannel]
        else:
            [entry.condChannel].toHashSet()

        # Search using pre-built lookup: find clauses containing an eq_reif for targetVar
        # with a constant testVal, paired with a cond equivalent.
        for condVar in condEquivs:
            if condVar notin defaultClausesByLit: continue
            for clause in defaultClausesByLit[condVar]:
                if clause.ci == entry.boolClauseCI: continue
                # The other literal (not condVar) should be an eq_reif for target with constant
                let otherLit = if clause.litA == condVar: clause.litB else: clause.litA
                if otherLit in eqReifMap:
                    let info = eqReifMap[otherLit]
                    if info.sourceVar == targetVar and info.testVal.kind == FznIntLit:
                        defaultConstant = info.testVal.intVal
                        defaultCI = clause.ci
                        break
            if defaultConstant != int.low: break

        if defaultConstant == int.low:
            # No constant default found. Try variable default: look for another
            # int_eq_reif(target, otherVar, otherBool) where otherVar is a channel
            # variable with a position. This handles multi-branch conditionals like
            # xs = if Node then var_element_result else gamete_lookup.
            var defaultVar = ""
            for ci in tr.reifChannelDefs:
                let rcon = tr.model.constraints[ci]
                let rname = stripSolverPrefix(rcon.name)
                if rname != "int_eq_reif": continue
                if rcon.args.len < 3 or rcon.args[0].kind != FznIdent: continue
                if rcon.args[0].ident != targetVar: continue
                if rcon.args[1].kind != FznIdent: continue
                let otherVar = rcon.args[1].ident
                if otherVar == entry.valVar: continue  # skip the already-found branch
                if otherVar in tr.paramValues: continue
                # otherVar must be a channel or at least have a position
                if otherVar in tr.channelVarNames or otherVar notin tr.definedVarNames:
                    defaultVar = otherVar
                    break
            if defaultVar != "":
                tr.boolGatedVarVarChannelDefs.add((
                    targetVar: targetVar,
                    condVar: entry.condChannel,
                    val1Var: entry.valVar,
                    val0Var: defaultVar))
                tr.channelVarNames.incl(targetVar)
                tr.definingConstraints.incl(entry.boolClauseCI)
                inc detected
            continue

        if defaultConstant notin targetDomain: continue

        # Determine which index corresponds to cond=0 (default) and cond=1 (variable)
        # cond is boolean {0,1}: when cond=1, target=valVar; when cond=0, target=defaultConstant
        var consumedCIs = @[entry.boolClauseCI]
        if defaultCI >= 0:
            consumedCIs.add(defaultCI)

        tr.boolGatedVarChannelDefs.add((
            targetVar: targetVar,
            condVar: entry.condChannel,
            valVar: entry.valVar,
            constValue: defaultConstant,
            consumedCIs: consumedCIs))
        tr.channelVarNames.incl(targetVar)
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} bool-gated variable channels")

proc detectConditionalExpressionChannels*(tr: var FznTranslator) =
    ## Detects conditional expression channels from optional variable decomposition:
    ##   target = if occurs then linear_expression else constant
    ##
    ## Pattern in FlatZinc:
    ##   int_eq_reif(target, constVal, isConstBool)     :: defines_var(isConstBool)
    ##   int_lin_eq_reif(coeffs, [target,...], rhs, eqBool) :: defines_var(eqBool)
    ##   bool_clause([occurs, isConstBool], [])           -- ¬occurs → target == constVal
    ##   array_bool_and([occurs, eqBool], combined)       -- combined = occurs ∧ eqBool
    ##
    ## When detected, creates a synthetic channel for the expression value and a
    ## BoolGated binding for target = element(occurs, [constVal, synthChannel]).
    ##
    ## Must run AFTER detectBoolGatedVariableChannels and detectLinEqReifChannels.

    # Step 1: Build map from isConstBool → (targetVar, constVal, constraintIdx)
    # from int_eq_reif(target, const, isConstBool) :: defines_var(isConstBool)
    type EqReifConstEntry = object
        targetVar: string
        constVal: int
        ci: int

    var eqReifConstMap: Table[string, EqReifConstEntry]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        if con.args[1].kind != FznIntLit: continue  # must be constant testVal
        let targetVar = con.args[0].ident
        let constVal = con.args[1].intVal
        let boolVar = con.args[2].ident
        eqReifConstMap[boolVar] = EqReifConstEntry(
            targetVar: targetVar, constVal: constVal, ci: ci)

    # Step 2: Build map from eqBool → (targetVar, exprVars, exprCoeffs, exprRhs, ci)
    # from int_lin_eq_reif(coeffs, vars, rhs, eqBool) :: defines_var(eqBool)
    # where target is one of vars with coefficient ±1.
    type LinEqReifExprEntry = object
        targetVar: string
        exprVars: seq[string]   # other variables (not target)
        exprCoeffs: seq[int]    # coefficients after isolating target
        exprRhs: int            # constant offset after isolating target
        ci: int

    var linEqReifExprMap: Table[string, LinEqReifExprEntry]
    for ci in tr.linEqReifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq_reif": continue
        if con.args.len < 4: continue
        if con.args[3].kind != FznIdent: continue
        let eqBool = con.args[3].ident
        let coeffsArg = con.args[0]
        let varsArg = con.args[1]
        let rhs = tr.resolveIntArg(con.args[2])

        # Resolve coefficients and variable names
        var coeffs: seq[int]
        if coeffsArg.kind == FznArrayLit:
            for e in coeffsArg.elems:
                if e.kind == FznIntLit: coeffs.add(e.intVal)
                else: break
        elif coeffsArg.kind == FznIdent and coeffsArg.ident in tr.paramValues:
            # Array parameter - skip for now (rare)
            continue
        else:
            let resolved = tr.resolveIntArray(coeffsArg)
            coeffs = resolved
        var varNames: seq[string]
        if varsArg.kind == FznArrayLit:
            for e in varsArg.elems:
                if e.kind == FznIdent: varNames.add(e.ident)
                else: break
        if coeffs.len != varNames.len or coeffs.len < 2: continue

        # Find a variable with coefficient ±1 that is NOT a channel and NOT a defined var
        var targetIdx = -1
        for i in 0..<varNames.len:
            if (coeffs[i] == 1 or coeffs[i] == -1) and
               varNames[i] notin tr.channelVarNames and
               varNames[i] notin tr.definedVarNames:
                targetIdx = i
                break
        if targetIdx < 0: continue

        let targetCoeff = coeffs[targetIdx]
        let targetVar = varNames[targetIdx]

        # Isolate: target = (rhs - sum of other terms) / targetCoeff
        var exprVars: seq[string]
        var exprCoeffs: seq[int]
        for i in 0..<varNames.len:
            if i == targetIdx: continue
            exprVars.add(varNames[i])
            if targetCoeff == 1:
                exprCoeffs.add(-coeffs[i])
            else:  # targetCoeff == -1
                exprCoeffs.add(coeffs[i])
        let exprRhs = if targetCoeff == 1: rhs else: -rhs

        linEqReifExprMap[eqBool] = LinEqReifExprEntry(
            targetVar: targetVar,
            exprVars: exprVars,
            exprCoeffs: exprCoeffs,
            exprRhs: exprRhs,
            ci: ci)

    if linEqReifExprMap.len == 0: return

    # Step 3: Find bool_clause([occurs, isConstBool], []) patterns and match.
    # Build a map: targetVar → (occurs, constVal, clauseCI)
    type DefaultEntry = object
        occursVar: string
        constVal: int
        clauseCI: int
        eqReifCI: int

    var defaultsByTarget: Table[string, DefaultEntry]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 2 or negArg.elems.len != 0: continue
        if posArg.elems[0].kind != FznIdent or posArg.elems[1].kind != FznIdent: continue

        # Check both orderings: [occurs, isConstBool] or [isConstBool, occurs]
        let litA = posArg.elems[0].ident
        let litB = posArg.elems[1].ident

        for (candidateConst, candidateOccurs) in [(litA, litB), (litB, litA)]:
            if candidateConst notin eqReifConstMap: continue
            # occurs variable must be boolean and not a parameter
            if candidateOccurs in tr.paramValues: continue
            if candidateOccurs in tr.definedVarNames: continue
            let occursDomain = tr.lookupVarDomain(candidateOccurs)
            if occursDomain.len == 0: continue
            if occursDomain != @[0, 1]: continue
            let eqEntry = eqReifConstMap[candidateConst]
            let targetVar = eqEntry.targetVar
            if targetVar in tr.channelVarNames or targetVar in tr.definedVarNames: continue
            if targetVar in defaultsByTarget: continue  # already found
            defaultsByTarget[targetVar] = DefaultEntry(
                occursVar: candidateOccurs,
                constVal: eqEntry.constVal,
                clauseCI: ci,
                eqReifCI: eqEntry.ci)

    if defaultsByTarget.len == 0: return

    # Step 4: Match targets that appear in BOTH defaultsByTarget and linEqReifExprMap.
    # Verify that occurs and eqBool are linked via array_bool_and.
    var andChannelInputs: Table[string, seq[string]]  # resultVar → inputVars
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_and": continue
        if con.args.len < 2 or con.args[1].kind != FznIdent: continue
        let resultVar = con.args[1].ident
        let arrArg = con.args[0]
        if arrArg.kind != FznArrayLit: continue
        var inputs: seq[string]
        for elem in arrArg.elems:
            if elem.kind == FznIdent: inputs.add(elem.ident)
        andChannelInputs[resultVar] = inputs

    # Also build reverse: for each pair of inputs, find if there's an AND channel
    var andByInputPair: Table[tuple[a, b: string], string]
    for resultVar, inputs in andChannelInputs:
        if inputs.len == 2:
            andByInputPair[(inputs[0], inputs[1])] = resultVar
            andByInputPair[(inputs[1], inputs[0])] = resultVar

    var detected = 0
    for eqBool, exprEntry in linEqReifExprMap:
        let targetVar = exprEntry.targetVar
        if targetVar notin defaultsByTarget: continue
        if targetVar in tr.channelVarNames: continue  # may have been channelized already

        let defEntry = defaultsByTarget[targetVar]

        # Verify: occurs and eqBool must be linked via array_bool_and
        let pair = (defEntry.occursVar, eqBool)
        if pair notin andByInputPair: continue

        # All checks passed. Verify expression variables are resolvable
        # (must be params, defined vars, channels, or regular vars that will get positions)
        var allResolvable = true
        for v in exprEntry.exprVars:
            if v notin tr.definedVarNames and v notin tr.definedVarExprs and
               v notin tr.paramValues and v notin tr.channelVarNames:
                # Must be a known variable (will get a position during translation)
                let vDomain = tr.lookupVarDomain(v)
                if vDomain.len == 0:
                    allResolvable = false
                    break
        if not allResolvable: continue

        # Record the detection
        tr.boolGatedExprChannelDefs.add((
            targetVar: targetVar,
            condVar: defEntry.occursVar,
            exprVars: exprEntry.exprVars,
            exprCoeffs: exprEntry.exprCoeffs,
            exprRhs: exprEntry.exprRhs,
            constValue: defEntry.constVal,
            consumedCIs: @[defEntry.clauseCI]))
        tr.channelVarNames.incl(targetVar)
        tr.definingConstraints.incl(defEntry.clauseCI)
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} conditional expression channels")

proc detectOverlapChannels*(tr: var FznTranslator) =
    ## Detects overlap variables connected to time-separation channels through bool_not.
    ## Pattern:
    ##   bool_not(overlap, sep) :: defines_var(sep)   [already consumed, sep is channel]
    ## Records the overlap variable names for use by multi-resource consolidation.
    ## The overlap variable itself stays as a search variable (to avoid circular
    ## channel dependencies).
    ##
    ## Must run after detectReifChannels().

    var detected = 0
    for ci in tr.boolNotChannelDefs:
        let con = tr.model.constraints[ci]
        let aArg = con.args[0]  # the 'overlap' variable
        let bArg = con.args[1]  # the 'sep' variable (already a channel)

        if aArg.kind != FznIdent or bArg.kind != FznIdent: continue
        let aName = aArg.ident
        let bName = bArg.ident

        # b must be a channel (the sep variable)
        if bName notin tr.channelVarNames: continue
        # a must NOT already be a channel or defined
        if aName in tr.channelVarNames or aName in tr.definedVarNames: continue

        # Record for multi-resource consolidation (overlap stays as search variable)
        tr.overlapChannelDefs.add((ci: ci, overlapVar: aName, sepVar: bName))
        inc detected

    if detected > 0:
        stderr.writeLine(&"[FZN] Detected {detected} overlap variables (a = NOT sep via bool_not)")


proc detectConditionalImplicationChannels*(tr: var FznTranslator) =
    ## Detects patterns where a variable is fully determined by implications through
    ## bool_clause([eq_reif(target, val)], [cond_channel]).
    ##
    ## Pattern A (Binary conditional / min-max pair):
    ##   bool_clause([eq_reif(Z, X)], [cond_lt]) + bool_clause([eq_reif(Z, Y)], [cond_gt])
    ##   where cond_lt and cond_gt are complementary int_lin_le_reif channels.
    ##   Result: Z = element(cond_lt, [Y, X]) — conditional assignment channel.
    ##
    ## Pattern B (One-hot conditional from allDifferent array):
    ##   bool_clause([eq_reif(Z, v_i)], [eq_reif(X_i, c)]) for i=1..N
    ##   where X_i are N different variables with same domain of size N (allDifferent),
    ##   c is a constant, and the conditions form a one-hot encoding.
    ##   Result: Z = element(weighted_one_hot_index, [v_0, ..., v_{N-1}])
    ##
    ## Requires: detectReifChannels() and detectBoolAndChannels() must have run first.

    # Step 1: Build eq_reif reverse map: output bool var → (sourceVar, testVal)
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        eqReifMap[con.args[2].ident] = (sourceVar: con.args[0].ident, testVal: con.args[1])

    # Step 2: Build int_lin_le_reif reverse map for complementarity checking
    # Maps output bool var → (varA, varB, rhs) for [1,-1] coefficient patterns
    type LinLeInfo = tuple[varA: string, varB: string, rhs: int]
    var linLeReifMap: Table[string, LinLeInfo]
    for ci in tr.linLeReifChannelDefs:
        let con = tr.model.constraints[ci]
        if con.args.len < 4 or con.args[3].kind != FznIdent: continue
        let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
        let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
        if coeffs.len != 2 or coeffs[0] != 1 or coeffs[1] != -1: continue
        let varArr = con.args[1]
        if varArr.kind != FznArrayLit or varArr.elems.len != 2: continue
        if varArr.elems[0].kind != FznIdent or varArr.elems[1].kind != FznIdent: continue
        linLeReifMap[con.args[3].ident] = (varA: varArr.elems[0].ident,
                                            varB: varArr.elems[1].ident,
                                            rhs: rhs)

    # Step 3: Scan non-consumed bool_clause([A], [B]) and group by target variable
    type ImplEntry = object
        boolClauseCI: int
        condChannel: string    # negative literal (the condition)
        testVal: FznExpr       # value from eq_reif (constant or variable)

    var implByTarget: Table[string, seq[ImplEntry]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 1 or negArg.elems.len != 1: continue
        let posLit = posArg.elems[0]
        let negLit = negArg.elems[0]
        if posLit.kind != FznIdent or negLit.kind != FznIdent: continue
        # posLit must be an eq_reif output
        if posLit.ident notin eqReifMap: continue
        # negLit must be a channel variable
        if negLit.ident notin tr.channelVarNames: continue
        let eqInfo = eqReifMap[posLit.ident]
        let targetVar = eqInfo.sourceVar
        # Skip if target is already channel or defined
        if targetVar in tr.channelVarNames or targetVar in tr.definedVarNames: continue
        implByTarget.mgetOrPut(targetVar, @[]).add(ImplEntry(
            boolClauseCI: ci,
            condChannel: negLit.ident,
            testVal: eqInfo.testVal))

    if implByTarget.len == 0: return

    var nBinary = 0
    var nOneHot = 0

    for targetVar, entries in implByTarget:
        if targetVar in tr.channelVarNames: continue  # may have been channelized in this loop

        # Pattern A: Binary conditional (exactly 2 entries with variable test values)
        if entries.len == 2:
            let e0 = entries[0]
            let e1 = entries[1]
            # Both test values must be variable references
            if e0.testVal.kind != FznIdent or e1.testVal.kind != FznIdent: continue
            # Both conditions must be int_lin_le_reif with [1,-1] coefficients
            if e0.condChannel notin linLeReifMap or e1.condChannel notin linLeReifMap: continue
            let info0 = linLeReifMap[e0.condChannel]
            let info1 = linLeReifMap[e1.condChannel]
            # Check complementarity: swapped variable order, rhs=-1 (strict <)
            # rhs=-1 ensures A-B <= -1 i.e. A < B, making the two conditions truly
            # complementary (exactly one is true). Other rhs values (e.g. 0 for <=)
            # would allow both conditions to be true when A == B.
            if info0.rhs != -1 or info1.rhs != -1: continue
            if not (info0.varA == info1.varB and info0.varB == info1.varA):
                continue
            # e0.condChannel = (info0.varA < info0.varB)  [rhs=-1 means strict <]
            # When cond0=1: target = e0.testVal
            # When cond0=0 (so cond1=1): target = e1.testVal
            tr.binaryCondChannelDefs.add((
                targetVar: targetVar,
                condChannel: e0.condChannel,
                val0Var: e1.testVal.ident,  # value when cond0=0
                val1Var: e0.testVal.ident,  # value when cond0=1
                consumedCIs: @[e0.boolClauseCI, e1.boolClauseCI]))
            tr.channelVarNames.incl(targetVar)
            tr.definingConstraints.incl(e0.boolClauseCI)
            tr.definingConstraints.incl(e1.boolClauseCI)
            inc nBinary
            continue

        # Pattern B: One-hot conditional (N entries with constant test values, different cond vars)
        if entries.len < 2: continue
        # All test values must be constants
        var allConst = true
        for e in entries:
            if e.testVal.kind != FznIntLit:
                allConst = false
                break
        if not allConst: continue
        # All conditions must be eq_reif channels from different source variables
        # with the SAME test constant value
        var condSourceVars: seq[string]
        var condConstVal: int = -1
        var condSourceOk = true
        for i, e in entries:
            if e.condChannel notin eqReifMap:
                condSourceOk = false
                break
            let condInfo = eqReifMap[e.condChannel]
            if condInfo.testVal.kind != FznIntLit:
                condSourceOk = false
                break
            if i == 0:
                condConstVal = condInfo.testVal.intVal
            elif condInfo.testVal.intVal != condConstVal:
                condSourceOk = false
                break
            if condInfo.sourceVar in condSourceVars:
                condSourceOk = false  # duplicate source var
                break
            condSourceVars.add(condInfo.sourceVar)
        if not condSourceOk: continue
        # Check completeness: N conditions should equal the domain size of the source vars
        # (ensures exactly one condition is true under allDifferent)
        let firstDom = tr.lookupVarDomain(condSourceVars[0])
        if firstDom.len == 0 or entries.len != firstDom.len: continue
        # Build ordered channels and values (sort by source var for deterministic ordering)
        type CondPair = tuple[sourceVar: string, condChannel: string, targetVal: int, ci: int]
        var pairs: seq[CondPair]
        for i, e in entries:
            pairs.add((sourceVar: condSourceVars[i], condChannel: e.condChannel,
                        targetVal: e.testVal.intVal, ci: e.boolClauseCI))
        pairs.sort(proc(a, b: CondPair): int = cmp(a.sourceVar, b.sourceVar))
        var orderedChannels: seq[string]
        var orderedVals: seq[int]
        var consumedCIs: seq[int]
        for p in pairs:
            orderedChannels.add(p.condChannel)
            orderedVals.add(p.targetVal)
            consumedCIs.add(p.ci)
        tr.oneHotCondChannelDefs.add((
            targetVar: targetVar,
            condChannels: orderedChannels,
            targetVals: orderedVals,
            consumedCIs: consumedCIs))
        tr.channelVarNames.incl(targetVar)
        for ci in consumedCIs:
            tr.definingConstraints.incl(ci)
        inc nOneHot

    if nBinary > 0 or nOneHot > 0:
        stderr.writeLine(&"[FZN] Detected conditional implication channels: {nBinary} binary (min/max pair), {nOneHot} one-hot (permutation lookup)")



proc detectBoolXorSimplification(tr: var FznTranslator) =
    ## Detects bool_xor constraints where inputs are constants and folds them.
    ## - bool_xor(const_a, const_b, result) → result becomes a defined constant
    ## - bool_xor(const_a, var_b, result) → result = var_b (if a=false) or result = 1-var_b (if a=true)
    ## - bool_xor(var_a, const_b, result) → similarly
    var nFolded = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_xor": continue
        if con.args.len < 3: continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args[2].kind != FznIdent: continue
        let resultVar = con.args[2].ident
        if resultVar in tr.channelVarNames or resultVar in tr.definedVarNames: continue

        # Resolve arguments — check if they are constants
        var aConst = false
        var aVal = 0
        var bConst = false
        var bVal = 0
        let argA = con.args[0]
        let argB = con.args[1]

        if argA.kind == FznBoolLit:
            aConst = true; aVal = if argA.boolVal: 1 else: 0
        elif argA.kind == FznIntLit:
            aConst = true; aVal = argA.intVal
        elif argA.kind == FznIdent and argA.ident in tr.paramValues:
            aConst = true; aVal = tr.paramValues[argA.ident]

        if argB.kind == FznBoolLit:
            bConst = true; bVal = if argB.boolVal: 1 else: 0
        elif argB.kind == FznIntLit:
            bConst = true; bVal = argB.intVal
        elif argB.kind == FznIdent and argB.ident in tr.paramValues:
            bConst = true; bVal = tr.paramValues[argB.ident]

        if aConst and bConst:
            # Both constants: result is known
            let xorVal = if aVal != bVal: 1 else: 0
            tr.paramValues[resultVar] = xorVal
            tr.definedVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            inc nFolded
        elif aConst:
            # One constant: result is identity or negation of the other variable
            tr.channelVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            if aVal != 0:
                # result = 1 - b (negation) — store (inputVarArg, resultVar) for channel building
                tr.boolXorNegDefs.add((inputArg: argB, resultVar: resultVar))
            else:
                # result = b (identity)
                if argB.kind == FznIdent:
                    tr.equalityCopyAliases[resultVar] = argB.ident
            inc nFolded
        elif bConst:
            # One constant: result is identity or negation of the other variable
            tr.channelVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            if bVal != 0:
                # result = 1 - a (negation)
                tr.boolXorNegDefs.add((inputArg: argA, resultVar: resultVar))
            else:
                # result = a (identity)
                if argA.kind == FznIdent:
                    tr.equalityCopyAliases[resultVar] = argA.ident
            inc nFolded

    if nFolded > 0:
        stderr.writeLine(&"[FZN] Folded {nFolded} bool_xor constraints with constant inputs")

proc detectBoolXorConstResultChannels*(tr: var FznTranslator) =
    ## Detects bool_xor(a, b, const_result) where the result is a constant and at
    ## least one of {a, b} is already a channel variable.
    ## - bool_xor(a, b, false) → a = b → identity channel: target = element(source, [0, 1])
    ## - bool_xor(a, b, true) → a = NOT b → negation channel: target = element(source, [1, 0])
    ##
    ## MUST run AFTER detectBoolXorVarChannels so channelVarNames is populated.
    ## Runs BEFORE detectReifChannels so that identity-channeled vars are known
    ## as channels when reif detection processes bool_eq_reif using them as inputs.
    var nIdentity = 0
    var nNegation = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_xor": continue
        if con.args.len < 3: continue
        if con.hasAnnotation("defines_var"): continue

        let argR = con.args[2]
        var resultConst = -1
        if argR.kind == FznBoolLit:
            resultConst = if argR.boolVal: 1 else: 0
        elif argR.kind == FznIntLit:
            resultConst = argR.intVal
        elif argR.kind == FznIdent and argR.ident in tr.paramValues:
            resultConst = tr.paramValues[argR.ident]
        if resultConst < 0: continue

        let argA = con.args[0]
        let argB = con.args[1]
        if argA.kind != FznIdent or argB.kind != FznIdent: continue
        let aName = argA.ident
        let bName = argB.ident
        if aName in tr.definedVarNames or bName in tr.definedVarNames: continue

        let aIsChannel = aName in tr.channelVarNames
        let bIsChannel = bName in tr.channelVarNames
        if not aIsChannel and not bIsChannel: continue
        if aIsChannel and bIsChannel: continue

        var targetVar: string
        var sourceArg: FznExpr
        if aIsChannel and not bIsChannel:
            targetVar = bName; sourceArg = argA
        else:
            targetVar = aName; sourceArg = argB

        tr.channelVarNames.incl(targetVar)
        tr.definingConstraints.incl(ci)

        if resultConst == 0:
            # a = b → identity channel: target = element(source, [0, 1])
            tr.boolXorIdentityDefs.add((inputArg: sourceArg, resultVar: targetVar))
            inc nIdentity
        else:
            # a = NOT b → negation channel: target = element(source, [1, 0])
            tr.boolXorNegDefs.add((inputArg: sourceArg, resultVar: targetVar))
            inc nNegation

    if nIdentity > 0 or nNegation > 0:
        stderr.writeLine(&"[FZN] Detected {nIdentity + nNegation} bool_xor constant-result channels ({nIdentity} identity, {nNegation} negation)")

proc detectBoolXorVarChannels*(tr: var FznTranslator) =
    ## Detects bool_xor and array_bool_xor constraints with 2 variable inputs and
    ## defines_var annotation, creating element channel bindings.
    ##
    ## bool_xor(a, b, result) with defines_var(result):
    ##   result = a XOR b = (a != b) → element(a*2 + b, [0, 1, 1, 0])
    ##
    ## array_bool_xor([result, a, b]) with defines_var(result):
    ##   result XOR a XOR b = true → result = XNOR(a, b) = (a == b)
    ##   → element(a*2 + b, [1, 0, 0, 1])
    ##
    ## Must run AFTER detectBoolXorSimplification (handles constant-input cases).
    var nBoolXor = 0
    var nArrayBoolXor = 0

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)

        if name == "bool_xor":
            # bool_xor(a, b, result) — 3 separate arguments
            if con.args.len < 3: continue
            if not con.hasAnnotation("defines_var"): continue
            if con.args[2].kind != FznIdent: continue
            let resultVar = con.args[2].ident
            let ann = con.getAnnotation("defines_var")
            if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != resultVar:
                continue
            if resultVar in tr.channelVarNames or resultVar in tr.definedVarNames: continue

            # Both inputs must be non-constant, non-defined variables
            let argA = con.args[0]
            let argB = con.args[1]
            if argA.kind == FznBoolLit or argA.kind == FznIntLit: continue  # handled by simplification
            if argB.kind == FznBoolLit or argB.kind == FznIntLit: continue
            if argA.kind == FznIdent and argA.ident in tr.paramValues: continue
            if argB.kind == FznIdent and argB.ident in tr.paramValues: continue
            if argA.kind == FznIdent and argA.ident in tr.definedVarNames: continue
            if argB.kind == FznIdent and argB.ident in tr.definedVarNames: continue

            tr.channelVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            tr.boolXorVarChannelDefs.add((resultVar: resultVar, arg1: argA, arg2: argB, isNe: true))
            inc nBoolXor

        elif name == "array_bool_xor":
            # array_bool_xor(array) — single array argument, parity constraint
            if con.args.len < 1: continue
            if not con.hasAnnotation("defines_var"): continue
            let ann = con.getAnnotation("defines_var")
            if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
            let resultVar = ann.args[0].ident
            if resultVar in tr.channelVarNames or resultVar in tr.definedVarNames: continue

            # Resolve the array elements
            let elems = tr.resolveVarArrayElems(con.args[0])
            if elems.len != 3: continue  # only handle 3-element (2 inputs + 1 output) for channels

            # Find the two input elements (non-result) and verify they're valid
            var inputs: seq[FznExpr]
            for elem in elems:
                if elem.kind == FznIdent and elem.ident == resultVar:
                    continue
                inputs.add(elem)

            if inputs.len != 2: continue  # result var not found in array or duplicate

            # Both inputs must be non-constant, non-defined variables
            var allValid = true
            for inp in inputs:
                if inp.kind == FznBoolLit or inp.kind == FznIntLit:
                    allValid = false; break
                if inp.kind == FznIdent and inp.ident in tr.paramValues:
                    allValid = false; break
                if inp.kind == FznIdent and inp.ident in tr.definedVarNames:
                    allValid = false; break
            if not allValid: continue

            # array_bool_xor([r, a, b]): r XOR a XOR b = true → r = XNOR(a, b) = (a == b)
            # Channel: element(a*2 + b, [1, 0, 0, 1]) — EQ pattern (isNe=false)
            tr.channelVarNames.incl(resultVar)
            tr.definingConstraints.incl(ci)
            tr.boolXorVarChannelDefs.add((resultVar: resultVar, arg1: inputs[0], arg2: inputs[1], isNe: false))
            inc nArrayBoolXor

    if nBoolXor > 0 or nArrayBoolXor > 0:
        stderr.writeLine(&"[FZN] Detected XOR variable channels: {nBoolXor} bool_xor, {nArrayBoolXor} array_bool_xor")


proc detectBool2intIdentityAliases(tr: var FznTranslator) =
    ## Detects bool2int(b, i) :: defines_var(i) where b has domain {0,1} (identity mapping).
    ## Instead of creating an element channel (i = element(b, [0,1])), aliases i to b.
    ## This eliminates redundant channel positions since i ≡ b for binary bools.
    ## MUST run after detectAtMostPairCliques (which references int var names)
    ## and before detectReifChannels (which would otherwise create channels for these).
    var nAliased = 0
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints:
            continue
        let name = stripSolverPrefix(con.name)
        if name != "bool2int" or not con.hasAnnotation("defines_var"):
            continue
        if con.args.len < 2 or con.args[0].kind != FznIdent or con.args[1].kind != FznIdent:
            continue

        let boolName = con.args[0].ident  # bool input
        let intName = con.args[1].ident   # int output

        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != intName:
            continue

        # Skip if already handled
        if intName in tr.definedVarNames or intName in tr.channelVarNames:
            continue
        # Bool input must not be a defined var or parameter
        if boolName in tr.definedVarNames or boolName in tr.paramValues:
            continue

        # Don't alias if the bool input is a reification output (has is_defined_var).
        # Keeping the intermediate channel preserves cascade topology depth for
        # channel-dep penalty maps (e.g., int_le_reif → bool2int → element chain).
        tr.buildVarDomainIndex()
        if boolName in tr.varDomainIndex:
            let boolDecl = tr.model.variables[tr.varDomainIndex[boolName]]
            if boolDecl.hasAnnotation("is_defined_var"):
                continue

        # Verify bool input has binary domain {0,1} (identity mapping)
        var boolDom = tr.lookupVarDomain(boolName)
        if boolName in tr.presolveDomains:
            boolDom = tr.presolveDomains[boolName]
        if boolDom != @[0, 1]:
            continue  # Fixed or non-binary — can't alias

        # Alias: i → b (i becomes a defined var expression pointing to b's position)
        tr.bool2intIdentityAliases[intName] = boolName
        tr.definedVarNames.incl(intName)
        tr.definingConstraints.incl(ci)
        # Populate bool2intSourceMap for NAND redundancy detection
        tr.bool2intSourceMap[intName] = boolName
        inc nAliased

    if nAliased > 0:
        stderr.writeLine(&"[FZN] Bool2int identity aliases: {nAliased} channel positions eliminated")


proc detectForwardBackwardEquivChannels*(tr: var FznTranslator) =
    ## Detects boolean variables B equivalent to a disjunction of equality conditions,
    ## established through forward + backward bool_clause implications:
    ##
    ##   Forward:  bool_clause([C1, ..., Ck], [B])    -- B -> OR(Ci)
    ##   Backward: bool_clause([ne_reif(X,v), B], []) -- (X==v) -> B   (for each arm)
    ##
    ## Each forward arm Ci may be:
    ##   - Direct: int_eq_reif(X, v, Ci) with matching backward condition
    ##   - AND-wrapped: array_bool_and([..., eq_reif(X,v), ...], Ci) with matching backward
    ##
    ## When all arms have matching backward conditions: B <-> OR(backward conditions).
    ## B becomes a channel with a constant {0,1} lookup table indexed by source variables.

    # === Phase 1: Build reverse indexes ===

    # 1a. neReifMap: ne_var_name -> (condVar, condVal)
    #     from int_ne_reif(X, v, ne_var) in reifChannelDefs
    var neReifMap: Table[string, tuple[condVar: string, condVal: int]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_ne_reif": continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        let condVal = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
        neReifMap[con.args[2].ident] = (condVar: con.args[0].ident, condVal: condVal)

    # 1b. eqReifMap: eq_var_name -> (sourceVar, testVal)
    #     from int_eq_reif(X, v, eq_var) in reifChannelDefs
    var eqReifMap: Table[string, tuple[sourceVar: string, testVal: int]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_eq_reif": continue
        if con.args.len < 3 or con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        let testVal = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
        eqReifMap[con.args[2].ident] = (sourceVar: con.args[0].ident, testVal: testVal)

    # 1c. andInputs: and_result -> [member names]
    #     from array_bool_and([...], and_result) in boolAndOrChannelDefs
    var andInputs: Table[string, seq[string]]
    for ci in tr.boolAndOrChannelDefs:
        let con = tr.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "array_bool_and": continue
        if con.args.len < 2 or con.args[1].kind != FznIdent: continue
        let elems = tr.resolveVarArrayElems(con.args[0])
        var names: seq[string]
        for e in elems:
            if e.kind == FznIdent: names.add(e.ident)
        if names.len > 0:
            andInputs[con.args[1].ident] = names

    if neReifMap.len == 0: return

    # 1d. backwardByTarget: B -> [(condVar, condVal, clauseIdx)]
    #     from unconsumed bool_clause([ne_var, B], []) where ne_var in neReifMap
    type BackwardEntry = object
        condVar: string
        condVal: int
        clauseIdx: int

    var backwardByTarget: Table[string, seq[BackwardEntry]]
    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if posArg.elems.len != 2 or negArg.elems.len != 0: continue
        let a = posArg.elems[0]
        let b = posArg.elems[1]
        if a.kind != FznIdent or b.kind != FznIdent: continue
        # Check both orderings: ne_reif could be either element
        for (neCandidate, bCandidate) in [(a.ident, b.ident), (b.ident, a.ident)]:
            if neCandidate in neReifMap:
                let info = neReifMap[neCandidate]
                backwardByTarget.mgetOrPut(bCandidate, @[]).add(
                    BackwardEntry(condVar: info.condVar, condVal: info.condVal, clauseIdx: ci))

    if backwardByTarget.len == 0: return

    # === Phase 2: Scan forward clauses and verify arms ===

    var nDetected, nConsumed = 0

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        let name = stripSolverPrefix(con.name)
        if name != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len != 1: continue  # exactly 1 negative literal (B)
        if posArg.elems.len < 1: continue
        let bElem = negArg.elems[0]
        if bElem.kind != FznIdent: continue
        let bName = bElem.ident

        # B must not already be a channel, defined var, or param
        if bName in tr.channelVarNames: continue
        if bName in tr.definedVarNames: continue
        if bName in tr.paramValues: continue

        # B must have backward implications
        if bName notin backwardByTarget: continue
        let backwards = backwardByTarget[bName]

        # Build a quick lookup of backward conditions for B
        var backwardSet: HashSet[string]  # "condVar\tcondVal" for fast matching
        for bw in backwards:
            backwardSet.incl(bw.condVar & "\t" & $bw.condVal)

        # Verify each forward arm
        var allArmsVerified = true
        var matchedBackwardCIs: seq[int]  # clause indices of matched backward entries

        for armElem in posArg.elems:
            if armElem.kind != FznIdent:
                allArmsVerified = false
                break

            let armName = armElem.ident
            var armVerified = false

            # Case 1: arm is an AND — check if any member's eq_reif matches a backward condition
            if armName in andInputs:
                for member in andInputs[armName]:
                    if member in eqReifMap:
                        let info = eqReifMap[member]
                        let key = info.sourceVar & "\t" & $info.testVal
                        if key in backwardSet:
                            armVerified = true
                            # Find the matching backward clause to consume
                            for bw in backwards:
                                if bw.condVar == info.sourceVar and bw.condVal == info.testVal:
                                    if bw.clauseIdx notin matchedBackwardCIs:
                                        matchedBackwardCIs.add(bw.clauseIdx)
                                    break
                            break

            # Case 2: arm is directly an eq_reif
            if not armVerified and armName in eqReifMap:
                let info = eqReifMap[armName]
                let key = info.sourceVar & "\t" & $info.testVal
                if key in backwardSet:
                    armVerified = true
                    for bw in backwards:
                        if bw.condVar == info.sourceVar and bw.condVal == info.testVal:
                            if bw.clauseIdx notin matchedBackwardCIs:
                                matchedBackwardCIs.add(bw.clauseIdx)
                            break

            if not armVerified:
                allArmsVerified = false
                break

        if not allArmsVerified: continue
        if matchedBackwardCIs.len == 0: continue

        # === Phase 3: Build lookup table ===

        # Collect all backward conditions (not just the arm-matched ones — all are valid)
        var sourceConditions: Table[string, seq[int]]  # sourceVar -> [values that make B=1]
        var allBackwardCIs: seq[int]
        for bw in backwards:
            sourceConditions.mgetOrPut(bw.condVar, @[]).add(bw.condVal)
            if bw.clauseIdx notin allBackwardCIs:
                allBackwardCIs.add(bw.clauseIdx)

        # Sort source variables for deterministic ordering
        var sourceVarNames: seq[string]
        for sv in sourceConditions.keys:
            sourceVarNames.add(sv)
        sourceVarNames.sort()

        # Trace source variables to ultimate search variables
        var ultimateSourceNames: seq[string]
        type SourceTrace = object
            isDirect: bool
            varName: string        # ultimate source var name
            constArray: seq[int]   # for element channels: lookup array
            offset: int            # for element channels: index offset

        var sourceTraces: seq[SourceTrace]
        var valid = true

        for sv in sourceVarNames:
            if sv in tr.constElementSources:
                # Element channel: trace through to index variable
                let src = tr.constElementSources[sv]
                if src.indexVar in tr.definedVarNames or src.indexVar in tr.channelVarNames:
                    valid = false
                    break
                sourceTraces.add(SourceTrace(isDirect: false, varName: src.indexVar,
                    constArray: src.constArray, offset: 0))
                ultimateSourceNames.add(src.indexVar)
            elif sv notin tr.definedVarNames and sv notin tr.channelVarNames:
                # Direct search variable
                sourceTraces.add(SourceTrace(isDirect: true, varName: sv))
                ultimateSourceNames.add(sv)
            else:
                valid = false
                break

        if not valid: continue
        if ultimateSourceNames.len == 0: continue

        # Check for duplicate ultimate source names (can't have same var as two dimensions)
        var srcSet: HashSet[string]
        var hasDup = false
        for sn in ultimateSourceNames:
            if sn in srcSet: hasDup = true; break
            srcSet.incl(sn)
        if hasDup: continue

        # Get domains and compute table size
        var domainOffsets, domainSizes: seq[int]
        for sn in ultimateSourceNames:
            let dom = tr.lookupVarDomain(sn)
            if dom.len == 0: valid = false; break
            domainOffsets.add(dom[0])
            domainSizes.add(dom[^1] - dom[0] + 1)
        if not valid: continue

        var tableSize = 1
        for ds in domainSizes:
            if ds <= 0 or tableSize > 100_000 div max(1, ds):
                valid = false
                break
            tableSize *= ds
        if not valid or tableSize > 100_000 or tableSize <= 0: continue

        # Build the lookup table (default 0)
        var lookupTable = newSeq[int](tableSize)

        # For each backward condition, set the appropriate entries to 1
        for svIdx, sv in sourceVarNames:
            let condVals = sourceConditions[sv]
            let trace = sourceTraces[svIdx]
            let dimIdx = ultimateSourceNames.find(trace.varName)
            if dimIdx < 0: valid = false; break

            for condVal in condVals:
                # Determine which index values in the ultimate source correspond to this condition
                var matchingIdxVals: seq[int]
                if trace.isDirect:
                    matchingIdxVals.add(condVal)
                else:
                    # Element channel: find all index values where constArray maps to condVal
                    for i, v in trace.constArray:
                        if v == condVal:
                            matchingIdxVals.add(i + 1 + trace.offset)  # FZN 1-based indexing

                # Set all table entries where this dimension has each matching value
                for idxVal in matchingIdxVals:
                    let relVal = idxVal - domainOffsets[dimIdx]
                    if relVal < 0 or relVal >= domainSizes[dimIdx]: continue

                    # Compute stride for this dimension
                    var stride = 1
                    for d in (dimIdx + 1) ..< domainSizes.len:
                        stride *= domainSizes[d]
                    let blockSize = stride  # entries per slice

                    # Iterate over all entries where dimension dimIdx == relVal
                    var outerStride = stride * domainSizes[dimIdx]
                    var outerCount = tableSize div outerStride
                    for outer in 0 ..< outerCount:
                        let base = outer * outerStride + relVal * stride
                        for inner in 0 ..< blockSize:
                            let flatIdx = base + inner
                            if flatIdx >= 0 and flatIdx < tableSize:
                                lookupTable[flatIdx] = 1

        if not valid: continue

        # === Phase 4: Register channel and consume constraints ===

        tr.caseAnalysisDefs.add(CaseAnalysisDef(
            targetVarName: bName,
            sourceVarNames: ultimateSourceNames,
            lookupTable: lookupTable,
            domainOffsets: domainOffsets,
            domainSizes: domainSizes,
            varEntries: initTable[int, CaseAnalysisVarEntry]()
        ))
        tr.channelVarNames.incl(bName)
        tr.definingConstraints.incl(ci)  # forward clause
        for bwCi in allBackwardCIs:
            tr.definingConstraints.incl(bwCi)
        inc nDetected
        nConsumed += 1 + allBackwardCIs.len  # forward + all backward clauses

    if nDetected > 0:
        stderr.writeLine(&"[FZN] Forward-backward equiv channels: {nDetected} detected, " &
            &"{nConsumed} clauses consumed")


proc detectImplicationOrChannels*(tr: var FznTranslator) =
    ## Detects "V is forced ≥ OR(W_i)" patterns and channelizes V = OR(W_i).
    ##
    ## Pattern in FlatZinc:
    ##   int_eq_reif(V, 1, B)        :: defines_var(B)   -- B ↔ (V = 1)
    ##   int_ne_reif(W_i, 1, N_i)    :: defines_var(N_i) -- N_i ↔ (W_i ≠ 1)
    ##   bool_clause([N_i, B], [])                       -- W_i = 1 → V = 1
    ##
    ## When V is binary {0,1} and held high by *multiple* W_i implications, AND V has
    ## a count constraint pulling it toward 0 (e.g., int_lin_eq with target K), then in
    ## any feasible/optimal solution V = OR(W_i) — the implications and count together
    ## ensure V is minimal subject to the forcers. Channelizing tightens the search
    ## space without losing solutions, and removes V from the search positions, breaking
    ## the implication-coupling that traps tabu local search.
    ##
    ## Use case: SFC chain — `selected_nodes[v] = OR(link_selection[arc] for arc incident to v)`,
    ## with the count `n_fun_nodes = vnflist_size` providing the "minimal" pull.
    ##
    ## MUST run after detectReifChannels() so eq/ne reif maps are populated, and after
    ## the bool channel detectors that consume related clauses (detectBoolOrChannels,
    ## detectForwardBackwardEquivChannels). Skips clauses already in definingConstraints.
    ##
    ## All eligibility checks (binary domains for V and every W_i, no self-loop)
    ## happen here, *before* anything is added to channelVarNames or
    ## definingConstraints. If a candidate fails any check we leave the original
    ## bool_clauses live so the standard constraint translator enforces the
    ## implications.
    var eqReifBy, neReifBy: Table[string, tuple[srcVar: string, val: int]]
    for ci in tr.reifChannelDefs:
        let con = tr.model.constraints[ci]
        let nm = stripSolverPrefix(con.name)
        if nm != "int_eq_reif" and nm != "int_ne_reif": continue
        if con.args.len < 3: continue
        if con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
        let v = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
        if nm == "int_eq_reif":
            eqReifBy[con.args[2].ident] = (srcVar: con.args[0].ident, val: v)
        else:
            neReifBy[con.args[2].ident] = (srcVar: con.args[0].ident, val: v)

    if eqReifBy.len == 0 or neReifBy.len == 0: return

    # Group implications by target var V: forceMap[V] = seq of (W_name, clause_ci)
    type ForceEntry = tuple[wName: string, clauseCi: int]
    var forceMap: Table[string, seq[ForceEntry]]
    var alreadySeenW: Table[string, HashSet[string]]  # V → set of W's already added (dedup)

    for ci, con in tr.model.constraints:
        if ci in tr.definingConstraints: continue
        if stripSolverPrefix(con.name) != "bool_clause": continue
        if con.args.len < 2: continue
        let posArg = con.args[0]
        let negArg = con.args[1]
        if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
        if negArg.elems.len != 0: continue   # only pure-positive 2-literal clauses
        if posArg.elems.len != 2: continue
        let a = posArg.elems[0]
        let b = posArg.elems[1]
        if a.kind != FznIdent or b.kind != FznIdent: continue

        # Try both orderings: (a=ne, b=eq) and (a=eq, b=ne)
        var matched = false
        var vName, wName: string
        for (neC, eqC) in [(a.ident, b.ident), (b.ident, a.ident)]:
            if neC notin neReifBy or eqC notin eqReifBy: continue
            let neInfo = neReifBy[neC]
            let eqInfo = eqReifBy[eqC]
            # We want: ne(W != 1) ∨ eq(V == 1) ≡ W = 1 → V = 1
            if neInfo.val != 1 or eqInfo.val != 1: continue
            vName = eqInfo.srcVar
            wName = neInfo.srcVar
            matched = true
            break
        if not matched: continue

        # Dedup
        if vName notin alreadySeenW:
            alreadySeenW[vName] = initHashSet[string]()
        if wName in alreadySeenW[vName]: continue
        alreadySeenW[vName].incl(wName)
        forceMap.mgetOrPut(vName, @[]).add((wName: wName, clauseCi: ci))

    if forceMap.len == 0: return

    proc isBinaryDomain(dom: seq[int]): bool =
        dom.len == 2 and dom[0] == 0 and dom[1] == 1

    var nDetected = 0
    var nClausesConsumed = 0
    var nRejectedDomain = 0
    for vName, forces in forceMap.pairs:
        if forces.len < 2: continue
        # Skip if V is already claimed by another detector or aliased.
        if vName in tr.channelVarNames: continue
        if vName in tr.definedVarNames: continue
        if vName in tr.equalityCopyAliases: continue
        # Validate V is binary {0,1}. lookupVarDomain returns @[0,1] for FznBool
        # and the explicit range for FznIntRange/FznIntSet.
        let vDom = tr.lookupVarDomain(vName)
        if not isBinaryDomain(vDom):
            nRejectedDomain += 1
            continue
        # Validate every W_i is binary, and there is no self-loop W_i == V.
        var allBinary = true
        var sourceNames: seq[string]
        var consumedClauses: seq[int]
        for f in forces:
            if f.wName == vName:
                allBinary = false
                break
            let wDom = tr.lookupVarDomain(f.wName)
            if not isBinaryDomain(wDom):
                allBinary = false
                break
            sourceNames.add(f.wName)
            consumedClauses.add(f.clauseCi)
        if not allBinary:
            nRejectedDomain += 1
            continue
        tr.implicationOrChannelDefs.add(
            (targetVar: vName, sourceVars: sourceNames, consumedClauses: consumedClauses))
        # Now safe to claim — every check the build phase will repeat has
        # already passed at the FZN-declaration level.
        tr.channelVarNames.incl(vName)
        for ci in consumedClauses:
            tr.definingConstraints.incl(ci)
        nDetected += 1
        nClausesConsumed += consumedClauses.len

    if nDetected > 0 or nRejectedDomain > 0:
        stderr.writeLine(&"[FZN] Detected {nDetected} implication-OR channel candidates " &
                         &"(V = OR(W_i) from {nClausesConsumed} bool_clauses; " &
                         &"rejected {nRejectedDomain} non-binary; deferred to build phase)")
