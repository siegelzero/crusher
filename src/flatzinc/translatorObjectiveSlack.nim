## Included from translator.nim -- not a standalone module.
## Objective slack-bool channel detection.
##
## Many MZN models contain "slack" boolean variables — a per-item indicator
## that contributes +1 to the minimisation objective and only ever appears as
## a positive literal in disjunctive clauses. At the optimum:
##
##   slack[i] = 1   iff   at least one of slack[i]'s containing clauses has
##                        body unsatisfied without slack[i]
##
## So slack[i] is fully determined by the rest of the model — keeping it as a
## search variable is wasted work. Local search neighbourhoods scale with the
## number of search positions; thousands of independent slack flips drown out
## the meaningful moves on the actual decision variables.
##
## This pass identifies these vars and turns them into derived channels via a
## sum-of-products algebraic expression:
##
##   slack[i] = OR over k of (clause_k_unsatisfied)
##            = (sum_k product_l literal_l) > 0
##
## where each `product_l literal_l` is the AND that makes clause_k's body
## evaluate to false (positive literals → 1-x, negative literals → x).
##
## Generally applicable to: misclassification indicators (decision sets),
## tardiness/late bools (scheduling), demand-unmet indicators (covering),
## constraint-violated bools in soft CP — anywhere a +1-in-obj slack appears
## only as a positive literal in a fixed set of clauses.

proc detectObjectiveSlackBools*(tr: var FznTranslator) =
    ## Detects boolean slack variables — bools with positive coefficient in
    ## the minimisation objective sum that appear ONLY as positive literals
    ## in `bool_clause` constraints. Builds a channel binding that derives
    ## each slack from the satisfaction of its containing clauses.
    ##
    ## Must run AFTER translateVariables (positions exist) and AFTER
    ## detectNandRedundancy (which populates bool2intSourceMap), but BEFORE
    ## the main constraint translation loop so consumed clauses are skipped.

    if tr.model.solve.kind != Minimize: return
    if tr.model.solve.objective == nil or tr.model.solve.objective.kind != FznIdent:
        return
    let objVar = tr.model.solve.objective.ident

    # ----- Step 1: index int_lin_eq defines_var → linear sum info.
    type LinEqInfo = object
        coefs: seq[int]
        vars: seq[string]
    var linEqByDefinedVar = initTable[string, LinEqInfo]()

    for ci, con in tr.model.constraints:
        if stripSolverPrefix(con.name) != "int_lin_eq": continue
        if not con.hasAnnotation("defines_var"): continue
        if con.args.len < 3: continue
        var coefs: seq[int]
        try: coefs = tr.resolveIntArray(con.args[0])
        except CatchableError: continue
        let varElems = tr.resolveVarArrayElems(con.args[1])
        if coefs.len != varElems.len: continue
        var rhs: int
        try: rhs = tr.resolveIntArg(con.args[2])
        except CatchableError: continue
        if rhs != 0: continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
        let target = ann.args[0].ident
        if target in linEqByDefinedVar: continue  # ambiguous; skip

        # Find target's index in the var list — its coefficient must be -1
        # so the sum represents `target = sum_{i != t} coefs[i] * vars[i]`.
        var targetIdx = -1
        for i, v in varElems:
            if v.kind == FznIdent and v.ident == target:
                targetIdx = i
                break
        if targetIdx == -1: continue
        if coefs[targetIdx] != -1: continue

        var info = LinEqInfo()
        var bad = false
        for i in 0..<varElems.len:
            if i == targetIdx: continue
            if varElems[i].kind != FznIdent:
                bad = true; break
            info.coefs.add(coefs[i])
            info.vars.add(varElems[i].ident)
        if bad: continue
        linEqByDefinedVar[target] = info

    if objVar notin linEqByDefinedVar: return

    # ----- Step 2: walk objective definition transitively to collect bool sources
    # with strictly-positive accumulated weight. We follow chains like
    # `objective = misclassified + 27*k`, `misclassified = sum(m_i)`, and stop
    # at non-defined vars. Any bool/0..1 leaf with positive weight whose int
    # counterpart traces back through `bool2int(b, b_int)` is a slack candidate.
    var slackCandidates = initHashSet[string]()  # bool var names
    var visited = initHashSet[string]()
    type WalkEntry = tuple[name: string, sign: int]
    var stack: seq[WalkEntry]
    stack.add((name: objVar, sign: 1))
    while stack.len > 0:
        let entry = stack.pop()
        if entry.name in visited: continue
        visited.incl(entry.name)
        if entry.sign <= 0: continue  # we only care about positive contributors
        if entry.name notin linEqByDefinedVar:
            # Leaf: check if it has a bool source via bool2int
            if entry.name in tr.bool2intSourceMap:
                slackCandidates.incl(tr.bool2intSourceMap[entry.name])
            continue
        let info = linEqByDefinedVar[entry.name]
        for i, v in info.vars:
            let coef = info.coefs[i]
            let newSign = if coef > 0: entry.sign elif coef < 0: -entry.sign else: 0
            if newSign > 0:
                stack.add((name: v, sign: newSign))

    if slackCandidates.len == 0: return

    # ----- Step 3: scan every constraint to collect clause membership for each
    # candidate, and disqualify any candidate that appears anywhere besides:
    #   - positive literal in a bool_clause
    #   - the bool side of a bool2int(b, b_int) :: defines_var(b_int)
    type ClauseInfo = object
        ci: int
        posLits: seq[string]   # excluding the slack itself
        negLits: seq[string]
    var clausesByVar = initTable[string, seq[ClauseInfo]]()
    var disqualified = initHashSet[string]()

    proc disqualifyAll(disq: var HashSet[string], cands: HashSet[string], arg: FznExpr) =
        case arg.kind
        of FznIdent:
            if arg.ident in cands: disq.incl(arg.ident)
        of FznArrayLit:
            for e in arg.elems:
                if e.kind == FznIdent and e.ident in cands:
                    disq.incl(e.ident)
        else: discard

    for ci, con in tr.model.constraints:
        let name = stripSolverPrefix(con.name)
        case name
        of "bool_clause":
            let lits = extractBoolClauseLiterals(con)
            if not lits.ok:
                # Unparseable clause — disqualify any slack mentioned anywhere
                for arg in con.args:
                    disqualifyAll(disqualified, slackCandidates, arg)
                continue

            # Collect the slack candidates that appear in this clause as positive
            # literals. Negative literal hits disqualify the candidate.
            var posSlacks = initHashSet[string]()
            for e in lits.posElems:
                if e.kind == FznIdent and e.ident in slackCandidates:
                    posSlacks.incl(e.ident)
            for e in lits.negElems:
                if e.kind == FznIdent and e.ident in slackCandidates:
                    disqualified.incl(e.ident)

            # If multiple slacks share a clause, disqualify them — the OR-of-slacks
            # body coupling makes the simple per-slack channel binding incorrect.
            if posSlacks.len > 1:
                for s in posSlacks: disqualified.incl(s)
                continue

            for s in posSlacks:
                if s in disqualified: continue
                # Build clause info: literals minus the slack itself, all required
                # to be plain identifiers.
                var info = ClauseInfo(ci: ci)
                var bad = false
                for e in lits.posElems:
                    if e.kind != FznIdent: bad = true; break
                    if e.ident == s: continue
                    info.posLits.add(e.ident)
                if bad:
                    disqualified.incl(s)
                    continue
                for e in lits.negElems:
                    if e.kind != FznIdent: bad = true; break
                    info.negLits.add(e.ident)
                if bad:
                    disqualified.incl(s)
                    continue
                clausesByVar.mgetOrPut(s, @[]).add(info)

        of "bool2int":
            # OK if a candidate appears as the bool source (already accounted for).
            # Disqualify if it appears as the int output (shouldn't happen for bools
            # but we handle defensively).
            if con.args.len < 2:
                for arg in con.args: disqualifyAll(disqualified, slackCandidates, arg)
                continue
            # First arg is the bool source; second is the int output.
            if con.args[1].kind == FznIdent and con.args[1].ident in slackCandidates:
                disqualified.incl(con.args[1].ident)
            # arg[0] (bool source) being a candidate is fine.
        else:
            # Any other constraint that references a slack candidate disqualifies it.
            for arg in con.args:
                disqualifyAll(disqualified, slackCandidates, arg)

    # ----- Step 4: build channel bindings for verified slack vars.
    var nBuilt = 0
    var nClausesConsumed = 0
    var slackList: seq[string]
    for s in slackCandidates:
        if s in disqualified: continue
        if s notin clausesByVar: continue
        if clausesByVar[s].len == 0: continue
        slackList.add(s)

    # Sort for deterministic build order
    slackList.sort()

    for s in slackList:
        # Position must exist (slack is a regular bool var).
        if s notin tr.varPositions: continue
        let sPos = tr.varPositions[s]
        # Already a channel? Skip — something else owns this position.
        if s in tr.channelVarNames: continue
        let clauses = clausesByVar[s]

        # All literals must resolve to positions (search or channel positions).
        var allResolvable = true
        for c in clauses:
            for lit in c.posLits:
                if lit notin tr.varPositions:
                    allResolvable = false; break
            if not allResolvable: break
            for lit in c.negLits:
                if lit notin tr.varPositions:
                    allResolvable = false; break
            if not allResolvable: break
        if not allResolvable: continue

        # Build sum-of-products index expression. Each clause k contributes the
        # AND `prod_p (1 - p) * prod_n n` — equal to 1 iff clause k's body is
        # unsatisfied without the slack.
        var indexExpr: AlgebraicExpression[int]
        var hasIndex = false
        for c in clauses:
            var prod: AlgebraicExpression[int]
            var hasProd = false
            for p in c.posLits:
                let term = constLitExpr(1) - tr.getExpr(tr.varPositions[p])
                if not hasProd:
                    prod = term; hasProd = true
                else:
                    prod = prod * term
            for n in c.negLits:
                let term = tr.getExpr(tr.varPositions[n])
                if not hasProd:
                    prod = term; hasProd = true
                else:
                    prod = prod * term
            if not hasProd:
                # Clause body is empty (just the slack literal). The original
                # constraint forces the slack true unconditionally — degenerate;
                # don't channel.
                hasIndex = false
                break
            if not hasIndex:
                indexExpr = prod; hasIndex = true
            else:
                indexExpr = indexExpr + prod
        if not hasIndex: continue

        # Lookup table: index = 0 → slack 0; index >= 1 → slack 1.
        var arrayElems: seq[ArrayElement[int]]
        for i in 0..clauses.len:
            arrayElems.add(ArrayElement[int](
                isConstant: true,
                constantValue: if i == 0: 0 else: 1
            ))

        tr.sys.baseArray.addChannelBinding(sPos, indexExpr, arrayElems)
        tr.channelVarNames.incl(s)
        for c in clauses:
            tr.definingConstraints.incl(c.ci)
            inc nClausesConsumed
        inc nBuilt

    if nBuilt > 0:
        stderr.writeLine(&"[FZN] Detected {nBuilt} objective slack-bool channels (consumed {nClausesConsumed} bool_clauses)")
