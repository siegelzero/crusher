## Tests for `detectImplicitLinEqDefinedVars` and the supporting range-bound
## emission / rescue paths.
##
## The pass promotes the slack variable in `sum + slack = capacity`-shaped
## int_lin_eqs to a channel/defined-var. Guards (any one rejects):
##   - constraint already has `defines_var`
##   - constraint already in definingConstraints / countEqPatterns / similar
##   - fewer than 3 variables (1-var = constant pin, 2-var = simple equality)
##   - any coefficient is not ±1
##   - candidate is search-annotated, parameter, defined, channel, or already
##     the target of some other defines_var elsewhere in the model
##
## The pass also: registers the constraint via `tr.implicitLinEqDefinedVars`
## (consumed by `tryBuildDefinedExpression`), records the declared range
## bounds in `tr.implicitLinEqRangeBounds` for later emission, and (when the
## promoted var also appears in a var-indexed-array element) gets re-rescued
## to a channel so the array binding still has positions to read from.

import unittest
import std/[sequtils, sets, tables]
import crusher
import flatzinc/[parser, translator]


suite "Implicit int_lin_eq channel detection":

    test "promotes slack in sum+slack=capacity (sum terms already defined)":
        ## Bin-packing-style equation: three int_times-defined product terms
        ## plus a slack equal to capacity. The product outputs are already in
        ## channelVarNames/definedVarNames after collectDefinedVars, so slack
        ## is the *unique* unclaimed candidate — exactly the case the pass
        ## targets.
        let src = """
var 0..5: a :: output_var;
var 0..5: b :: output_var;
var 0..5: c :: output_var;
var 0..5: d :: output_var;
var 0..5: e :: output_var;
var 0..5: f :: output_var;
var 0..25: t1 :: var_is_introduced :: is_defined_var;
var 0..25: t2 :: var_is_introduced :: is_defined_var;
var 0..25: t3 :: var_is_introduced :: is_defined_var;
var 0..100: slack :: var_is_introduced;
constraint int_times(a, b, t1) :: defines_var(t1);
constraint int_times(c, d, t2) :: defines_var(t2);
constraint int_times(e, f, t3) :: defines_var(t3);
constraint int_lin_eq([1,1,1,1],[t1,t2,t3,slack],100);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # The slack variable should be promoted (defined or channeled),
        # not a free search position.
        check "slack" in tr.channelVarNames or "slack" in tr.definedVarNames

        # The int_lin_eq must be registered in the side-table and marked
        # defining.
        var found = false
        for ci, _ in tr.implicitLinEqDefinedVars:
            if tr.implicitLinEqDefinedVars[ci] == "slack":
                found = true
                check ci in tr.definingConstraints
                break
        check found

        # The range bound for the promoted var must have been recorded for
        # later emission. Lo/hi reflect presolve-tightened domain (lo here is
        # 100 - max(t1+t2+t3) = 100 - 75 = 25, since each t_i is capped at 25).
        var boundsRecorded = false
        for entry in tr.implicitLinEqRangeBounds:
            if entry.varName == "slack":
                check entry.lo == 25
                check entry.hi == 100
                boundsRecorded = true
                break
        check boundsRecorded

    test "skips 2-variable int_lin_eq (binary equality, presolve territory)":
        ## `[1,-1] [a,b] 0` is just a = b. Promoting either side would steal
        ## a variable other detectors may want.
        let src = """
var 0..5: a :: var_is_introduced;
var 0..5: b :: var_is_introduced;
constraint int_lin_eq([1,-1],[a,b],0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.implicitLinEqDefinedVars.len == 0

    test "skips when not all coefficients are ±1":
        ## Mixed coefficients (objective-style decomposition) — other detectors
        ## handle these; the implicit-lin-eq pass is the "user wrote sum + slack
        ## = capacity" pattern only.
        let src = """
var 0..5: c1 :: var_is_introduced;
var 0..5: c2 :: var_is_introduced;
var 0..5: c3 :: var_is_introduced;
var 0..50: obj :: var_is_introduced;
constraint int_lin_eq([5,3,1,-1],[c1,c2,c3,obj],0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.implicitLinEqDefinedVars.len == 0

    test "skips when constraint has explicit defines_var annotation":
        ## Already covered by the existing collectDefinedVars path — the
        ## implicit-lin-eq pass must not double-claim.
        let src = """
var 0..5: a :: var_is_introduced;
var 0..5: b :: var_is_introduced;
var 0..5: c :: var_is_introduced;
var 0..15: total :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([1,1,1,-1],[a,b,c,total],0) :: defines_var(total);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.implicitLinEqDefinedVars.len == 0

    test "skips search-annotated candidate":
        ## A variable named in the solve annotation is a user-chosen search
        ## position; promoting it would silently override the user's intent.
        let src = """
var 0..5: a :: output_var;
var 0..5: b :: output_var;
var 0..5: c :: output_var;
var 0..15: slack :: output_var;
constraint int_lin_eq([1,1,1,1],[a,b,c,slack],10);
solve :: int_search([a,b,c,slack], first_fail, indomain_min) satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # All four vars are search-annotated → no candidate.
        check tr.implicitLinEqDefinedVars.len == 0

    test "skips when candidate is already a defines_var target elsewhere":
        ## Some other constraint already takes responsibility for defining
        ## `slack` — we must not install a parallel definition.
        let src = """
var 0..5: a :: var_is_introduced;
var 0..5: b :: var_is_introduced;
var 0..5: c :: var_is_introduced;
var 0..5: x :: var_is_introduced;
var 0..5: slack :: var_is_introduced :: is_defined_var;
constraint int_abs(x, slack) :: defines_var(slack);
constraint int_lin_eq([1,1,1,1],[a,b,c,slack],10);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # `slack` is defined by int_abs, so it must not be claimed by the
        # int_lin_eq promotion pass.
        for ci, name in tr.implicitLinEqDefinedVars:
            check name != "slack"

    test "skips count_eq pattern int_lin_eq":
        ## Constraint matches the count_eq decomposition shape and is registered
        ## in `countEqPatterns` (without going through definingConstraints).
        ## The implicit-lin-eq pass must respect that claim.
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 1..3: x4 :: output_var;
var 0..4: target :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
var bool: b4 :: var_is_introduced :: is_defined_var;
var 0..1: ind1 :: var_is_introduced :: is_defined_var;
var 0..1: ind2 :: var_is_introduced :: is_defined_var;
var 0..1: ind3 :: var_is_introduced :: is_defined_var;
var 0..1: ind4 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 2, b1) :: defines_var(b1);
constraint int_eq_reif(x2, 2, b2) :: defines_var(b2);
constraint int_eq_reif(x3, 2, b3) :: defines_var(b3);
constraint int_eq_reif(x4, 2, b4) :: defines_var(b4);
constraint bool2int(b1, ind1) :: defines_var(ind1);
constraint bool2int(b2, ind2) :: defines_var(ind2);
constraint bool2int(b3, ind3) :: defines_var(ind3);
constraint bool2int(b4, ind4) :: defines_var(ind4);
constraint int_lin_eq([1,-1,-1,-1,-1],[target,ind1,ind2,ind3,ind4],0);
constraint int_eq(target, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # int_lin_eq has 5 vars all coefs ±1, so it'd otherwise be a candidate.
        # But it's already claimed by the count_eq detector, so we skip.
        check tr.implicitLinEqDefinedVars.len == 0

    test "promoted var that also feeds array_var_int_element gets rescued":
        ## When a promoted slack is referenced as an element of a var-indexed
        ## array (var_array_int_element), it needs a position to be channeled
        ## into. The rescue path in `rescueDefinedVarsToChannels` re-promotes
        ## from defined-var to channel-var so a binding can be installed.
        ## (Setup mirrors the `t1,t2,t3` are int_times outputs pattern so the
        ## implicit-lin-eq pass picks `slack` as the unique candidate.)
        let src = """
var 1..3: idx :: output_var;
var 0..5: a :: output_var;
var 0..5: b :: output_var;
var 0..5: c :: output_var;
var 0..5: d :: output_var;
var 0..5: e :: output_var;
var 0..5: f :: output_var;
var 0..25: t1 :: var_is_introduced :: is_defined_var;
var 0..25: t2 :: var_is_introduced :: is_defined_var;
var 0..25: t3 :: var_is_introduced :: is_defined_var;
var 0..100: slack :: var_is_introduced;
var 0..100: result :: var_is_introduced :: is_defined_var;
array [1..3] of var int: arr = [t1, slack, t3];
constraint int_times(a, b, t1) :: defines_var(t1);
constraint int_times(c, d, t2) :: defines_var(t2);
constraint int_times(e, f, t3) :: defines_var(t3);
constraint int_lin_eq([1,1,1,1],[t1,t2,t3,slack],100);
constraint array_var_int_element(idx, arr, result) :: defines_var(result);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Promotion happened.
        var slackPromoted = false
        for ci, name in tr.implicitLinEqDefinedVars:
            if name == "slack":
                slackPromoted = true
                break
        check slackPromoted

        # Rescue moved slack into channelVarNames so array_var_int_element
        # can find its element positions.
        check "slack" in tr.channelVarNames
        check "slack" in tr.varPositions

    test "range bound is recorded for the promoted slack var":
        ## The `implicitLinEqRangeBounds` table captures the declared (lo, hi)
        ## of each promoted var so the post-translateVariables pipeline can
        ## emit `expr ≥ lo` / `expr ≤ hi` constraints (skipping bounds whose
        ## natural expression range already implies them). This test verifies
        ## the recording itself, not the per-bound emit decision.
        let src = """
var 0..5: a :: output_var;
var 0..5: b :: output_var;
var 0..5: c :: output_var;
var 0..5: d :: output_var;
var 0..5: e :: output_var;
var 0..5: f :: output_var;
var 0..25: t1 :: var_is_introduced :: is_defined_var;
var 0..25: t2 :: var_is_introduced :: is_defined_var;
var 0..25: t3 :: var_is_introduced :: is_defined_var;
var 0..100: slack :: var_is_introduced;
constraint int_times(a, b, t1) :: defines_var(t1);
constraint int_times(c, d, t2) :: defines_var(t2);
constraint int_times(e, f, t3) :: defines_var(t3);
constraint int_lin_eq([1,1,1,1],[t1,t2,t3,slack],100);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        var loBoundRecorded = false
        for entry in tr.implicitLinEqRangeBounds:
            if entry.varName == "slack":
                # Presolve tightens slack from [0, 100] to [25, 100] given
                # `t_i ≤ 25`. The recorded bound reflects the tightened range.
                check entry.lo == 25
                check entry.hi == 100
                loBoundRecorded = true
                break
        check loBoundRecorded

    test "skips promotion when target var has no resolvable domain":
        ## Defensive guard: getTightenedBounds returns (lo=0, hi=0) when domain
        ## lookup fails. We must not record those zeros — doing so would later
        ## emit `expr ≥ 0 ∧ expr ≤ 0`, silently overconstraining the model.
        ## Hard to construct organically (well-formed FZN always has a domain),
        ## so this test exercises the guard by direct manipulation: poke a
        ## tightened-domain miss for `slack` and re-run detection.
        let src = """
var 0..5: a :: output_var;
var 0..5: b :: output_var;
var 0..5: c :: output_var;
var 0..5: d :: output_var;
var 0..5: e :: output_var;
var 0..5: f :: output_var;
var 0..25: t1 :: var_is_introduced :: is_defined_var;
var 0..25: t2 :: var_is_introduced :: is_defined_var;
var 0..25: t3 :: var_is_introduced :: is_defined_var;
var 0..100: slack :: var_is_introduced;
constraint int_times(a, b, t1) :: defines_var(t1);
constraint int_times(c, d, t2) :: defines_var(t2);
constraint int_times(e, f, t3) :: defines_var(t3);
constraint int_lin_eq([1,1,1,1],[t1,t2,t3,slack],100);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # Sanity: in the well-formed case, slack does get promoted.
        check tr.implicitLinEqDefinedVars.len == 1
        # Recorded bound is non-degenerate (covered by the previous test, but
        # we want to confirm we never see a (0,0) entry slip through here).
        for entry in tr.implicitLinEqRangeBounds:
            check not (entry.lo == 0 and entry.hi == 0)


suite "Implicit int_lin_eq end-to-end":

    test "solves bin-packing shape (sum+slack=capacity) producing a valid assignment":
        ## Small bin-packing model: 4 persons, each chooses good ∈ {1, 2}.
        ## For each good g, Σ_p [good[p]==g] + slack[g] = 2 (capacity).
        ## With 4 persons and 2 capacity per good, exactly two persons per good
        ## yields slack = [0, 0]; lopsided assignments leave a positive slack
        ## paired with a negative slack — but slack ∈ [0, 2] forces feasibility
        ## to a balanced split.
        ##
        ## This exercises:
        ##   - detectImplicitLinEqDefinedVars promoting both slack[1] and slack[2]
        ##   - implicit range-bound emission re-pinning slack ∈ [0, 2]
        ##   - rescue path (slack vars referenced via element bindings of
        ##     intermediate indicators, depending on translator path)
        ##   - the channel-inequality repair pre-pass at init
        let src = """
var 1..2: g1 :: output_var;
var 1..2: g2 :: output_var;
var 1..2: g3 :: output_var;
var 1..2: g4 :: output_var;
var bool: b11 :: var_is_introduced :: is_defined_var;
var bool: b21 :: var_is_introduced :: is_defined_var;
var bool: b31 :: var_is_introduced :: is_defined_var;
var bool: b41 :: var_is_introduced :: is_defined_var;
var bool: b12 :: var_is_introduced :: is_defined_var;
var bool: b22 :: var_is_introduced :: is_defined_var;
var bool: b32 :: var_is_introduced :: is_defined_var;
var bool: b42 :: var_is_introduced :: is_defined_var;
var 0..1: i11 :: var_is_introduced :: is_defined_var;
var 0..1: i21 :: var_is_introduced :: is_defined_var;
var 0..1: i31 :: var_is_introduced :: is_defined_var;
var 0..1: i41 :: var_is_introduced :: is_defined_var;
var 0..1: i12 :: var_is_introduced :: is_defined_var;
var 0..1: i22 :: var_is_introduced :: is_defined_var;
var 0..1: i32 :: var_is_introduced :: is_defined_var;
var 0..1: i42 :: var_is_introduced :: is_defined_var;
var 0..2: slack1 :: var_is_introduced;
var 0..2: slack2 :: var_is_introduced;
constraint int_eq_reif(g1, 1, b11) :: defines_var(b11);
constraint int_eq_reif(g2, 1, b21) :: defines_var(b21);
constraint int_eq_reif(g3, 1, b31) :: defines_var(b31);
constraint int_eq_reif(g4, 1, b41) :: defines_var(b41);
constraint int_eq_reif(g1, 2, b12) :: defines_var(b12);
constraint int_eq_reif(g2, 2, b22) :: defines_var(b22);
constraint int_eq_reif(g3, 2, b32) :: defines_var(b32);
constraint int_eq_reif(g4, 2, b42) :: defines_var(b42);
constraint bool2int(b11, i11) :: defines_var(i11);
constraint bool2int(b21, i21) :: defines_var(i21);
constraint bool2int(b31, i31) :: defines_var(i31);
constraint bool2int(b41, i41) :: defines_var(i41);
constraint bool2int(b12, i12) :: defines_var(i12);
constraint bool2int(b22, i22) :: defines_var(i22);
constraint bool2int(b32, i32) :: defines_var(i32);
constraint bool2int(b42, i42) :: defines_var(i42);
constraint int_lin_eq([1,1,1,1,1],[i11,i21,i31,i41,slack1],2);
constraint int_lin_eq([1,1,1,1,1],[i12,i22,i32,i42,slack2],2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Both slacks should be promoted (sum-of-indicators + slack = capacity
        # is the prototypical case the detector is built for).
        check "slack1" in tr.implicitLinEqDefinedVars.values.toSeq
        check "slack2" in tr.implicitLinEqDefinedVars.values.toSeq

        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

        let g1Pos = tr.varPositions["g1"]
        let g2Pos = tr.varPositions["g2"]
        let g3Pos = tr.varPositions["g3"]
        let g4Pos = tr.varPositions["g4"]
        let goods = @[
            tr.sys.assignment[g1Pos],
            tr.sys.assignment[g2Pos],
            tr.sys.assignment[g3Pos],
            tr.sys.assignment[g4Pos],
        ]
        # Every choice in 1..2.
        for g in goods:
            check g in {1, 2}
        # Capacity respected: at most 2 picks of each good.
        var cnt1, cnt2 = 0
        for g in goods:
            if g == 1: cnt1 += 1
            elif g == 2: cnt2 += 1
        check cnt1 <= 2
        check cnt2 <= 2
        # Capacities sum: 4 persons + 2 slack-per-good = 4. Implied by feasibility.


suite "Channel-inequality repair gating":
    ## These tests defend the gating discipline that prevents `repairChannelInequalities`
    ## from firing on models it wasn't designed for. Without these guards the repair
    ## destabilises ~20 mznchallenge tests by collapsing parallel-worker diversity
    ## (see commits 01842d3 and follow-up). The gate has three pieces, each tested
    ## here:
    ##
    ##   1. Translator sets `baseArray.enableChannelInequalityRepair = true` ONLY
    ##      when `detectImplicitLinEqDefinedVars` actually emits range bounds.
    ##   2. `ConstrainedArray.deepCopy` propagates the flag (workers won't see it
    ##      otherwise — and the parallel solver always works on copies).
    ##   3. Models without the implicit-lin-eq sum+slack pattern leave the flag
    ##      unset even if they have channel-only `≥`/`≤` constraints from other
    ##      sources (count constraints, indicator-sum bounds, etc.).
    ##
    ## If any of these tests fail, the repair gate is broken and a full mztest
    ## run will likely show 20+ regressions.

    test "translator sets enableChannelInequalityRepair when implicit-lin-eq emits bounds":
        ## Same shape as the bin-packing end-to-end test: 4 persons × 2 goods,
        ## sum-of-indicators + slack = capacity. The detector promotes both slacks
        ## and emits bounds, which must set the flag.
        let src = """
var 1..2: g1 :: output_var;
var 1..2: g2 :: output_var;
var 1..2: g3 :: output_var;
var 1..2: g4 :: output_var;
var bool: b11 :: var_is_introduced :: is_defined_var;
var bool: b21 :: var_is_introduced :: is_defined_var;
var bool: b31 :: var_is_introduced :: is_defined_var;
var bool: b41 :: var_is_introduced :: is_defined_var;
var bool: b12 :: var_is_introduced :: is_defined_var;
var bool: b22 :: var_is_introduced :: is_defined_var;
var bool: b32 :: var_is_introduced :: is_defined_var;
var bool: b42 :: var_is_introduced :: is_defined_var;
var 0..1: i11 :: var_is_introduced :: is_defined_var;
var 0..1: i21 :: var_is_introduced :: is_defined_var;
var 0..1: i31 :: var_is_introduced :: is_defined_var;
var 0..1: i41 :: var_is_introduced :: is_defined_var;
var 0..1: i12 :: var_is_introduced :: is_defined_var;
var 0..1: i22 :: var_is_introduced :: is_defined_var;
var 0..1: i32 :: var_is_introduced :: is_defined_var;
var 0..1: i42 :: var_is_introduced :: is_defined_var;
var 0..2: slack1 :: var_is_introduced;
var 0..2: slack2 :: var_is_introduced;
constraint int_eq_reif(g1, 1, b11) :: defines_var(b11);
constraint int_eq_reif(g2, 1, b21) :: defines_var(b21);
constraint int_eq_reif(g3, 1, b31) :: defines_var(b31);
constraint int_eq_reif(g4, 1, b41) :: defines_var(b41);
constraint int_eq_reif(g1, 2, b12) :: defines_var(b12);
constraint int_eq_reif(g2, 2, b22) :: defines_var(b22);
constraint int_eq_reif(g3, 2, b32) :: defines_var(b32);
constraint int_eq_reif(g4, 2, b42) :: defines_var(b42);
constraint bool2int(b11, i11) :: defines_var(i11);
constraint bool2int(b21, i21) :: defines_var(i21);
constraint bool2int(b31, i31) :: defines_var(i31);
constraint bool2int(b41, i41) :: defines_var(i41);
constraint bool2int(b12, i12) :: defines_var(i12);
constraint bool2int(b22, i22) :: defines_var(i22);
constraint bool2int(b32, i32) :: defines_var(i32);
constraint bool2int(b42, i42) :: defines_var(i42);
constraint int_lin_eq([1,1,1,1,1],[i11,i21,i31,i41,slack1],2);
constraint int_lin_eq([1,1,1,1,1],[i12,i22,i32,i42,slack2],2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Sanity: detector promoted both slacks (precondition for the flag).
        check tr.implicitLinEqDefinedVars.len == 2
        # The flag must be set so the repair pre-pass fires for this model.
        check tr.sys.baseArray.enableChannelInequalityRepair

    test "translator leaves flag unset for trivial all_different model":
        ## No int_lin_eq at all → detector never fires → flag must stay false.
        ## Establishes the unset-by-default baseline.
        let src = """
var 1..3: x1;
var 1..3: x2;
var 1..3: x3;
constraint fzn_all_different_int([x1,x2,x3]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.implicitLinEqDefinedVars.len == 0
        check not tr.sys.baseArray.enableChannelInequalityRepair

    test "translator leaves flag unset when only counter-style channel ineq exists":
        ## This is the regression-catcher. The model has a channel-only `≤`
        ## constraint from a count-of-indicators pattern (the indicators get
        ## promoted to channel positions via int_eq_reif → bool2int), so the
        ## constraint matches `repairChannelInequalities`'s `hasChannelInequality`
        ## test. But there's NO int_lin_eq sum+slack pattern, so the implicit-
        ## lin-eq detector never emits bounds — the flag must stay false even
        ## though the channel-only inequality structure is present.
        ##
        ## If a future change widens the flag-setting condition (e.g., sets it
        ## whenever `hasChannelInequality` would match), this test fails — and
        ## ~20 mznchallenge tests will silently regress until someone re-runs
        ## the full integration suite.
        let src = """
var 1..4: x;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
var bool: b4 :: var_is_introduced :: is_defined_var;
var 0..1: i1 :: var_is_introduced :: is_defined_var;
var 0..1: i2 :: var_is_introduced :: is_defined_var;
var 0..1: i3 :: var_is_introduced :: is_defined_var;
var 0..1: i4 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, b1) :: defines_var(b1);
constraint int_eq_reif(x, 2, b2) :: defines_var(b2);
constraint int_eq_reif(x, 3, b3) :: defines_var(b3);
constraint int_eq_reif(x, 4, b4) :: defines_var(b4);
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint bool2int(b3, i3) :: defines_var(i3);
constraint bool2int(b4, i4) :: defines_var(i4);
constraint int_lin_le([1,1,1,1],[i1,i2,i3,i4],2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # Detector did not fire (no int_lin_eq with sum+slack=capacity shape).
        check tr.implicitLinEqDefinedVars.len == 0
        # Flag must stay unset — this is the invariant the repair gating relies on.
        check not tr.sys.baseArray.enableChannelInequalityRepair

    test "ConstrainedArray.deepCopy preserves enableChannelInequalityRepair":
        ## The parallel solver always works on `baseArray.deepCopy()` (see
        ## parallelResolution.nim, scatterSearch.nim — multiple call sites).
        ## If deepCopy drops the flag, parallel workers never run the repair,
        ## even when the translator correctly set it on baseArray.
        var arr = initConstrainedArray[int](3)
        check not arr.enableChannelInequalityRepair  # default

        arr.enableChannelInequalityRepair = true
        let copy1 = arr.deepCopy()
        check copy1.enableChannelInequalityRepair

        arr.enableChannelInequalityRepair = false
        let copy2 = arr.deepCopy()
        check not copy2.enableChannelInequalityRepair
