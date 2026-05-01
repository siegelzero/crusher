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
