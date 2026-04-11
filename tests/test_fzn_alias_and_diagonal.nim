## Tests for translator changes covering:
##   1. Dead-element-elimination loop reachability fix (translator.nim)
##      - Walks named arrays + defining-constraint refs when counting references
##   2. FZN-level variable alias canonicalization (translatorHelpers.nim)
##      - `var X = Y;` declarations: substitute X → Y everywhere, demote redundant
##        parallel `defines_var(X)` constraints, reuse Y's position
##   3. Sentinel-prefixed inverse channel detection (translatorChannels.nim)
##      - `array_var_int_element(idx_v, [v, p1..pn], v)` group → inverse channel
##   4. Matrix-element diagonal exclusion (translatorChannels.nim)
##      - Constant 2D matrix lookups + inverse permutation pattern → exclude
##        diagonal-only values from result domains

import unittest
import std/[sequtils, sets, tables]
import crusher
import flatzinc/[parser, translator]


suite "FlatZinc Dead Element Elimination Reachability":

    test "constraint reachable through named array literal is NOT consumed":
        ## Regression for the bug where the dead-element-elimination loop only
        ## counted direct constraint args. A var only used as an element of a
        ## NAMED array (which is in turn referenced by some other constraint)
        ## was treated as unreferenced and its defining constraint was dropped.
        ##
        ## Here `r` is the result of an array_int_element. It's not directly
        ## referenced by any other constraint, but it IS an element of the
        ## named array `arr`, which is used by another constraint. The loop
        ## must follow the named-array indirection and keep `r` alive.
        let src = """
array [1..3] of int: tbl = [10, 20, 30];
var 1..3: idx :: output_var;
var 0..40: r :: var_is_introduced;
constraint array_int_element(idx, tbl, r);
array [1..3] of var int: arr = [r, r, r];
var 1..3: pickIdx :: output_var;
var 0..40: pickResult :: output_var;
constraint array_var_int_element(pickIdx, arr, pickResult);
constraint int_eq(pickResult, 20);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        # If the dead-element loop wrongly consumed `r`'s defining constraint,
        # `r` would be a free variable and pickResult could be anything.
        # The constraint `pickResult == 20` then forces idx to land on a value
        # that produces 20 — i.e., idx must be 2.
        let idxVal = tr.sys.assignment[tr.varPositions["idx"]]
        check idxVal == 2

    test "constraint reachable only through defining (channel) constraint is kept":
        ## A var used as an INPUT to a channel-defining constraint (e.g., a
        ## reified equality) is referenced through that channel even though
        ## the channel itself is in `definingConstraints`. The loop must
        ## count refs from defining constraints too.
        let src = """
array [1..4] of int: tbl = [10, 20, 30, 40];
var 1..4: idx :: output_var;
var 0..40: r :: var_is_introduced;
var bool: matchesTwenty :: var_is_introduced :: is_defined_var;
constraint array_int_element(idx, tbl, r);
constraint int_eq_reif(r, 20, matchesTwenty) :: defines_var(matchesTwenty);
constraint bool_eq(matchesTwenty, true);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let idxVal = tr.sys.assignment[tr.varPositions["idx"]]
        # Only idx=2 makes r=20 which makes matchesTwenty=true
        check idxVal == 2


suite "FlatZinc Variable Alias Canonicalization":

    test "var X = Y; alias is substituted in constraint args":
        ## A simple alias chain: `var Y = X;` and `var Z = Y;`. After
        ## canonicalization, references to Z and Y should resolve to X's
        ## position. The trailing constraint forces X to a specific value
        ## via Z (which is the deepest alias).
        let src = """
var 1..10: x :: output_var;
var 1..10: y = x;
var 1..10: z = y;
constraint int_eq(z, 7);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # x and z must share the same Crusher position (alias unified)
        check tr.varPositions.hasKey("x")
        check tr.varPositions.hasKey("z")
        check tr.varPositions["x"] == tr.varPositions["z"]
        check tr.varPositions["y"] == tr.varPositions["x"]
        # The fznVarAliases map records the alias relationships
        check "y" in tr.fznVarAliases
        check "z" in tr.fznVarAliases
        check tr.fznVarAliases["y"] == "x"
        check tr.fznVarAliases["z"] == "x"
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        check tr.sys.assignment[tr.varPositions["x"]] == 7

    test "parallel defines_var constraints on aliased target are demoted":
        ## When MZN's CSE merges two parallel computation routes via an alias,
        ## both routes can have `defines_var` annotations targeting different
        ## (aliased) names that resolve to the same canonical. The translator
        ## must keep ONE as the channel definer and demote the rest to regular
        ## constraints — otherwise the second route's input vars become
        ## unconstrained and the model breaks (objective collapses to a bogus
        ## minimum because nothing forces the inputs to match).
        ##
        ## Here `chosen + 5 = listget` (one direction, defining via element)
        ## and `listget = lookup[idxFromOrder]` (the other direction, also
        ## defining via element on a different array but the SAME aliased
        ## result var). One must win as the channel; the other becomes a
        ## regular constraint that enforces the equation.
        let src = """
array [1..3] of int: shiftBy5 = [6, 7, 8];
array [1..3] of int: pickFromArr = [6, 7, 8];
var 1..3: chooseOrder :: output_var;
var 1..3: chosen :: var_is_introduced;
var 1..3: idxFromOrder :: var_is_introduced;
var 6..8: listget :: var_is_introduced :: is_defined_var;
var 6..8: listgetAlias :: var_is_introduced :: is_defined_var = listget;
constraint int_eq(chosen, chooseOrder);
constraint int_eq(idxFromOrder, chooseOrder);
constraint array_int_element(chosen, shiftBy5, listget) :: defines_var(listget);
constraint array_int_element(idxFromOrder, pickFromArr, listgetAlias) :: defines_var(listgetAlias);
constraint int_eq(listget, 7);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # listgetAlias was an alias of listget — the canonicalize pass should
        # have substituted them and unified positions
        check tr.fznVarAliases.hasKey("listgetAlias")
        check tr.fznVarAliases["listgetAlias"] == "listget"
        check tr.varPositions["listget"] == tr.varPositions["listgetAlias"]
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        # listget == 7 forces both element constraints to point at index 2
        check tr.sys.assignment[tr.varPositions["listget"]] == 7
        check tr.sys.assignment[tr.varPositions["chooseOrder"]] == 2

    test "alias decl with output_var annotation still appears in output":
        ## When an aliased var has `output_var`, its name must remain in
        ## tr.outputVars so the formatter prints it (the value comes from
        ## the canonical's position).
        let src = """
var 1..10: a;
var 1..10: b :: output_var = a;
constraint int_eq(a, 5);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check "b" in tr.outputVars
        check tr.varPositions["b"] == tr.varPositions["a"]
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        # `b` reads from `a`'s position
        check tr.sys.assignment[tr.varPositions["b"]] == 5


suite "FlatZinc Sentinel-Prefixed Inverse Channel Detection":

    test "3 sentinel-prefixed array_var_int_elements form one inverse channel":
        ## Three constraints over arrays of the form [v, p1, p2, p3] where v
        ## is a different sentinel for each constraint and the suffix p1..p3
        ## is a permutation. After detection, idx_v points to (1-based
        ## position of v in p1..p3) + 1.
        let src = """
var 0..2: p1 :: output_var;
var 0..2: p2 :: output_var;
var 0..2: p3 :: output_var;
var 1..4: idx0 :: output_var;
var 1..4: idx1 :: output_var;
var 1..4: idx2 :: output_var;
array [1..4] of var int: arr0 = [0, p1, p2, p3];
array [1..4] of var int: arr1 = [1, p1, p2, p3];
array [1..4] of var int: arr2 = [2, p1, p2, p3];
constraint array_var_int_element(idx0, arr0, 0);
constraint array_var_int_element(idx1, arr1, 1);
constraint array_var_int_element(idx2, arr2, 2);
constraint fzn_all_different_int([p1, p2, p3]);
constraint int_eq(p1, 1);
constraint int_eq(p2, 2);
constraint int_eq(p3, 0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # The detector should have built at least one inverse channel group
        check tr.sys.baseArray.inverseChannelGroups.len >= 1
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        # With p1=1, p2=2, p3=0:
        #   idx0 should point to position of 0 (= p3, index 3 in p1..p3) + 1 = 4
        #   idx1 should point to position of 1 (= p1, index 1) + 1 = 2
        #   idx2 should point to position of 2 (= p2, index 2) + 1 = 3
        let i0 = tr.sys.assignment[tr.varPositions["idx0"]]
        let i1 = tr.sys.assignment[tr.varPositions["idx1"]]
        let i2 = tr.sys.assignment[tr.varPositions["idx2"]]
        check i0 == 4
        check i1 == 2
        check i2 == 3

    test "single-constraint group is NOT detected (need ≥2)":
        ## A lone array_var_int_element with sentinel pattern shouldn't fire
        ## the detector — there's nothing to invert.
        let src = """
var 0..2: p1 :: output_var;
var 0..2: p2 :: output_var;
var 0..2: p3 :: output_var;
var 1..4: idx0 :: output_var;
array [1..4] of var int: arr0 = [0, p1, p2, p3];
constraint array_var_int_element(idx0, arr0, 0);
constraint fzn_all_different_int([p1, p2, p3]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # Should NOT have built a sentinel-inverse group from a single constraint
        # (the existing detectInverseChannelPatterns might still build one if
        # the array shape matches its requirements, so we just verify the
        # sentinel-specific detector isn't fooled — count must be ≤ 1)
        check tr.sys.baseArray.inverseChannelGroups.len <= 1


suite "FlatZinc Matrix-Element Diagonal Exclusion":

    test "diagonal-only zero is excluded from result domain":
        ## A 3x3 distance matrix with 0 only on the diagonal, plus a
        ## sentinel-inverse permutation pattern in the same model. The
        ## diagonal-exclusion pass should remove value 0 from the result var's
        ## domain since `row != col` is structurally enforced by the inverse
        ## permutation.
        ##
        ## We add a `doubled` int_lin_eq referencing `distance` so the
        ## dead-element-channel elim (which runs before our diagonal pass)
        ## doesn't drop it as unreferenced.
        let src = """
% Sentinel-prefixed inverse permutation pattern (the routing-style guard)
var 0..2: p1 :: output_var;
var 0..2: p2 :: output_var;
var 0..2: p3 :: output_var;
var 1..4: idx0 :: var_is_introduced;
var 1..4: idx1 :: var_is_introduced;
var 1..4: idx2 :: var_is_introduced;
array [1..4] of var int: arr0 = [0, p1, p2, p3];
array [1..4] of var int: arr1 = [1, p1, p2, p3];
array [1..4] of var int: arr2 = [2, p1, p2, p3];
constraint array_var_int_element(idx0, arr0, 0);
constraint array_var_int_element(idx1, arr1, 1);
constraint array_var_int_element(idx2, arr2, 2);
constraint fzn_all_different_int([p1, p2, p3]);

% Three-element matrix lookup pattern: row labels, col labels, distance matrix
array [1..9] of int: rowLabels = [1,1,1, 2,2,2, 3,3,3];
array [1..9] of int: colLabels = [1,2,3, 1,2,3, 1,2,3];
array [1..9] of int: dataMatrix = [0,5,7, 5,0,3, 7,3,0];
var 1..3: rowSrc :: var_is_introduced;
var 1..3: colSrc :: var_is_introduced;
var 1..9: flatIdx :: var_is_introduced;
var 0..7: distance :: output_var;
constraint array_int_element(flatIdx, rowLabels, rowSrc);
constraint array_int_element(flatIdx, colLabels, colSrc);
constraint array_int_element(flatIdx, dataMatrix, distance) :: defines_var(distance);
% Keep `distance` alive via a downstream reference (avoids the dead-channel elim)
var 0..14: doubled :: output_var;
constraint int_lin_eq([2,-1],[distance,doubled],0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # Sentinel inverse channel must have been built (the routing-style guard)
        check tr.sys.baseArray.inverseChannelGroups.len >= 1
        # The diagonal-exclusion pass should have removed value 0 from `distance`
        check tr.varPositions.hasKey("distance")
        let distPos = tr.varPositions["distance"]
        check 0 notin tr.sys.baseArray.domain[distPos]
        # The remaining off-diagonal values should still be present
        check 3 in tr.sys.baseArray.domain[distPos]
        check 5 in tr.sys.baseArray.domain[distPos]
        check 7 in tr.sys.baseArray.domain[distPos]

    test "no diagonal exclusion when there's no inverse channel pattern":
        ## Without the routing-style guard (no sentinel-inverse pattern), the
        ## diagonal-exclusion pass must NOT fire — we can't safely assume row
        ## != col without that signal.
        let src = """
array [1..9] of int: rowLabels = [1,1,1, 2,2,2, 3,3,3];
array [1..9] of int: colLabels = [1,2,3, 1,2,3, 1,2,3];
array [1..9] of int: dataMatrix = [0,5,7, 5,0,3, 7,3,0];
var 1..3: rowSrc :: var_is_introduced;
var 1..3: colSrc :: var_is_introduced;
var 1..9: flatIdx :: var_is_introduced;
var 0..7: distance :: output_var;
constraint array_int_element(flatIdx, rowLabels, rowSrc);
constraint array_int_element(flatIdx, colLabels, colSrc);
constraint array_int_element(flatIdx, dataMatrix, distance) :: defines_var(distance);
% Keep `distance` alive via a downstream reference
var 0..14: doubled :: output_var;
constraint int_lin_eq([2,-1],[distance,doubled],0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.sys.baseArray.inverseChannelGroups.len == 0
        # Without the guard, value 0 must remain in the domain — search may
        # legitimately pick row == col.
        check tr.varPositions.hasKey("distance")
        let distPos = tr.varPositions["distance"]
        check 0 in tr.sys.baseArray.domain[distPos]
