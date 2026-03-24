## Tests for FlatZinc pattern detection logic in translator.nim.
## Covers detection procs that were previously untested:
##   detectCountPatterns, detectReifChannels (sub-patterns),
##   detectImplicationPatterns, detectDisjunctivePairs,
##   detectDisjunctiveResources, detectRedundantOrderings,
##   detectInversePatterns, detectInverseChannelPatterns,
##   tryTableFunctionalDep (generalized key column detection),
##   detectMaxFromLinLe, tightenDiffnTimeProfile.

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]
import crusher
import flatzinc/[parser, translator, output]

suite "FlatZinc Count Pattern Detection":

    test "detectCountPatterns: int_lin_eq → bool2int → int_eq_reif chain":
        ## Encodes count_eq(xs, 2) == target via the standard decomposition:
        ##   int_eq_reif(x_i, 2, b_i) :: defines_var(b_i)
        ##   bool2int(b_i, ind_i) :: defines_var(ind_i)
        ##   int_lin_eq([1,-1,-1,-1],[target,ind1,ind2,ind3,ind4],0)
        ## The detector should replace this with a single count_eq constraint.
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

        # Verify count_eq pattern was detected
        check tr.countEqPatterns.len == 1
        for _, pat in tr.countEqPatterns:
            check pat.countValue == 2
            check pat.targetVarName == "target"
            check pat.arrayVarNames.len == 4

        # Verify it solves correctly
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal == 2

        # Count how many x_i actually equal 2
        var count = 0
        for name in ["x1", "x2", "x3", "x4"]:
            if tr.sys.assignment[tr.varPositions[name]] == 2:
                inc count
        check count == 2

    test "detectCountPatterns: two count patterns for different values":
        ## Two count_eq patterns: count(xs, 1) == c1, count(xs, 3) == c3
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 0..3: c1 :: output_var;
var 0..3: c3 :: output_var;
var bool: b1a :: var_is_introduced :: is_defined_var;
var bool: b2a :: var_is_introduced :: is_defined_var;
var bool: b3a :: var_is_introduced :: is_defined_var;
var 0..1: i1a :: var_is_introduced :: is_defined_var;
var 0..1: i2a :: var_is_introduced :: is_defined_var;
var 0..1: i3a :: var_is_introduced :: is_defined_var;
var bool: b1b :: var_is_introduced :: is_defined_var;
var bool: b2b :: var_is_introduced :: is_defined_var;
var bool: b3b :: var_is_introduced :: is_defined_var;
var 0..1: i1b :: var_is_introduced :: is_defined_var;
var 0..1: i2b :: var_is_introduced :: is_defined_var;
var 0..1: i3b :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 1, b1a) :: defines_var(b1a);
constraint int_eq_reif(x2, 1, b2a) :: defines_var(b2a);
constraint int_eq_reif(x3, 1, b3a) :: defines_var(b3a);
constraint bool2int(b1a, i1a) :: defines_var(i1a);
constraint bool2int(b2a, i2a) :: defines_var(i2a);
constraint bool2int(b3a, i3a) :: defines_var(i3a);
constraint int_lin_eq([1,-1,-1,-1],[c1,i1a,i2a,i3a],0);
constraint int_eq_reif(x1, 3, b1b) :: defines_var(b1b);
constraint int_eq_reif(x2, 3, b2b) :: defines_var(b2b);
constraint int_eq_reif(x3, 3, b3b) :: defines_var(b3b);
constraint bool2int(b1b, i1b) :: defines_var(i1b);
constraint bool2int(b2b, i2b) :: defines_var(i2b);
constraint bool2int(b3b, i3b) :: defines_var(i3b);
constraint int_lin_eq([1,-1,-1,-1],[c3,i1b,i2b,i3b],0);
constraint int_eq(c1, 1);
constraint int_eq(c3, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Two count_eq patterns detected
        check tr.countEqPatterns.len == 2

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let c1Val = tr.sys.assignment[tr.varPositions["c1"]]
        let c3Val = tr.sys.assignment[tr.varPositions["c3"]]
        check c1Val == 1
        check c3Val == 1

        # With c1=1 and c3=1, exactly one x_i=1 and one x_i=3, so one x_i=2
        var vals: seq[int]
        for name in ["x1", "x2", "x3"]:
            vals.add(tr.sys.assignment[tr.varPositions[name]])
        vals.sort()
        check vals == @[1, 2, 3]

    test "detectCountPatterns: inverted coefficients [1,1,...,1,-1] — target last":
        ## MiniZinc 2.9.5 generates int_lin_eq([1,1,1,1,-1], [ind1,...,ind4, target], 0)
        ## instead of the original [1,-1,-1,-1,-1] pattern. Both mean target = sum(indicators).
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
constraint int_lin_eq([1,1,1,1,-1],[ind1,ind2,ind3,ind4,target],0);
constraint int_eq(target, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Verify count_eq pattern was detected with inverted coefficients
        check tr.countEqPatterns.len == 1
        for _, pat in tr.countEqPatterns:
            check pat.countValue == 2
            check pat.targetVarName == "target"
            check pat.arrayVarNames.len == 4

        # Verify it solves correctly
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal == 2

        var count = 0
        for name in ["x1", "x2", "x3", "x4"]:
            if tr.sys.assignment[tr.varPositions[name]] == 2:
                inc count
        check count == 2

    test "detectCountPatterns: bool vars shared with bool_clause constraints":
        ## Regression test: when the intermediate bool variables from the count_eq
        ## decomposition are also referenced by other constraints (e.g. bool_clause),
        ## the translator must NOT mark them as consumed/defined-only. They need
        ## channel positions so that bool_clause constraints can resolve them.
        ## Bug: "Unknown identifier 'b1' in expression" when bool_clause references
        ## a bool var that was consumed by count_eq pattern detection.
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 0..3: target :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
var 0..1: ind1 :: var_is_introduced :: is_defined_var;
var 0..1: ind2 :: var_is_introduced :: is_defined_var;
var 0..1: ind3 :: var_is_introduced :: is_defined_var;
var bool: other :: output_var;
constraint int_eq_reif(x1, 2, b1) :: defines_var(b1);
constraint int_eq_reif(x2, 2, b2) :: defines_var(b2);
constraint int_eq_reif(x3, 2, b3) :: defines_var(b3);
constraint bool2int(b1, ind1) :: defines_var(ind1);
constraint bool2int(b2, ind2) :: defines_var(ind2);
constraint bool2int(b3, ind3) :: defines_var(ind3);
constraint int_lin_eq([1,-1,-1,-1],[target,ind1,ind2,ind3],0);
constraint bool_clause([b1, other], []);
constraint bool_clause([b2], [other]);
constraint int_eq(target, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Count_eq pattern should still be detected
        check tr.countEqPatterns.len == 1
        for _, pat in tr.countEqPatterns:
            check pat.countValue == 2
            check pat.targetVarName == "target"
            check pat.arrayVarNames.len == 3

        # Bool vars must have positions (either channel or search) — not just defined
        check "b1" in tr.channelVarNames or "b1" in tr.varPositions
        check "b2" in tr.channelVarNames or "b2" in tr.varPositions

        # Must solve without crashing
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal == 2

    test "detectCountPatterns: balanced count pattern count(A) = count(B)":
        ## Two patterns:
        ##   int_lin_eq([1,1,1,1,-1], [ind_b1,...,ind_b4, target], 0) → count(x, 2) == target
        ##   int_lin_eq([1,1,1,1,-1,-1,-1,-1], [ind_b1,..., ind_w1,...], 0) → count(x, 2) == count(x, 3)
        ## The second should detect count(x, 3) == target via balanced pattern.
        let src = """
var 1..4: x1 :: output_var;
var 1..4: x2 :: output_var;
var 1..4: x3 :: output_var;
var 1..4: x4 :: output_var;
var 0..4: target :: output_var;
var bool: bb1 :: var_is_introduced :: is_defined_var;
var bool: bb2 :: var_is_introduced :: is_defined_var;
var bool: bb3 :: var_is_introduced :: is_defined_var;
var bool: bb4 :: var_is_introduced :: is_defined_var;
var 0..1: ib1 :: var_is_introduced :: is_defined_var;
var 0..1: ib2 :: var_is_introduced :: is_defined_var;
var 0..1: ib3 :: var_is_introduced :: is_defined_var;
var 0..1: ib4 :: var_is_introduced :: is_defined_var;
var bool: bw1 :: var_is_introduced :: is_defined_var;
var bool: bw2 :: var_is_introduced :: is_defined_var;
var bool: bw3 :: var_is_introduced :: is_defined_var;
var bool: bw4 :: var_is_introduced :: is_defined_var;
var 0..1: iw1 :: var_is_introduced :: is_defined_var;
var 0..1: iw2 :: var_is_introduced :: is_defined_var;
var 0..1: iw3 :: var_is_introduced :: is_defined_var;
var 0..1: iw4 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 2, bb1) :: defines_var(bb1);
constraint int_eq_reif(x2, 2, bb2) :: defines_var(bb2);
constraint int_eq_reif(x3, 2, bb3) :: defines_var(bb3);
constraint int_eq_reif(x4, 2, bb4) :: defines_var(bb4);
constraint bool2int(bb1, ib1) :: defines_var(ib1);
constraint bool2int(bb2, ib2) :: defines_var(ib2);
constraint bool2int(bb3, ib3) :: defines_var(ib3);
constraint bool2int(bb4, ib4) :: defines_var(ib4);
constraint int_lin_eq([1,1,1,1,-1],[ib1,ib2,ib3,ib4,target],0);
constraint int_eq_reif(x1, 3, bw1) :: defines_var(bw1);
constraint int_eq_reif(x2, 3, bw2) :: defines_var(bw2);
constraint int_eq_reif(x3, 3, bw3) :: defines_var(bw3);
constraint int_eq_reif(x4, 3, bw4) :: defines_var(bw4);
constraint bool2int(bw1, iw1) :: defines_var(iw1);
constraint bool2int(bw2, iw2) :: defines_var(iw2);
constraint bool2int(bw3, iw3) :: defines_var(iw3);
constraint bool2int(bw4, iw4) :: defines_var(iw4);
constraint int_lin_eq([1,1,1,1,-1,-1,-1,-1],[ib1,ib2,ib3,ib4,iw1,iw2,iw3,iw4],0);
constraint int_ge(target, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should detect two countEq patterns: value 2 (from inverted) and value 3 (from balanced)
        check tr.countEqPatterns.len == 2

        var foundVal2, foundVal3 = false
        for _, pat in tr.countEqPatterns:
            check pat.targetVarName == "target"
            check pat.arrayVarNames.len == 4
            if pat.countValue == 2: foundVal2 = true
            if pat.countValue == 3: foundVal3 = true
        check foundVal2
        check foundVal3

        # Verify it solves correctly: count(x, 2) == count(x, 3) == target >= 1
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal >= 1

        var countVal2, countVal3 = 0
        for name in ["x1", "x2", "x3", "x4"]:
            let v = tr.sys.assignment[tr.varPositions[name]]
            if v == 2: inc countVal2
            if v == 3: inc countVal3
        check countVal2 == targetVal
        check countVal3 == targetVal


suite "FlatZinc Reification Channel Detection":

    test "int_eq_reif channel with constant value":
        ## int_eq_reif(x, 2, b) :: defines_var(b) → b is a channel
        let src = """
var 1..3: x :: output_var;
var bool: b :: output_var;
constraint int_eq_reif(x, 2, b) :: defines_var(b);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check tr.reifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let xVal = tr.sys.assignment[tr.varPositions["x"]]
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check xVal == 2
        check bVal == 1  # b = (x == 2) = true = 1

    test "int_ne_reif channel":
        ## int_ne_reif(x, 2, b) :: defines_var(b) → b is a channel (b = x != 2)
        let src = """
var 1..3: x :: output_var;
var bool: b :: output_var;
constraint int_ne_reif(x, 2, b) :: defines_var(b);
constraint int_eq(x, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1  # b = (x != 2) = true = 1

    test "set_in_reif channel":
        ## set_in_reif(x, {2,4}, b) :: defines_var(b) → b is a channel
        let src = """
var 1..5: x :: output_var;
var bool: b :: output_var;
constraint set_in_reif(x, {2,4}, b) :: defines_var(b);
constraint int_eq(x, 4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check tr.setInReifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1  # 4 is in {2,4}

    test "set_in_reif channel — value not in set":
        let src = """
var 1..5: x :: output_var;
var bool: b :: output_var;
constraint set_in_reif(x, {2,4}, b) :: defines_var(b);
constraint int_eq(x, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 0  # 3 is not in {2,4}

    test "array_bool_and channel":
        ## array_bool_and([a,b], r) :: defines_var(r) → r is a channel
        let src = """
var bool: a :: output_var;
var bool: b :: output_var;
var bool: r :: output_var;
constraint array_bool_and([a,b], r) :: defines_var(r);
constraint int_eq(a, 1);
constraint int_eq(b, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "r" in tr.channelVarNames
        check tr.boolAndOrChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let rVal = tr.sys.assignment[tr.varPositions["r"]]
        check rVal == 1  # AND(true, true) = true

    test "array_bool_or channel":
        ## array_bool_or([a,b], r) :: defines_var(r) → r is a channel
        let src = """
var bool: a :: output_var;
var bool: b :: output_var;
var bool: r :: output_var;
constraint array_bool_or([a,b], r) :: defines_var(r);
constraint int_eq(a, 0);
constraint int_eq(b, 0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "r" in tr.channelVarNames
        check tr.boolAndOrChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let rVal = tr.sys.assignment[tr.varPositions["r"]]
        check rVal == 0  # OR(false, false) = false

    test "int_le_reif channel":
        ## int_le_reif(x, 3, b) :: defines_var(b) → b is a channel (b = x <= 3)
        let src = """
var 1..5: x :: output_var;
var bool: b :: output_var;
constraint int_le_reif(x, 3, b) :: defines_var(b);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check tr.leReifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1  # 2 <= 3 → true

    test "int_lt_reif channel":
        ## int_lt_reif(x, 3, b) :: defines_var(b) → b is a channel (b = x < 3)
        let src = """
var 1..5: x :: output_var;
var bool: b :: output_var;
constraint int_lt_reif(x, 3, b) :: defines_var(b);
constraint int_eq(x, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check tr.leReifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 0  # 3 < 3 is false

    test "int_lin_le_reif channel — binary":
        ## int_lin_le_reif([2,1], [x,y], 5, b) :: defines_var(b) → b = (2x+y <= 5)
        let src = """
var 1..5: x :: output_var;
var 1..5: y :: output_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_le_reif([2,1],[x,y],5,b) :: defines_var(b);
constraint int_eq(x, 1);
constraint int_eq(y, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check tr.linLeReifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1  # 2*1 + 2 = 4 <= 5 → true

    test "int_lin_le_reif channel — false case":
        ## int_lin_le_reif([3,1], [x,y], 5, b) :: defines_var(b) → b = (3x+y <= 5)
        let src = """
var 1..5: x :: output_var;
var 1..5: y :: output_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_le_reif([3,1],[x,y],5,b) :: defines_var(b);
constraint int_eq(x, 2);
constraint int_eq(y, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 0  # 3*2 + 3 = 9 > 5 → false

    test "int_lin_le_reif channel — with defined var inputs":
        ## Variables in the linear expression are defined vars (from int_lin_eq).
        ## b = (pad_xy_1 - pad_xy_2 <= 0) where pad_xy = 13*row + col
        let src = """
var 1..3: r1 :: output_var;
var 1..5: c1 :: output_var;
var 1..3: r2 :: output_var;
var 1..5: c2 :: output_var;
var int: pad1 :: is_defined_var;
var int: pad2 :: is_defined_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq([13,1,-1],[r1,c1,pad1],0) :: defines_var(pad1);
constraint int_lin_eq([13,1,-1],[r2,c2,pad2],0) :: defines_var(pad2);
constraint int_lin_le_reif([1,-1],[pad1,pad2],0,b) :: defines_var(b);
constraint int_eq(r1, 1);
constraint int_eq(c1, 2);
constraint int_eq(r2, 2);
constraint int_eq(c2, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check "pad1" in tr.definedVarNames
        check "pad2" in tr.definedVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        # pad1 = 13*1 + 2 = 15, pad2 = 13*2 + 1 = 27
        # 15 - 27 = -12 <= 0 → true
        check bVal == 1

    test "int_lin_eq_reif channel — true case":
        ## int_lin_eq_reif([2,1], [x,y], 4, b) :: defines_var(b) → b = (2x+y == 4)
        let src = """
var 1..5: x :: output_var;
var 1..5: y :: output_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq_reif([2,1],[x,y],4,b) :: defines_var(b);
constraint int_eq(x, 1);
constraint int_eq(y, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check tr.linEqReifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1  # 2*1 + 2 = 4 == 4 → true

    test "int_lin_eq_reif channel — false case":
        ## int_lin_eq_reif([3,1], [x,y], 5, b) :: defines_var(b) → b = (3x+y == 5)
        let src = """
var 1..5: x :: output_var;
var 1..5: y :: output_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq_reif([3,1],[x,y],5,b) :: defines_var(b);
constraint int_eq(x, 2);
constraint int_eq(y, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 0  # 3*2 + 3 = 9 != 5 → false

    test "int_lin_eq_reif channel — with defined var inputs":
        ## Variables in the linear expression are defined vars (from int_lin_eq).
        ## b = (pad1 - pad2 == 0) where pad = 13*row + col
        let src = """
var 1..3: r1 :: output_var;
var 1..5: c1 :: output_var;
var 1..3: r2 :: output_var;
var 1..5: c2 :: output_var;
var int: pad1 :: is_defined_var;
var int: pad2 :: is_defined_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq([13,1,-1],[r1,c1,pad1],0) :: defines_var(pad1);
constraint int_lin_eq([13,1,-1],[r2,c2,pad2],0) :: defines_var(pad2);
constraint int_lin_eq_reif([1,-1],[pad1,pad2],0,b) :: defines_var(b);
constraint int_eq(r1, 2);
constraint int_eq(c1, 3);
constraint int_eq(r2, 2);
constraint int_eq(c2, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames
        check "pad1" in tr.definedVarNames
        check "pad2" in tr.definedVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        # pad1 = 13*2 + 3 = 29, pad2 = 13*2 + 3 = 29
        # 29 - 29 = 0 == 0 → true
        check bVal == 1

    test "int_lin_eq_reif channel — with defined var inputs (false)":
        ## b = (pad1 - pad2 == 0) where pads differ
        let src = """
var 1..3: r1 :: output_var;
var 1..5: c1 :: output_var;
var 1..3: r2 :: output_var;
var 1..5: c2 :: output_var;
var int: pad1 :: is_defined_var;
var int: pad2 :: is_defined_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq([13,1,-1],[r1,c1,pad1],0) :: defines_var(pad1);
constraint int_lin_eq([13,1,-1],[r2,c2,pad2],0) :: defines_var(pad2);
constraint int_lin_eq_reif([1,-1],[pad1,pad2],0,b) :: defines_var(b);
constraint int_eq(r1, 1);
constraint int_eq(c1, 2);
constraint int_eq(r2, 2);
constraint int_eq(c2, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        # pad1 = 13*1 + 2 = 15, pad2 = 13*2 + 1 = 27
        # 15 - 27 = -12 != 0 → false
        check bVal == 0

    test "bool_clause_reif channel":
        ## bool_clause_reif([a], [b], r) :: defines_var(r) → r is a channel (r = a OR NOT b)
        let src = """
var bool: a :: output_var;
var bool: b :: output_var;
var bool: r :: output_var;
constraint bool_clause_reif([a], [b], r) :: defines_var(r);
constraint int_eq(a, 0);
constraint int_eq(b, 0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "r" in tr.channelVarNames
        check tr.boolClauseReifChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let rVal = tr.sys.assignment[tr.varPositions["r"]]
        check rVal == 1  # (false) OR (NOT false) = true

    test "int_eq_reif 2D channel — two variables":
        ## int_eq_reif(x, y, b) :: defines_var(b) with variable y → 2D table channel
        let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: output_var;
constraint int_eq_reif(x, y, b) :: defines_var(b);
constraint int_eq(x, 2);
constraint int_eq(y, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1  # x == y → true


suite "FlatZinc Implication Pattern Detection":

    test "ne_reif + eq_reif complete case → detected by case-analysis":
        ## Complete implications (x==1→y==2, x==2→y==3, x==3→y==1) are handled
        ## by detectCaseAnalysisChannels (runs first), which converts y to a channel.
        ## This verifies case-analysis handles the complete implication table correctly.
        let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: ne1 :: var_is_introduced :: is_defined_var;
var bool: eq1 :: var_is_introduced :: is_defined_var;
var bool: ne2 :: var_is_introduced :: is_defined_var;
var bool: eq2 :: var_is_introduced :: is_defined_var;
var bool: ne3 :: var_is_introduced :: is_defined_var;
var bool: eq3 :: var_is_introduced :: is_defined_var;
constraint int_ne_reif(x, 1, ne1) :: defines_var(ne1);
constraint int_eq_reif(y, 2, eq1) :: defines_var(eq1);
constraint bool_clause([ne1, eq1], []);
constraint int_ne_reif(x, 2, ne2) :: defines_var(ne2);
constraint int_eq_reif(y, 3, eq2) :: defines_var(eq2);
constraint bool_clause([ne2, eq2], []);
constraint int_ne_reif(x, 3, ne3) :: defines_var(ne3);
constraint int_eq_reif(y, 1, eq3) :: defines_var(eq3);
constraint bool_clause([ne3, eq3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Case-analysis detects the complete mapping x→y and channels y
        check tr.caseAnalysisDefs.len == 1
        check "y" in tr.channelVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let xVal = tr.sys.assignment[tr.varPositions["x"]]
        let yVal = tr.sys.assignment[tr.varPositions["y"]]

        # Verify the mapping holds
        case xVal
        of 1: check yVal == 2
        of 2: check yVal == 3
        of 3: check yVal == 1
        else: check false

    test "detectImplicationPatterns: one-hot channel detection":
        ## Pattern: two int_eq_reif constraints sharing the same result bool ch:
        ##   int_eq_reif(bV, 1, ch) :: defines_var(ch)  -- ch = (bV == 1)
        ##   int_eq_reif(intVar, v, ch)                  -- ch = (intVar == v)
        ## Combined: bV ↔ (intVar == v), so bV becomes a one-hot channel.
        let src = """
var 1..3: x :: output_var;
var bool: bv :: output_var;
var bool: ch :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(bv, 1, ch) :: defines_var(ch);
constraint int_eq_reif(x, 2, ch);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # bv should be detected as one-hot channel: bv = (x == 2)
        check tr.oneHotChannelDefs.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bvVal = tr.sys.assignment[tr.varPositions["bv"]]
        check bvVal == 1  # x==2, so bv = (x==2) = 1

    test "detectImplicationPatterns: constant-zero channel":
        ## int_eq_reif(bVar, 1, false) means bVar can never be 1.
        ## Since bVar is bool (domain {0,1}), it's always 0 → constant-zero channel.
        let src = """
var bool: bv :: output_var;
constraint int_eq_reif(bv, 1, false);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.constantZeroChannels.len >= 1
        check "bv" in tr.channelVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bvVal = tr.sys.assignment[tr.varPositions["bv"]]
        check bvVal == 0


suite "FlatZinc Disjunctive Pair Detection":

    test "detectDisjunctivePairs: basic two-task disjunction":
        ## Encodes: (b >= a+3) OR (a >= b+5) — tasks a and b don't overlap
        ## via int_lin_le_reif + bool_clause
        let src = """
var 1..20: a :: output_var;
var 1..20: b :: output_var;
var bool: d1 :: var_is_introduced :: is_defined_var;
var bool: d2 :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[a,b],-3,d1) :: defines_var(d1);
constraint int_lin_le_reif([-1,1],[a,b],-5,d2) :: defines_var(d2);
constraint bool_clause([d1,d2],[]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctivePairs.len == 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let aVal = tr.sys.assignment[tr.varPositions["a"]]
        let bVal = tr.sys.assignment[tr.varPositions["b"]]

        # Either b >= a+3 or a >= b+5
        check (bVal >= aVal + 3 or aVal >= bVal + 5)

    test "detectDisjunctiveResources: three-task clique → cumulative":
        ## Three tasks with pairwise disjunctive constraints forming a complete graph.
        ## Tasks: a (dur=3), b (dur=5), c (dur=4).
        ## Should be detected as one resource group.
        let src = """
var 1..30: a :: output_var;
var 1..30: b :: output_var;
var 1..30: c :: output_var;
var bool: d_ab1 :: var_is_introduced :: is_defined_var;
var bool: d_ab2 :: var_is_introduced :: is_defined_var;
var bool: d_ac1 :: var_is_introduced :: is_defined_var;
var bool: d_ac2 :: var_is_introduced :: is_defined_var;
var bool: d_bc1 :: var_is_introduced :: is_defined_var;
var bool: d_bc2 :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[a,b],-3,d_ab1) :: defines_var(d_ab1);
constraint int_lin_le_reif([-1,1],[a,b],-5,d_ab2) :: defines_var(d_ab2);
constraint bool_clause([d_ab1,d_ab2],[]);
constraint int_lin_le_reif([1,-1],[a,c],-3,d_ac1) :: defines_var(d_ac1);
constraint int_lin_le_reif([-1,1],[a,c],-4,d_ac2) :: defines_var(d_ac2);
constraint bool_clause([d_ac1,d_ac2],[]);
constraint int_lin_le_reif([1,-1],[b,c],-5,d_bc1) :: defines_var(d_bc1);
constraint int_lin_le_reif([-1,1],[b,c],-4,d_bc2) :: defines_var(d_bc2);
constraint bool_clause([d_bc1,d_bc2],[]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # 3 disjunctive pairs detected
        check tr.disjunctivePairs.len == 3
        # Should form 1 resource group (clique of 3 tasks)
        check tr.disjunctiveResourceGroups.len == 1
        check tr.disjunctiveResourceGroups[0].varNames.len == 3

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let aVal = tr.sys.assignment[tr.varPositions["a"]]
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        let cVal = tr.sys.assignment[tr.varPositions["c"]]

        # All pairwise disjunctions must hold
        check (bVal >= aVal + 3 or aVal >= bVal + 5)
        check (cVal >= aVal + 3 or aVal >= cVal + 4)
        check (cVal >= bVal + 5 or bVal >= cVal + 4)


suite "FlatZinc Redundant Ordering Detection":

    test "detectRedundantOrderings: transitively implied constraint removed":
        ## Three ordering constraints using int_lin_le([1,-1],[a,b],rhs) → a-b<=rhs → b>=a+(-rhs):
        ##   b >= a + 2: int_lin_le([1,-1],[a,b],-2)
        ##   c >= b + 3: int_lin_le([1,-1],[b,c],-3)
        ##   c >= a + 4: int_lin_le([1,-1],[a,c],-4) — redundant: path gives c >= a+5
        let src = """
var 1..20: a :: output_var;
var 1..20: b :: output_var;
var 1..20: c :: output_var;
constraint int_lin_le([1,-1],[a,b],-2);
constraint int_lin_le([1,-1],[b,c],-3);
constraint int_lin_le([1,-1],[a,c],-4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # The third constraint (c >= a+4) should be marked redundant
        check tr.redundantOrderings.len == 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let aVal = tr.sys.assignment[tr.varPositions["a"]]
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        let cVal = tr.sys.assignment[tr.varPositions["c"]]

        check bVal >= aVal + 2
        check cVal >= bVal + 3
        check cVal >= aVal + 4  # implied

    test "detectRedundantOrderings: non-redundant constraint preserved":
        ## Two orderings that don't form a transitive chain:
        ##   b >= a + 2
        ##   c >= a + 10
        ## Neither is implied by the other.
        let src = """
var 1..20: a :: output_var;
var 1..20: b :: output_var;
var 1..20: c :: output_var;
constraint int_lin_le([1,-1],[a,b],-2);
constraint int_lin_le([1,-1],[a,c],-10);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Neither constraint is redundant
        check tr.redundantOrderings.len == 0

    test "detectRedundantOrderings: stronger direct edge not redundant":
        ## Three orderings where the direct edge is stronger than the transitive path:
        ##   b >= a + 2
        ##   c >= b + 3
        ##   c >= a + 10 (NOT redundant: transitive gives c >= a+5, but direct says c >= a+10)
        let src = """
var 1..20: a :: output_var;
var 1..20: b :: output_var;
var 1..20: c :: output_var;
constraint int_lin_le([1,-1],[a,b],-2);
constraint int_lin_le([1,-1],[b,c],-3);
constraint int_lin_le([1,-1],[a,c],-10);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # The direct edge (c >= a+10) is NOT redundant (stronger than transitive a+5)
        check tr.redundantOrderings.len == 0


suite "FlatZinc Inverse Pattern Detection":

    test "detectInversePatterns: involution A[A[i]] = i":
        ## Three array_var_int_element constraints encoding A[A[i]]=i.
        ## Valid involutions of {1,2,3}: identity, swap(1,2), swap(1,3), swap(2,3).
        let src = """
var 1..3: a1 :: output_var;
var 1..3: a2 :: output_var;
var 1..3: a3 :: output_var;
array [1..3] of var int: A :: output_array([1..3]) = [a1,a2,a3];
constraint array_var_int_element(a1, A, 1);
constraint array_var_int_element(a2, A, 2);
constraint array_var_int_element(a3, A, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # All 3 element constraints should be consumed (involution detected)
        # Check the inverse group was registered
        check tr.sys.baseArray.inverseGroups.len >= 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let a1 = tr.sys.assignment[tr.varPositions["a1"]]
        let a2 = tr.sys.assignment[tr.varPositions["a2"]]
        let a3 = tr.sys.assignment[tr.varPositions["a3"]]
        let arr = [a1, a2, a3]

        # Verify involution: A[A[i]] = i for all i
        check arr[arr[0] - 1] == 1
        check arr[arr[1] - 1] == 2
        check arr[arr[2] - 1] == 3

    test "detectInverseChannelPatterns: inverse channel A[idx_p] = p":
        ## Three index variables map to positions in array A.
        ## A[idx_p] = p means A is the inverse permutation of idx.
        let src = """
var 1..3: idx1 :: output_var;
var 1..3: idx2 :: output_var;
var 1..3: idx3 :: output_var;
var 0..3: a1;
var 0..3: a2;
var 0..3: a3;
array [1..3] of var int: A :: output_array([1..3]) = [a1,a2,a3];
constraint array_var_int_element(idx1, A, 1);
constraint array_var_int_element(idx2, A, 2);
constraint array_var_int_element(idx3, A, 3);
constraint fzn_all_different_int([idx1, idx2, idx3]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Inverse channel pattern should be detected
        check tr.inverseChannelPatterns.len == 1
        check tr.inverseChannelPatterns[0].indexVarNames.len == 3

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let idx1 = tr.sys.assignment[tr.varPositions["idx1"]]
        let idx2 = tr.sys.assignment[tr.varPositions["idx2"]]
        let idx3 = tr.sys.assignment[tr.varPositions["idx3"]]

        # All idx values must be distinct (all_different)
        check idx1 != idx2
        check idx1 != idx3
        check idx2 != idx3

        # A[idx_p] = p: verify inverse relationship
        let positions = tr.arrayPositions["A"]
        let a = @[tr.sys.assignment[positions[0]],
                  tr.sys.assignment[positions[1]],
                  tr.sys.assignment[positions[2]]]
        check a[idx1 - 1] == 1
        check a[idx2 - 1] == 2
        check a[idx3 - 1] == 3


suite "Table Functional Dependency Detection":

    test "col0 as key (existing behavior)":
        ## Standard case: col0 uniquely determines col1.
        ## table([x, y], [[1,10],[2,20],[3,30]]) → y = channel(x)
        let src = """
var 1..3: x :: output_var;
var 10..30: y :: output_var;
array [1..6] of int: t = [1,10, 2,20, 3,30];
constraint fzn_table_int([x, y], t);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # y should become a channel or be domain-reduced (presolve may fix x first)
        check tr.sys.baseArray.constraints.len <= 2
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let yVal = tr.sys.assignment[tr.varPositions["y"]]
        check yVal == 20  # x=2 → y=20

    test "last column as key (WCSP unary pattern)":
        ## WCSP unary cost table: [cost, p_val] where p_val (col1) is the unique key.
        ## The key is NOT col0. The generalized detection must find col1 as key.
        let src = """
var 0..100: cost :: output_var;
var 1..4: p :: output_var;
array [1..8] of int: t = [10,1, 20,2, 30,3, 40,4];
constraint fzn_table_int([cost, p], t);
constraint int_eq(p, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # cost should become a channel or be domain-reduced (presolve may fix p first)
        check tr.sys.baseArray.constraints.len <= 2
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let costVal = tr.sys.assignment[tr.varPositions["cost"]]
        check costVal == 30  # p=3 → cost=30

    test "composite key in last columns (WCSP binary pattern)":
        ## WCSP binary cost table: [cost, p_x, p_y] where (col1, col2) is the key.
        ## Neither col0 nor (col0, col1) works as key — must try (col1, col2).
        let src = """
var 0..100: cost :: output_var;
var 1..2: px :: output_var;
var 1..2: py :: output_var;
array [1..12] of int: t = [10,1,1, 20,1,2, 30,2,1, 40,2,2];
constraint fzn_table_int([cost, px, py], t);
constraint int_eq(px, 2);
constraint int_eq(py, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # cost should become a channel or be domain-reduced (presolve may fix px,py first)
        check tr.sys.baseArray.constraints.len <= 3
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let costVal = tr.sys.assignment[tr.varPositions["cost"]]
        check costVal == 30  # px=2, py=1 → cost=30

    test "WCSP pattern: multiple cost channels from tables":
        ## Mini WCSP: 2 decision vars, 2 unary costs + 1 binary cost.
        ## All cost vars should become channels via generalized key detection.
        let src = """
var 1..3: p1 :: output_var;
var 1..3: p2 :: output_var;
var 0..100: ucost1 :: output_var;
var 0..100: ucost2 :: output_var;
var 0..100: bcost :: output_var;
array [1..6] of int: ut1 = [5,1, 3,2, 8,3];
constraint fzn_table_int([ucost1, p1], ut1);
array [1..6] of int: ut2 = [7,1, 2,2, 6,3];
constraint fzn_table_int([ucost2, p2], ut2);
array [1..27] of int: bt = [10,1,1, 1,1,2, 9,1,3, 8,2,1, 4,2,2, 7,2,3, 6,3,1, 3,3,2, 2,3,3];
constraint fzn_table_int([bcost, p1, p2], bt);
constraint int_eq(p1, 1);
constraint int_eq(p2, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # All 3 cost vars should be channels or domain-reduced (presolve may fix p1,p2 first)
        tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)
        let ucost1 = tr.sys.assignment[tr.varPositions["ucost1"]]
        let ucost2 = tr.sys.assignment[tr.varPositions["ucost2"]]
        let bcost = tr.sys.assignment[tr.varPositions["bcost"]]

        # p1=1, p2=2: ucost1=5, ucost2=2, bcost=1
        check ucost1 == 5
        check ucost2 == 2
        check bcost == 1

suite "FlatZinc Argmax Pattern Detection":

    test "detectArgmaxPattern: 3-signal argmax → element constraint":
        ## Encodes tower = argmax([s1, s2, s3]) via MiniZinc's decomposition:
        ##   int_ne_reif(tower, t, ne_t) :: defines_var(ne_t)  for t = 1..3
        ##   int_lin_le_reif([1, -1], [s_t, max_s], 0, ne_t)  for t = 1..3
        ##   array_int_maximum(max_s, [s1, s2, s3]) :: defines_var(max_s)
        ## The detector should replace this with: s[tower-1] == max_s (element constraint).
        let src = """
var 1..3: tower :: output_var;
var 1..10: s1 :: output_var;
var 1..10: s2 :: output_var;
var 1..10: s3 :: output_var;
var 1..10: max_s :: var_is_introduced :: is_defined_var;
var bool: ne1 :: var_is_introduced :: is_defined_var;
var bool: ne2 :: var_is_introduced :: is_defined_var;
var bool: ne3 :: var_is_introduced :: is_defined_var;
constraint int_ne_reif(tower, 1, ne1) :: defines_var(ne1);
constraint int_ne_reif(tower, 2, ne2) :: defines_var(ne2);
constraint int_ne_reif(tower, 3, ne3) :: defines_var(ne3);
constraint int_lin_le_reif([1, -1], [s1, max_s], 0, ne1);
constraint int_lin_le_reif([1, -1], [s2, max_s], 0, ne2);
constraint int_lin_le_reif([1, -1], [s3, max_s], 0, ne3);
constraint array_int_maximum(max_s, [s1, s2, s3]) :: defines_var(max_s);
constraint int_eq(s1, 3);
constraint int_eq(s2, 7);
constraint int_eq(s3, 5);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Verify argmax pattern was detected
        check tr.argmaxPatterns.len == 1
        for _, pat in tr.argmaxPatterns:
            check pat.towerVarName == "tower"
            check pat.maxVarName == "max_s"
            check pat.signalVarNames == @["s1", "s2", "s3"]

        # ne_vars should be removed from channelVarNames (dead channels)
        check "ne1" notin tr.channelVarNames
        check "ne2" notin tr.channelVarNames
        check "ne3" notin tr.channelVarNames

        # max_s should remain a channel (array_int_maximum is NOT consumed)
        check "max_s" in tr.channelVarNames

        # Solve and verify: s2=7 is the max, so tower should be 2
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let towerVal = tr.sys.assignment[tr.varPositions["tower"]]
        check towerVal == 2
        let maxVal = tr.sys.assignment[tr.varPositions["max_s"]]
        check maxVal == 7

    test "detectArgmaxPattern: non-contiguous tower values are not matched":
        ## If the ne_reif constants are not contiguous (e.g., 1, 3, 5), the pattern
        ## should NOT be detected.
        let src = """
var 1..5: tower :: output_var;
var 1..10: s1 :: output_var;
var 1..10: s2 :: output_var;
var 1..10: s3 :: output_var;
var 1..10: max_s :: var_is_introduced :: is_defined_var;
var bool: ne1 :: var_is_introduced :: is_defined_var;
var bool: ne3 :: var_is_introduced :: is_defined_var;
var bool: ne5 :: var_is_introduced :: is_defined_var;
constraint int_ne_reif(tower, 1, ne1) :: defines_var(ne1);
constraint int_ne_reif(tower, 3, ne3) :: defines_var(ne3);
constraint int_ne_reif(tower, 5, ne5) :: defines_var(ne5);
constraint int_lin_le_reif([1, -1], [s1, max_s], 0, ne1);
constraint int_lin_le_reif([1, -1], [s2, max_s], 0, ne3);
constraint int_lin_le_reif([1, -1], [s3, max_s], 0, ne5);
constraint array_int_maximum(max_s, [s1, s2, s3]) :: defines_var(max_s);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Non-contiguous values: pattern should NOT be detected
        check tr.argmaxPatterns.len == 0

    test "detectArgmaxPattern: incomplete group (missing lin_le_reif) not matched":
        ## If one of the ne_reif booleans has no matching int_lin_le_reif, the
        ## entire group should be skipped.
        let src = """
var 1..3: tower :: output_var;
var 1..10: s1 :: output_var;
var 1..10: s2 :: output_var;
var 1..10: s3 :: output_var;
var 1..10: max_s :: var_is_introduced :: is_defined_var;
var bool: ne1 :: var_is_introduced :: is_defined_var;
var bool: ne2 :: var_is_introduced :: is_defined_var;
var bool: ne3 :: var_is_introduced :: is_defined_var;
constraint int_ne_reif(tower, 1, ne1) :: defines_var(ne1);
constraint int_ne_reif(tower, 2, ne2) :: defines_var(ne2);
constraint int_ne_reif(tower, 3, ne3) :: defines_var(ne3);
constraint int_lin_le_reif([1, -1], [s1, max_s], 0, ne1);
constraint int_lin_le_reif([1, -1], [s3, max_s], 0, ne3);
constraint array_int_maximum(max_s, [s1, s2, s3]) :: defines_var(max_s);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Missing ne2's lin_le_reif → pattern should NOT be detected
        check tr.argmaxPatterns.len == 0

suite "FlatZinc Max-from-LinLe Detection":

    test "detectMaxFromLinLe: basic D = max(y_i + offset_i) pattern":
        ## 4 constraints: int_lin_le([1,-1], [y_i, D], -offset_i)
        ## encode D >= y_i + offset_i. With minimize objective = D,
        ## D becomes a max channel = max(y1+3, y2+2, y3+4, y4+1).
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..20: y4 :: output_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint int_lin_le([1,-1],[y4,D],-1);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
constraint int_eq(y1, 5);
constraint int_eq(y2, 10);
constraint int_eq(y3, 3);
constraint int_eq(y4, 15);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # D should be detected as a max channel
        check tr.maxFromLinLeDefs.len == 1
        check tr.maxFromLinLeDefs[0].ceilingVarName == "D"
        check tr.maxFromLinLeDefs[0].sourceVarNames.len == 4
        check "D" in tr.channelVarNames
        # D should NOT be in definedVarNames (needs a position for channel binding)
        check "D" notin tr.definedVarNames

        # The 4 int_lin_le constraints should be consumed
        for ci in tr.maxFromLinLeDefs[0].consumedCIs:
            check ci in tr.definingConstraints

        # Solve and verify: D = max(5+3, 10+2, 3+4, 15+1) = max(8,12,7,16) = 16
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let dVal = tr.sys.assignment[tr.varPositions["D"]]
        check dVal == 16

    test "detectMaxFromLinLe: reversed coefficient order [−1, 1]":
        ## Same pattern but with coefficients [-1, 1] instead of [1, -1].
        ## int_lin_le([-1,1], [D, y_i], -offset_i) → -D + y_i <= -offset → D >= y_i + offset
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([-1,1],[D,y1],-3);
constraint int_lin_le([-1,1],[D,y2],-5);
constraint int_lin_le([-1,1],[D,y3],-2);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
constraint int_eq(y1, 4);
constraint int_eq(y2, 6);
constraint int_eq(y3, 10);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 1
        check tr.maxFromLinLeDefs[0].ceilingVarName == "D"

        # D = max(4+3, 6+5, 10+2) = max(7, 11, 12) = 12
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let dVal = tr.sys.assignment[tr.varPositions["D"]]
        check dVal == 12

    test "detectMaxFromLinLe: detected for satisfy problems":
        ## Satisfy has no objective preference, so ceiling is safe to channel.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 1
        check "D" in tr.channelVarNames

    test "detectMaxFromLinLe: detected when ceiling is not in objective":
        ## D does not appear in the objective at all — only Z does.
        ## D is not forced-large, so it's safe to channel as max.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var 1..50: Z :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint int_lin_eq([1,-1],[objective,Z],0) :: defines_var(objective);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 1
        check "D" in tr.channelVarNames

    test "detectMaxFromLinLe: group too small (2 constraints) is not detected":
        ## Need at least 3 int_lin_le constraints to qualify.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 0

    test "detectMaxFromLinLe: multi-component objective":
        ## objective = D + S where both D and S are minimized.
        ## Only D has the int_lin_le pattern; S is just a plain variable.
        ## D should be detected, S should not.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var 1..50: S :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint int_lin_eq([1,-1,-1],[objective,D,S],0) :: defines_var(objective);
constraint int_eq(y1, 5);
constraint int_eq(y2, 10);
constraint int_eq(y3, 3);
constraint int_eq(S, 7);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 1
        check tr.maxFromLinLeDefs[0].ceilingVarName == "D"
        check "D" in tr.channelVarNames
        # S should not be a max-from-lin-le channel (it may be a presolve-fixed channel)
        check "S" notin tr.maxFromLinLeDefs[0].sourceVarNames

        # D = max(5+3, 10+2, 3+4) = 12, objective = D + S = 12 + 7 = 19
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let dVal = tr.sys.assignment[tr.varPositions["D"]]
        check dVal == 12

    test "detectMaxFromLinLe: zero offset handled correctly":
        ## int_lin_le([1,-1], [y_i, D], 0) → D >= y_i (offset = 0)
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],0);
constraint int_lin_le([1,-1],[y2,D],0);
constraint int_lin_le([1,-1],[y3,D],0);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
constraint int_eq(y1, 5);
constraint int_eq(y2, 10);
constraint int_eq(y3, 3);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 1
        # All offsets should be 0
        for o in tr.maxFromLinLeDefs[0].offsets:
            check o == 0

        # D = max(5, 10, 3) = 10
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let dVal = tr.sys.assignment[tr.varPositions["D"]]
        check dVal == 10

    test "detectMaxFromLinLe: source variables are defined vars (regression 361662f)":
        ## When source variables in the max-from-lin-le pattern are defined vars
        ## (not search vars), emitMaxFromLinLeChannels must resolve them via
        ## definedVarExprs. This requires buildDefinedExpressions to run first.
        ## Before the fix, emitMaxFromLinLeChannels ran before buildDefinedExpressions,
        ## causing a KeyError when resolving the defined source variables.
        let src = """
var 1..10: x1 :: output_var;
var 1..10: x2 :: output_var;
var 1..10: x3 :: output_var;
var int: s1 :: is_defined_var;
var int: s2 :: is_defined_var;
var int: s3 :: is_defined_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_eq([2,-1],[x1,s1],-1) :: defines_var(s1);
constraint int_lin_eq([3,-1],[x2,s2],0) :: defines_var(s2);
constraint int_lin_eq([1,-1],[x3,s3],-5) :: defines_var(s3);
constraint int_lin_le([1,-1],[s1,D],0);
constraint int_lin_le([1,-1],[s2,D],0);
constraint int_lin_le([1,-1],[s3,D],0);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
constraint int_eq(x1, 5);
constraint int_eq(x2, 4);
constraint int_eq(x3, 8);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Pattern should be detected with defined source vars
        check tr.maxFromLinLeDefs.len == 1
        check tr.maxFromLinLeDefs[0].ceilingVarName == "D"

        # s1, s2, s3 should be defined (not search) variables
        check "s1" in tr.definedVarNames
        check "s2" in tr.definedVarNames
        check "s3" in tr.definedVarNames

        # s1=2*5+1=11, s2=3*4=12, s3=8+5=13 → D = max(11,12,13) = 13
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let dVal = tr.sys.assignment[tr.varPositions["D"]]
        check dVal == 13

    test "detectMaxFromLinLe: not detected when ceiling is forced-large in minimize":
        ## objective = Z - D, so minimizing wants D large (same-sign coeff as objective).
        ## Max channel would force D to minimum feasible, fighting the objective.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var 1..50: Z :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint int_lin_eq([1,1,-1],[objective,D,Z],0) :: defines_var(objective);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # D has same-sign coeff as objective → forced-large → not detected
        check tr.maxFromLinLeDefs.len == 0
        check "D" notin tr.channelVarNames

    test "detectMaxFromLinLe: not detected when ceiling is forced-large in maximize":
        ## objective = D + Z, maximizing wants D large (opposite-sign coeff to objective).
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var 1..50: Z :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint int_lin_eq([1,-1,-1],[objective,D,Z],0) :: defines_var(objective);
solve maximize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # D has opposite-sign coeff to objective in maximize → forced-large → not detected
        check tr.maxFromLinLeDefs.len == 0
        check "D" notin tr.channelVarNames

    test "detectMaxFromLinLe: not detected when ceiling is already a defined var":
        ## D is defined by int_lin_eq with defines_var → already has a defining expression.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..20: x :: output_var;
var 1..50: D :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint int_lin_eq([2,-1],[x,D],0) :: defines_var(D);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 0
        check "D" in tr.definedVarNames

suite "FlatZinc Diffn Time Profile Tightening":

    test "tightenDiffnTimeProfile: constant x/dx/dy tightens ceiling domain":
        ## 3 rectangles with constant x, dx, dy placed at x=0..9:
        ##   rect 0: x=0, dx=5, dy=3  (covers x=[0,5), contributes 3 to load)
        ##   rect 1: x=3, dx=4, dy=2  (covers x=[3,7), contributes 2 to load)
        ##   rect 2: x=6, dx=4, dy=4  (covers x=[6,10), contributes 4 to load)
        ## Time profile: at x=3..5 load=5 (rects 0+1), at x=6..7 load=6 (rects 1+2)
        ## max_load = 6. So D (ceiling) domain should be tightened to >= 6.
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint fzn_diffn([0,3,6],[y1,y2,y3],[5,4,4],[3,2,4]);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # D should be a max channel
        check tr.maxFromLinLeDefs.len == 1
        check "D" in tr.channelVarNames

        # D's domain should be tightened: values < 6 removed
        let dPos = tr.varPositions["D"]
        let dDom = tr.sys.baseArray.domain[dPos]
        check dDom[0] >= 6  # first value in domain is at least 6

    test "tightenDiffnTimeProfile: no tightening without max-from-lin-le":
        ## If there's no max-from-lin-le pattern, tightenDiffnTimeProfile
        ## should not crash or modify anything (satisfy problem).
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
constraint fzn_diffn([0,3],[y1,y2],[5,4],[3,2]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.maxFromLinLeDefs.len == 0
        # Should solve without errors
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    test "tightenDiffnTimeProfile: non-constant x/dx skipped":
        ## When x or dx are variables (not constants), the time profile
        ## tightening should be skipped (only applies to all-constant cases).
        let src = """
var 1..20: y1 :: output_var;
var 1..20: y2 :: output_var;
var 1..20: y3 :: output_var;
var 1..20: x1 :: output_var;
var 1..50: D :: output_var;
var int: objective :: is_defined_var;
constraint int_lin_le([1,-1],[y1,D],-3);
constraint int_lin_le([1,-1],[y2,D],-2);
constraint int_lin_le([1,-1],[y3,D],-4);
constraint fzn_diffn([x1,3,6],[y1,y2,y3],[5,4,4],[3,2,4]);
constraint int_lin_eq([1,-1],[objective,D],0) :: defines_var(objective);
solve minimize objective;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # D is still a max channel (from int_lin_le pattern)
        check tr.maxFromLinLeDefs.len == 1
        # Domain is NOT tightened by diffn time profile (x1 is variable),
        # but IS tightened by max channel bounds: D >= max(min(y_i) + offset_i) = max(1+3,1+2,1+4) = 5
        let dPos = tr.varPositions["D"]
        let dDom = tr.sys.baseArray.domain[dPos]
        check dDom[0] == 5  # tightened by source lower bounds, not by diffn time profile

suite "FlatZinc int_lin_le_reif Multi-Position Bounds":

    test "int_lin_le_reif channel — 3-position defined var input":
        ## b = (pad1 - pad2 <= 0) where pad = 7*r + 3*c + z
        ## pad has 3 positions (r, c, z). The bounds computation must
        ## linearize the multi-position expression correctly.
        let src = """
var 1..3: r1 :: output_var;
var 1..5: c1 :: output_var;
var 1..2: z1 :: output_var;
var 1..3: r2 :: output_var;
var 1..5: c2 :: output_var;
var 1..2: z2 :: output_var;
var int: pad1 :: is_defined_var;
var int: pad2 :: is_defined_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq([7,3,1,-1],[r1,c1,z1,pad1],0) :: defines_var(pad1);
constraint int_lin_eq([7,3,1,-1],[r2,c2,z2,pad2],0) :: defines_var(pad2);
constraint int_lin_le_reif([1,-1],[pad1,pad2],0,b) :: defines_var(b);
constraint int_eq(r1, 1);
constraint int_eq(c1, 1);
constraint int_eq(z1, 1);
constraint int_eq(r2, 3);
constraint int_eq(c2, 5);
constraint int_eq(z2, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames

        # pad1 = 7*1 + 3*1 + 1 = 11, pad2 = 7*3 + 3*5 + 2 = 38
        # 11 - 38 = -27 <= 0 → true
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 1

    test "int_lin_le_reif channel — 3-position false case":
        ## Same structure but values arranged so the reif result is false.
        let src = """
var 1..3: r1 :: output_var;
var 1..5: c1 :: output_var;
var 1..2: z1 :: output_var;
var 1..3: r2 :: output_var;
var 1..5: c2 :: output_var;
var 1..2: z2 :: output_var;
var int: pad1 :: is_defined_var;
var int: pad2 :: is_defined_var;
var bool: b :: output_var :: is_defined_var;
constraint int_lin_eq([7,3,1,-1],[r1,c1,z1,pad1],0) :: defines_var(pad1);
constraint int_lin_eq([7,3,1,-1],[r2,c2,z2,pad2],0) :: defines_var(pad2);
constraint int_lin_le_reif([1,-1],[pad1,pad2],0,b) :: defines_var(b);
constraint int_eq(r1, 3);
constraint int_eq(c1, 5);
constraint int_eq(z1, 2);
constraint int_eq(r2, 1);
constraint int_eq(c2, 1);
constraint int_eq(z2, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check "b" in tr.channelVarNames

        # pad1 = 7*3 + 3*5 + 2 = 38, pad2 = 7*1 + 3*1 + 1 = 11
        # 38 - 11 = 27 > 0 → false
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let bVal = tr.sys.assignment[tr.varPositions["b"]]
        check bVal == 0


suite "FlatZinc Cumulative Zero-Height Filtering":

    test "cumulative with zero-height tasks is filtered":
        ## cumulative([s1,s2,s3], [5,5,5], [2,0,3], 4)
        ## Task 2 has height 0, so it should be filtered out.
        ## With tasks 1 and 3 (heights 2+3=5 > limit 4), constraint is non-trivial.
        let src = """
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
var 0..10: s3 :: output_var;
constraint fzn_cumulative([s1,s2,s3], [5,5,5], [2,0,3], 4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should solve: tasks 1 and 3 can't overlap (2+3>4)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error

    test "cumulative with all zero heights is eliminated":
        ## cumulative([s1,s2], [5,5], [0,0], 4)
        ## Both tasks have zero height → trivially satisfied, no constraint emitted.
        let src = """
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
constraint fzn_cumulative([s1,s2], [5,5], [0,0], 4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error

    test "cumulative with sum(heights) <= limit is eliminated":
        ## cumulative([s1,s2], [5,5], [1,2], 4)
        ## sum = 3 <= limit 4 → trivially satisfied
        let src = """
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
constraint fzn_cumulative([s1,s2], [5,5], [1,2], 4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error


suite "FlatZinc Tautological Disjunctive Pair Detection":

    test "tautological pair x<=y OR y<=x is detected and skipped":
        ## int_lin_le_reif([1,-1],[x,y],0,b1) :: defines_var(b1)   -- b1 = (x <= y)
        ## int_lin_le_reif([1,-1],[y,x],0,b2) :: defines_var(b2)   -- b2 = (y <= x)
        ## bool_clause([b1,b2],[])                                    -- x<=y OR y<=x, always true
        let src = """
var 1..10: x :: output_var;
var 1..10: y :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[x,y],0,b1) :: defines_var(b1);
constraint int_lin_le_reif([1,-1],[y,x],0,b2) :: defines_var(b2);
constraint bool_clause([b1,b2],[]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should have 0 disjunctive pairs (tautology skipped)
        check tr.disjunctivePairs.len == 0
        # Both bool vars should still be consumed (defined)
        check "b1" in tr.definedVarNames
        check "b2" in tr.definedVarNames

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error

    test "non-tautological pair is kept":
        ## int_lin_le_reif([1,-1],[x,y],-2,b1)  -- b1 = (x - y <= -2) i.e. x + 2 <= y
        ## int_lin_le_reif([1,-1],[y,x],-3,b2)  -- b2 = (y - x <= -3) i.e. y + 3 <= x
        ## bool_clause([b1,b2],[])                 -- non-overlapping OR
        let src = """
var 1..20: x :: output_var;
var 1..20: y :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[x,y],-2,b1) :: defines_var(b1);
constraint int_lin_le_reif([1,-1],[y,x],-3,b2) :: defines_var(b2);
constraint bool_clause([b1,b2],[]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should have 1 disjunctive pair (not a tautology: rhs1+rhs2 = -5 < 0)
        check tr.disjunctivePairs.len == 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error


suite "FlatZinc int_lin_le Tautological Detection":

    test "int_lin_le always satisfied by domain bounds is skipped":
        ## x in 1..3, y in 1..3: 1*x + 1*y <= 10 is always true (max 3+3=6 <= 10)
        let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
constraint int_lin_le([1,1],[x,y],10);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedTautological >= 1

    test "int_lin_le with negative coefficients uses correct bound":
        ## x in 1..5: -1*x <= -1, i.e. x >= 1. max(-1*x) = -1*1 = -1 <= -1, tautological
        let src = """
var 1..5: x :: output_var;
constraint int_lin_le([-1],[x],-1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedTautological >= 1

    test "int_lin_le not tautological is kept":
        ## x in 1..5, y in 1..5: 1*x + 1*y <= 3 is NOT always true (max 5+5=10 > 3)
        let src = """
var 1..5: x :: output_var;
var 1..5: y :: output_var;
constraint int_lin_le([1,1],[x,y],3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedTautological == 0


suite "FlatZinc NAND Redundancy Detection":

    test "int_lin_le duplicating bool_clause NAND is skipped":
        ## bool_clause([], [b1, b2]) encodes NOT(b1 AND b2), i.e. b1+b2 <= 1
        ## int_lin_le([1,1],[i1,i2],1) with bool2int(b1,i1), bool2int(b2,i2) is redundant
        let src = """
var bool: b1 :: output_var;
var bool: b2 :: output_var;
var 0..1: i1 :: var_is_introduced :: is_defined_var;
var 0..1: i2 :: var_is_introduced :: is_defined_var;
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint bool_clause([], [b1, b2]);
constraint int_lin_le([1,1],[i1,i2],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedRedundantNand >= 1
        # The bool_clause NAND should still exist as a constraint
        check tr.nandBoolPairs.len > 0

    test "int_lin_le with scaled coefficients duplicating NAND is skipped":
        ## bool_clause([], [b1, b2]) → NAND
        ## int_lin_le([3,3],[i1,i2],3) → 3*i1 + 3*i2 <= 3 → i1+i2 <= 1, same NAND
        let src = """
var bool: b1 :: output_var;
var bool: b2 :: output_var;
var 0..1: i1 :: var_is_introduced :: is_defined_var;
var 0..1: i2 :: var_is_introduced :: is_defined_var;
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint bool_clause([], [b1, b2]);
constraint int_lin_le([3,3],[i1,i2],3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedRedundantNand >= 1

    test "int_lin_le without matching bool_clause is not skipped":
        ## No bool_clause NAND exists, so int_lin_le should be kept
        let src = """
var bool: b1 :: output_var;
var bool: b2 :: output_var;
var 0..1: i1 :: var_is_introduced :: is_defined_var;
var 0..1: i2 :: var_is_introduced :: is_defined_var;
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint int_lin_le([1,1],[i1,i2],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedRedundantNand == 0

    test "int_lin_le with unequal coefficients is not treated as NAND":
        ## [2,1] != equal coefficients, should not be detected as NAND
        let src = """
var bool: b1 :: output_var;
var bool: b2 :: output_var;
var 0..1: i1 :: var_is_introduced :: is_defined_var;
var 0..1: i2 :: var_is_introduced :: is_defined_var;
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint bool_clause([], [b1, b2]);
constraint int_lin_le([2,1],[i1,i2],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.nSkippedRedundantNand == 0


suite "FlatZinc Overlap Channel Detection":

    test "overlap = NOT sep detected as channel":
        ## int_le_reif(5, s2, b1) :: defines_var(b1)     -- b1 = (5 <= s2) i.e. s1+dur1 <= s2
        ## int_le_reif(8, s1, b2) :: defines_var(b2)     -- b2 = (8 <= s1) i.e. s2+dur2 <= s1
        ## bool_clause_reif([b1,b2],[],sep) :: defines_var(sep)  -- sep = b1 OR b2
        ## bool_not(overlap, sep) :: defines_var(sep)            -- overlap = NOT sep
        ## The overlap variable should become a channel.
        let src = """
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: sep :: var_is_introduced :: is_defined_var;
var bool: overlap :: output_var;
constraint int_le_reif(5, s2, b1) :: defines_var(b1);
constraint int_le_reif(8, s1, b2) :: defines_var(b2);
constraint bool_clause_reif([b1,b2],[],sep) :: defines_var(sep);
constraint bool_not(overlap, sep) :: defines_var(sep);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # overlap should be detected as an overlap variable
        check tr.overlapChannelDefs.len == 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error


suite "FlatZinc Multi-Resource No-Overlap Detection":

    test "grouped bool_clause([], [a,b,overlap]) → single constraint":
        ## 3 resources, overlap detected as channel, 3 clauses grouped into 1 constraint.
        let src = """
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: sep :: var_is_introduced :: is_defined_var;
var bool: overlap :: output_var;
var bool: a1r1 :: output_var;
var bool: a2r1 :: output_var;
var bool: a1r2 :: output_var;
var bool: a2r2 :: output_var;
var bool: a1r3 :: output_var;
var bool: a2r3 :: output_var;
constraint int_le_reif(5, s2, b1) :: defines_var(b1);
constraint int_le_reif(8, s1, b2) :: defines_var(b2);
constraint bool_clause_reif([b1,b2],[],sep) :: defines_var(sep);
constraint bool_not(overlap, sep) :: defines_var(sep);
constraint bool_clause([], [a1r1, a2r1, overlap]);
constraint bool_clause([], [a1r2, a2r2, overlap]);
constraint bool_clause([], [a1r3, a2r3, overlap]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # 3 clauses should be grouped into 1 multi-resource constraint
        check tr.multiResourceNoOverlapInfos.len == 1
        check tr.multiResourceNoOverlapInfos[0].assignPairNames.len == 3

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        discard  # solve completed without error

suite "FlatZinc AtMost-1 Pairwise Clique Merging":

    test "3-variable clique: 3 pairwise → 1 atMost":
        ## Three binary variables with all 3 pairwise int_lin_le([1,1],[xi,xj],1)
        ## constraints should be merged into a single atMost(3 vars, 1, 1).
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_lin_le([1,1],[x1,x2],1);
constraint int_lin_le([1,1],[x1,x3],1);
constraint int_lin_le([1,1],[x2,x3],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should detect 1 clique of 3 variables
        check tr.atMostPairCliques.len == 1
        check tr.atMostPairCliques[0].len == 3

        # Solve and verify at most 1 is set to 1
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        var count = 0
        for name in ["x1", "x2", "x3"]:
            count += tr.sys.assignment[tr.varPositions[name]]
        check count <= 1

    test "two disjoint cliques":
        ## 6 variables forming two cliques of 3: {x1,x2,x3} and {y1,y2,y3}
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
var 0..1: y1 :: output_var;
var 0..1: y2 :: output_var;
var 0..1: y3 :: output_var;
constraint int_lin_le([1,1],[x1,x2],1);
constraint int_lin_le([1,1],[x1,x3],1);
constraint int_lin_le([1,1],[x2,x3],1);
constraint int_lin_le([1,1],[y1,y2],1);
constraint int_lin_le([1,1],[y1,y3],1);
constraint int_lin_le([1,1],[y2,y3],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.atMostPairCliques.len == 2
        check tr.atMostPairCliques[0].len == 3
        check tr.atMostPairCliques[1].len == 3

    test "incomplete graph — no clique of size 3":
        ## Three variables but only 2 of 3 pairs present — no clique possible.
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_lin_le([1,1],[x1,x2],1);
constraint int_lin_le([1,1],[x1,x3],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # No clique of size >= 3
        check tr.atMostPairCliques.len == 0

    test "clique merging with bool2int channels":
        ## Realistic pattern: bool vars → bool2int → int_lin_le pairwise on int outputs.
        ## The int outputs of bool2int are channel variables but the clique detection
        ## should still work because it runs before detectReifChannels.
        let src = """
var bool: b1 :: output_var;
var bool: b2 :: output_var;
var bool: b3 :: output_var;
var bool: b4 :: output_var;
var 0..1: i1 :: var_is_introduced :: is_defined_var;
var 0..1: i2 :: var_is_introduced :: is_defined_var;
var 0..1: i3 :: var_is_introduced :: is_defined_var;
var 0..1: i4 :: var_is_introduced :: is_defined_var;
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint bool2int(b3, i3) :: defines_var(i3);
constraint bool2int(b4, i4) :: defines_var(i4);
constraint int_lin_le([1,1],[i1,i2],1);
constraint int_lin_le([1,1],[i1,i3],1);
constraint int_lin_le([1,1],[i1,i4],1);
constraint int_lin_le([1,1],[i2,i3],1);
constraint int_lin_le([1,1],[i2,i4],1);
constraint int_lin_le([1,1],[i3,i4],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should detect 1 clique of 4 bool2int outputs
        check tr.atMostPairCliques.len == 1
        check tr.atMostPairCliques[0].len == 4

        # Solve and verify correctness
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        var count = 0
        for name in ["b1", "b2", "b3", "b4"]:
            count += tr.sys.assignment[tr.varPositions[name]]
        check count <= 1

    test "fixed binary variables adjust atMost RHS":
        ## When some binary variables are fixed, their contribution should be
        ## folded into the RHS. Here x3=1 is fixed, so x1+x2 <= 0.
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 1..1: x3;
constraint int_lin_le([1,1,1],[x1,x2,x3],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        # x3=1 uses the budget, so x1 and x2 must both be 0
        check tr.sys.assignment[tr.varPositions["x1"]] == 0
        check tr.sys.assignment[tr.varPositions["x2"]] == 0

    test "fixed-to-zero binary does not change RHS":
        ## x3=0 contributes nothing, so x1+x2 <= 1 remains.
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..0: x3;
constraint int_lin_le([1,1,1],[x1,x2,x3],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let v1 = tr.sys.assignment[tr.varPositions["x1"]]
        let v2 = tr.sys.assignment[tr.varPositions["x2"]]
        check v1 + v2 <= 1

    test "clique with reif bool2int channels (non-aliasable)":
        ## Bool inputs are reification outputs (is_defined_var) so bool2int
        ## identity aliasing is skipped. The int outputs become channel vars
        ## via detectReifChannels and the clique resolves through varPositions.
        let src = """
var 0..10: y1 :: output_var;
var 0..10: y2 :: output_var;
var 0..10: y3 :: output_var;
var bool: b1 :: is_defined_var;
var bool: b2 :: is_defined_var;
var bool: b3 :: is_defined_var;
var 0..1: i1 :: is_defined_var;
var 0..1: i2 :: is_defined_var;
var 0..1: i3 :: is_defined_var;
constraint int_le_reif(y1, 5, b1) :: defines_var(b1);
constraint int_le_reif(y2, 5, b2) :: defines_var(b2);
constraint int_le_reif(y3, 5, b3) :: defines_var(b3);
constraint bool2int(b1, i1) :: defines_var(i1);
constraint bool2int(b2, i2) :: defines_var(i2);
constraint bool2int(b3, i3) :: defines_var(i3);
constraint int_lin_le([1,1],[i1,i2],1);
constraint int_lin_le([1,1],[i1,i3],1);
constraint int_lin_le([1,1],[i2,i3],1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Bool2int identity aliasing should be skipped (bool inputs have is_defined_var)
        check tr.bool2intIdentityAliases.len == 0
        # Clique should still be detected (on the int var names before they become channels)
        check tr.atMostPairCliques.len == 1
        check tr.atMostPairCliques[0].len == 3

        # Solve — the atMost clique resolves through channel variable positions
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        # At most one of y1,y2,y3 can be <= 5
        var count = 0
        for name in ["b1", "b2", "b3"]:
            count += tr.sys.assignment[tr.varPositions[name]]
        check count <= 1


suite "FlatZinc Multi-Machine No-Overlap Detection":

    test "detectMultiMachineNoOverlap: all variable machines":
        ## 3 tasks × 2 machines.  Each cumulative(limit=1) per machine has heights
        ## derived from bool2int(int_eq_reif(machine_var, machine_val)).
        ## The detector should collapse the two cumulatives + reif chains into one
        ## MultiMachineNoOverlap constraint.
        let src = """
var 0..10: s0 :: output_var;
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
var 0..1: m0 :: output_var;
var 0..1: m1 :: output_var;
var 0..1: m2 :: output_var;
var bool: b0_eq0 :: var_is_introduced :: is_defined_var;
var bool: b1_eq0 :: var_is_introduced :: is_defined_var;
var bool: b2_eq0 :: var_is_introduced :: is_defined_var;
var 0..1: h0_m0 :: var_is_introduced :: is_defined_var;
var 0..1: h1_m0 :: var_is_introduced :: is_defined_var;
var 0..1: h2_m0 :: var_is_introduced :: is_defined_var;
var bool: b0_eq1 :: var_is_introduced :: is_defined_var;
var bool: b1_eq1 :: var_is_introduced :: is_defined_var;
var bool: b2_eq1 :: var_is_introduced :: is_defined_var;
var 0..1: h0_m1 :: var_is_introduced :: is_defined_var;
var 0..1: h1_m1 :: var_is_introduced :: is_defined_var;
var 0..1: h2_m1 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(m0, 0, b0_eq0) :: defines_var(b0_eq0);
constraint int_eq_reif(m1, 0, b1_eq0) :: defines_var(b1_eq0);
constraint int_eq_reif(m2, 0, b2_eq0) :: defines_var(b2_eq0);
constraint bool2int(b0_eq0, h0_m0) :: defines_var(h0_m0);
constraint bool2int(b1_eq0, h1_m0) :: defines_var(h1_m0);
constraint bool2int(b2_eq0, h2_m0) :: defines_var(h2_m0);
constraint int_eq_reif(m0, 1, b0_eq1) :: defines_var(b0_eq1);
constraint int_eq_reif(m1, 1, b1_eq1) :: defines_var(b1_eq1);
constraint int_eq_reif(m2, 1, b2_eq1) :: defines_var(b2_eq1);
constraint bool2int(b0_eq1, h0_m1) :: defines_var(h0_m1);
constraint bool2int(b1_eq1, h1_m1) :: defines_var(h1_m1);
constraint bool2int(b2_eq1, h2_m1) :: defines_var(h2_m1);
constraint fzn_cumulative([s0,s1,s2], [3,2,4], [h0_m0,h1_m0,h2_m0], 1);
constraint fzn_cumulative([s0,s1,s2], [3,2,4], [h0_m1,h1_m1,h2_m1], 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Pattern should be detected
        check tr.multiMachineNoOverlapInfos.len == 1
        let info = tr.multiMachineNoOverlapInfos[0]
        check info.startVarNames == @["s0", "s1", "s2"]
        check info.durations == @[3, 2, 4]
        check info.machineVarNames == @["m0", "m1", "m2"]
        check info.numMachineValues == 2
        # All variable machines → all fixedMachineValues should be -1
        check info.fixedMachineValues == @[-1, -1, -1]

        # Intermediate bool/int vars should be consumed
        for vn in ["b0_eq0", "b1_eq0", "b2_eq0", "h0_m0", "h1_m0", "h2_m0",
                    "b0_eq1", "b1_eq1", "b2_eq1", "h0_m1", "h1_m1", "h2_m1"]:
            check vn in tr.definedVarNames

        # Constraint system should contain a MultiMachineNoOverlap constraint
        var foundMMNO = false
        for c in tr.sys.baseArray.constraints:
            if c.stateType == MultiMachineNoOverlapType:
                foundMMNO = true
                break
        check foundMMNO

        # Solve and verify no-overlap semantics
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let starts = [tr.sys.assignment[tr.varPositions["s0"]],
                      tr.sys.assignment[tr.varPositions["s1"]],
                      tr.sys.assignment[tr.varPositions["s2"]]]
        let machines = [tr.sys.assignment[tr.varPositions["m0"]],
                        tr.sys.assignment[tr.varPositions["m1"]],
                        tr.sys.assignment[tr.varPositions["m2"]]]
        let durations = [3, 2, 4]

        # For each machine, verify no two tasks overlap
        for machine in 0..1:
            var tasksOnMachine: seq[int]
            for t in 0..2:
                if machines[t] == machine:
                    tasksOnMachine.add(t)
            for i in 0..<tasksOnMachine.len:
                for j in (i+1)..<tasksOnMachine.len:
                    let ti = tasksOnMachine[i]
                    let tj = tasksOnMachine[j]
                    # Intervals [s, s+d) must not overlap
                    check(starts[ti] + durations[ti] <= starts[tj] or
                          starts[tj] + durations[tj] <= starts[ti])


    test "detectMultiMachineNoOverlap: fixed machine task":
        ## 3 tasks × 2 machines, but task 2 is pre-assigned to machine 1.
        ## Heights for task 2: constant 0 in machine-0 cumulative, constant 1 in machine-1.
        ## Verifies the fixed machine value is correctly inferred as 1, not 0.
        let src = """
var 0..10: s0 :: output_var;
var 0..10: s1 :: output_var;
var 0..10: s2 :: output_var;
var 0..1: m0 :: output_var;
var 0..1: m1 :: output_var;
var bool: b0_eq0 :: var_is_introduced :: is_defined_var;
var bool: b1_eq0 :: var_is_introduced :: is_defined_var;
var 0..1: h0_m0 :: var_is_introduced :: is_defined_var;
var 0..1: h1_m0 :: var_is_introduced :: is_defined_var;
var bool: b0_eq1 :: var_is_introduced :: is_defined_var;
var bool: b1_eq1 :: var_is_introduced :: is_defined_var;
var 0..1: h0_m1 :: var_is_introduced :: is_defined_var;
var 0..1: h1_m1 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(m0, 0, b0_eq0) :: defines_var(b0_eq0);
constraint int_eq_reif(m1, 0, b1_eq0) :: defines_var(b1_eq0);
constraint bool2int(b0_eq0, h0_m0) :: defines_var(h0_m0);
constraint bool2int(b1_eq0, h1_m0) :: defines_var(h1_m0);
constraint int_eq_reif(m0, 1, b0_eq1) :: defines_var(b0_eq1);
constraint int_eq_reif(m1, 1, b1_eq1) :: defines_var(b1_eq1);
constraint bool2int(b0_eq1, h0_m1) :: defines_var(h0_m1);
constraint bool2int(b1_eq1, h1_m1) :: defines_var(h1_m1);
constraint fzn_cumulative([s0,s1,s2], [3,2,4], [h0_m0,h1_m0,0], 1);
constraint fzn_cumulative([s0,s1,s2], [3,2,4], [h0_m1,h1_m1,1], 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Pattern should be detected
        check tr.multiMachineNoOverlapInfos.len == 1
        let info = tr.multiMachineNoOverlapInfos[0]
        check info.startVarNames == @["s0", "s1", "s2"]
        check info.machineVarNames[0] == "m0"
        check info.machineVarNames[1] == "m1"
        check info.machineVarNames[2] == ""    # task 2 has no machine variable

        # Critical: fixed machine value for task 2 should be 1, not 0
        check info.fixedMachineValues[0] == -1  # variable
        check info.fixedMachineValues[1] == -1  # variable
        check info.fixedMachineValues[2] == 1   # fixed to machine 1

        # Verify the built constraint has the correct fixed machine
        var foundConstraint = false
        for c in tr.sys.baseArray.constraints:
            if c.stateType == MultiMachineNoOverlapType:
                foundConstraint = true
                check c.multiMachineNoOverlapState.fixedMachines[2] == 1
                break
        check foundConstraint

        # Solve and verify task 2 is always on machine 1 and no overlaps
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let starts = [tr.sys.assignment[tr.varPositions["s0"]],
                      tr.sys.assignment[tr.varPositions["s1"]],
                      tr.sys.assignment[tr.varPositions["s2"]]]
        let machines = [tr.sys.assignment[tr.varPositions["m0"]],
                        tr.sys.assignment[tr.varPositions["m1"]],
                        1]  # task 2 is fixed to machine 1
        let durations = [3, 2, 4]

        for machine in 0..1:
            var tasksOnMachine: seq[int]
            for t in 0..2:
                if machines[t] == machine:
                    tasksOnMachine.add(t)
            for i in 0..<tasksOnMachine.len:
                for j in (i+1)..<tasksOnMachine.len:
                    let ti = tasksOnMachine[i]
                    let tj = tasksOnMachine[j]
                    check(starts[ti] + durations[ti] <= starts[tj] or
                          starts[tj] + durations[tj] <= starts[ti])
