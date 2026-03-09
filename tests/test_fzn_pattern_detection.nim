## Tests for FlatZinc pattern detection logic in translator.nim.
## Covers detection procs that were previously untested:
##   detectCountPatterns, detectReifChannels (sub-patterns),
##   detectImplicationPatterns, detectDisjunctivePairs,
##   detectDisjunctiveResources, detectRedundantOrderings,
##   detectInversePatterns, detectInverseChannelPatterns.

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
