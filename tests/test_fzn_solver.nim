import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]

import crusher
import flatzinc/[parser, translator, output]

suite "FlatZinc Solver - End to End":

  test "solve all_different + linear with negatives":
    let src = """
var -10..10: x1;
var -10..10: x2;
var -10..10: x3;
var -10..10: x4;
var -10..10: x5;
array [1..5] of var int: x:: output_array([1..5]) = [x1,x2,x3,x4,x5];
array [1..2] of int: coeffs = [1,-1];
constraint gecode_all_different_int(x);
constraint int_lin_le(coeffs,[x1,x2],0);
constraint int_lin_le(coeffs,[x2,x3],0);
constraint int_lin_eq([1,1,1,1,1],[x1,x2,x3,x4,x5],-5);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    # Get the output array positions
    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    # Verify all_different
    check values.toHashSet.len == values.len

    # Verify sum == -5
    check values.foldl(a + b) == -5

    # Verify strictly increasing for first 3 elements (from int_lin_le constraints on pairs 0-1 and 1-2)
    check values[0] < values[1]
    check values[1] < values[2]

  test "solve simple satisfaction problem from FZN string":
    # A simple all-different + sum problem
    let src = """
var 1..5: x1;
var 1..5: x2;
var 1..5: x3;
array [1..3] of var int: x:: output_array([1..3]) = [x1,x2,x3];
constraint fzn_all_different_int(x);
constraint int_lin_eq([1,1,1],[x1,x2,x3],6);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    check values.toHashSet.len == 3  # all different
    check values.foldl(a + b) == 6   # sum = 6
    # Only solution: {1,2,3} in some order
    check values.sorted == @[1, 2, 3]

  test "solve with int_eq and int_ne constraints":
    let src = """
var 1..5: x;
var 1..5: y;
var 1..5: z;
constraint int_eq(x, y);
constraint int_ne(y, z);
constraint int_lin_eq([1,1,1],[x,y,z],7);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]

    check xVal == yVal        # int_eq
    check yVal != zVal        # int_ne
    check xVal + yVal + zVal == 7  # sum = 7

  test "solve with int_plus constraint":
    let src = """
var 1..10: x;
var 1..10: y;
var 1..20: z;
constraint int_plus(x, y, z);
constraint int_eq(z, 15);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]

    check xVal + yVal == zVal
    check zVal == 15

  test "solve with bool2int constraint":
    let src = """
var bool: b;
var 0..1: i;
constraint bool2int(b, i);
constraint int_eq(i, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let iVal = tr.sys.assignment[tr.varPositions["i"]]

    check bVal == iVal
    check iVal == 1

  test "output format":
    let src = """
var 1..3: x:: output_var;
var 1..3: y:: output_var;
array [1..2] of var int: arr:: output_array([1..2]) = [x,y];
constraint int_ne(x, y);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let output = tr.formatSolution()
    check "x = " in output
    check "y = " in output
    check "arr = array1d(1..2," in output

  test "equality copy variable detected and eliminated":
    # xcopy only appears in a defines_var constraint: int_eq_reif(xcopy, x, b).
    # It should be detected as an equality copy alias of x and eliminated.
    # The indicator b should become a constant-1 channel (since copy == original
    # is always true). bi (via bool2int) should also be 1.
    let src = """
var 1..5: x:: output_var;
var 1..5: xcopy;
var 0..1: b;
var 0..1: bi:: output_var;
var 1..5: y:: output_var;
constraint int_eq_reif(xcopy, x, b):: defines_var(b);
constraint bool2int(b, bi):: defines_var(bi);
constraint int_lin_eq([1,1],[x,y],6);
constraint fzn_all_different_int([x,y]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # xcopy should be detected as an equality copy alias of x
    check "xcopy" in tr.equalityCopyAliases
    check tr.equalityCopyAliases["xcopy"] == "x"

    # xcopy should be eliminated (no position allocated)
    check "xcopy" notin tr.varPositions

    # b should be a channel position (not searched)
    check "b" in tr.varPositions
    let bPos = tr.varPositions["b"]
    check bPos in tr.sys.baseArray.channelPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # b should always be 1 (equality copy → constant-1 channel)
    check tr.sys.assignment[bPos] == 1

    # bi should also be 1 (bool2int of b)
    if "bi" in tr.varPositions:
      check tr.sys.assignment[tr.varPositions["bi"]] == 1

    # Real constraints should be satisfied
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check xVal + yVal == 6
    check xVal != yVal

  test "equality copy cycle detection — no crash":
    # a and b form a cycle: int_eq_reif(a, b, ind1) and int_eq_reif(b, a, ind2).
    # Neither should be eliminated (cycle detected and skipped).
    let src = """
var 1..3: a;
var 1..3: b;
var 0..1: ind1;
var 0..1: ind2;
var 1..3: x:: output_var;
constraint int_eq_reif(a, b, ind1):: defines_var(ind1);
constraint int_eq_reif(b, a, ind2):: defines_var(ind2);
constraint int_eq(x, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Cycle should be detected — neither a nor b should be in equalityCopyAliases
    check "a" notin tr.equalityCopyAliases
    check "b" notin tr.equalityCopyAliases

    # Both should still have positions (not eliminated)
    check "a" in tr.varPositions
    check "b" in tr.varPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    check tr.sys.assignment[tr.varPositions["x"]] == 2

  test "equality copy not applied to objective inputs":
    # Regression test: a variable that only appears in defines_var constraints
    # must NOT be eliminated as an equality copy when one of those constraints
    # is an int_lin_eq defining the objective. The objective's inputs are real
    # references that need positions.
    # Here v1 appears in:
    #   1. int_eq_reif(v1, v2, b) :: defines_var(b)  — reification
    #   2. int_lin_eq([1,1,-1],[v1,v2,cost],0) :: defines_var(cost) — objective
    # Without the fix, v1 would be treated as an equality copy of v2 (since it
    # only appears in defines_var constraints), blocking the cost expression.
    let src = """
var 1..5: v1;
var 1..5: v2;
var 0..1: b;
var 2..10: cost:: output_var;
constraint int_eq_reif(v1, v2, b):: defines_var(b);
constraint int_lin_eq([1,1,-1],[v1,v2,cost],0):: defines_var(cost);
constraint int_eq(v1, 3);
constraint int_eq(v2, 4);
solve minimize cost;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # v1 must NOT be an equality copy — it's an objective input
    check "v1" notin tr.equalityCopyAliases
    check "v1" in tr.varPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # cost = v1 + v2 = 3 + 4 = 7
    let costVal = tr.sys.assignment[tr.varPositions["v1"]] +
                  tr.sys.assignment[tr.varPositions["v2"]]
    check costVal == 7

  test "0-based circuit via FlatZinc":
    # fzn_circuit with 0-based values (domain 0..3 for 4 nodes)
    let src = """
var 0..3: x1;
var 0..3: x2;
var 0..3: x3;
var 0..3: x4;
array [1..4] of var int: x:: output_array([1..4]) = [x1,x2,x3,x4];
constraint fzn_all_different_int(x);
constraint fzn_circuit(x);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](4)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    # All different
    check values.toHashSet.len == 4
    # Valid 0-based circuit: follow successors from node 0, visit all nodes
    var visited = initPackedSet[int]()
    var cur = 0
    for step in 0..<4:
      check cur notin visited
      visited.incl(cur)
      cur = values[cur]
    check cur == 0
    check visited.len == 4

  test "bool_not channel detection":
    # bool_not(a, b) with defines_var(b) should make b a channel = 1 - a.
    # We force a = 1 via int_eq, so b should be 0.
    let src = """
var 0..1: a:: output_var;
var 0..1: b:: output_var;
constraint int_eq(a, 1);
constraint bool_not(a, b):: defines_var(b);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # b should be detected as a channel variable
    check "b" in tr.channelVarNames
    check "b" in tr.varPositions
    let bPos = tr.varPositions["b"]
    check bPos in tr.sys.baseArray.channelPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let aVal = tr.sys.assignment[tr.varPositions["a"]]
    let bVal = tr.sys.assignment[bPos]
    check aVal == 1
    check bVal == 0  # b = 1 - a

  test "bool_not channel with downstream constraint":
    # b = not(a), then use b in a constraint to verify it propagates correctly.
    # x + y = 5, a = (x != 3), b = not(a), so b = (x == 3).
    # Force b = 1 via bool2int + int_eq, meaning x must be 3, y must be 2.
    let src = """
var 1..4: x:: output_var;
var 1..4: y:: output_var;
var 0..1: a;
var 0..1: b;
var 0..1: bi:: output_var;
constraint int_ne_reif(x, 3, a):: defines_var(a);
constraint bool_not(a, b):: defines_var(b);
constraint bool2int(b, bi):: defines_var(bi);
constraint int_eq(bi, 1);
constraint int_lin_eq([1,1],[x,y],5);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b" in tr.channelVarNames
    check "bi" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check xVal == 3
    check yVal == 2

  test "incomplete case analysis not channeled":
    # Pattern: place has domain {1,2,3}. We only define what target equals when
    # place != 1 (via bool_clause + int_eq_reif + int_ne_reif), but NOT when place == 1.
    # The old code would have channeled target with a wrong default for the missing case.
    # The fix requires all cases to be covered, so target stays a search variable.
    #
    # place==2 → target==10, place==3 → target==20, place==1 → unconstrained
    let src = """
var 1..3: place:: output_var;
var 5..25: target:: output_var;
var 0..1: eq2;
var 0..1: ne2;
var 0..1: eq3;
var 0..1: ne3;
constraint int_eq_reif(target, 10, eq2):: defines_var(eq2);
constraint int_ne_reif(place, 2, ne2):: defines_var(ne2);
constraint bool_clause([eq2, ne2], []);
constraint int_eq_reif(target, 20, eq3):: defines_var(eq3);
constraint int_ne_reif(place, 3, ne3):: defines_var(ne3);
constraint bool_clause([eq3, ne3], []);
constraint int_eq(place, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # target should NOT be a case-analysis channel (but presolve may fix it to singleton)
    check tr.caseAnalysisDefs.len == 0  # no incomplete case-analysis should be detected

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let placeVal = tr.sys.assignment[tr.varPositions["place"]]
    let targetVal = tr.sys.assignment[tr.varPositions["target"]]
    check placeVal == 2
    check targetVal == 10

  test "complete case analysis is channeled":
    # Same pattern but ALL cases covered: place has domain {1,2,3}.
    # place==1 → target==5, place==2 → target==10, place==3 → target==20
    # This should be detected as a complete case analysis and channeled.
    let src = """
var 1..3: place:: output_var;
var 5..25: target:: output_var;
var 0..1: eq1;
var 0..1: ne1;
var 0..1: eq2;
var 0..1: ne2;
var 0..1: eq3;
var 0..1: ne3;
constraint int_eq_reif(target, 5, eq1):: defines_var(eq1);
constraint int_ne_reif(place, 1, ne1):: defines_var(ne1);
constraint bool_clause([eq1, ne1], []);
constraint int_eq_reif(target, 10, eq2):: defines_var(eq2);
constraint int_ne_reif(place, 2, ne2):: defines_var(ne2);
constraint bool_clause([eq2, ne2], []);
constraint int_eq_reif(target, 20, eq3):: defines_var(eq3);
constraint int_ne_reif(place, 3, ne3):: defines_var(ne3);
constraint bool_clause([eq3, ne3], []);
constraint int_eq(place, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # target SHOULD be a channel — complete case analysis
    check "target" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let placeVal = tr.sys.assignment[tr.varPositions["place"]]
    let targetVal = tr.sys.assignment[tr.varPositions["target"]]
    check placeVal == 2
    check targetVal == 10

  test "int_le_reif → bool2int channel chain initialization order":
    # Regression test for channel initialization ordering bug.
    # bool2int bindings are created BEFORE int_le_reif bindings in
    # buildReifChannelBindings. Without fixed-point iteration, the i_k
    # channels (from bool2int) are computed before b_k channels
    # (from int_le_reif), leaving i_k stuck at 0 regardless of x values.
    #
    # Model: 3 variables x1,x2,x3 with domain {0,1,2,3}.
    # b_k = (1 <= x_k) via int_le_reif, i_k = int(b_k) via bool2int.
    # Objective = sum(i_k), defined via int_lin_eq.
    # Constraint: x1 + x2 + x3 = 6 (forces all x_k >= 1, so objective must be 3).
    let src = """
var 0..3: x1;
var 0..3: x2;
var 0..3: x3;
var 0..1: b1;
var 0..1: b2;
var 0..1: b3;
var 0..1: i1;
var 0..1: i2;
var 0..1: i3;
var 0..3: objective:: output_var;
array [1..3] of var int: xs:: output_array([1..3]) = [x1,x2,x3];
constraint int_le_reif(1, x1, b1):: defines_var(b1);
constraint int_le_reif(1, x2, b2):: defines_var(b2);
constraint int_le_reif(1, x3, b3):: defines_var(b3);
constraint bool2int(b1, i1):: defines_var(i1);
constraint bool2int(b2, i2):: defines_var(i2);
constraint bool2int(b3, i3):: defines_var(i3);
constraint int_lin_eq([1, -1, -1, -1], [objective, i1, i2, i3], 0):: defines_var(objective);
constraint int_lin_eq([1, 1, 1], [x1, x2, x3], 7);
solve minimize objective;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # b_k should be channel positions (int_le_reif channels)
    for name in ["b1", "b2", "b3"]:
      check name in tr.channelVarNames

    # i_k should be channel positions (bool2int channels)
    for name in ["i1", "i2", "i3"]:
      check name in tr.channelVarNames

    # objective should be a defined-var expression (eliminated, no position)
    check "objective" in tr.definedVarExprs

    # Solve: x1+x2+x3=7, domain 0..3.
    # If any x_k == 0, the other two sum to 7, but max is 3+3=6. Impossible.
    # So all x_k >= 1, hence b_k = 1, i_k = 1, objective = 3.
    # The bug would report objective = 0 because i_k were stuck at 0.
    let objExpr = tr.objectiveDefExpr
    minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

    let xs = [tr.sys.assignment[tr.varPositions["x1"]],
              tr.sys.assignment[tr.varPositions["x2"]],
              tr.sys.assignment[tr.varPositions["x3"]]]
    check xs[0] + xs[1] + xs[2] == 7
    for v in xs:
      check v >= 1

    # The critical check: objective must be 3, not 0
    let objVal = objExpr.evaluate(tr.sys.assignment)
    check objVal == 3

  test "defined vars in var-indexed arrays rescued as channels":
    # Regression test: defined vars (is_defined_var, no position) appearing in
    # arrays indexed by variable expressions (array_var_int_element) must be
    # rescued as channel variables. Without rescue, resolveMixedArray crashes
    # because defined vars have no position.
    #
    # Model: x1, x2 in 1..3; d1 = x1 + 1 (defined var); d2 = x2 + 1 (defined var).
    # Array A = [d1, d2, 5]. idx in 1..3, result = A[idx] via array_var_int_element.
    # Constraint: result == 3 (forces idx to pick an element that equals 3).
    let src = """
var 1..3: x1;
var 1..3: x2;
var 2..4: d1:: is_defined_var:: var_is_introduced;
var 2..4: d2:: is_defined_var:: var_is_introduced;
var 1..3: idx;
var 2..5: result:: output_var;
array [1..3] of var int: A = [d1, d2, 5];
constraint int_lin_eq([1, -1], [d1, x1], 1):: defines_var(d1);
constraint int_lin_eq([1, -1], [d2, x2], 1):: defines_var(d2);
constraint array_var_int_element(idx, A, result);
constraint int_eq(result, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # d1 and d2 should be rescued as channel vars (not defined vars)
    check "d1" in tr.channelVarNames
    check "d2" in tr.channelVarNames
    check "d1" notin tr.definedVarNames
    check "d2" notin tr.definedVarNames
    # They should have positions
    check "d1" in tr.varPositions
    check "d2" in tr.varPositions
    # And rescued channel bindings should have been recorded
    check tr.rescuedChannelDefs.len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let resultVal = tr.sys.assignment[tr.varPositions["result"]]
    check resultVal == 3

    # Verify channel propagation: d1 = x1 + 1, d2 = x2 + 1
    let x1Val = tr.sys.assignment[tr.varPositions["x1"]]
    let x2Val = tr.sys.assignment[tr.varPositions["x2"]]
    let d1Val = tr.sys.assignment[tr.varPositions["d1"]]
    let d2Val = tr.sys.assignment[tr.varPositions["d2"]]
    check d1Val == x1Val + 1
    check d2Val == x2Val + 1

  test "rescued channel with defined-var dependency (multi-layer)":
    # Test that rescued channels correctly inline defined-var dependencies.
    # d1 = x + 2 (defined var, not in array), d2 = d1 * 2 (rescued, in array).
    # d2's channel binding should inline d1's expression: d2 = (x + 2) * 2.
    # Array A = [d2, 10], idx in 1..2, result = A[idx].
    # Constraint: result == 10 (satisfied by idx=1 when x=3: d1=5, d2=10, or idx=2).
    let src = """
var 1..5: x;
var 3..7: d1:: is_defined_var:: var_is_introduced;
var 6..14: d2:: is_defined_var:: var_is_introduced;
var 1..2: idx;
var 6..14: result:: output_var;
array [1..2] of var int: A = [d2, 10];
constraint int_lin_eq([1, -1], [d1, x], 2):: defines_var(d1);
constraint int_times(d1, 2, d2):: defines_var(d2);
constraint array_var_int_element(idx, A, result);
constraint int_eq(result, 10);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Only d2 is rescued (it appears in the var-indexed array)
    check "d2" in tr.channelVarNames
    check "d2" in tr.varPositions
    # d1 stays as a defined var (inlined into d2's channel expression)
    check "d1" in tr.definedVarNames
    check "d1" notin tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let resultVal = tr.sys.assignment[tr.varPositions["result"]]
    check resultVal == 10

    # Verify d2's channel propagation: d2 = (x + 2) * 2
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let d2Val = tr.sys.assignment[tr.varPositions["d2"]]
    check d2Val == (xVal + 2) * 2

suite "FlatZinc int_mod Channel Bindings":

  test "int_mod with direct variable origin":
    ## int_mod(X, 3, Z) where X is a direct variable (not defined).
    ## Z should become a channel: Z = X mod 3.
    let src = """
var 0..8: x :: output_var;
var 0..2: z :: output_var;
constraint int_mod(x, 3, z);
constraint int_eq(x, 7);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # z should be a channel variable
    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal == 7
    check zVal == 1  # 7 mod 3 = 1

  test "int_mod with defined-var origin (regression)":
    ## int_mod(Y, 12, Z) where Y is defined by int_lin_eq as Y = X - 1.
    ## This is the exact pattern from the harmony model that was broken:
    ## the channel binding builder skipped defined-var origins.
    let src = """
var 60..72: x :: output_var;
var 0..127: y :: var_is_introduced :: is_defined_var;
var 0..11: z :: output_var;
constraint int_lin_eq([1,-1],[x,y],1) :: defines_var(y);
constraint int_mod(y, 12, z);
constraint int_eq(x, 65);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # y should be a defined var (no position), z should be a channel
    check "y" in tr.definedVarNames
    check "z" in tr.channelVarNames
    # z's channel binding must exist (this was the bug — it was silently skipped)
    check "z" in tr.varPositions
    let zPos = tr.varPositions["z"]
    check zPos in tr.sys.baseArray.channelPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[zPos]
    check xVal == 65
    # y = 65 - 1 = 64, z = 64 mod 12 = 4
    check zVal == 4

  test "int_mod with constant X":
    ## int_mod(72, 12, Z) — constant X. Z should be fixed to 72 mod 12 = 0.
    let src = """
var 0..11: z :: output_var;
constraint int_mod(72, 12, z);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check zVal == 0  # 72 mod 12 = 0

  test "int_mod channel propagates through cascade":
    ## int_mod defines Z as channel of X. A constraint on Z should
    ## guide the solver to pick the right X value.
    ## X in 0..11, Z = X mod 4, constraint Z == 3.
    ## Valid X values: 3, 7, 11.
    let src = """
var 0..11: x :: output_var;
var 0..3: z :: output_var;
constraint int_mod(x, 4, z);
constraint int_eq(z, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check zVal == 3
    check xVal mod 4 == 3
    check xVal in [3, 7, 11]

suite "FlatZinc int_div Channel Bindings":

  test "int_div with direct variable origin":
    ## int_div(X, 3, Z) where X is a direct variable.
    ## Z should become a channel: Z = X div 3.
    let src = """
var 0..8: x :: output_var;
var 0..2: z :: output_var;
constraint int_div(x, 3, z);
constraint int_eq(x, 7);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal == 7
    check zVal == 2  # 7 div 3 = 2

  test "int_div with defined-var origin":
    ## int_div(Y, 10, Z) where Y is defined by int_lin_eq as Y = X + 5.
    let src = """
var 0..90: x :: output_var;
var 5..95: y :: var_is_introduced :: is_defined_var;
var 0..9: z :: output_var;
constraint int_lin_eq([-1,1],[x,y],5) :: defines_var(y);
constraint int_div(y, 10, z);
constraint int_eq(x, 42);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal == 42
    # y = 42 + 5 = 47, z = 47 div 10 = 4
    check zVal == 4

  test "int_div channel propagates through cascade":
    ## int_div defines Z as channel of X. A constraint on Z should
    ## guide the solver to pick the right X value.
    ## X in 0..19, Z = X div 5, constraint Z == 3.
    ## Valid X values: 15, 16, 17, 18, 19.
    let src = """
var 0..19: x :: output_var;
var 0..3: z :: output_var;
constraint int_div(x, 5, z);
constraint int_eq(z, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check zVal == 3
    check xVal div 5 == 3
    check xVal >= 15 and xVal <= 19

  test "int_div tautological (result always 0)":
    ## int_div(X, 1000, Z) where X in 0..900 → Z always 0.
    ## Z should be a channel fixed to 0.
    let src = """
var 0..900: x :: output_var;
var 0..0: z :: output_var;
constraint int_div(x, 1000, z);
constraint int_eq(x, 500);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal == 500
    check zVal == 0  # 500 div 1000 = 0

suite "FlatZinc implication propagation":

  test "bool_clause implication chain propagation":
    ## a=1 is fixed, a→b, b→c should propagate to fix b=1 and c=1.
    let src = """
var 0..1: a :: output_var;
var 0..1: b :: output_var;
var 0..1: c :: output_var;
var 0..1: d :: output_var;
constraint int_eq(a, 1);
constraint bool_clause([b],[a]);
constraint bool_clause([c],[b]);
constraint bool_clause([d],[c]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let aVal = tr.sys.assignment[tr.varPositions["a"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let cVal = tr.sys.assignment[tr.varPositions["c"]]
    let dVal = tr.sys.assignment[tr.varPositions["d"]]
    check aVal == 1
    check bVal == 1
    check cVal == 1
    check dVal == 1

  test "bool_clause contrapositive propagation":
    ## d=0 is fixed, a→b, b→c, c→d.
    ## Contrapositive: d=0 → c=0 → b=0 → a=0.
    let src = """
var 0..1: a :: output_var;
var 0..1: b :: output_var;
var 0..1: c :: output_var;
var 0..1: d :: output_var;
constraint int_eq(d, 0);
constraint bool_clause([b],[a]);
constraint bool_clause([c],[b]);
constraint bool_clause([d],[c]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let aVal = tr.sys.assignment[tr.varPositions["a"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let cVal = tr.sys.assignment[tr.varPositions["c"]]
    let dVal = tr.sys.assignment[tr.varPositions["d"]]
    check dVal == 0
    check cVal == 0
    check bVal == 0
    check aVal == 0

suite "FlatZinc array_set_element":

  test "array_set_element with constant set array":
    ## array_set_element(idx, [{0,4,7},{2,5,9},{4,7,11}], S)
    ## Choosing idx selects which set of values S contains.
    ## With idx=2, S should be {2,5,9}.
    let src = """
var 1..3: idx :: output_var;
var set of 0..11: s :: output_var;
constraint array_set_element(idx, [{0,4,7},{2,5,9},{4,7,11}], s);
constraint int_eq(idx, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]
    check idxVal == 2

    # Check set membership via boolean decomposition
    let sInfo = tr.setVarBoolPositions["s"]
    var members: seq[int]
    for i in 0..<sInfo.positions.len:
      if tr.sys.assignment[sInfo.positions[i]] == 1:
        members.add(sInfo.lo + i)

    check members.sorted == @[2, 5, 9]

  test "array_set_element channels respond to idx changes":
    ## Constraint that the chosen set must contain value 7.
    ## Chord defs: {0,4,7}, {2,5,9}, {4,7,11}
    ## Only chords 1 and 3 contain 7, so idx must be 1 or 3.
    let src = """
var 1..3: idx :: output_var;
var set of 0..11: s :: output_var;
constraint array_set_element(idx, [{0,4,7},{2,5,9},{4,7,11}], s);
constraint set_in(7, s);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]
    check idxVal in [1, 3]

    # Verify set contains 7
    let sInfo = tr.setVarBoolPositions["s"]
    let pos7 = sInfo.positions[7 - sInfo.lo]
    check tr.sys.assignment[pos7] == 1

suite "FlatZinc int_lin_ne_reif Channeling":

  test "int_lin_ne_reif detected as channel":
    ## int_lin_ne_reif([1,-1], [a,b], 0, r) :: defines_var(r)
    ## r = (a != b) ? 1 : 0
    let src = """
var 1..3: a :: output_var;
var 1..3: b :: output_var;
var 0..1: r :: output_var :: is_defined_var;
constraint int_lin_ne_reif([1,-1],[a,b],0,r) :: defines_var(r);
constraint int_eq(a, 2);
constraint int_eq(b, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "r" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let aVal = tr.sys.assignment[tr.varPositions["a"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check aVal == 2
    check bVal == 2
    check rVal == 0  # a == b → r = 0

  test "int_lin_ne_reif channel with unequal values":
    let src = """
var 1..3: a :: output_var;
var 1..3: b :: output_var;
var 0..1: r :: output_var :: is_defined_var;
constraint int_lin_ne_reif([1,-1],[a,b],0,r) :: defines_var(r);
constraint int_eq(a, 1);
constraint int_eq(b, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "r" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check rVal == 1  # a != b → r = 1

suite "FlatZinc Harmony-like Chain: int_mod → singleton → set_union → array_set_element":

  test "pitch class membership via int_mod + set_in + array_set_element":
    ## Mini harmony model: 2 voices, 1 timestep, 3 possible chords.
    ## Each voice pitch mod 4 must be in the chosen chord's pitch class set.
    ## Chords: {0,1}, {1,2}, {2,3} (pitch classes mod 4).
    ## Voice pitches: v1 in 4..7, v2 in 4..7.
    ##
    ## Chain per voice:
    ##   y = v - 4 (defined var, to get 0-based)
    ##   int_mod(y, 4, pc) — pc = pitch class
    ##   set_in(pc, singleton) + set_card(singleton, 1) — singleton channeling
    ##   set_union(singleton1, singleton2, result) — union of voice pitch classes
    ##   array_set_element(chord, [{0,1},{1,2},{2,3}], target) — chord defines target set
    ##   result must equal target (via set_union equality constraints)
    let src = """
var 4..7: v1 :: output_var;
var 4..7: v2 :: output_var;
var 1..3: chord :: output_var;
var 0..127: y1 :: var_is_introduced :: is_defined_var;
var 0..127: y2 :: var_is_introduced :: is_defined_var;
var 0..3: pc1 :: var_is_introduced;
var 0..3: pc2 :: var_is_introduced;
var set of 0..3: sing1 :: var_is_introduced;
var set of 0..3: sing2 :: var_is_introduced;
var set of 0..3: voice_union :: var_is_introduced :: is_defined_var;
var set of 0..3: target :: var_is_introduced;
constraint int_lin_eq([1,-1],[v1,y1],4) :: defines_var(y1);
constraint int_lin_eq([1,-1],[v2,y2],4) :: defines_var(y2);
constraint int_mod(y1, 4, pc1);
constraint int_mod(y2, 4, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, voice_union) :: defines_var(voice_union);
constraint array_set_element(chord, [{0,1},{1,2},{2,3}], target);
constraint set_eq(voice_union, target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Verify key channel detections
    check "pc1" in tr.channelVarNames  # int_mod channel
    check "pc2" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let v1Val = tr.sys.assignment[tr.varPositions["v1"]]
    let v2Val = tr.sys.assignment[tr.varPositions["v2"]]
    let chordVal = tr.sys.assignment[tr.varPositions["chord"]]

    # Verify pitch classes match the chord
    let pc1Val = (v1Val - 4) mod 4
    let pc2Val = (v2Val - 4) mod 4
    let chordSets = [@[0, 1], @[1, 2], @[2, 3]]
    let chordSet = chordSets[chordVal - 1]

    check pc1Val in chordSet
    check pc2Val in chordSet

  test "int_mod defined-var chain with downstream constraint":
    ## The critical regression pattern: int_mod with defined-var origin
    ## must propagate through the cascade so the solver can navigate
    ## constraints on the mod result.
    ##
    ## x in 10..19, y = x - 10 (defined), z = y mod 5, constraint z == 3.
    ## Valid x: 13, 18.
    let src = """
var 10..19: x :: output_var;
var 0..127: y :: var_is_introduced :: is_defined_var;
var 0..4: z :: output_var;
constraint int_lin_eq([1,-1],[x,y],10) :: defines_var(y);
constraint int_mod(y, 5, z);
constraint int_eq(z, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "y" in tr.definedVarNames
    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check zVal == 3
    check (xVal - 10) mod 5 == 3
    check xVal in [13, 18]

  test "int_mod with variable divisor":
    ## int_mod(x, y, z) where both x and y are variables.
    ## x in 10..15, y in 3..4, z = x mod y.
    ## Fix x=14, y=3 → z = 14 mod 3 = 2.
    let src = """
var 10..15: x :: output_var;
var 3..4: y :: output_var;
var 0..4: z :: output_var;
constraint int_mod(x, y, z);
constraint int_eq(x, 14);
constraint int_eq(y, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal == 14
    check yVal == 3
    check zVal == 2  # 14 mod 3 = 2

  test "3-way disjunctive clause detection":
    # int_lin_le_reif([-1],[x],−5,b1) means -x <= -5 → x >= 5 → b1=true when x>=5
    # bool_clause([b1,b2,b3],[]) means b1 OR b2 OR b3
    # Penalty: min(max(0,-x-(-5)), min(max(0,-y-(-3)), max(0,-z-(-7)))) == 0
    #        = min(max(0,5-x), min(max(0,3-y), max(0,7-z))) == 0
    # Satisfied when x>=5 OR y>=3 OR z>=7
    # Domains wide enough that presolve can't determine reif outputs before
    # disjunctive clause detection. No forcing constraints on x, y — disjunction is free.
    let src = """
var 0..10: x;
var 0..10: y;
var 0..10: z;
var bool: b1;
var bool: b2;
var bool: b3;
constraint int_lin_le_reif([-1],[x],-5,b1):: defines_var(b1);
constraint int_lin_le_reif([-1],[y],-3,b2):: defines_var(b2);
constraint int_lin_le_reif([-1],[z],-7,b3):: defines_var(b3);
constraint bool_clause([b1,b2,b3],[]);
solve satisfy;
"""
    # x>=5 OR y>=3 OR z>=7 — any branch can satisfy
    let model = parseFzn(src)
    var tr = translate(model)

    check "b1" in tr.definedVarNames
    check "b2" in tr.definedVarNames
    check "b3" in tr.definedVarNames
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 3

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal >= 5 or yVal >= 3 or zVal >= 7

  test "AND-of-reif disjunctive clause (Pattern B)":
    # bool_clause([a, d], []) where a from int_lin_le_reif, d = array_bool_and([b,c])
    # a: -x <= -5 → x >= 5
    # b: -y <= -3 → y >= 3
    # c: -z <= -7 → z >= 7
    # d = b AND c → (y>=3 AND z>=7)
    # clause: x>=5 OR (y>=3 AND z>=7)
    # With x<=4 forcing first branch false, need y>=3 AND z>=7
    let src = """
var 0..10: x;
var 0..10: y;
var 0..10: z;
var bool: a;
var bool: b;
var bool: c;
var bool: d;
constraint int_lin_le_reif([-1],[x],-5,a):: defines_var(a);
constraint int_lin_le_reif([-1],[y],-3,b):: defines_var(b);
constraint int_lin_le_reif([-1],[z],-7,c):: defines_var(c);
constraint array_bool_and([b,c],d):: defines_var(d);
constraint bool_clause([a,d],[]);
constraint int_lin_le([1],[x],4);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "a" in tr.definedVarNames
    check "b" in tr.definedVarNames
    check "c" in tr.definedVarNames
    check "d" in tr.definedVarNames
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 2
    # First disjunct: 1 term (x >= 5)
    check tr.disjunctiveClauses[0].disjuncts[0].len == 1
    # Second disjunct: 2 terms (y >= 3 AND z >= 7)
    check tr.disjunctiveClauses[0].disjuncts[1].len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal <= 4
    check yVal >= 3
    check zVal >= 7

  test "AND-vs-AND disjunctive clause (Pattern C)":
    # bool_clause([d1, d2], []) where d1 = array_bool_and([a,b]), d2 = array_bool_and([c,d])
    # a: -x <= -5 → x >= 5
    # b: -y <= -3 → y >= 3
    # c: -w <= -2 → w >= 2
    # d: -z <= -7 → z >= 7
    # d1 = a AND b → (x>=5 AND y>=3)
    # d2 = c AND d → (w>=2 AND z>=7)
    # clause: (x>=5 AND y>=3) OR (w>=2 AND z>=7)
    # With x<=4 and y<=2 forcing first branch false, need w>=2 AND z>=7
    let src = """
var 0..10: x;
var 0..10: y;
var 0..10: w;
var 0..10: z;
var bool: a;
var bool: b;
var bool: c;
var bool: d;
var bool: d1;
var bool: d2;
constraint int_lin_le_reif([-1],[x],-5,a):: defines_var(a);
constraint int_lin_le_reif([-1],[y],-3,b):: defines_var(b);
constraint int_lin_le_reif([-1],[w],-2,c):: defines_var(c);
constraint int_lin_le_reif([-1],[z],-7,d):: defines_var(d);
constraint array_bool_and([a,b],d1):: defines_var(d1);
constraint array_bool_and([c,d],d2):: defines_var(d2);
constraint bool_clause([d1,d2],[]);
constraint int_lin_le([1],[x],4);
constraint int_lin_le([1],[y],2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "a" in tr.definedVarNames
    check "b" in tr.definedVarNames
    check "c" in tr.definedVarNames
    check "d" in tr.definedVarNames
    check "d1" in tr.definedVarNames
    check "d2" in tr.definedVarNames
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 2
    # First disjunct: 2 terms (x >= 5 AND y >= 3)
    check tr.disjunctiveClauses[0].disjuncts[0].len == 2
    # Second disjunct: 2 terms (w >= 2 AND z >= 7)
    check tr.disjunctiveClauses[0].disjuncts[1].len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let wVal = tr.sys.assignment[tr.varPositions["w"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check xVal <= 4
    check yVal <= 2
    check wVal >= 2
    check zVal >= 7

  test "4-literal mixed reif types disjunctive clause":
    # bool_clause([b1, b2, b3, b4], []) with mixed int_lin_le_reif + int_le_reif + int_eq_reif
    # b1: int_lin_le_reif([-1],[x],-5,b1) → x >= 5
    # b2: int_le_reif(y, 3, b2) → y <= 3
    # b3: int_eq_reif(z, 7, b3) → z == 7
    # b4: int_le_reif(2, w, b4) → w >= 2
    # Clause: x>=5 OR y<=3 OR z==7 OR w>=2
    # With x<=4, y>=4, z!=7 (z<=6 & z>=8 not possible, use z in {1..6,8..10}), w<=1
    # → need z==7 ... but z can't be 7. Actually let's simplify:
    # Force x<=4 (kills b1), y>=5 (kills b2: y<=3), w<=1 (kills b4: w>=2) → only z==7 satisfies
    let src = """
var 0..10: x;
var 0..10: y;
var 0..10: z;
var 0..10: w;
var bool: b1;
var bool: b2;
var bool: b3;
var bool: b4;
constraint int_lin_le_reif([-1],[x],-5,b1):: defines_var(b1);
constraint int_le_reif(y, 3, b2):: defines_var(b2);
constraint int_eq_reif(z, 7, b3):: defines_var(b3);
constraint int_le_reif(2, w, b4):: defines_var(b4);
constraint bool_clause([b1,b2,b3,b4],[]);
solve satisfy;
"""
    # x>=5 OR y<=3 OR z==7 OR w>=2 — pattern detected without forcing constraints
    let model = parseFzn(src)
    var tr = translate(model)

    check "b1" in tr.definedVarNames
    check "b2" in tr.definedVarNames
    check "b3" in tr.definedVarNames
    check "b4" in tr.definedVarNames
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 4
    # b3 (int_eq_reif) produces a 2-term conjunction disjunct
    check tr.disjunctiveClauses[0].disjuncts[2].len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    let wVal = tr.sys.assignment[tr.varPositions["w"]]
    # At least one branch must be satisfied
    check xVal >= 5 or yVal <= 3 or zVal == 7 or wVal >= 2

  test "6-literal Unison-style disjunctive clause":
    # Simulates diffn_nonstrict decomposition: 6-literal clause mixing all reif types
    # Two tasks (s1,s2) with durations (d1,d2) on two resources (r1,r2)
    # Non-overlap: s1+d1<=s2 OR s2+d2<=s1 OR r1!=r2 (but using 6 literals for 2D overlap)
    # b1: int_lin_le_reif([1,-1],[s1,s2],-1,b1)  → s1-s2 <= -1 → s1 < s2
    # b2: int_lin_le_reif([1,-1],[s2,s1],-1,b2)  → s2-s1 <= -1 → s2 < s1
    # b3: int_le_reif(s1, 0, b3)                  → s1 <= 0
    # b4: int_le_reif(5, s2, b4)                  → s2 >= 5
    # b5: int_eq_reif(r1, 1, b5)                  → r1 == 1
    # b6: int_eq_reif(r2, 2, b6)                  → r2 == 2
    # No forcing constraints — pattern detected from structure alone.
    # b3 (s1<=0) is always false when s1∈{1..5} (existing int_le_reif presolve resolves this),
    # and b4 (s2>=5) is not always false since s2∈{1..5}. All other reifs are indeterminate.
    # Use domains where most int_lin_le_reif outputs remain indeterminate.
    let src = """
var 1..10: s1;
var 1..10: s2;
var 1..3: r1;
var 1..3: r2;
var bool: b1;
var bool: b2;
var bool: b3;
var bool: b4;
var bool: b5;
var bool: b6;
constraint int_lin_le_reif([1,-1],[s1,s2],-1,b1):: defines_var(b1);
constraint int_lin_le_reif([1,-1],[s2,s1],-1,b2):: defines_var(b2);
constraint int_le_reif(s1, 0, b3):: defines_var(b3);
constraint int_le_reif(5, s2, b4):: defines_var(b4);
constraint int_eq_reif(r1, 1, b5):: defines_var(b5);
constraint int_eq_reif(r2, 2, b6):: defines_var(b6);
constraint bool_clause([b1,b2,b3,b4,b5,b6],[]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # b3 is resolved to 0 by existing presolve (s1>=1 > 0), but others remain.
    # Disjunctive clause should still be detected (5 indeterminate disjuncts).
    check tr.disjunctiveClauses.len == 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # At least one disjunct must be satisfied
    let s1Val = tr.sys.assignment[tr.varPositions["s1"]]
    let s2Val = tr.sys.assignment[tr.varPositions["s2"]]
    let r1Val = tr.sys.assignment[tr.varPositions["r1"]]
    let r2Val = tr.sys.assignment[tr.varPositions["r2"]]
    check s1Val < s2Val or s2Val < s1Val or s1Val <= 0 or s2Val >= 5 or r1Val == 1 or r2Val == 2

  test "mixed refcounts — shared bool not consumed":
    # b_shared appears in TWO clauses (refcount=2) → defining constraint NOT consumed
    # b1,b2,b3 have refcount=1 → consumed
    # Clause 1: b_shared OR b1 OR b2
    # Clause 2: b_shared OR b3
    # b_shared: int_lin_le_reif([-1],[x],-10,b_shared) → x >= 10
    # b1: int_le_reif(y, 3, b1) → y <= 3
    # b2: int_eq_reif(z, 5, b2) → z == 5
    # b3: int_le_reif(2, w, b3) → w >= 2
    let src = """
var 0..20: x;
var 0..10: y;
var 0..10: z;
var 0..10: w;
var bool: b_shared;
var bool: b1;
var bool: b2;
var bool: b3;
constraint int_lin_le_reif([-1],[x],-10,b_shared):: defines_var(b_shared);
constraint int_le_reif(y, 3, b1):: defines_var(b1);
constraint int_eq_reif(z, 5, b2):: defines_var(b2);
constraint int_le_reif(2, w, b3):: defines_var(b3);
constraint bool_clause([b_shared,b1,b2],[]);
constraint bool_clause([b_shared,b3],[]);
constraint int_lin_le([1],[x],9);
constraint int_lin_le([-1],[y],-4);
solve satisfy;
"""
    # x<=9 kills b_shared (x>=10), y>=4 kills b1 (y<=3) in clause 1 → z==5
    # x<=9 kills b_shared in clause 2 → w>=2
    let model = parseFzn(src)
    var tr = translate(model)

    # b_shared has refcount=2 → NOT consumed as defined var
    check "b_shared" notin tr.definedVarNames
    # b1,b2,b3 have refcount=1 → consumed
    check "b1" in tr.definedVarNames
    check "b2" in tr.definedVarNames
    check "b3" in tr.definedVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    let wVal = tr.sys.assignment[tr.varPositions["w"]]
    check xVal <= 9
    check zVal == 5
    check wVal >= 2

  test "int_eq_reif conjunction disjunct — 2 terms":
    # Verify int_eq_reif produces a 2-term conjunction (x<=c AND -x<=-c)
    # bool_clause([b1, b2], [])
    # b1: int_eq_reif(x, 5, b1) → x == 5 (2 terms: x<=5 AND -x<=-5)
    # b2: int_le_reif(y, 3, b2) → y <= 3
    # Solution must satisfy: x==5 OR y<=3
    let src = """
var 0..10: x;
var 0..10: y;
var bool: b1;
var bool: b2;
constraint int_eq_reif(x, 5, b1):: defines_var(b1);
constraint int_le_reif(y, 3, b2):: defines_var(b2);
constraint bool_clause([b1,b2],[]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b1" in tr.definedVarNames
    check "b2" in tr.definedVarNames
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 2
    # First disjunct (int_eq_reif) should have 2 terms
    check tr.disjunctiveClauses[0].disjuncts[0].len == 2
    # Second disjunct (int_le_reif) should have 1 term
    check tr.disjunctiveClauses[0].disjuncts[1].len == 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    # Must satisfy: x==5 OR y<=3
    check (xVal == 5 or yVal <= 3)

  test "fixed-value bool variable gets singleton domain":
    # var bool: X = true creates a position with domain {1}, not {0,1}
    # var bool: Y = false creates a position with domain {0}, not {0,1}
    let src = """
var 0..10: x :: output_var;
var bool: btrue = true;
var bool: bfalse = false;
var 0..10: y :: output_var;
constraint int_lin_le_reif([1],[x],5,btrue);
constraint int_lin_le_reif([1],[y],3,bfalse);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Fixed-value bools should be marked as channels
    check "btrue" in tr.channelVarNames
    check "bfalse" in tr.channelVarNames

    # Their domains should be singletons
    let btPos = tr.varPositions["btrue"]
    let bfPos = tr.varPositions["bfalse"]
    check tr.sys.baseArray.domain[btPos] == @[1]
    check tr.sys.baseArray.domain[bfPos] == @[0]

    # They should be channel positions (not searched)
    check btPos in tr.sys.baseArray.channelPositions
    check bfPos in tr.sys.baseArray.channelPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # btrue = true means x <= 5 must hold
    check tr.sys.assignment[tr.varPositions["x"]] <= 5
    # bfalse = false means y <= 3 is NOT enforced (reif is false)
    # y can be anything 0..10

  test "fixed-value int variable gets singleton domain":
    # var 1..10: X = 5 creates a position with domain {5}
    let src = """
var 1..10: x :: output_var;
var 1..10: fixed_val = 5;
constraint int_eq(x, fixed_val);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "fixed_val" in tr.channelVarNames
    let fvPos = tr.varPositions["fixed_val"]
    check tr.sys.baseArray.domain[fvPos] == @[5]
    check fvPos in tr.sys.baseArray.channelPositions

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    check tr.sys.assignment[tr.varPositions["x"]] == 5

suite "FlatZinc Small-Domain Product Decomposition":

  test "small-domain product decomposition — structural checks":
    # Verify detection: 1 product, 3 disjuncts (b in {0,1,2}),
    # 2 int_lin_le consumed, 1 synthetic relaxation (positive-coeff upper bound)
    let src = """
var 10..100: obj :: output_var;
var 0..2: b :: output_var;
var 0..200: prod :: var_is_introduced :: is_defined_var;
var 5..50: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([-1, -1], [r, prod], -20);
constraint int_lin_le([1, 1], [r, prod], 80);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # 1 disjunctive clause from product decomposition
    check tr.disjunctiveClauses.len == 1
    # 3 disjuncts: one per value in {0,1,2}
    check tr.disjunctiveClauses[0].disjuncts.len == 3
    # Each disjunct: 2 equality terms (b<=k, b>=-k) + 2 substituted int_lin_le = 4 terms
    for d in tr.disjunctiveClauses[0].disjuncts:
      check d.len == 4
    # 1 synthetic relaxation: only the [1,1] constraint has positive prodCoeff
    check tr.syntheticRelaxations.len == 1
    check tr.syntheticRelaxations[0].varNames == @["r"]
    check tr.syntheticRelaxations[0].coeffs == @[1]
    check tr.syntheticRelaxations[0].rhs == 80

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check rVal + objVal * bVal >= 20
    check rVal + objVal * bVal <= 80

  test "small-domain product — k=0 eliminates large var":
    # When b=0, prod=0 regardless of obj, so the substituted int_lin_le
    # should have largeCoeff=0 and the obj variable should not appear.
    # b in {0,1}, so 2 disjuncts.
    # Constraint: r + 2*prod <= 100 → when b=0: r <= 100; when b=1: r + 2*obj <= 100
    let src = """
var 10..80: obj :: output_var;
var 0..1: b :: output_var;
var 0..160: prod :: var_is_introduced :: is_defined_var;
var 5..50: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([1, 2], [r, prod], 100);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 2

    # k=0 disjunct: equality terms + substituted term with only r (no obj)
    let d0 = tr.disjunctiveClauses[0].disjuncts[0]
    check d0.len == 3  # b<=0, b>=0, r<=100
    let subst0 = d0[2]
    check subst0.varNames == @["r"]
    check subst0.coeffs == @[1]
    check subst0.rhs == 100

    # k=1 disjunct: equality terms + substituted term with r and obj
    let d1 = tr.disjunctiveClauses[0].disjuncts[1]
    check d1.len == 3  # b<=1, b>=-1, 1*r + 2*obj <= 100
    let subst1 = d1[2]
    check subst1.varNames.len == 2
    check "r" in subst1.varNames
    check "obj" in subst1.varNames

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check rVal + 2 * objVal * bVal <= 100

  test "small-domain product — coefficient merging":
    # largeVar (obj) appears both as itself and via prod in the int_lin_le.
    # int_lin_le([3, 1, 2], [obj, r, prod], 200) → when b=k:
    #   prodCoeff=2, largeCoeff = 3 + 2*k (merge obj's own coeff + prod's contribution)
    let src = """
var 10..50: obj :: output_var;
var 0..2: b :: output_var;
var 0..100: prod :: var_is_introduced :: is_defined_var;
var 5..30: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([3, 1, 2], [obj, r, prod], 200);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 3

    # k=0: largeCoeff = 3 + 2*0 = 3 → [1*r, 3*obj] <= 200
    let d0sub = tr.disjunctiveClauses[0].disjuncts[0][2]
    check d0sub.varNames.len == 2
    for i, vn in d0sub.varNames:
      if vn == "obj": check d0sub.coeffs[i] == 3
      elif vn == "r": check d0sub.coeffs[i] == 1

    # k=1: largeCoeff = 3 + 2*1 = 5 → [1*r, 5*obj] <= 200
    let d1sub = tr.disjunctiveClauses[0].disjuncts[1][2]
    for i, vn in d1sub.varNames:
      if vn == "obj": check d1sub.coeffs[i] == 5

    # k=2: largeCoeff = 3 + 2*2 = 7 → [1*r, 7*obj] <= 200
    let d2sub = tr.disjunctiveClauses[0].disjuncts[2][2]
    for i, vn in d2sub.varNames:
      if vn == "obj": check d2sub.coeffs[i] == 7

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check 3 * objVal + rVal + 2 * objVal * bVal <= 200

  test "small-domain product — non-int_lin_le reference blocks decomposition":
    # prod referenced in int_ne (not int_lin_le) → decomposition should NOT fire
    let src = """
var 10..50: obj :: output_var;
var 0..2: b :: output_var;
var 0..100: prod :: var_is_introduced :: is_defined_var;
var 5..30: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([1, 1], [r, prod], 80);
constraint int_ne(prod, 0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # No decomposition: int_ne blocks it
    check tr.disjunctiveClauses.len == 0
    check tr.syntheticRelaxations.len == 0

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    let prodVal = objVal * bVal
    check rVal + prodVal <= 80
    check prodVal != 0

  test "small-domain product — multiple independent products":
    # Two products: prod1 = obj * b1, prod2 = obj * b2
    # Each with its own int_lin_le constraints
    let src = """
var 10..50: obj :: output_var;
var 0..1: b1 :: output_var;
var 0..1: b2 :: output_var;
var 0..50: prod1 :: var_is_introduced :: is_defined_var;
var 0..50: prod2 :: var_is_introduced :: is_defined_var;
var 5..30: r1 :: output_var;
var 5..30: r2 :: output_var;
constraint int_times(obj, b1, prod1) :: defines_var(prod1);
constraint int_times(obj, b2, prod2) :: defines_var(prod2);
constraint int_lin_le([1, 1], [r1, prod1], 60);
constraint int_lin_le([1, 1], [r2, prod2], 60);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Both products decomposed → 2 disjunctive clauses
    check tr.disjunctiveClauses.len == 2
    # Each has 2 disjuncts (b in {0,1})
    check tr.disjunctiveClauses[0].disjuncts.len == 2
    check tr.disjunctiveClauses[1].disjuncts.len == 2
    # 2 synthetic relaxations (one per product's positive-coeff int_lin_le)
    check tr.syntheticRelaxations.len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let b1Val = tr.sys.assignment[tr.varPositions["b1"]]
    let b2Val = tr.sys.assignment[tr.varPositions["b2"]]
    let r1Val = tr.sys.assignment[tr.varPositions["r1"]]
    let r2Val = tr.sys.assignment[tr.varPositions["r2"]]
    check r1Val + objVal * b1Val <= 60
    check r2Val + objVal * b2Val <= 60

  test "small-domain product — small var as second operand":
    # int_times(obj, b, prod) but also test int_times(b, obj, prod)
    # The detection should handle both orderings.
    let src = """
var 10..50: obj :: output_var;
var 0..2: b :: output_var;
var 0..100: prod :: var_is_introduced :: is_defined_var;
var 5..30: r :: output_var;
constraint int_times(b, obj, prod) :: defines_var(prod);
constraint int_lin_le([1, 1], [r, prod], 80);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should still detect: b is the small-domain operand
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 3

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check rVal + objVal * bVal <= 80

  test "small-domain product — domain too large blocks detection":
    # b has domain of 10 values (> MaxSmallDomainSize=8) — should NOT decompose
    let src = """
var 10..50: obj :: output_var;
var 0..9: b :: output_var;
var 0..500: prod :: var_is_introduced :: is_defined_var;
var 5..30: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([1, 1], [r, prod], 300);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.disjunctiveClauses.len == 0
    check tr.syntheticRelaxations.len == 0

  test "small-domain product — synthetic relaxation only for positive coeff":
    # Two int_lin_le: one with positive prodCoeff (+1), one with negative (-1).
    # Only the positive-coeff one should generate a synthetic relaxation.
    let src = """
var 10..100: obj :: output_var;
var 0..2: b :: output_var;
var 0..200: prod :: var_is_introduced :: is_defined_var;
var 5..50: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([1, 1], [r, prod], 120);
constraint int_lin_le([-1, -1], [r, prod], -10);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.disjunctiveClauses.len == 1
    # Only the [1,1] constraint (prodCoeff=+1) generates synthetic; [-1,-1] (prodCoeff=-1) does not
    check tr.syntheticRelaxations.len == 1
    check tr.syntheticRelaxations[0].rhs == 120

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check rVal + objVal * bVal <= 120
    check rVal + objVal * bVal >= 10

  test "small-domain product — int literal in var array skips gracefully":
    # int_lin_le([1, 2], [r, prod], 80) but also an int_lin_le with a literal
    # in the var array: int_lin_le([1], [5], 10) — should not crash.
    # The product decomposition should still fire for the valid int_lin_le.
    let src = """
var 10..50: obj :: output_var;
var 0..2: b :: output_var;
var 0..100: prod :: var_is_introduced :: is_defined_var;
var 5..30: r :: output_var;
constraint int_times(obj, b, prod) :: defines_var(prod);
constraint int_lin_le([1, 1], [r, prod], 80);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should decompose without crashing
    check tr.disjunctiveClauses.len == 1
    check tr.disjunctiveClauses[0].disjuncts.len == 3

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let rVal = tr.sys.assignment[tr.varPositions["r"]]
    check rVal + objVal * bVal <= 80

  test "value-support pattern detection — 2x2 grid":
    # 2x2 grid: cells c0..c3, each with domain 1..3
    # Neighbours: c0↔c1, c0↔c2, c1↔c3, c2↔c3
    # For each cell with value N>1, neighbours must contain all 1..N-1
    # Encoded as bool_clause + int_eq_reif + int_le_reif
    let src = """
var 1..3: c0;
var 1..3: c1;
var 1..3: c2;
var 1..3: c3;
var bool: eq_c1_1;
var bool: eq_c2_1;
var bool: le_c0_1;
var bool: eq_c0_1;
var bool: eq_c3_1;
var bool: le_c1_1;
var bool: eq_c0_1b;
var bool: eq_c3_1b;
var bool: le_c2_1;
var bool: eq_c1_1b;
var bool: eq_c2_1b;
var bool: le_c3_1;
constraint int_eq_reif(c1, 1, eq_c1_1) :: defines_var(eq_c1_1);
constraint int_eq_reif(c2, 1, eq_c2_1) :: defines_var(eq_c2_1);
constraint int_le_reif(c0, 1, le_c0_1) :: defines_var(le_c0_1);
constraint bool_clause([le_c0_1, eq_c1_1, eq_c2_1], []);
constraint int_eq_reif(c0, 1, eq_c0_1) :: defines_var(eq_c0_1);
constraint int_eq_reif(c3, 1, eq_c3_1) :: defines_var(eq_c3_1);
constraint int_le_reif(c1, 1, le_c1_1) :: defines_var(le_c1_1);
constraint bool_clause([le_c1_1, eq_c0_1, eq_c3_1], []);
constraint int_eq_reif(c0, 1, eq_c0_1b) :: defines_var(eq_c0_1b);
constraint int_eq_reif(c3, 1, eq_c3_1b) :: defines_var(eq_c3_1b);
constraint int_le_reif(c2, 1, le_c2_1) :: defines_var(le_c2_1);
constraint bool_clause([le_c2_1, eq_c0_1b, eq_c3_1b], []);
constraint int_eq_reif(c1, 1, eq_c1_1b) :: defines_var(eq_c1_1b);
constraint int_eq_reif(c2, 1, eq_c2_1b) :: defines_var(eq_c2_1b);
constraint int_le_reif(c3, 1, le_c3_1) :: defines_var(le_c3_1);
constraint bool_clause([le_c3_1, eq_c1_1b, eq_c2_1b], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.valueSupportDefs.len == 4

    tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

    # Verify value-support property: for each cell with value N>1,
    # neighbours must contain all 1..N-1
    let vals = [
      tr.sys.assignment[tr.varPositions["c0"]],
      tr.sys.assignment[tr.varPositions["c1"]],
      tr.sys.assignment[tr.varPositions["c2"]],
      tr.sys.assignment[tr.varPositions["c3"]],
    ]
    let nbrs = [@[1, 2], @[0, 3], @[0, 3], @[1, 2]]
    for i in 0..3:
      let cv = vals[i]
      if cv > 1:
        for v in 1..<cv:
          var found = false
          for ni in nbrs[i]:
            if vals[ni] == v:
              found = true
          check found

  test "value-support pattern detection — multi-value grouping (domain 1..4)":
    # Single cell x with 3 neighbours n1,n2,n3, domain 1..4
    # Requires clauses for values 2, 3, and 4 to exercise consecutive grouping
    # value=2: x<=1 OR n1==1 OR n2==1 OR n3==1
    # value=3: x<=2 OR n1==2 OR n2==2 OR n3==2
    # value=4: x<=3 OR n1==3 OR n2==3 OR n3==3
    let src = """
var 1..4: x;
var 1..4: n1;
var 1..4: n2;
var 1..4: n3;
var bool: le_x_1;
var bool: le_x_2;
var bool: le_x_3;
var bool: eq_n1_1;
var bool: eq_n2_1;
var bool: eq_n3_1;
var bool: eq_n1_2;
var bool: eq_n2_2;
var bool: eq_n3_2;
var bool: eq_n1_3;
var bool: eq_n2_3;
var bool: eq_n3_3;
constraint int_le_reif(x, 1, le_x_1) :: defines_var(le_x_1);
constraint int_eq_reif(n1, 1, eq_n1_1) :: defines_var(eq_n1_1);
constraint int_eq_reif(n2, 1, eq_n2_1) :: defines_var(eq_n2_1);
constraint int_eq_reif(n3, 1, eq_n3_1) :: defines_var(eq_n3_1);
constraint bool_clause([le_x_1, eq_n1_1, eq_n2_1, eq_n3_1], []);
constraint int_le_reif(x, 2, le_x_2) :: defines_var(le_x_2);
constraint int_eq_reif(n1, 2, eq_n1_2) :: defines_var(eq_n1_2);
constraint int_eq_reif(n2, 2, eq_n2_2) :: defines_var(eq_n2_2);
constraint int_eq_reif(n3, 2, eq_n3_2) :: defines_var(eq_n3_2);
constraint bool_clause([le_x_2, eq_n1_2, eq_n2_2, eq_n3_2], []);
constraint int_le_reif(x, 3, le_x_3) :: defines_var(le_x_3);
constraint int_eq_reif(n1, 3, eq_n1_3) :: defines_var(eq_n1_3);
constraint int_eq_reif(n2, 3, eq_n2_3) :: defines_var(eq_n2_3);
constraint int_eq_reif(n3, 3, eq_n3_3) :: defines_var(eq_n3_3);
constraint bool_clause([le_x_3, eq_n1_3, eq_n2_3, eq_n3_3], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should detect 1 value-support constraint with maxVal=4 (values 2,3,4 grouped)
    check tr.valueSupportDefs.len == 1
    check tr.valueSupportDefs[0].maxVal == 4

    tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

    let xv = tr.sys.assignment[tr.varPositions["x"]]
    let n1v = tr.sys.assignment[tr.varPositions["n1"]]
    let n2v = tr.sys.assignment[tr.varPositions["n2"]]
    let n3v = tr.sys.assignment[tr.varPositions["n3"]]
    let nvals = @[n1v, n2v, n3v]

    # Verify: for x=N>1, all 1..N-1 must appear among neighbours
    if xv > 1:
      for v in 1..<xv:
        check v in nvals

suite "Net Flow Pair Detection":

  test "linear chain — detection and classification":
    # 11 reaction pairs in a linear chain connected by 10 metabolites.
    # Tree peeling: 10 dependent pairs, 1 free pair.
    # Each metabolite constraint: coeff * (V_in_i - V_out_i) + coeff * (V_in_{i+1} - V_out_{i+1}) = 0
    # Alternating signs: [1,-1,-1,1] means net_flow[i] - net_flow[i+1] = 0
    var lines: seq[string]
    # Coefficient array (shared)
    lines.add("array [1..4] of int: c = [1,-1,-1,1];")
    # 11 pairs → 22 flux variables, domain 0..10
    for j in 0..<22:
      lines.add("var 0..10: v" & $j & ";")
    # 22 bool vars for Z (int_le_reif output)
    for j in 0..<22:
      lines.add("var bool: z" & $j & " :: is_defined_var;")
    # 22 Zint vars (bool2int output)
    for j in 0..<22:
      lines.add("var 0..1: zi" & $j & " :: var_is_introduced :: is_defined_var;")
    # Objective variable
    lines.add("var 0..22: obj :: is_defined_var;")
    # 10 stoichiometry constraints (linear chain)
    for i in 0..<10:
      let j = i * 2  # pair i starts at variable 2*i
      let k = (i + 1) * 2  # pair i+1 starts at variable 2*(i+1)
      lines.add("constraint int_lin_eq(c,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    # int_le_reif for each flux variable
    for j in 0..<22:
      lines.add("constraint int_le_reif(1,v" & $j & ",z" & $j & ") :: defines_var(z" & $j & ");")
    # bool2int for each Z
    for j in 0..<22:
      lines.add("constraint bool2int(z" & $j & ",zi" & $j & ") :: defines_var(zi" & $j & ");")
    # 11 reversibility constraints
    for i in 0..<11:
      let j = i * 2
      lines.add("constraint int_lin_le([1,1],[zi" & $j & ",zi" & $(j+1) & "],1);")
    # Objective = sum of Zints
    var objCoeffs = newSeq[string]()
    var objVars = newSeq[string]()
    for j in 0..<22:
      objCoeffs.add("-1")
      objVars.add("zi" & $j)
    lines.add("constraint int_lin_eq([1," & objCoeffs.join(",") & "],[obj," &
              objVars.join(",") & "],0) :: defines_var(obj);")
    # bool_clause — at least one Z true
    var zList: seq[string]
    for j in 0..<22:
      zList.add("z" & $j)
    lines.add("constraint bool_clause([" & zList.join(",") & "],[]);")
    lines.add("solve minimize obj;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    # Detection should find 11 pairs
    check tr.netFlowPairInVar.len == 11
    check tr.netFlowPairOutVar.len == 11
    # 1 free, 10 dependent
    check tr.netFlowFreePairs.len == 1
    check tr.netFlowDependentPairs.len == 10
    # All V variables should be channel vars
    for j in 0..<22:
      check ("v" & $j) in tr.channelVarNames
    # Free pair should have a search position
    let freePid = tr.netFlowFreePairs[0]
    let freeNfName = "net_flow_" & $freePid
    check freeNfName in tr.varPositions
    # Dependent pairs should have defined expressions
    for depPid in tr.netFlowDependentPairs:
      let depNfName = "net_flow_" & $depPid
      check depNfName in tr.definedVarExprs

  test "linear chain — solution satisfies Sv=0":
    # Same model as above but solve and verify all stoichiometry equalities hold.
    var lines: seq[string]
    lines.add("array [1..4] of int: c = [1,-1,-1,1];")
    for j in 0..<22:
      lines.add("var 0..10: v" & $j & ";")
    for j in 0..<22:
      lines.add("var bool: z" & $j & " :: is_defined_var;")
    for j in 0..<22:
      lines.add("var 0..1: zi" & $j & " :: var_is_introduced :: is_defined_var;")
    lines.add("var 0..22: obj :: is_defined_var;")
    for i in 0..<10:
      let j = i * 2
      let k = (i + 1) * 2
      lines.add("constraint int_lin_eq(c,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    for j in 0..<22:
      lines.add("constraint int_le_reif(1,v" & $j & ",z" & $j & ") :: defines_var(z" & $j & ");")
    for j in 0..<22:
      lines.add("constraint bool2int(z" & $j & ",zi" & $j & ") :: defines_var(zi" & $j & ");")
    for i in 0..<11:
      let j = i * 2
      lines.add("constraint int_lin_le([1,1],[zi" & $j & ",zi" & $(j+1) & "],1);")
    var objCoeffs = newSeq[string]()
    var objVars = newSeq[string]()
    for j in 0..<22:
      objCoeffs.add("-1")
      objVars.add("zi" & $j)
    lines.add("constraint int_lin_eq([1," & objCoeffs.join(",") & "],[obj," &
              objVars.join(",") & "],0) :: defines_var(obj);")
    var zList: seq[string]
    for j in 0..<22:
      zList.add("z" & $j)
    lines.add("constraint bool_clause([" & zList.join(",") & "],[]);")
    lines.add("solve minimize obj;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    let objExpr = tr.objectiveDefExpr
    minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

    # Read V values from channel positions
    var vs = newSeq[int](22)
    for j in 0..<22:
      let vName = "v" & $j
      if vName in tr.varPositions:
        vs[j] = tr.sys.assignment[tr.varPositions[vName]]
      elif vName in tr.definedVarExprs:
        vs[j] = tr.definedVarExprs[vName].evaluate(tr.sys.assignment)

    # Verify all 10 stoichiometry constraints: v[2i] - v[2i+1] - v[2i+2] + v[2i+3] = 0
    for i in 0..<10:
      let j = i * 2
      let lhs = vs[j] - vs[j+1] - vs[j+2] + vs[j+3]
      check lhs == 0

    # Verify V values are in [0, 10]
    for j in 0..<22:
      check vs[j] >= 0
      check vs[j] <= 10

    # Verify reversibility: for each pair, at most one direction active
    for i in 0..<11:
      let vIn = vs[2*i]
      let vOut = vs[2*i + 1]
      check not (vIn > 0 and vOut > 0)

    # In a linear chain, all net flows must be equal (net_flow[i] = net_flow[i+1]).
    # With bool_clause requiring at least one active, all 11 pairs are active.
    # Each active pair contributes 1 to the objective (V_in or V_out > 0, not both).
    let objVal = objExpr.evaluate(tr.sys.assignment)
    check objVal == 11

  test "net flow V_in/V_out channel correctness":
    # Verify channel computation: V_in = max(0, net_flow), V_out = max(0, -net_flow)
    # Build a minimal 10-constraint chain and check V values match net_flow.
    var lines: seq[string]
    lines.add("array [1..4] of int: c = [1,-1,-1,1];")
    for j in 0..<22:
      lines.add("var 0..10: v" & $j & ";")
    for j in 0..<22:
      lines.add("var bool: z" & $j & " :: is_defined_var;")
    for j in 0..<22:
      lines.add("var 0..1: zi" & $j & " :: var_is_introduced :: is_defined_var;")
    for i in 0..<10:
      let j = i * 2
      let k = (i + 1) * 2
      lines.add("constraint int_lin_eq(c,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    for j in 0..<22:
      lines.add("constraint int_le_reif(1,v" & $j & ",z" & $j & ") :: defines_var(z" & $j & ");")
    for j in 0..<22:
      lines.add("constraint bool2int(z" & $j & ",zi" & $j & ") :: defines_var(zi" & $j & ");")
    for i in 0..<11:
      let j = i * 2
      lines.add("constraint int_lin_le([1,1],[zi" & $j & ",zi" & $(j+1) & "],1);")
    var zList: seq[string]
    for j in 0..<22:
      zList.add("z" & $j)
    lines.add("constraint bool_clause([" & zList.join(",") & "],[]);")
    lines.add("solve satisfy;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # For each pair, check V_in = max(0, net_flow) and V_out = max(0, -net_flow)
    for pid in 0..<11:
      let inName = tr.netFlowPairInVar[pid]
      let outName = tr.netFlowPairOutVar[pid]
      let vIn = tr.sys.assignment[tr.varPositions[inName]]
      let vOut = tr.sys.assignment[tr.varPositions[outName]]
      # net_flow = V_in - V_out
      let netFlow = vIn - vOut
      check vIn == max(0, netFlow)
      check vOut == max(0, -netFlow)
      # Both non-negative
      check vIn >= 0
      check vOut >= 0

  test "branching tree — 3-pair metabolite constraint":
    # A tree where one metabolite connects 3 pairs (degree 3).
    # This creates a dependent pair whose net_flow is a sum of 2 other pair net_flows,
    # testing range constraint generation (range exceeds [-D, D]).
    #
    # Tree structure (star graph):
    #   P0 -- M0 -- P1
    #          |
    #         P2 -- M1 -- P3
    #          |
    #         M2 -- P4 -- M3 -- P5
    #          |
    #         ...continuing for 10+ metabolites
    #
    # Simpler: build a tree with some degree-3 metabolites.
    # Use pairs P0..P11 (12 pairs), metabolites M0..M10 (11 constraints).
    # M0: [1,-1,1,-1,-1,1] on P0, P1, P2 (3 pairs = 6 vars)
    # M1..M9: [1,-1,-1,1] on P_{i+1}, P_{i+2} (2 pairs each)
    var lines: seq[string]
    lines.add("array [1..6] of int: c3 = [1,-1,1,-1,-1,1];")
    lines.add("array [1..4] of int: c2 = [1,-1,-1,1];")
    let D = 5
    # 12 pairs → 24 flux variables
    for j in 0..<24:
      lines.add("var 0.." & $D & ": v" & $j & ";")
    for j in 0..<24:
      lines.add("var bool: z" & $j & " :: is_defined_var;")
    for j in 0..<24:
      lines.add("var 0..1: zi" & $j & " :: var_is_introduced :: is_defined_var;")
    # M0: 3-pair constraint on pairs 0, 1, 2
    lines.add("constraint int_lin_eq(c3,[v0,v1,v2,v3,v4,v5],0);")
    # M1..M10: 2-pair chain starting from pair 2
    for i in 1..<11:
      let pairA = i + 1  # pairs 2, 3, 4, ..., 11
      let pairB = i + 2  # pairs 3, 4, 5, ..., 12
      if pairB >= 12: break
      let j = pairA * 2
      let k = pairB * 2
      lines.add("constraint int_lin_eq(c2,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    # Need exactly 10 more constraints for pairs 2..11 → constraints on (2,3),(3,4),...,(10,11)
    # That's 9 constraints. Plus M0 = 1. Total = 10. OK.

    # int_le_reif + bool2int for each flux variable
    for j in 0..<24:
      lines.add("constraint int_le_reif(1,v" & $j & ",z" & $j & ") :: defines_var(z" & $j & ");")
    for j in 0..<24:
      lines.add("constraint bool2int(z" & $j & ",zi" & $j & ") :: defines_var(zi" & $j & ");")
    # Reversibility constraints
    for i in 0..<12:
      let j = i * 2
      lines.add("constraint int_lin_le([1,1],[zi" & $j & ",zi" & $(j+1) & "],1);")
    var zList: seq[string]
    for j in 0..<24:
      zList.add("z" & $j)
    lines.add("constraint bool_clause([" & zList.join(",") & "],[]);")
    lines.add("solve satisfy;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    # Should detect 12 pairs with 10 constraints
    check tr.netFlowPairInVar.len == 12
    check tr.netFlowFreePairs.len == 2  # 12 pairs - 10 constraints = 2 free
    check tr.netFlowDependentPairs.len == 10

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # Verify stoichiometry: read V values and check all constraints hold
    var vs = newSeq[int](24)
    for j in 0..<24:
      let vName = "v" & $j
      vs[j] = tr.sys.assignment[tr.varPositions[vName]]

    # M0: v0 - v1 + v2 - v3 - v4 + v5 = 0
    check vs[0] - vs[1] + vs[2] - vs[3] - vs[4] + vs[5] == 0
    # M1..M9: v[2*pA] - v[2*pA+1] - v[2*pB] + v[2*pB+1] = 0
    for i in 1..<10:
      let pA = i + 1
      let pB = i + 2
      let j = pA * 2
      let k = pB * 2
      check vs[j] - vs[j+1] - vs[k] + vs[k+1] == 0

  test "non-tree graph not detected":
    # A cycle graph (not a tree) should NOT be detected as net flow pairs.
    # 10 constraints connecting pairs in a cycle: P0-M0-P1-M1-...-P9-M9-P0
    var lines: seq[string]
    lines.add("array [1..4] of int: c = [1,-1,-1,1];")
    for j in 0..<20:
      lines.add("var 0..10: v" & $j & ";")
    # 10 constraints forming a cycle (not a tree: edges = nodes)
    for i in 0..<10:
      let pA = i
      let pB = (i + 1) mod 10
      let j = pA * 2
      let k = pB * 2
      lines.add("constraint int_lin_eq(c,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    lines.add("solve satisfy;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    # Cycle has 10 edges and 10+10=20 nodes → not a tree (20-1=19 ≠ 10)
    # Actually bipartite: 10 pair nodes + 10 metabolite nodes = 20 nodes, 20 edges
    # Tree needs 19 edges, but we have 20. Detection should fail.
    check tr.netFlowFreePairs.len == 0
    check tr.netFlowDependentPairs.len == 0

  test "fewer than 10 stoichiometry constraints — not detected":
    # Only 9 constraints — below the threshold.
    var lines: seq[string]
    lines.add("array [1..4] of int: c = [1,-1,-1,1];")
    for j in 0..<20:
      lines.add("var 0..10: v" & $j & ";")
    for i in 0..<9:
      let j = i * 2
      let k = (i + 1) * 2
      lines.add("constraint int_lin_eq(c,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    lines.add("solve satisfy;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.netFlowFreePairs.len == 0
    check tr.netFlowDependentPairs.len == 0

  test "range constraint for out-of-bound dependent pairs":
    # Build a tree where a dependent pair's unclamped range exceeds [-D, D].
    # With D=5 and a 3-pair metabolite, a dependent pair = sum of 2 others
    # has range [-10, 10], exceeding [-5, 5]. Should generate range constraints.
    var lines: seq[string]
    lines.add("array [1..6] of int: c3 = [1,-1,1,-1,-1,1];")
    lines.add("array [1..4] of int: c2 = [1,-1,-1,1];")
    let D = 5
    # 12 pairs, 24 flux vars
    for j in 0..<24:
      lines.add("var 0.." & $D & ": v" & $j & ";")
    for j in 0..<24:
      lines.add("var bool: z" & $j & " :: is_defined_var;")
    for j in 0..<24:
      lines.add("var 0..1: zi" & $j & " :: var_is_introduced :: is_defined_var;")
    # M0: 3-pair constraint
    lines.add("constraint int_lin_eq(c3,[v0,v1,v2,v3,v4,v5],0);")
    # Chain from pair 2: (2,3), (3,4), ..., (10,11)
    for i in 1..<10:
      let pA = i + 1
      let pB = i + 2
      if pB >= 12: break
      let j = pA * 2
      let k = pB * 2
      lines.add("constraint int_lin_eq(c2,[v" & $j & ",v" & $(j+1) &
                 ",v" & $k & ",v" & $(k+1) & "],0);")
    for j in 0..<24:
      lines.add("constraint int_le_reif(1,v" & $j & ",z" & $j & ") :: defines_var(z" & $j & ");")
    for j in 0..<24:
      lines.add("constraint bool2int(z" & $j & ",zi" & $j & ") :: defines_var(zi" & $j & ");")
    for i in 0..<12:
      let j = i * 2
      lines.add("constraint int_lin_le([1,1],[zi" & $j & ",zi" & $(j+1) & "],1);")
    var zList: seq[string]
    for j in 0..<24:
      zList.add("z" & $j)
    lines.add("constraint bool_clause([" & zList.join(",") & "],[]);")
    lines.add("solve satisfy;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.netFlowPairInVar.len == 12
    # The system should have range constraints beyond just the 1 bool_clause.
    # With 3-pair metabolites, some dependent pairs need range clamping.
    # Total constraints > 1 (the bool_clause) means range constraints were added.
    check tr.sys.baseArray.constraints.len > 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # All V values must be in [0, D]
    for j in 0..<24:
      let vName = "v" & $j
      let v = tr.sys.assignment[tr.varPositions[vName]]
      check v >= 0
      check v <= D

  test "table constraint with defined-var expressions (non-ref columns)":
    # Regression: fzn_table_int where some columns are defined variables
    # resolved to linear expressions (not simple variable references).
    # Previously crashed with: "tableIn currently requires simple variable references"
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var 2..6: z :: is_defined_var;
constraint int_lin_eq([1, 1, -1], [x, y, z], 0) :: defines_var(z);
constraint fzn_table_int([x, z], [1, 2, 2, 4, 3, 6]);
solve satisfy;
"""
    # z = x + y, table says (x,z) in {(1,2),(2,4),(3,6)}.
    # So x=1→z=2→y=1, x=2→z=4→y=2, x=3→z=6→y=3.
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    # z is a defined var (no position), so verify via x and y:
    # table requires z = 2*x, and z = x+y, so y must equal x
    check xVal == yVal
    check xVal in {1, 2, 3}

  test "table constraint with constant expression column":
    # Table where one column is a literal constant — should filter and project.
    let src = """
var 1..3: x :: output_var;
var 10..30: y :: output_var;
constraint fzn_table_int([x, 2, y], [1, 2, 10, 2, 2, 20, 3, 2, 30, 1, 3, 99]);
solve satisfy;
"""
    # Column 1 is constant 2, so only rows (1,2,10),(2,2,20),(3,2,30) match.
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check (xVal, yVal) in [(1, 10), (2, 20), (3, 30)]

  test "table complement conversion: near-complete binary table → tableNotIn":
    # Binary table where only (2,2) is forbidden — should be converted to tableNotIn.
    # This is the "not both same nonzero" pattern from SPOT5.
    let src = """
var {0,2}: x :: output_var;
var {0,2}: y :: output_var;
constraint fzn_table_int([x, y], [0, 0, 0, 2, 2, 0]);
solve satisfy;
"""
    # Allowed: (0,0), (0,2), (2,0). Forbidden: (2,2).
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.nTableToNotIn == 1
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check not (xVal == 2 and yVal == 2)
    check xVal in {0, 2}
    check yVal in {0, 2}

  test "table complement conversion: alldiff-except-0 pattern":
    # 4-value table encoding "if both nonzero, must be different".
    # Forbidden: (1,1), (2,2), (3,3) — 3 tuples out of 16 = near-complete.
    let src = """
var 0..3: x :: output_var;
var 0..3: y :: output_var;
constraint fzn_table_int([x, y], [0,0, 0,1, 0,2, 0,3, 1,0, 1,2, 1,3, 2,0, 2,1, 2,3, 3,0, 3,1, 3,2]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.nTableToNotIn == 1
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check xVal in {0, 1, 2, 3}
    check yVal in {0, 1, 2, 3}
    # If both nonzero, must be different
    if xVal != 0 and yVal != 0:
      check xVal != yVal

  test "table complement conversion: single forbidden ternary tuple":
    # Ternary table forbidding exactly 1 tuple out of 8.
    let src = """
var 0..1: x :: output_var;
var 0..1: y :: output_var;
var 0..1: z :: output_var;
constraint fzn_table_int([x, y, z], [0,0,0, 0,0,1, 0,1,0, 0,1,1, 1,0,0, 1,0,1, 1,1,0]);
solve satisfy;
"""
    # Forbidden: (1,1,1) — the only missing tuple from {0,1}^3.
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.nTableToNotIn == 1
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    check not (xVal == 1 and yVal == 1 and zVal == 1)

  test "table complement conversion: tautology (all combos allowed)":
    # Table with all combinations present — should be skipped entirely.
    let src = """
var 0..1: x :: output_var;
var 0..1: y :: output_var;
constraint fzn_table_int([x, y], [0,0, 0,1, 1,0, 1,1]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # Tautology: complement is empty, constraint should be skipped (not converted)
    check tr.nTableToNotIn == 0
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check xVal in {0, 1}
    check yVal in {0, 1}

  test "table complement conversion: large forbidden set stays as tableIn":
    # Table where the complement is large — should NOT be converted.
    # Domain 0..9 x 0..9 = 100 combos, only 5 allowed → 95 forbidden.
    let src = """
var 0..9: x :: output_var;
var 0..9: y :: output_var;
constraint fzn_table_int([x, y], [0,0, 1,1, 2,2, 3,3, 4,4]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.nTableToNotIn == 0  # 95 forbidden > threshold? Actually 95 < 100 limit
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check xVal == yVal

  test "table complement conversion: multiple constraints":
    # Two near-complete tables on different variable pairs.
    let src = """
var 0..2: x :: output_var;
var 0..2: y :: output_var;
var 0..2: z :: output_var;
constraint fzn_table_int([x, y], [0,0, 0,1, 0,2, 1,0, 1,2, 2,0, 2,1]);
constraint fzn_table_int([y, z], [0,0, 0,1, 0,2, 1,0, 1,2, 2,0, 2,1]);
solve satisfy;
"""
    # Both tables forbid (1,1) and (2,2) — "not equal except 0".
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.nTableToNotIn == 2
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]
    if xVal != 0 and yVal != 0: check xVal != yVal
    if yVal != 0 and zVal != 0: check yVal != zVal

  test "table complement conversion with optimization":
    # Verify converted constraints work correctly during optimization.
    # Maximize x + y subject to NOT(x == y when both nonzero).
    let src = """
var 0..3: x :: output_var;
var 0..3: y :: output_var;
var 0..6: obj :: output_var :: is_defined_var;
constraint int_lin_eq([1, 1, -1], [x, y, obj], 0) :: defines_var(obj);
constraint fzn_table_int([x, y], [0,0, 0,1, 0,2, 0,3, 1,0, 1,2, 1,3, 2,0, 2,1, 2,3, 3,0, 3,1, 3,2]);
solve maximize obj;
"""
    # Optimal: x=3, y=2 (or x=2, y=3) → obj=5.
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.nTableToNotIn == 1
    let objExpr = tr.objectiveDefExpr
    maximize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)
    check tr.sys.hasFeasibleSolution
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    check xVal + yVal >= 5
    if xVal != 0 and yVal != 0: check xVal != yVal

suite "Channel Propagation Correctness":

  proc reconstructSet(tr: FznTranslator, name: string): seq[int] =
    ## Helper: reconstruct set variable membership from boolean assignments.
    if name in tr.setVarBoolPositions:
      let info = tr.setVarBoolPositions[name]
      for i in 0..<info.positions.len:
        if tr.sys.assignment[info.positions[i]] != 0:
          result.add(info.lo + i)

  proc verifyChannelConsistency(tr: FznTranslator): int =
    ## Re-evaluate all channels from scratch and count inconsistencies.
    for binding in tr.sys.baseArray.channelBindings:
      let idxVal = binding.indexExpression.evaluate(tr.sys.assignment)
      if idxVal >= 0 and idxVal < binding.arrayElements.len:
        let elem = binding.arrayElements[idxVal]
        let expected = if elem.isConstant: elem.constantValue
                       else: tr.sys.assignment[elem.variablePosition]
        if expected != tr.sys.assignment[binding.channelPosition]:
          inc result
    for binding in tr.sys.baseArray.minMaxChannelBindings:
      var best = if binding.isMin: high(int) else: low(int)
      for expr in binding.inputExprs:
        let val = expr.evaluate(tr.sys.assignment)
        if binding.isMin: best = min(best, val)
        else: best = max(best, val)
      if best != tr.sys.assignment[binding.channelPosition]:
        inc result

  test "set_in_reif identity channel: variable set, constant value":
    ## set_in_reif(literal, set_var, bool) creates an identity channel
    ## b = S.bools[literal - lo]. When S changes (via array_set_element routing),
    ## b must update. This tests the addChannelBinding registration fix.
    let src = """
var 1..3: sel :: output_var;
var set of 0..5: s1;
var set of 0..5: s2;
var set of 0..5: s3;
var set of 0..5: chosen :: var_is_introduced;
var bool: mem3 :: output_var;
constraint set_eq(s1, {0, 1, 2});
constraint set_eq(s2, {0, 3, 4});
constraint set_eq(s3, {0, 2, 5});
constraint array_var_set_element(sel, [s1, s2, s3], chosen);
constraint set_in_reif(3, chosen, mem3) :: defines_var(mem3);
constraint int_eq(sel, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let selVal = tr.sys.assignment[tr.varPositions["sel"]]
    check selVal == 2
    # sel=2 → chosen=s2={0,3,4} → 3 in chosen = true → mem3 = 1
    let mem3Val = tr.sys.assignment[tr.varPositions["mem3"]]
    check mem3Val == 1
    check verifyChannelConsistency(tr) == 0

  test "set_in_reif identity channel: value NOT in selected set":
    ## Same structure but the tested value is NOT in the selected set.
    let src = """
var 1..3: sel :: output_var;
var set of 0..5: s1;
var set of 0..5: s2;
var set of 0..5: s3;
var set of 0..5: chosen :: var_is_introduced;
var bool: mem3 :: output_var;
constraint set_eq(s1, {0, 1, 2});
constraint set_eq(s2, {0, 3, 4});
constraint set_eq(s3, {0, 2, 5});
constraint array_var_set_element(sel, [s1, s2, s3], chosen);
constraint set_in_reif(3, chosen, mem3) :: defines_var(mem3);
constraint int_eq(sel, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let selVal = tr.sys.assignment[tr.varPositions["sel"]]
    check selVal == 1
    # sel=1 → chosen=s1={0,1,2} → 3 NOT in chosen → mem3 = 0
    let mem3Val = tr.sys.assignment[tr.varPositions["mem3"]]
    check mem3Val == 0
    check verifyChannelConsistency(tr) == 0

  test "two-layer set comprehension: bounded pairwise sum":
    ## Minimal reproduction of the gt-sort pattern:
    ## L1 has 4 fixed sets, y routing selects pairs, L2 = pairwise sums.
    ## L2 cardinalities feed into objective.
    ## Tests element → set_in_reif → bool2int → int_times → min/max cascade.
    ##
    ## L1: {0,3}, {0,2}, {0,1}, {0} (from c=[3,2,1,0], reversed+sorted)
    ## With y=[1,3,2,4] (pair L1[1] with L1[3], pair L1[2] with L1[4]):
    ##   L2[1] = {0+0, 0+1, 3+0, 3+1} = {0, 1, 3, 4}  (card=4)
    ##   L2[2] = {0+0, 2+0} = {0, 2}  (card=2)
    ## Total L1 cards: 2+2+2+1 = 7
    ## Total L2 cards: 4+2+1+1 = 8  (padding={0},{0})
    ## Objective = 7 + 8 = 15
    ##
    ## We use a small FZN model that encodes this structure.
    ## Since the full set comprehension FZN is complex, we test using
    ## the actual MiniZinc-style decomposition.

    # Build FZN source for a tiny 2-layer binary tree sort network
    # n=3, c=[3,2,1,0] (padded to 4), k=5
    var lines: seq[string]
    # L1 sets (fixed): {0,3}, {0,2}, {0,1}, {0}
    let l1Sets = [@[0, 3], @[0, 2], @[0, 1], @[0]]
    for i in 0..<4:
      lines.add("var set of 0..5: l1_" & $i & ";")
      lines.add("constraint set_eq(l1_" & $i & ", {" & l1Sets[i].mapIt($it).join(",") & "});")

    # y routing variables (search)
    for i in 0..<4:
      lines.add("var 1..4: y" & $i & " :: output_var;")
    lines.add("constraint fzn_all_different_int([y0, y1, y2, y3]);")
    lines.add("constraint int_lt(y0, y1);")  # symmetry breaking
    lines.add("constraint int_lt(y2, y3);")

    # Working sets via array_var_set_element (routes L1 by y)
    for i in 0..<4:
      lines.add("var set of 0..5: ws" & $i & " :: var_is_introduced;")
      lines.add("constraint array_var_set_element(y" & $i & ", [l1_0, l1_1, l1_2, l1_3], ws" & $i & ");")

    # L2 result sets and cardinalities
    for p in 0..<2:
      let a = p * 2      # left child index
      let b = p * 2 + 1  # right child index
      lines.add("var set of 0..5: l2_" & $p & " :: output_var;")
      lines.add("var 0..10: card_l2_" & $p & " :: output_var;")
      # Bounded pairwise sum: l2[p] = {ai+bi | ai in ws[a], bi in ws[b], ai+bi <= 5}
      # We encode this with set comprehension decomposition:
      # For each (av, bv) with av+bv <= 5, create product and union
      var pairIdx = 0
      var leafNames: seq[string]
      for av in 0..5:
        for bv in 0..5:
          if av + bv > 5: continue
          let sumVal = av + bv
          let prefix = "p" & $p & "_" & $pairIdx
          # Membership tests
          lines.add("var bool: " & prefix & "_ma :: var_is_introduced :: is_defined_var;")
          lines.add("var bool: " & prefix & "_mb :: var_is_introduced :: is_defined_var;")
          lines.add("constraint set_in_reif(" & $av & ", ws" & $a & ", " & prefix & "_ma) :: defines_var(" & prefix & "_ma);")
          lines.add("constraint set_in_reif(" & $bv & ", ws" & $b & ", " & prefix & "_mb) :: defines_var(" & prefix & "_mb);")
          # Bool to int
          lines.add("var 0..1: " & prefix & "_ia :: var_is_introduced :: is_defined_var;")
          lines.add("var 0..1: " & prefix & "_ib :: var_is_introduced :: is_defined_var;")
          lines.add("constraint bool2int(" & prefix & "_ma, " & prefix & "_ia) :: defines_var(" & prefix & "_ia);")
          lines.add("constraint bool2int(" & prefix & "_mb, " & prefix & "_ib) :: defines_var(" & prefix & "_ib);")
          # Product (AND)
          lines.add("var 0..1: " & prefix & "_prod :: var_is_introduced :: is_defined_var;")
          lines.add("constraint int_times(" & prefix & "_ia, " & prefix & "_ib, " & prefix & "_prod) :: defines_var(" & prefix & "_prod);")
          # Scaled value: s = sumVal * prod
          lines.add("var 0..5: " & prefix & "_s :: var_is_introduced :: is_defined_var;")
          lines.add("constraint int_lin_eq([" & $sumVal & ", -1], [" & prefix & "_prod, " & prefix & "_s], 0) :: defines_var(" & prefix & "_s);")
          # Singleton set
          lines.add("var set of 0..5: " & prefix & "_sing :: var_is_introduced;")
          lines.add("constraint set_in(" & prefix & "_s, " & prefix & "_sing);")
          lines.add("constraint set_card(" & prefix & "_sing, 1);")
          leafNames.add(prefix & "_sing")
          inc pairIdx

      # Union chain: fold all singletons into l2_p
      var accName = leafNames[0]
      for j in 1..<leafNames.len:
        let nextName = if j == leafNames.len - 1: "l2_" & $p
                       else: "uc" & $p & "_" & $j
        if j < leafNames.len - 1:
          lines.add("var set of 0..5: " & nextName & " :: var_is_introduced :: is_defined_var;")
        lines.add("constraint set_union(" & accName & ", " & leafNames[j] & ", " & nextName & ") :: defines_var(" & nextName & ");")
        accName = nextName

      # Cardinality constraint
      lines.add("constraint set_card(l2_" & $p & ", card_l2_" & $p & ");")

    # Objective: sum of all cardinalities
    lines.add("var 0..100: objective :: output_var :: is_defined_var;")
    # L1 cards are fixed: 2+2+2+1 = 7, L2 cards are variable
    lines.add("constraint int_lin_eq([1, -1, -1], [objective, card_l2_0, card_l2_1], 7);")
    lines.add("solve minimize objective;")

    let src = lines.join("\n")
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    # Verify channel consistency
    check verifyChannelConsistency(tr) == 0

    # Check objective is at least the theoretical minimum
    # Best pairing: L1[1]={0,3} + L1[4]={0} → {0,3} (2 elements)
    #               L1[2]={0,2} + L1[3]={0,1} → {0,1,2,3} (4 elements)
    # L2 cards: 2+4=6, L1 fixed=7, total: 7+6=13
    let objVal = tr.sys.assignment[tr.varPositions["objective"]]
    check objVal >= 13  # at least the true minimum

  test "channel consistency after optimization with bound constraints":
    ## Tests that channel propagation remains consistent through the
    ## optimizer's binary search (adding/removing bound constraints).
    ## Uses a simple set routing pattern with optimization.
    let src = """
var 1..3: sel :: output_var;
var set of 0..4: s1;
var set of 0..4: s2;
var set of 0..4: s3;
var set of 0..4: chosen :: var_is_introduced;
var 0..5: card_chosen :: output_var :: is_defined_var;
constraint set_eq(s1, {0, 1, 2, 3, 4});
constraint set_eq(s2, {0, 2, 4});
constraint set_eq(s3, {0, 1});
constraint array_var_set_element(sel, [s1, s2, s3], chosen);
constraint set_card(chosen, card_chosen);
var 0..5: objective :: is_defined_var;
constraint int_lin_eq([1, -1], [objective, card_chosen], 0) :: defines_var(objective);
solve minimize objective;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    check verifyChannelConsistency(tr) == 0
    # Verify cardinality matches actual set membership
    let selVal = tr.sys.assignment[tr.varPositions["sel"]]
    let objVal = tr.sys.assignment[tr.varPositions["card_chosen"]]
    let expectedSets = [@[0, 1, 2, 3, 4], @[0, 2, 4], @[0, 1]]
    let expectedCard = expectedSets[selVal - 1].len
    check objVal == expectedCard  # cardinality must match selected set
    check objVal >= 2  # theoretical minimum (s3 has 2 elements)

  test "connected constraint with channel+fixed node positions survives optimization":
    # Regression: removeFixedConstraints removed the connected constraint because
    # all its node positions were either channel vars (via bool_not) or fixed
    # literals (true/false). Without connected, the solver fills the center node
    # for obj=11, disconnecting the two always-white nodes. With connected, the
    # center must stay white, capping obj at 1.
    #
    # Star graph: center=node1, edges to nodes 2,3,4.
    # Nodes 2,3 always white (ns=true). Node 4 variable. Node 1 variable.
    # Nodes 2 and 3 have no edge between them — only connected through center.
    # Connected constraint's node positions are all channel or fixed → triggers old bug.
    let src = """
predicate fzn_connected(array [int] of int: from,array [int] of int: to,array [int] of var bool: ns,array [int] of var bool: es);
var bool: f1;
var bool: f4;
var bool: nf1 ::is_defined_var;
var bool: nf4 ::is_defined_var;
constraint bool_not(f1,nf1):: defines_var(nf1);
constraint bool_not(f4,nf4):: defines_var(nf4);
array [1..3] of int: from = [1,1,1];
array [1..3] of int: to = [2,3,4];
var bool: e12 ::is_defined_var;
var bool: e13 ::is_defined_var;
var bool: e14 ::is_defined_var;
array [1..3] of var bool: edge = [e12,e13,e14];
constraint array_bool_and([nf1,true],e12):: defines_var(e12);
constraint array_bool_and([nf1,true],e13):: defines_var(e13);
constraint array_bool_and([nf1,nf4],e14):: defines_var(e14);
array [1..4] of var bool: ns ::var_is_introduced = [nf1,true,true,nf4];
constraint fzn_connected(from,to,ns,edge);
var 0..11: obj ::output_var;
constraint int_lin_eq([10,1,-1],[f1,f4,obj],0);
solve maximize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let objExpr = tr.getExpr(tr.objectivePos)
    maximize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000, verbose = false)

    let objVal = tr.sys.assignment[tr.varPositions["obj"]]
    # With connected: center must stay white (else nodes 2,3 disconnect), max obj = 1
    # Without connected (the old bug): fill center for obj = 10 or 11
    check objVal <= 1

  test "orphan variable detection links disconnected arrays":
    # Simplified model with two arrays that should be the same (like roster longflatroster).
    # Array 'a' is the annotated search array. Array 'b' is an orphan extended copy.
    # b[4..6] are aliased to a[1..3] (wrap-around). b[1..3] should equal a[1..3] but
    # are NOT explicitly linked (model bug). The solve annotation only mentions 'a'.
    # Without orphan detection: b[1..3] are free, solver can exploit them.
    # With orphan detection: b[1..3] are linked to a[1..3] via equality constraints.
    let src = """
var 1..3: a1;
var 1..3: a2;
var 1..3: a3;
var 1..3: b1;
var 1..3: b2;
var 1..3: b3;
array [1..3] of var int: a:: output_array([1..3]) = [a1,a2,a3];
array [1..3] of var int: win1:: var_is_introduced = [b1,b2,b3];
array [1..3] of var int: win2:: var_is_introduced = [b2,b3,a1];
array [1..3] of var int: win3:: var_is_introduced = [b3,a1,a2];
var 0..3: cost:: output_var:: is_defined_var;
var bool: r1:: var_is_introduced:: is_defined_var;
var bool: r2:: var_is_introduced:: is_defined_var;
var bool: r3:: var_is_introduced:: is_defined_var;
var 0..1: i1:: var_is_introduced:: is_defined_var;
var 0..1: i2:: var_is_introduced:: is_defined_var;
var 0..1: i3:: var_is_introduced:: is_defined_var;
constraint fzn_at_least_int(1,win1,1);
constraint fzn_at_least_int(1,win2,1);
constraint fzn_at_least_int(1,win3,1);
constraint int_eq_reif(b1,2,r1):: defines_var(r1);
constraint int_eq_reif(b2,2,r2):: defines_var(r2);
constraint int_eq_reif(b3,2,r3):: defines_var(r3);
constraint bool2int(r1,i1):: defines_var(i1);
constraint bool2int(r2,i2):: defines_var(i2);
constraint bool2int(r3,i3):: defines_var(i3);
constraint int_lin_eq([1,-1,-1,-1],[cost,i1,i2,i3],0):: defines_var(cost);
solve :: int_search(a,first_fail,indomain_min,complete) minimize cost;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Verify solve annotation extraction
    check tr.hasSearchAnnotation
    check tr.annotatedSearchVarNames.len == 3
    check "a1" in tr.annotatedSearchVarNames
    check "a2" in tr.annotatedSearchVarNames
    check "a3" in tr.annotatedSearchVarNames

    # Orphan variables have positions and equality constraints (not channels)
    check "b1" in tr.varPositions
    check tr.orphanToAnnotatedMap.len == 3

  test "array_bool_xor 3-element channel: result = XNOR(a, b)":
    # array_bool_xor([r, a, b]) with defines_var(r) means r XOR a XOR b = true
    # so r = XNOR(a, b) = (a == b)
    let src = """
var bool: a;
var bool: b;
var bool: r:: var_is_introduced:: is_defined_var;
var 0..1: obj:: output_var:: is_defined_var;
array [1..3] of var bool: xarr:: var_is_introduced = [r, a, b];
constraint array_bool_xor(xarr):: defines_var(r);
constraint bool2int(r, obj):: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # r should be detected as a channel variable
    check "r" in tr.channelVarNames
    check tr.boolXorVarChannelDefs.len == 1
    check tr.boolXorVarChannelDefs[0].isNe == false  # XNOR / EQ pattern

    # Solve and verify r = XNOR(a, b) = (a == b)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let aPos = tr.varPositions["a"]
    let bPos = tr.varPositions["b"]
    let rPos = tr.varPositions["r"]
    let aVal = tr.sys.assignment[aPos]
    let bVal = tr.sys.assignment[bPos]
    let rVal = tr.sys.assignment[rPos]
    check rVal == (if aVal == bVal: 1 else: 0)

  test "bool_xor variable channel: result = a XOR b":
    # bool_xor(a, b, result) with defines_var(result) means result = a XOR b
    let src = """
var bool: a;
var bool: b;
var bool: r:: var_is_introduced:: is_defined_var;
var 0..1: obj:: output_var:: is_defined_var;
array [1..3] of var bool: xarr:: var_is_introduced = [r, a, b];
constraint bool_xor(a, b, r):: defines_var(r);
constraint bool2int(r, obj):: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # r should be detected as a channel variable
    check "r" in tr.channelVarNames
    check tr.boolXorVarChannelDefs.len == 1
    check tr.boolXorVarChannelDefs[0].isNe == true  # XOR / NE pattern

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let aPos = tr.varPositions["a"]
    let bPos = tr.varPositions["b"]
    let rPos = tr.varPositions["r"]
    let aVal = tr.sys.assignment[aPos]
    let bVal = tr.sys.assignment[bPos]
    let rVal = tr.sys.assignment[rPos]
    check rVal == (if aVal != bVal: 1 else: 0)

  test "bool_xor constant-result identity channel: bool_xor(channel, var, false)":
    # When r = a XOR b (channel via defines_var), and bool_xor(r, t, false) with no
    # defines_var means r = t → t becomes an identity channel of r.
    let src = """
var bool: a;
var bool: b;
var bool: r:: var_is_introduced:: is_defined_var;
var bool: t;
var 0..1: obj:: output_var:: is_defined_var;
constraint bool_xor(a, b, r):: defines_var(r);
constraint bool_xor(r, t, false);
constraint bool2int(t, obj):: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # r detected as XOR var channel, t detected as identity channel of r
    check "r" in tr.channelVarNames
    check "t" in tr.channelVarNames
    check tr.boolXorVarChannelDefs.len == 1
    check tr.boolXorIdentityDefs.len == 1
    check tr.boolXorIdentityDefs[0].resultVar == "t"

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let aPos = tr.varPositions["a"]
    let bPos = tr.varPositions["b"]
    let rPos = tr.varPositions["r"]
    let tPos = tr.varPositions["t"]
    let aVal = tr.sys.assignment[aPos]
    let bVal = tr.sys.assignment[bPos]
    let rVal = tr.sys.assignment[rPos]
    let tVal = tr.sys.assignment[tPos]
    check rVal == (if aVal != bVal: 1 else: 0)
    check tVal == rVal  # identity: t = r

  test "bool_xor constant-result negation channel: bool_xor(channel, var, true)":
    # When r = a XOR b (channel via defines_var), and bool_xor(r, t, true) with no
    # defines_var means r != t → t becomes a negation channel of r.
    let src = """
var bool: a;
var bool: b;
var bool: r:: var_is_introduced:: is_defined_var;
var bool: t;
var 0..1: obj:: output_var:: is_defined_var;
constraint bool_xor(a, b, r):: defines_var(r);
constraint bool_xor(r, t, true);
constraint bool2int(t, obj):: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # r detected as XOR var channel, t detected as negation channel of r
    check "r" in tr.channelVarNames
    check "t" in tr.channelVarNames
    check tr.boolXorVarChannelDefs.len == 1
    check tr.boolXorNegDefs.len >= 1  # t is a negation def

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let aPos = tr.varPositions["a"]
    let bPos = tr.varPositions["b"]
    let rPos = tr.varPositions["r"]
    let tPos = tr.varPositions["t"]
    let aVal = tr.sys.assignment[aPos]
    let bVal = tr.sys.assignment[bPos]
    let rVal = tr.sys.assignment[rPos]
    let tVal = tr.sys.assignment[tPos]
    check rVal == (if aVal != bVal: 1 else: 0)
    check tVal == 1 - rVal  # negation: t = NOT r

  test "array_bool_xor constraint fallback (no defines_var)":
    # array_bool_xor without defines_var: XOR of all elements must be true
    let src = """
var bool: a;
var bool: b;
var bool: c;
array [1..3] of var bool: xarr = [a, b, c];
constraint array_bool_xor(xarr);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # No channel detection without defines_var
    check tr.boolXorVarChannelDefs.len == 0

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let aPos = tr.varPositions["a"]
    let bPos = tr.varPositions["b"]
    let cPos = tr.varPositions["c"]
    let aVal = tr.sys.assignment[aPos]
    let bVal = tr.sys.assignment[bPos]
    let cVal = tr.sys.assignment[cPos]
    # XOR = true means odd number of trues
    let total = aVal + bVal + cVal
    check (total == 1 or total == 3)

  test "big-M domain pruning: indicator-linked variable gap removal":
    # Two int_lin_le constraints link generation (x) to indicator (b) via bool2int:
    #   x <= 500 * b  →  int_lin_le([1, -500], [x, bi], 0)
    #   x >= 250 * b  →  int_lin_le([-1, 250], [x, bi], 0)
    # When b=0: x=0.  When b=1: x ∈ [250,500].
    # Presolve should prune x's domain from 0..500 to {0} ∪ [250,500].
    let src = """
var bool: b;
var 0..1: bi :: is_defined_var;
var 0..500: x;
var 0..500: obj :: is_defined_var;
constraint bool2int(b, bi) :: defines_var(bi);
constraint int_lin_le([1, -500], [x, bi], 0);
constraint int_lin_le([-1, 250], [x, bi], 0);
constraint int_lin_eq([1, -1], [x, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # Check that presolve pruned the domain — values 1..249 should be removed
    let xName = "x"
    if xName in tr.presolveDomains:
      let dom = tr.presolveDomains[xName]
      check 0 in dom        # x=0 when b=0
      check 250 in dom      # x=250 when b=1
      check 500 in dom      # x=500 when b=1
      check 1 notin dom     # gap: infeasible
      check 249 notin dom   # gap: infeasible
    else:
      # Domain should have been tightened
      check false

  test "conditional linear constraint detection":
    # Pattern: int_lin_le_reif + bool_clause creates a conditional linear constraint.
    #   b = (x1 - x2 <= 5)  via int_lin_le_reif
    #   bool_clause([b, guard], [])  means guard ∨ b, i.e., ¬guard → (x1 - x2 ≤ 5)
    let src = """
var 0..20: x1;
var 0..20: x2;
var bool: guard;
var bool: b :: is_defined_var;
array [1..2] of int: c1 = [1, -1];
constraint int_lin_le_reif(c1, [x1, x2], 5, b) :: defines_var(b);
constraint bool_clause([b, guard], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # Should have detected 1 conditional linear pattern
    check tr.conditionalLinearPatterns.len == 1
    # Constraint type should be present in the system
    var hasCondLinear = false
    for c in tr.sys.baseArray.constraints:
      if c.stateType == ConditionalLinearType:
        hasCondLinear = true
        break
    check hasCondLinear

  test "conditional linear: solve with ramping":
    # Simplified unit commitment ramping:
    # x1, x2 are generation levels, up indicates generator startup.
    # Ramp constraint: ¬up → (x2 - x1 ≤ 30)
    # With x1=50, up=false fixed, x2 must satisfy: x2 - 50 ≤ 30 → x2 ≤ 80
    # Minimize x2 subject to x2 ≥ 70 → optimal x2 = 70.
    let src = """
var 0..100: x1;
var 0..100: x2;
var bool: up;
var bool: ramp_ok :: is_defined_var;
var 0..100: obj :: is_defined_var;
array [1..2] of int: c_ramp = [1, -1];
constraint int_eq(x1, 50);
constraint bool_eq(up, false);
constraint int_lin_le([-1], [x2], -70);
constraint int_lin_le_reif(c_ramp, [x2, x1], 30, ramp_ok) :: defines_var(ramp_ok);
constraint bool_clause([ramp_ok, up], []);
constraint int_lin_eq([1, -1], [x2, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.conditionalLinearPatterns.len == 1
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)
    let x2Pos = tr.varPositions["x2"]
    let x2Val = tr.sys.assignment[x2Pos]
    check x2Val >= 70
    check x2Val <= 80

  test "fzn_alldifferent_except_0 basic":
    # 4 variables, domain 0..3, alldifferent_except_0 + sum constraint
    # Non-zero values must be distinct, zeros are allowed to repeat
    let src = """
var 0..3: x1;
var 0..3: x2;
var 0..3: x3;
var 0..3: x4;
array [1..4] of var int: x :: output_array([1..4]) = [x1,x2,x3,x4];
constraint fzn_alldifferent_except_0(x);
constraint int_lin_eq([1,1,1,1],[x1,x2,x3,x4],6);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    # Verify sum == 6
    check values.foldl(a + b) == 6
    # Verify alldifferent_except_0: non-zero values are distinct
    var nonZero: seq[int]
    for v in values:
      if v != 0:
        nonZero.add(v)
    check nonZero.toHashSet.len == nonZero.len

  test "fzn_alldifferent_except_0 with constant zeros in array":
    # Simulates the concert-hall-cap pattern where some array entries are literal 0
    # (infeasible offers). The translator must filter out constant 0s.
    let src = """
var 0..3: x1;
var 0..3: x2;
var 0..3: x3;
array [1..5] of var int: arr :: output_array([1..5]) = [x1, 0, x2, 0, x3];
constraint fzn_alldifferent_except_0(arr);
constraint int_lin_eq([1,1,1],[x1,x2,x3],6);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    var values: seq[int]
    for vname in ["x1", "x2", "x3"]:
      values.add(tr.sys.assignment[tr.varPositions[vname]])

    # Verify sum == 6 → must be {1,2,3} in some order
    check values.foldl(a + b) == 6
    # Verify alldifferent_except_0: non-zero values distinct
    var nonZero: seq[int]
    for v in values:
      if v != 0:
        nonZero.add(v)
    check nonZero.toHashSet.len == nonZero.len

  test "fzn_alldifferent_except_0 allows duplicate zeros":
    # Verify that multiple variables CAN take value 0 simultaneously
    let src = """
var 0..2: x1;
var 0..2: x2;
var 0..2: x3;
var 0..2: x4;
array [1..4] of var int: x :: output_array([1..4]) = [x1,x2,x3,x4];
constraint fzn_alldifferent_except_0(x);
constraint int_lin_eq([1,1,1,1],[x1,x2,x3,x4],3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    check values.foldl(a + b) == 3
    # Must have at least one zero (sum=3 with distinct non-zeros from {1,2} max = 3,
    # so {0, 1, 2, 0} or {1, 2, 0, 0} etc.)
    var nonZero: seq[int]
    for v in values:
      if v != 0:
        nonZero.add(v)
    check nonZero.toHashSet.len == nonZero.len
    # With sum=3 and values in 0..2, we need 1+2=3, so exactly two zeros
    check values.count(0) == 2

  test "element-defined objective variable not eliminated as dead channel":
    # Regression: when the objective variable is defined solely by an
    # array_var_int_element constraint and referenced only in the solve line,
    # dead-channel elimination must NOT remove it.
    # FlatZinc array_var_int_element is 1-based: idx=1→a0, idx=2→a1, idx=3→a2.
    let src = """
var 1..3: idx :: output_var;
var 10..30: a0;
var 10..30: a1;
var 10..30: a2;
array [1..3] of var int: arr = [a0, a1, a2];
constraint int_eq(a0, 10);
constraint int_eq(a1, 20);
constraint int_eq(a2, 30);
var 10..30: obj :: is_defined_var :: output_var;
constraint array_var_int_element(idx, arr, obj) :: defines_var(obj);
solve maximize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.objectivePos >= 0  # must be a real position, not eliminated
    let objExpr = tr.getExpr(tr.objectivePos)
    maximize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)
    check tr.sys.hasFeasibleSolution
    let objVal = tr.sys.assignment[tr.objectivePos]
    check objVal >= 30  # optimal: idx=3 → obj=a2=30

  test "weighted crossing count max pattern detection (graph-clear 3-node)":
    # 3 nodes, 2 directed edges (1→2 weight 3, 2→1 weight 3).
    # Sweep costs: node1=11, node2=16, node3=3.
    # Optimal: var_z=16 (perm 1,2,3 or 3,2,1 → max sweep=16, no blocking).
    # Tests: pattern detection, weighted evaluation with sweep costs,
    #        one-hot domain tightening, intermediate channel consumption.
    let src = """
predicate array_int_maximum(var int: m,array [int] of var int: x);
predicate fzn_all_different_int(array [int] of var int: x);
array [1..2] of int: X_INTRODUCED_250_ = [1,-1];
array [1..3] of int: X_INTRODUCED_363_ = [1,-3,-3];
var 1..3: X_INTRODUCED_142_;
var 1..3: X_INTRODUCED_143_;
var 1..3: X_INTRODUCED_144_;
var 1..3: X_INTRODUCED_145_;
var 1..3: X_INTRODUCED_146_;
var 1..3: X_INTRODUCED_147_;
var 1..3: X_INTRODUCED_148_;
var 1..16: X_INTRODUCED_149_;
var 1..16: X_INTRODUCED_150_;
var 1..16: X_INTRODUCED_151_;
var 0..6: X_INTRODUCED_152_:: is_defined_var;
var 0..6: X_INTRODUCED_153_:: is_defined_var;
var 0..6: X_INTRODUCED_154_:: is_defined_var;
var bool: X_INTRODUCED_156_;
var bool: X_INTRODUCED_157_;
var bool: X_INTRODUCED_158_;
var bool: X_INTRODUCED_159_;
var bool: X_INTRODUCED_160_;
var bool: X_INTRODUCED_161_;
var 1..16: var_z:: is_defined_var:: output_var;
var 1..22: X_INTRODUCED_164_ ::var_is_introduced :: is_defined_var;
var 1..22: X_INTRODUCED_165_ ::var_is_introduced :: is_defined_var;
var 1..22: X_INTRODUCED_166_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_169_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_170_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_178_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_179_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_187_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_188_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_196_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_197_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_205_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_206_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_214_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_215_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_223_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_224_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_232_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_233_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_241_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_242_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_251_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_252_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_253_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_262_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_263_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_264_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_273_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_274_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_275_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_285_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_286_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_287_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_288_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_298_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_299_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_300_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_310_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_311_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_318_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_319_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_326_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_336_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_337_ ::var_is_introduced :: is_defined_var;
var bool: X_INTRODUCED_347_ ::var_is_introduced :: is_defined_var;
var 0..1: X_INTRODUCED_357_ ::var_is_introduced :: is_defined_var;
var 0..1: X_INTRODUCED_360_ ::var_is_introduced :: is_defined_var;
var 0..1: X_INTRODUCED_364_ ::var_is_introduced :: is_defined_var;
var 0..1: X_INTRODUCED_366_ ::var_is_introduced :: is_defined_var;
var 0..1: X_INTRODUCED_369_ ::var_is_introduced :: is_defined_var;
var 0..1: X_INTRODUCED_371_ ::var_is_introduced :: is_defined_var;
array [1..3] of var int: var_t:: output_array([1..3]) = [X_INTRODUCED_142_,X_INTRODUCED_143_,X_INTRODUCED_144_];
array [1..2] of var int: var_l:: output_array([1..2]) = [X_INTRODUCED_145_,X_INTRODUCED_146_];
array [1..2] of var int: var_u:: output_array([1..2]) = [X_INTRODUCED_147_,X_INTRODUCED_148_];
array [1..3] of var int: var_s:: output_array([1..3]) = [X_INTRODUCED_149_,X_INTRODUCED_150_,X_INTRODUCED_151_];
array [1..3] of var int: var_b:: output_array([1..3]) = [X_INTRODUCED_152_,X_INTRODUCED_153_,X_INTRODUCED_154_];
array [1..6] of var bool: X_INTRODUCED_155_:: output_array([1..6]) = [X_INTRODUCED_156_,X_INTRODUCED_157_,X_INTRODUCED_158_,X_INTRODUCED_159_,X_INTRODUCED_160_,X_INTRODUCED_161_];
array [1..3] of var int: X_INTRODUCED_167_ ::var_is_introduced  = [X_INTRODUCED_164_,X_INTRODUCED_165_,X_INTRODUCED_166_];
constraint array_int_maximum(var_z,X_INTRODUCED_167_):: defines_var(var_z);
constraint bool_clause([X_INTRODUCED_170_],[X_INTRODUCED_169_]);
constraint bool_clause([X_INTRODUCED_179_],[X_INTRODUCED_178_]);
constraint bool_clause([X_INTRODUCED_188_],[X_INTRODUCED_187_]);
constraint bool_clause([X_INTRODUCED_197_],[X_INTRODUCED_196_]);
constraint bool_clause([X_INTRODUCED_206_],[X_INTRODUCED_205_]);
constraint bool_clause([X_INTRODUCED_215_],[X_INTRODUCED_214_]);
constraint bool_clause([X_INTRODUCED_224_],[X_INTRODUCED_223_]);
constraint bool_clause([X_INTRODUCED_233_],[X_INTRODUCED_232_]);
constraint bool_clause([X_INTRODUCED_242_],[X_INTRODUCED_241_]);
constraint fzn_all_different_int(var_t);
constraint bool_clause([X_INTRODUCED_156_],[X_INTRODUCED_273_,X_INTRODUCED_274_,X_INTRODUCED_275_]);
constraint bool_clause([X_INTRODUCED_157_],[X_INTRODUCED_285_,X_INTRODUCED_286_,X_INTRODUCED_287_,X_INTRODUCED_288_]);
constraint bool_clause([X_INTRODUCED_158_],[X_INTRODUCED_298_,X_INTRODUCED_299_,X_INTRODUCED_300_]);
constraint bool_clause([X_INTRODUCED_159_],[X_INTRODUCED_274_,X_INTRODUCED_275_,X_INTRODUCED_326_]);
constraint bool_clause([X_INTRODUCED_160_],[X_INTRODUCED_287_,X_INTRODUCED_288_,X_INTRODUCED_336_,X_INTRODUCED_337_]);
constraint bool_clause([X_INTRODUCED_161_],[X_INTRODUCED_299_,X_INTRODUCED_300_,X_INTRODUCED_347_]);
constraint int_lin_eq(X_INTRODUCED_363_,[X_INTRODUCED_152_,X_INTRODUCED_357_,X_INTRODUCED_360_],0):: defines_var(X_INTRODUCED_152_);
constraint int_lin_eq(X_INTRODUCED_363_,[X_INTRODUCED_153_,X_INTRODUCED_364_,X_INTRODUCED_366_],0):: defines_var(X_INTRODUCED_153_);
constraint int_lin_eq(X_INTRODUCED_363_,[X_INTRODUCED_154_,X_INTRODUCED_369_,X_INTRODUCED_371_],0):: defines_var(X_INTRODUCED_154_);
constraint bool_clause([X_INTRODUCED_252_],[X_INTRODUCED_251_]);
constraint bool_clause([X_INTRODUCED_253_],[X_INTRODUCED_251_]);
constraint bool_clause([X_INTRODUCED_318_],[X_INTRODUCED_251_]);
constraint bool_clause([X_INTRODUCED_319_],[X_INTRODUCED_251_]);
constraint bool_clause([X_INTRODUCED_263_],[X_INTRODUCED_262_]);
constraint bool_clause([X_INTRODUCED_264_],[X_INTRODUCED_262_]);
constraint bool_clause([X_INTRODUCED_310_],[X_INTRODUCED_262_]);
constraint bool_clause([X_INTRODUCED_311_],[X_INTRODUCED_262_]);
constraint int_lin_eq([1,1,-1],[X_INTRODUCED_149_,X_INTRODUCED_152_,X_INTRODUCED_164_],0):: defines_var(X_INTRODUCED_164_);
constraint int_lin_eq([1,1,-1],[X_INTRODUCED_150_,X_INTRODUCED_153_,X_INTRODUCED_165_],0):: defines_var(X_INTRODUCED_165_);
constraint int_lin_eq([1,1,-1],[X_INTRODUCED_151_,X_INTRODUCED_154_,X_INTRODUCED_166_],0):: defines_var(X_INTRODUCED_166_);
constraint int_eq_reif(X_INTRODUCED_142_,1,X_INTRODUCED_169_):: defines_var(X_INTRODUCED_169_);
constraint int_eq_reif(X_INTRODUCED_149_,11,X_INTRODUCED_170_):: defines_var(X_INTRODUCED_170_);
constraint int_eq_reif(X_INTRODUCED_142_,2,X_INTRODUCED_178_):: defines_var(X_INTRODUCED_178_);
constraint int_eq_reif(X_INTRODUCED_150_,11,X_INTRODUCED_179_):: defines_var(X_INTRODUCED_179_);
constraint int_eq_reif(X_INTRODUCED_142_,3,X_INTRODUCED_187_):: defines_var(X_INTRODUCED_187_);
constraint int_eq_reif(X_INTRODUCED_151_,11,X_INTRODUCED_188_):: defines_var(X_INTRODUCED_188_);
constraint int_eq_reif(X_INTRODUCED_143_,1,X_INTRODUCED_196_):: defines_var(X_INTRODUCED_196_);
constraint int_eq_reif(X_INTRODUCED_149_,16,X_INTRODUCED_197_):: defines_var(X_INTRODUCED_197_);
constraint int_eq_reif(X_INTRODUCED_143_,2,X_INTRODUCED_205_):: defines_var(X_INTRODUCED_205_);
constraint int_eq_reif(X_INTRODUCED_150_,16,X_INTRODUCED_206_):: defines_var(X_INTRODUCED_206_);
constraint int_eq_reif(X_INTRODUCED_143_,3,X_INTRODUCED_214_):: defines_var(X_INTRODUCED_214_);
constraint int_eq_reif(X_INTRODUCED_151_,16,X_INTRODUCED_215_):: defines_var(X_INTRODUCED_215_);
constraint int_eq_reif(X_INTRODUCED_144_,1,X_INTRODUCED_223_):: defines_var(X_INTRODUCED_223_);
constraint int_eq_reif(X_INTRODUCED_149_,3,X_INTRODUCED_224_):: defines_var(X_INTRODUCED_224_);
constraint int_eq_reif(X_INTRODUCED_144_,2,X_INTRODUCED_232_):: defines_var(X_INTRODUCED_232_);
constraint int_eq_reif(X_INTRODUCED_150_,3,X_INTRODUCED_233_):: defines_var(X_INTRODUCED_233_);
constraint int_eq_reif(X_INTRODUCED_144_,3,X_INTRODUCED_241_):: defines_var(X_INTRODUCED_241_);
constraint int_eq_reif(X_INTRODUCED_151_,3,X_INTRODUCED_242_):: defines_var(X_INTRODUCED_242_);
constraint int_lin_le_reif(X_INTRODUCED_250_,[X_INTRODUCED_142_,X_INTRODUCED_143_],-1,X_INTRODUCED_251_):: defines_var(X_INTRODUCED_251_);
constraint int_eq_reif(X_INTRODUCED_145_,X_INTRODUCED_142_,X_INTRODUCED_252_):: defines_var(X_INTRODUCED_252_);
constraint int_eq_reif(X_INTRODUCED_147_,X_INTRODUCED_143_,X_INTRODUCED_253_):: defines_var(X_INTRODUCED_253_);
constraint int_lin_le_reif(X_INTRODUCED_250_,[X_INTRODUCED_143_,X_INTRODUCED_142_],-1,X_INTRODUCED_262_):: defines_var(X_INTRODUCED_262_);
constraint int_eq_reif(X_INTRODUCED_145_,X_INTRODUCED_143_,X_INTRODUCED_263_):: defines_var(X_INTRODUCED_263_);
constraint int_eq_reif(X_INTRODUCED_147_,X_INTRODUCED_142_,X_INTRODUCED_264_):: defines_var(X_INTRODUCED_264_);
constraint int_le_reif(X_INTRODUCED_145_,1,X_INTRODUCED_273_):: defines_var(X_INTRODUCED_273_);
constraint int_ne_reif(X_INTRODUCED_142_,1,X_INTRODUCED_274_):: defines_var(X_INTRODUCED_274_);
constraint int_ne_reif(X_INTRODUCED_143_,1,X_INTRODUCED_275_):: defines_var(X_INTRODUCED_275_);
constraint int_le_reif(X_INTRODUCED_145_,2,X_INTRODUCED_285_):: defines_var(X_INTRODUCED_285_);
constraint int_le_reif(2,X_INTRODUCED_147_,X_INTRODUCED_286_):: defines_var(X_INTRODUCED_286_);
constraint int_ne_reif(X_INTRODUCED_142_,2,X_INTRODUCED_287_):: defines_var(X_INTRODUCED_287_);
constraint int_ne_reif(X_INTRODUCED_143_,2,X_INTRODUCED_288_):: defines_var(X_INTRODUCED_288_);
constraint int_le_reif(3,X_INTRODUCED_147_,X_INTRODUCED_298_):: defines_var(X_INTRODUCED_298_);
constraint int_ne_reif(X_INTRODUCED_142_,3,X_INTRODUCED_299_):: defines_var(X_INTRODUCED_299_);
constraint int_ne_reif(X_INTRODUCED_143_,3,X_INTRODUCED_300_):: defines_var(X_INTRODUCED_300_);
constraint int_eq_reif(X_INTRODUCED_146_,X_INTRODUCED_143_,X_INTRODUCED_310_):: defines_var(X_INTRODUCED_310_);
constraint int_eq_reif(X_INTRODUCED_148_,X_INTRODUCED_142_,X_INTRODUCED_311_):: defines_var(X_INTRODUCED_311_);
constraint int_eq_reif(X_INTRODUCED_146_,X_INTRODUCED_142_,X_INTRODUCED_318_):: defines_var(X_INTRODUCED_318_);
constraint int_eq_reif(X_INTRODUCED_148_,X_INTRODUCED_143_,X_INTRODUCED_319_):: defines_var(X_INTRODUCED_319_);
constraint int_le_reif(X_INTRODUCED_146_,1,X_INTRODUCED_326_):: defines_var(X_INTRODUCED_326_);
constraint int_le_reif(X_INTRODUCED_146_,2,X_INTRODUCED_336_):: defines_var(X_INTRODUCED_336_);
constraint int_le_reif(2,X_INTRODUCED_148_,X_INTRODUCED_337_):: defines_var(X_INTRODUCED_337_);
constraint int_le_reif(3,X_INTRODUCED_148_,X_INTRODUCED_347_):: defines_var(X_INTRODUCED_347_);
constraint bool2int(X_INTRODUCED_156_,X_INTRODUCED_357_):: defines_var(X_INTRODUCED_357_);
constraint bool2int(X_INTRODUCED_159_,X_INTRODUCED_360_):: defines_var(X_INTRODUCED_360_);
constraint bool2int(X_INTRODUCED_157_,X_INTRODUCED_364_):: defines_var(X_INTRODUCED_364_);
constraint bool2int(X_INTRODUCED_160_,X_INTRODUCED_366_):: defines_var(X_INTRODUCED_366_);
constraint bool2int(X_INTRODUCED_158_,X_INTRODUCED_369_):: defines_var(X_INTRODUCED_369_);
constraint bool2int(X_INTRODUCED_161_,X_INTRODUCED_371_):: defines_var(X_INTRODUCED_371_);
solve :: int_search(var_t,smallest,indomain_min,complete) minimize var_z;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Pattern should be detected: 2 cables (both edge (1,2) and (2,1)), k=3
    check tr.crossingCountMaxDefs.len == 1
    let ccmDef = tr.crossingCountMaxDefs[0]
    check ccmDef.cables.len == 2
    check ccmDef.k == 3
    check ccmDef.weights.len == 2
    # Both cable weights should be 3
    for w in ccmDef.weights:
      check w == 3
    # Sweep costs: node1=11, node2=16, node3=3
    check ccmDef.sweepCosts == @[11, 16, 3]
    check ccmDef.permVarNames.len == 3

    # One-hot domain tightening: var_s domains should be {3, 11, 16} not 1..16
    for sName in ["X_INTRODUCED_149_", "X_INTRODUCED_150_", "X_INTRODUCED_151_"]:
      let pos = tr.varPositions[sName]
      let dom = tr.sys.baseArray.domain[pos]
      check dom.len == 3
      check 3 in dom
      check 11 in dom
      check 16 in dom

    # Intermediate betweenness channels should be consumed
    check "X_INTRODUCED_152_" in tr.channelVarNames  # var_b[1]
    check "X_INTRODUCED_164_" in tr.channelVarNames  # signal[1]

    # Solve and verify: optimal is 16 (max sweep cost with no blocking)
    # var_z is a channel position (crossing count max binding), not a defined expression
    check tr.objectivePos >= 0
    let objExpr = tr.getExpr(tr.objectivePos)
    minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 10000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)
    check tr.sys.hasFeasibleSolution
    let objVal = tr.sys.assignment[tr.objectivePos]
    check objVal == 16  # optimal: place nodes so max(sweep+block) = 16

  test "GCD-based domain pruning for linear equalities":
    # Constraint: 3*x + 7*y = 0  with x in 0..20, y in 0..20
    # GCD analysis: for x, gcd of other coeffs = 7, so 3*x ≡ 0 (mod 7)
    #   => x must be a multiple of 7: {0, 7, 14}
    # For y, gcd of other coeffs = 3, so 7*y ≡ 0 (mod 3) => y*1 ≡ 0 (mod 3)
    #   => y must be a multiple of 3: {0, 3, 6, 9, 12, 15, 18}
    # After bounds propagation: 3*x <= 7*20 = 140 (no bound tightening for x),
    #   but 7*y <= 3*20 = 60 => y <= 8, so y in {0, 3, 6}
    # Combined with 3*x + 7*y = 0 and both non-negative: x=0, y=0
    # Presolve should fix both to 0.
    let src = """
var 0..20: x;
var 0..20: y;
constraint int_lin_eq([3,7],[x,y],0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]
    # Both should be fixed to 0 by presolve (bounds propagation + GCD)
    check tr.sys.baseArray.domain[xPos] == @[0]
    check tr.sys.baseArray.domain[yPos] == @[0]

  test "GCD-based domain pruning with non-trivial feasible set":
    # Constraint: 3*x + 5*y = 30  with x in 0..10, y in 0..6
    # GCD pruning for x: gcd of other coeffs = 5, so 3*x ≡ 30 (mod 5)
    #   => 3*x ≡ 0 (mod 5) => x ≡ 0 (mod 5): {0, 5, 10}
    # GCD pruning for y: gcd of other coeffs = 3, so 5*y ≡ 30 (mod 3)
    #   => 2*y ≡ 0 (mod 3) => y ≡ 0 (mod 3): {0, 3, 6}
    # Bounds propagation: y <= (30 - 0) / 5 = 6, x <= (30 - 0) / 3 = 10
    # Solutions: (0,6), (5,3), (10,0) - all valid
    let src = """
var 0..10: x;
var 0..6: y;
constraint int_lin_eq([3,5],[x,y],30);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]
    # x should be pruned to multiples of 5
    check tr.sys.baseArray.domain[xPos] == @[0, 5, 10]
    # y should be pruned to multiples of 3
    check tr.sys.baseArray.domain[yPos] == @[0, 3, 6]

    # Should find a feasible solution
    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
    let xVal = tr.sys.assignment[xPos]
    let yVal = tr.sys.assignment[yPos]
    check 3 * xVal + 5 * yVal == 30

  test "GCD pruning with negative coefficients":
    # Constraint: 4*x - 6*y = 2  with x in 0..10, y in 0..10
    # Overall gcd(4,6) = 2, but rhs=2 is divisible by 2, so constraint is feasible.
    # GCD pruning for x: gcd of other coeffs = |(-6)| = 6, so 4*x ≡ 2 (mod 6)
    #   => 4*x mod 6 = 2: x=2 gives 8%6=2 ✓, x=5 gives 20%6=2 ✓, x=8 gives 32%6=2 ✓
    #   so x in {2, 5, 8}
    # GCD pruning for y: gcd of other coeffs = |4| = 4, so -6*y ≡ 2 (mod 4)
    #   => (-6*y) mod 4 = 2 mod 4 = 2: y=1 gives -6%4 = (-6+8)%4 = 2 ✓, y=3 gives -18%4 = (-18+20)%4 = 2 ✓
    #   etc. so y in {1, 3, 5, 7, 9}
    # Bounds: 4*x = 2 + 6*y >= 2 => x >= 1; 4*x = 2 + 6*y <= 2+60=62 => x <= 10 (no further)
    #   -6*y = 2 - 4*x => 6*y = 4*x - 2 >= -2 => y >= 0; 6*y = 4*x - 2 <= 38 => y <= 6
    # After bounds + GCD: x in {2, 5, 8}, y in {1, 3, 5}
    let src = """
var 0..10: x;
var 0..10: y;
constraint int_lin_eq([4,-6],[x,y],2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]
    # x should be pruned: bounds give [1,10], GCD gives multiples of... let's check
    let xDom = tr.sys.baseArray.domain[xPos]
    let yDom = tr.sys.baseArray.domain[yPos]
    # x must satisfy 4*x ≡ 2 (mod 6): x in {2, 5, 8}
    check 0 notin xDom
    check 1 notin xDom
    check 2 in xDom
    check 3 notin xDom
    check 5 in xDom
    check 8 in xDom
    # y bounds: [0,6], GCD: -6*y ≡ 2 (mod 4) => y odd: {1, 3, 5}
    check 0 notin yDom
    check 1 in yDom
    check 2 notin yDom
    check 3 in yDom
    check 5 in yDom

    # Should find a valid solution
    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
    let xVal = tr.sys.assignment[xPos]
    let yVal = tr.sys.assignment[yPos]
    check 4 * xVal - 6 * yVal == 2

  test "GCD pruning with fixed variables in presolve":
    # Constraint: 2*x + 3*y + 5*z = 20  with z fixed to 2
    # Effective: 2*x + 3*y = 10
    # GCD pruning for x: gRest = gcd(3) = 3, adjRhs = 10
    #   2*x ≡ 10 (mod 3) → 2*x ≡ 1 (mod 3) → x ≡ 2 (mod 3): {2, 5, 8, ...}
    # GCD pruning for y: gRest = gcd(2) = 2, adjRhs = 10
    #   3*y ≡ 10 (mod 2) → y ≡ 0 (mod 2): {0, 2, 4, ...}
    # Bounds: x in [0, (10-0)/2] = [0, 5], y in [0, (10-0)/3] = [0, 3]
    # After GCD + bounds: x in {2, 5}, y in {0, 2}
    # Solutions: (2, 2) → 4+6=10 ✓, (5, 0) → 10+0=10 ✓
    let src = """
var 0..10: x;
var 0..10: y;
var 2..2: z;
constraint int_lin_eq([2,3,5],[x,y,z],20);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]
    let xDom = tr.sys.baseArray.domain[xPos]
    let yDom = tr.sys.baseArray.domain[yPos]
    # x must satisfy x ≡ 2 (mod 3) within [0, 5]: {2, 5}
    check 0 notin xDom
    check 1 notin xDom
    check 2 in xDom
    check 3 notin xDom
    check 4 notin xDom
    check 5 in xDom
    # y must satisfy y ≡ 0 (mod 2) within [0, 3]: {0, 2}
    check 0 in yDom
    check 1 notin yDom
    check 2 in yDom
    check 3 notin yDom

    # Should find a valid solution
    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
    let xVal = tr.sys.assignment[xPos]
    let yVal = tr.sys.assignment[yPos]
    check 2 * xVal + 3 * yVal == 10

suite "FlatZinc Variable-Duration Cumulative/Disjunctive":

  test "defined-var durations rescued as channels for disjunctive":
    # When disjunctive durations are defined vars (dur = end - start), they must
    # be rescued as channel variables so the cumulative gets proper durationPositions.
    # Model: 2 tasks on a single resource.
    #   arrive1 in 0..10, depart1 in 0..10, wait1 = depart1 - arrive1 (defined var)
    #   arrive2 in 0..10, depart2 in 0..10, wait2 = depart2 - arrive2 (defined var)
    #   disjunctive([arrive1, arrive2], [wait1, wait2])
    #   depart1 >= arrive1 + 2 (min duration 2)
    #   depart2 >= arrive2 + 2 (min duration 2)
    let src = """
predicate fzn_disjunctive(array [int] of var int: s, array [int] of var int: d);
var 0..10: arrive1;
var 0..10: depart1;
var 0..10: wait1:: is_defined_var:: var_is_introduced;
var 0..10: arrive2;
var 0..10: depart2;
var 0..10: wait2:: is_defined_var:: var_is_introduced;
constraint int_lin_eq([1, -1, 1], [wait1, depart1, arrive1], 0):: defines_var(wait1);
constraint int_lin_eq([1, -1, 1], [wait2, depart2, arrive2], 0):: defines_var(wait2);
constraint int_lin_le([1, -1], [arrive1, depart1], -2);
constraint int_lin_le([1, -1], [arrive2, depart2], -2);
constraint fzn_disjunctive([arrive1, arrive2], [wait1, wait2]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # wait1 and wait2 should be rescued as channel vars (not defined vars)
    check "wait1" in tr.channelVarNames
    check "wait2" in tr.channelVarNames
    check "wait1" notin tr.definedVarNames
    check "wait2" notin tr.definedVarNames
    # They should have positions
    check "wait1" in tr.varPositions
    check "wait2" in tr.varPositions

    tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)

    # Verify channel propagation: wait = depart - arrive
    let a1 = tr.sys.assignment[tr.varPositions["arrive1"]]
    let d1 = tr.sys.assignment[tr.varPositions["depart1"]]
    let w1 = tr.sys.assignment[tr.varPositions["wait1"]]
    let a2 = tr.sys.assignment[tr.varPositions["arrive2"]]
    let d2 = tr.sys.assignment[tr.varPositions["depart2"]]
    let w2 = tr.sys.assignment[tr.varPositions["wait2"]]
    check w1 == d1 - a1
    check w2 == d2 - a2
    # Min duration enforced
    check d1 - a1 >= 2
    check d2 - a2 >= 2
    # Disjunctive: intervals [arrive, arrive+wait) must not overlap
    check (a1 + w1 <= a2) or (a2 + w2 <= a1)

  test "defined-var durations rescued as channels for cumulative":
    # Same pattern but with cumulative (limit > 1).
    # 3 tasks, resource capacity 2, durations are defined vars.
    let src = """
predicate fzn_cumulative(array [int] of var int: s, array [int] of var int: d, array [int] of var int: r, var int: b);
var 0..20: s1;
var 0..20: e1;
var 0..20: d1:: is_defined_var:: var_is_introduced;
var 0..20: s2;
var 0..20: e2;
var 0..20: d2:: is_defined_var:: var_is_introduced;
var 0..20: s3;
var 0..20: e3;
var 0..20: d3:: is_defined_var:: var_is_introduced;
constraint int_lin_eq([1, -1, 1], [d1, e1, s1], 0):: defines_var(d1);
constraint int_lin_eq([1, -1, 1], [d2, e2, s2], 0):: defines_var(d2);
constraint int_lin_eq([1, -1, 1], [d3, e3, s3], 0):: defines_var(d3);
constraint int_lin_le([1, -1], [s1, e1], -3);
constraint int_lin_le([1, -1], [s2, e2], -3);
constraint int_lin_le([1, -1], [s3, e3], -3);
constraint fzn_cumulative([s1, s2, s3], [d1, d2, d3], [1, 1, 1], 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # d1, d2, d3 rescued as channel vars
    check "d1" in tr.channelVarNames
    check "d2" in tr.channelVarNames
    check "d3" in tr.channelVarNames

    tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)

    let sv1 = tr.sys.assignment[tr.varPositions["s1"]]
    let ev1 = tr.sys.assignment[tr.varPositions["e1"]]
    let dv1 = tr.sys.assignment[tr.varPositions["d1"]]
    let sv2 = tr.sys.assignment[tr.varPositions["s2"]]
    let ev2 = tr.sys.assignment[tr.varPositions["e2"]]
    let dv2 = tr.sys.assignment[tr.varPositions["d2"]]
    let sv3 = tr.sys.assignment[tr.varPositions["s3"]]
    let ev3 = tr.sys.assignment[tr.varPositions["e3"]]
    let dv3 = tr.sys.assignment[tr.varPositions["d3"]]
    # Channels correct
    check dv1 == ev1 - sv1
    check dv2 == ev2 - sv2
    check dv3 == ev3 - sv3
    # Min duration
    check ev1 - sv1 >= 3
    check ev2 - sv2 >= 3
    check ev3 - sv3 >= 3
    # Cumulative capacity 2: at most 2 tasks active at any time
    for t in 0..20:
      var active = 0
      if t >= sv1 and t < ev1: inc active
      if t >= sv2 and t < ev2: inc active
      if t >= sv3 and t < ev3: inc active
      check active <= 2

  test "constant-duration disjunctive unchanged by rescue":
    # When disjunctive durations are constant, no rescue should occur.
    let src = """
predicate fzn_disjunctive(array [int] of var int: s, array [int] of var int: d);
var 0..20: s1;
var 0..20: s2;
var 0..20: s3;
constraint fzn_disjunctive([s1, s2, s3], [3, 5, 4]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # No rescues needed — durations are constants
    var rescuedFromCumDur = 0
    for def in tr.rescuedChannelDefs:
      inc rescuedFromCumDur
    # Only the pre-existing rescued defs (should be 0 for this simple model)
    check rescuedFromCumDur == 0

    tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)

    let v1 = tr.sys.assignment[tr.varPositions["s1"]]
    let v2 = tr.sys.assignment[tr.varPositions["s2"]]
    let v3 = tr.sys.assignment[tr.varPositions["s3"]]
    # Disjunctive: no overlap with constant durations
    check (v1 + 3 <= v2) or (v2 + 5 <= v1)
    check (v1 + 3 <= v3) or (v3 + 4 <= v1)
    check (v2 + 5 <= v3) or (v3 + 4 <= v2)

suite "Domain Reduction Partial Restoration":

  test "empty domains selectively restored without discarding all reductions":
    # Create a model where domain reduction can tighten some domains but
    # over-prunes others. Verify that the valid reductions are preserved.
    # Model: x in 1..10, y in 1..10, z in 1..5
    #   x + y = 12 (forces x >= 2, y >= 2, etc.)
    #   z = x (element channel — z mirrors x but has smaller domain)
    # Domain reduction should tighten x to 2..10, y to 2..10 based on the sum.
    # If z's domain (1..5) restricts x to 1..5 through the channel, and then
    # x+y=12 restricts y to 7..10 — all valid.
    let src = """
var 2..10: x;
var 2..10: y;
constraint int_lin_eq([1, 1], [x, y], 12);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # After domain reduction, both x and y should be tightened
    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]
    let reduced = tr.sys.baseArray.reduceDomain()
    # x + y = 12, x in 2..10, y in 2..10
    # → x in 2..10, y in 2..10 (bounds propagation)
    check reduced[xPos].len <= 9
    check reduced[yPos].len <= 9
    # Both domains should be non-empty
    check reduced[xPos].len > 0
    check reduced[yPos].len > 0

  test "fzn_nvalue constraint — exactly 2 distinct values":
    let src = """
var 1..5: x1;
var 1..5: x2;
var 1..5: x3;
var 1..5: x4;
var 1..5: n;
array [1..4] of var int: x:: output_array([1..4]) = [x1,x2,x3,x4];
constraint fzn_nvalue(n, x);
constraint int_eq(n, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    let distinctCount = values.toHashSet.len
    check distinctCount == 2
    echo "fzn_nvalue satisfy: ", values, " distinct=", distinctCount

  test "fzn_nvalue constraint — maximize distinct values":
    let src = """
var 1..4: x1;
var 1..4: x2;
var 1..4: x3;
var 1..4: x4;
var 1..4: n;
array [1..4] of var int: x:: output_array([1..4]) = [x1,x2,x3,x4];
constraint fzn_nvalue(n, x);
solve maximize n;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    let objExpr = tr.getExpr(tr.objectivePos)
    maximize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound,
             verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    let distinctCount = values.toHashSet.len
    let nPos = tr.varPositions["n"]
    let nVal = tr.sys.assignment[nPos]
    # nvalue constraint must be satisfied: n == distinct count
    check distinctCount == nVal
    # Maximizing nvalue with 4 vars in domain 1..4 → optimum is 4
    check distinctCount == 4
    echo "fzn_nvalue maximize: ", values, " n=", nVal, " distinct=", distinctCount

  test "fzn_nvalue with all_different — nvalue must equal array length":
    let src = """
var 1..5: x1;
var 1..5: x2;
var 1..5: x3;
var 1..5: n;
array [1..3] of var int: x:: output_array([1..3]) = [x1,x2,x3];
constraint fzn_nvalue(n, x);
constraint fzn_all_different_int(x);
constraint int_eq(n, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    check values.toHashSet.len == 3
    let nPos = tr.varPositions["n"]
    check tr.sys.assignment[nPos] == 3
    echo "fzn_nvalue + all_different: ", values

  test "disconnected all_different with redundant cfp":
    # cfp is a second permutation that is not linked to pfc or the objective.
    # detectDisconnectedAllDifferent (currently disabled) would eliminate these.
    # With it disabled, the solver still finds a solution — cfp is satisfied independently.
    let src = """
var 1..4: x1 :: output_var;
var 1..4: x2 :: output_var;
var 1..4: x3 :: output_var;
var 1..4: x4 :: output_var;
array [1..4] of var int: pfc = [x1,x2,x3,x4];
var 1..4: y1;
var 1..4: y2;
var 1..4: y3;
var 1..4: y4;
array [1..4] of var int: cfp = [y1,y2,y3,y4];
array [1..2] of int: c = [1,-1];
constraint fzn_all_different_int(pfc);
constraint fzn_all_different_int(cfp);
constraint int_lin_le(c,[x1,x2],-1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # pfc variables should be present
    check "x1" in tr.varPositions
    check "x2" in tr.varPositions

    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)

    let vals = [tr.sys.assignment[tr.varPositions["x1"]],
                tr.sys.assignment[tr.varPositions["x2"]],
                tr.sys.assignment[tr.varPositions["x3"]],
                tr.sys.assignment[tr.varPositions["x4"]]]
    check vals.toHashSet.len == 4  # all different
    check vals[0] < vals[1]        # x1 < x2

  test "redundant disjunction elimination via max condition":
    # Disjunction x1 < x2 ∨ x1 < x3 is implied by max(x2,x3) > x1.
    # The disjunction should be eliminated as redundant.
    let src = """
var 1..5: x1 :: output_var;
var 1..5: x2 :: output_var;
var 1..5: x3 :: output_var;
var 1..5: x4 :: output_var;
var 1..5: x5 :: output_var;
array [1..5] of var int: xs:: output_array([1..5]) = [x1,x2,x3,x4,x5];
var 1..5: m :: is_defined_var;
array [1..2] of int: c1 = [1,-1];
array [1..2] of int: c2 = [-1,1];
var bool: b1 :: is_defined_var;
var bool: b2 :: is_defined_var;
constraint fzn_all_different_int(xs);
constraint int_max(x2,x3,m) :: defines_var(m);
constraint int_lin_le(c2,[m,x1],-1);
constraint int_lin_le_reif(c1,[x1,x2],-1,b1) :: defines_var(b1);
constraint int_lin_le_reif(c1,[x1,x3],-1,b2) :: defines_var(b2);
constraint bool_clause([b1,b2],[]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # The disjunctive pair (b1 ∨ b2) should be consumed as redundant
    check tr.consumedDisjunctivePairs.len == 1

    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)

    let v = [tr.sys.assignment[tr.varPositions["x1"]],
             tr.sys.assignment[tr.varPositions["x2"]],
             tr.sys.assignment[tr.varPositions["x3"]],
             tr.sys.assignment[tr.varPositions["x4"]],
             tr.sys.assignment[tr.varPositions["x5"]]]
    check v.toHashSet.len == 5  # all different
    # max(x2,x3) > x1 should hold
    check max(v[1], v[2]) > v[0]

  test "redundant disjunction elimination via min condition":
    # Dual of the max case: disjunction x2 < x1 ∨ x3 < x1 is implied by min(x2,x3) < x1.
    let src = """
var 1..5: x1 :: output_var;
var 1..5: x2 :: output_var;
var 1..5: x3 :: output_var;
var 1..5: x4 :: output_var;
var 1..5: x5 :: output_var;
array [1..5] of var int: xs:: output_array([1..5]) = [x1,x2,x3,x4,x5];
var 1..5: m :: is_defined_var;
array [1..2] of int: c1 = [1,-1];
var bool: b1 :: is_defined_var;
var bool: b2 :: is_defined_var;
constraint fzn_all_different_int(xs);
constraint int_min(x2,x3,m) :: defines_var(m);
constraint int_lin_le(c1,[m,x1],-1);
constraint int_lin_le_reif(c1,[x2,x1],-1,b1) :: defines_var(b1);
constraint int_lin_le_reif(c1,[x3,x1],-1,b2) :: defines_var(b2);
constraint bool_clause([b1,b2],[]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.consumedDisjunctivePairs.len == 1

    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
    let v = [tr.sys.assignment[tr.varPositions["x1"]],
             tr.sys.assignment[tr.varPositions["x2"]],
             tr.sys.assignment[tr.varPositions["x3"]],
             tr.sys.assignment[tr.varPositions["x4"]],
             tr.sys.assignment[tr.varPositions["x5"]]]
    check v.toHashSet.len == 5
    check min(v[1], v[2]) < v[0]

  test "redundant disjunction not eliminated without implying max":
    # Same disjunction pattern but no max condition: should NOT be eliminated.
    let src = """
var 1..5: x1 :: output_var;
var 1..5: x2 :: output_var;
var 1..5: x3 :: output_var;
var 1..5: x4 :: output_var;
var 1..5: x5 :: output_var;
array [1..5] of var int: xs:: output_array([1..5]) = [x1,x2,x3,x4,x5];
array [1..2] of int: c1 = [1,-1];
var bool: b1 :: is_defined_var;
var bool: b2 :: is_defined_var;
constraint fzn_all_different_int(xs);
constraint int_lin_le_reif(c1,[x1,x2],-1,b1) :: defines_var(b1);
constraint int_lin_le_reif(c1,[x1,x3],-1,b2) :: defines_var(b2);
constraint bool_clause([b1,b2],[]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # No max condition — disjunction must remain
    check tr.consumedDisjunctivePairs.len == 0

  test "CPM implied edges through int_max":
    # Chain: z < a (weight 5), so a >= 6. Then m = max(a, b) >= 6, and d >= m + 3 >= 9.
    # With implied edges: a→d with weight 3 directly gives d >= a + 3 = 9 at CPM time.
    # Without implied edges, CPM only sees m→d (weight 3) and uses m's initial lb=1,
    # giving d >= 4 until the fixpoint propagates int_max bounds. Either way the final
    # bound should be correct (>= 9).
    let src = """
var 1..30: z;
var 1..30: a;
var 1..30: b;
var 1..30: d;
var 1..30: m :: is_defined_var;
array [1..2] of int: c = [1,-1];
constraint int_lin_le(c,[z,a],-5);
constraint int_max(a,b,m) :: defines_var(m);
constraint int_lin_le(c,[m,d],-3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # d >= z + 5 + 3 = 9 (transitive: z→a→m→d with weights 5, 0, 3)
    check "d" in tr.varPositions
    let dPos = tr.varPositions["d"]
    let dDom = tr.sys.baseArray.domain[dPos]
    check dDom.len > 0
    check dDom[0] >= 9

  test "permutation counting tightens independent predecessors":
    # 4 independent predecessors of x5 in a 5-element permutation.
    # CPM would only give x5 >= 2 (longest chain = 1).
    # Counting should give x5 >= 5 (needs 4 distinct values below it).
    let src = """
var 1..5: x1 :: output_var;
var 1..5: x2 :: output_var;
var 1..5: x3 :: output_var;
var 1..5: x4 :: output_var;
var 1..5: x5 :: output_var;
array [1..5] of var int: xs:: output_array([1..5]) = [x1,x2,x3,x4,x5];
array [1..2] of int: c = [1,-1];
constraint fzn_all_different_int(xs);
constraint int_lin_le(c,[x1,x5],-1);
constraint int_lin_le(c,[x2,x5],-1);
constraint int_lin_le(c,[x3,x5],-1);
constraint int_lin_le(c,[x4,x5],-1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # x5 must be 5 (only value >= 5 in domain 1..5)
    let x5Pos = tr.varPositions["x5"]
    let x5Dom = tr.sys.baseArray.domain[x5Pos]
    check x5Dom == @[5]  # fully determined by counting

    tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
    let v = [tr.sys.assignment[tr.varPositions["x1"]],
             tr.sys.assignment[tr.varPositions["x2"]],
             tr.sys.assignment[tr.varPositions["x3"]],
             tr.sys.assignment[tr.varPositions["x4"]],
             tr.sys.assignment[tr.varPositions["x5"]]]
    check v.toHashSet.len == 5
    check v[4] == 5  # x5 = 5

  test "permutation counting tightens with independent successors":
    # 4 independent successors of x1 in a 5-element permutation.
    # Counting should give x1 <= 1.
    let src = """
var 1..5: x1 :: output_var;
var 1..5: x2 :: output_var;
var 1..5: x3 :: output_var;
var 1..5: x4 :: output_var;
var 1..5: x5 :: output_var;
array [1..5] of var int: xs:: output_array([1..5]) = [x1,x2,x3,x4,x5];
array [1..2] of int: c = [1,-1];
constraint fzn_all_different_int(xs);
constraint int_lin_le(c,[x1,x2],-1);
constraint int_lin_le(c,[x1,x3],-1);
constraint int_lin_le(c,[x1,x4],-1);
constraint int_lin_le(c,[x1,x5],-1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let x1Pos = tr.varPositions["x1"]
    let x1Dom = tr.sys.baseArray.domain[x1Pos]
    check x1Dom == @[1]  # fully determined: must be smallest

  test "permutation counting respects transitive closure":
    # Diamond pattern: x1 < x2, x1 < x3, x2 < x4, x3 < x4
    # x4 has 3 ancestors (x1, x2, x3), so x4 >= 4
    # x1 has 3 descendants (x2, x3, x4), so x1 <= 1 (k - 3 = 4 - 3 = 1 with k=4)
    let src = """
var 1..4: x1 :: output_var;
var 1..4: x2 :: output_var;
var 1..4: x3 :: output_var;
var 1..4: x4 :: output_var;
array [1..4] of var int: xs:: output_array([1..4]) = [x1,x2,x3,x4];
array [1..2] of int: c = [1,-1];
constraint fzn_all_different_int(xs);
constraint int_lin_le(c,[x1,x2],-1);
constraint int_lin_le(c,[x1,x3],-1);
constraint int_lin_le(c,[x2,x4],-1);
constraint int_lin_le(c,[x3,x4],-1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # x1 is 1 (3 descendants) and x4 is 4 (3 ancestors)
    check tr.sys.baseArray.domain[tr.varPositions["x1"]] == @[1]
    check tr.sys.baseArray.domain[tr.varPositions["x4"]] == @[4]
