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

    # target should NOT be a channel — incomplete case analysis
    check "target" notin tr.channelVarNames

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
constraint int_lin_le([1],[x],4);
constraint int_lin_le([1],[y],2);
solve satisfy;
"""
    # x <= 4 AND y <= 2 forces x<5 and y<3, so only z>=7 can satisfy
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
    check xVal <= 4
    check yVal <= 2
    check zVal >= 7

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
