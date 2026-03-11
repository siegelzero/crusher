## Tests for conditional implication channel detection and solving:
## 1. Binary conditional channels: Z = element(cond, [val0, val1])
##    from complementary int_lin_le_reif + bool_clause([eq_reif(Z,X)],[cond]) patterns.
## 2. One-hot conditional channels: Z = element(weighted_index, [v_0, ..., v_{N-1}])
##    from exhaustive bool_clause([eq_reif(Z,v_i)],[eq_reif(X_i,c)]) patterns.

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]
import crusher
import flatzinc/[parser, translator]

proc getObjectiveExpr(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
  elif tr.objectivePos == ObjPosDefinedExpr: tr.objectiveDefExpr
  else: raise newException(ValueError, "No objective")

suite "Binary Conditional Implication Channels":

  test "binary conditional channel detection — min/max pair":
    ## Pattern: Z = min(A, B) decomposed via complementary int_lin_le_reif.
    ## bool_clause([eq_reif(Z, A)], [lt_AB]) — when A < B, Z = A
    ## bool_clause([eq_reif(Z, B)], [lt_BA]) — when B < A, Z = B
    ## lt_AB: int_lin_le_reif([1,-1],[A,B],-1, lt_AB)  (A - B <= -1 → A < B)
    ## lt_BA: int_lin_le_reif([1,-1],[B,A],-1, lt_BA)  (B - A <= -1 → B < A)
    let src = """
var 1..5: a :: output_var;
var 1..5: b :: output_var;
var 1..5: z :: output_var;
var bool: lt_ab :: var_is_introduced :: is_defined_var;
var bool: lt_ba :: var_is_introduced :: is_defined_var;
var bool: eq_za :: var_is_introduced :: is_defined_var;
var bool: eq_zb :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[a,b],-1, lt_ab) :: defines_var(lt_ab);
constraint int_lin_le_reif([1,-1],[b,a],-1, lt_ba) :: defines_var(lt_ba);
constraint int_eq_reif(z, a, eq_za) :: defines_var(eq_za);
constraint int_eq_reif(z, b, eq_zb) :: defines_var(eq_zb);
constraint bool_clause([eq_za],[lt_ab]);
constraint bool_clause([eq_zb],[lt_ba]);
constraint int_ne(a, b);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Z should be detected as a binary conditional channel
    check tr.binaryCondChannelDefs.len == 1
    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let aVal = tr.sys.assignment[tr.varPositions["a"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]

    check aVal != bVal
    # Z should be min(a, b) since the conditions enforce it
    check zVal == min(aVal, bVal)

  test "binary conditional channel optimization — minimize max":
    ## Z = max(A, B) via complementary conditions. Minimize Z with constraints.
    ## When A < B: Z = B. When B < A: Z = A. So Z = max(A, B).
    let src = """
var 1..5: a :: output_var;
var 1..5: b :: output_var;
var 1..5: z :: output_var;
var bool: lt_ab :: var_is_introduced :: is_defined_var;
var bool: lt_ba :: var_is_introduced :: is_defined_var;
var bool: eq_zb :: var_is_introduced :: is_defined_var;
var bool: eq_za :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[a,b],-1, lt_ab) :: defines_var(lt_ab);
constraint int_lin_le_reif([1,-1],[b,a],-1, lt_ba) :: defines_var(lt_ba);
constraint int_eq_reif(z, b, eq_zb) :: defines_var(eq_zb);
constraint int_eq_reif(z, a, eq_za) :: defines_var(eq_za);
constraint bool_clause([eq_zb],[lt_ab]);
constraint bool_clause([eq_za],[lt_ba]);
constraint int_ne(a, b);
solve minimize z;
"""
    for trial in 0..<5:
      let model = parseFzn(src)
      var tr = translate(model)

      check tr.binaryCondChannelDefs.len == 1
      check "z" in tr.channelVarNames

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      let aVal = tr.sys.assignment[tr.varPositions["a"]]
      let bVal = tr.sys.assignment[tr.varPositions["b"]]
      let zVal = objExpr.evaluate(tr.sys.assignment)

      check aVal != bVal
      check zVal == max(aVal, bVal)
      # Optimal: a=1, b=2 (or vice versa), z=max(1,2)=2
      check zVal == 2

  test "binary conditional channel — non-complementary rhs rejected":
    ## int_lin_le_reif with rhs=0 (<=, not <) should NOT be detected
    ## as a binary conditional channel because the conditions aren't
    ## truly complementary (both true when A == B).
    let src = """
var 1..3: a :: output_var;
var 1..3: b :: output_var;
var 1..3: z :: output_var;
var bool: le_ab :: var_is_introduced :: is_defined_var;
var bool: le_ba :: var_is_introduced :: is_defined_var;
var bool: eq_za :: var_is_introduced :: is_defined_var;
var bool: eq_zb :: var_is_introduced :: is_defined_var;
constraint int_lin_le_reif([1,-1],[a,b],0, le_ab) :: defines_var(le_ab);
constraint int_lin_le_reif([1,-1],[b,a],0, le_ba) :: defines_var(le_ba);
constraint int_eq_reif(z, a, eq_za) :: defines_var(eq_za);
constraint int_eq_reif(z, b, eq_zb) :: defines_var(eq_zb);
constraint bool_clause([eq_za],[le_ab]);
constraint bool_clause([eq_zb],[le_ba]);
constraint int_ne(a, b);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should NOT be detected (rhs=0, not -1)
    check tr.binaryCondChannelDefs.len == 0
    check "z" notin tr.channelVarNames

suite "One-Hot Conditional Implication Channels":

  test "one-hot conditional channel detection — 3-variable permutation":
    ## Pattern: 3 variables X1, X2, X3 with domain {1,2,3}, allDifferent.
    ## Z is determined by which variable equals a constant c=1:
    ##   bool_clause([eq_reif(Z, 10)], [eq_reif(X1, 1)])  — if X1=1 then Z=10
    ##   bool_clause([eq_reif(Z, 20)], [eq_reif(X2, 1)])  — if X2=1 then Z=20
    ##   bool_clause([eq_reif(Z, 30)], [eq_reif(X3, 1)])  — if X3=1 then Z=30
    let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 10..30: z :: output_var;
var bool: eq_x1_1 :: var_is_introduced :: is_defined_var;
var bool: eq_x2_1 :: var_is_introduced :: is_defined_var;
var bool: eq_x3_1 :: var_is_introduced :: is_defined_var;
var bool: eq_z_10 :: var_is_introduced :: is_defined_var;
var bool: eq_z_20 :: var_is_introduced :: is_defined_var;
var bool: eq_z_30 :: var_is_introduced :: is_defined_var;
array [1..3] of var int: xs :: output_array([1..3]) = [x1, x2, x3];
constraint gecode_all_different_int(xs);
constraint int_eq_reif(x1, 1, eq_x1_1) :: defines_var(eq_x1_1);
constraint int_eq_reif(x2, 1, eq_x2_1) :: defines_var(eq_x2_1);
constraint int_eq_reif(x3, 1, eq_x3_1) :: defines_var(eq_x3_1);
constraint int_eq_reif(z, 10, eq_z_10) :: defines_var(eq_z_10);
constraint int_eq_reif(z, 20, eq_z_20) :: defines_var(eq_z_20);
constraint int_eq_reif(z, 30, eq_z_30) :: defines_var(eq_z_30);
constraint bool_clause([eq_z_10],[eq_x1_1]);
constraint bool_clause([eq_z_20],[eq_x2_1]);
constraint bool_clause([eq_z_30],[eq_x3_1]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Z should be detected as a one-hot conditional channel
    check tr.oneHotCondChannelDefs.len == 1
    check "z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let x1 = tr.sys.assignment[tr.varPositions["x1"]]
    let x2 = tr.sys.assignment[tr.varPositions["x2"]]
    let x3 = tr.sys.assignment[tr.varPositions["x3"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]

    check @[x1, x2, x3].sorted == @[1, 2, 3]

    # Z = 10 if X1=1, 20 if X2=1, 30 if X3=1
    let expected = if x1 == 1: 10 elif x2 == 1: 20 else: 30
    check zVal == expected

  test "one-hot conditional channel optimization — minimize":
    ## Minimize Z where Z depends on which variable in a permutation
    ## equals a target constant. The solver must propagate through the
    ## one-hot channel to find the optimal assignment.
    let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 5..15: z :: output_var;
var bool: eq_x1_1 :: var_is_introduced :: is_defined_var;
var bool: eq_x2_1 :: var_is_introduced :: is_defined_var;
var bool: eq_x3_1 :: var_is_introduced :: is_defined_var;
var bool: eq_z_5 :: var_is_introduced :: is_defined_var;
var bool: eq_z_10 :: var_is_introduced :: is_defined_var;
var bool: eq_z_15 :: var_is_introduced :: is_defined_var;
array [1..3] of var int: xs :: output_array([1..3]) = [x1, x2, x3];
constraint gecode_all_different_int(xs);
constraint int_eq_reif(x1, 1, eq_x1_1) :: defines_var(eq_x1_1);
constraint int_eq_reif(x2, 1, eq_x2_1) :: defines_var(eq_x2_1);
constraint int_eq_reif(x3, 1, eq_x3_1) :: defines_var(eq_x3_1);
constraint int_eq_reif(z, 15, eq_z_15) :: defines_var(eq_z_15);
constraint int_eq_reif(z, 10, eq_z_10) :: defines_var(eq_z_10);
constraint int_eq_reif(z, 5, eq_z_5) :: defines_var(eq_z_5);
constraint bool_clause([eq_z_15],[eq_x1_1]);
constraint bool_clause([eq_z_10],[eq_x2_1]);
constraint bool_clause([eq_z_5],[eq_x3_1]);
solve minimize z;
"""
    for trial in 0..<5:
      let model = parseFzn(src)
      var tr = translate(model)

      check tr.oneHotCondChannelDefs.len == 1
      check "z" in tr.channelVarNames

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      let x1 = tr.sys.assignment[tr.varPositions["x1"]]
      let x2 = tr.sys.assignment[tr.varPositions["x2"]]
      let x3 = tr.sys.assignment[tr.varPositions["x3"]]
      let zVal = objExpr.evaluate(tr.sys.assignment)

      check @[x1, x2, x3].sorted == @[1, 2, 3]

      # Z = 15 if X1=1, 10 if X2=1, 5 if X3=1
      # Optimal: X3=1, Z=5
      check zVal == 5
      check x3 == 1

  test "one-hot conditional channel — incomplete pattern not detected":
    ## If only 2 out of 3 required bool_clause entries are present,
    ## the pattern should NOT be detected (incomplete coverage).
    let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 10..30: z :: output_var;
var bool: eq_x1_1 :: var_is_introduced :: is_defined_var;
var bool: eq_x2_1 :: var_is_introduced :: is_defined_var;
var bool: eq_z_10 :: var_is_introduced :: is_defined_var;
var bool: eq_z_20 :: var_is_introduced :: is_defined_var;
array [1..3] of var int: xs :: output_array([1..3]) = [x1, x2, x3];
constraint gecode_all_different_int(xs);
constraint int_eq_reif(x1, 1, eq_x1_1) :: defines_var(eq_x1_1);
constraint int_eq_reif(x2, 1, eq_x2_1) :: defines_var(eq_x2_1);
constraint int_eq_reif(z, 10, eq_z_10) :: defines_var(eq_z_10);
constraint int_eq_reif(z, 20, eq_z_20) :: defines_var(eq_z_20);
constraint bool_clause([eq_z_10],[eq_x1_1]);
constraint bool_clause([eq_z_20],[eq_x2_1]);
constraint int_le(z, 30);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should NOT detect one-hot: only 2 entries for domain size 3
    check tr.oneHotCondChannelDefs.len == 0
    check "z" notin tr.channelVarNames
