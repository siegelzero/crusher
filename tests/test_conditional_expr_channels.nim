## Tests for conditional expression channel detection and propagation.
##
## Covers:
## 1. detectConditionalExpressionChannels: int_lin_eq_reif + bool_clause → conditional channel
## 2. Bool-gated detection with non-channel (search variable) conditions
## 3. Channel propagation correctness through solve

import unittest
import std/[sequtils, tables, packedsets, sets]
import crusher
import flatzinc/[parser, translator]

suite "Conditional Expression Channel Detection":

  test "basic conditional expression: target = if cond then (a + b) else 0":
    ## Pattern from optional variable decomposition:
    ##   int_eq_reif(target, 0, isZero) :: defines_var(isZero)
    ##   int_lin_eq_reif([1, -1, -1], [target, a, b], 0, eqBool) :: defines_var(eqBool)
    ##   bool_clause([cond, isZero], [])          -- ¬cond → target == 0
    ##   array_bool_and([cond, eqBool], combined) :: defines_var(combined)
    let src = """
var 1..10: a :: output_var;
var 1..10: b :: output_var;
var 0..20: target :: output_var;
var bool: cond :: output_var;
var bool: isZero :: var_is_introduced :: is_defined_var;
var bool: eqBool :: var_is_introduced :: is_defined_var;
var bool: combined :: var_is_introduced :: is_defined_var;
array [1..3] of int: X_COEFFS = [1, -1, -1];
constraint int_eq_reif(target, 0, isZero) :: defines_var(isZero);
constraint int_lin_eq_reif(X_COEFFS, [target, a, b], 0, eqBool) :: defines_var(eqBool);
constraint bool_clause([cond, isZero], []);
constraint array_bool_and([cond, eqBool], combined) :: defines_var(combined);
constraint bool_eq(cond, true);
constraint int_eq(a, 3);
constraint int_eq(b, 5);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # target should be detected as a conditional expression channel
    check tr.boolGatedExprChannelDefs.len >= 1
    check tr.channelVarNames.contains("target")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let aVal = tr.sys.assignment[tr.varPositions["a"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let targetVal = tr.sys.assignment[tr.varPositions["target"]]

    check aVal == 3
    check bVal == 5
    check targetVal == 8  # cond=true, so target = a + b = 3 + 5

  test "conditional expression with false condition → default":
    ## Same pattern but cond = false, so target should be 0.
    let src = """
var 1..10: a :: output_var;
var 1..10: b :: output_var;
var 0..20: target :: output_var;
var bool: cond :: output_var;
var bool: isZero :: var_is_introduced :: is_defined_var;
var bool: eqBool :: var_is_introduced :: is_defined_var;
var bool: combined :: var_is_introduced :: is_defined_var;
array [1..3] of int: X_COEFFS = [1, -1, -1];
constraint int_eq_reif(target, 0, isZero) :: defines_var(isZero);
constraint int_lin_eq_reif(X_COEFFS, [target, a, b], 0, eqBool) :: defines_var(eqBool);
constraint bool_clause([cond, isZero], []);
constraint array_bool_and([cond, eqBool], combined) :: defines_var(combined);
constraint bool_eq(cond, false);
constraint int_eq(a, 7);
constraint int_eq(b, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.channelVarNames.contains("target")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let targetVal = tr.sys.assignment[tr.varPositions["target"]]
    check targetVal == 0  # cond=false, so target = 0 (default)

  test "conditional expression with non-zero default constant":
    ## target = if cond then (a + b) else -1 (used in optional GCC patterns)
    let src = """
var 1..10: a :: output_var;
var 1..10: b :: output_var;
var -1..20: target :: output_var;
var bool: cond :: output_var;
var bool: isDefault :: var_is_introduced :: is_defined_var;
var bool: eqBool :: var_is_introduced :: is_defined_var;
var bool: combined :: var_is_introduced :: is_defined_var;
array [1..3] of int: X_COEFFS = [1, -1, -1];
constraint int_eq_reif(target, -1, isDefault) :: defines_var(isDefault);
constraint int_lin_eq_reif(X_COEFFS, [target, a, b], 0, eqBool) :: defines_var(eqBool);
constraint bool_clause([cond, isDefault], []);
constraint array_bool_and([cond, eqBool], combined) :: defines_var(combined);
constraint bool_eq(cond, true);
constraint int_eq(a, 4);
constraint int_eq(b, 6);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.channelVarNames.contains("target")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let targetVal = tr.sys.assignment[tr.varPositions["target"]]
    check targetVal == 10  # cond=true, target = a + b = 4 + 6

  test "conditional expression with defined-var operands":
    ## Expression operands are themselves defined vars (from int_times squaring).
    ## target = if cond then (sq_a + sq_b) else 0
    ## where sq_a = a * a, sq_b = b * b (defined vars via int_times)
    let src = """
var 1..5: a :: output_var;
var 1..5: b :: output_var;
var 0..25: sq_a :: var_is_introduced :: is_defined_var;
var 0..25: sq_b :: var_is_introduced :: is_defined_var;
var 0..50: target :: output_var;
var bool: cond :: output_var;
var bool: isZero :: var_is_introduced :: is_defined_var;
var bool: eqBool :: var_is_introduced :: is_defined_var;
var bool: combined :: var_is_introduced :: is_defined_var;
array [1..3] of int: X_COEFFS = [1, -1, -1];
constraint int_times(a, a, sq_a) :: defines_var(sq_a);
constraint int_times(b, b, sq_b) :: defines_var(sq_b);
constraint int_eq_reif(target, 0, isZero) :: defines_var(isZero);
constraint int_lin_eq_reif(X_COEFFS, [target, sq_a, sq_b], 0, eqBool) :: defines_var(eqBool);
constraint bool_clause([cond, isZero], []);
constraint array_bool_and([cond, eqBool], combined) :: defines_var(combined);
constraint bool_eq(cond, true);
constraint int_eq(a, 3);
constraint int_eq(b, 4);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.channelVarNames.contains("target")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let targetVal = tr.sys.assignment[tr.varPositions["target"]]
    check targetVal == 25  # cond=true, target = 3² + 4² = 9 + 16 = 25

suite "Bool-Gated Channel with Search Variable Condition":

  test "bool-gated with non-channel condition variable":
    ## The condition is a plain search variable (not a channel/defined var).
    ## Pattern: x = if cond then y else 0
    ## where cond is a plain boolean (no defines_var annotation).
    let src = """
var 1..5: y :: output_var;
var 0..5: x :: output_var;
var bool: cond :: output_var;
var bool: b_eq_xy :: var_is_introduced :: is_defined_var;
var bool: b_eq_x0 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, y, b_eq_xy) :: defines_var(b_eq_xy);
constraint int_eq_reif(x, 0, b_eq_x0) :: defines_var(b_eq_x0);
constraint bool_clause([b_eq_xy], [cond]);
constraint bool_clause([b_eq_x0, cond], []);
constraint bool_eq(cond, true);
constraint int_eq(y, 4);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # x should be detected as a bool-gated channel even though cond is not a channel
    check tr.channelVarNames.contains("x")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    check xVal == 4  # cond=true, x = y = 4

  test "bool-gated with non-channel condition → default when false":
    let src = """
var 1..5: y :: output_var;
var 0..5: x :: output_var;
var bool: cond :: output_var;
var bool: b_eq_xy :: var_is_introduced :: is_defined_var;
var bool: b_eq_x0 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, y, b_eq_xy) :: defines_var(b_eq_xy);
constraint int_eq_reif(x, 0, b_eq_x0) :: defines_var(b_eq_x0);
constraint bool_clause([b_eq_xy], [cond]);
constraint bool_clause([b_eq_x0, cond], []);
constraint bool_eq(cond, false);
constraint int_eq(y, 4);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.channelVarNames.contains("x")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    check xVal == 0  # cond=false, x = default = 0
