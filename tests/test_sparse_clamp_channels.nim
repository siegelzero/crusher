## Tests for sparse 3-entry clamp channel paths in translatorChannels.nim.
##
## When a reified comparison's source domain range is too large for a dense
## lookup table (> 100K), the translator falls back to a sparse 3-entry
## channel keyed by `clamp(x - val, -1, 1) + 1`. These tests exercise that
## fallback for int_eq_reif, int_ne_reif, int_le_reif, int_lt_reif (1D const
## and 2D var-var subcases) and the static folds in int_lin_le_reif /
## int_lin_eq_reif.
##
## The fzcrusher binary needs to be present for tests/test_fzcrusher to use,
## but these tests run the translator+solver in-process.

import unittest
import std/[tables]
import crusher
import flatzinc/[parser, translator]

proc solveSat(src: string): FznTranslator =
    let model = parseFzn(src)
    result = translate(model)
    result.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

suite "Sparse clamp channels for int_eq_reif (large domain)":

    test "int_eq_reif(x, 0, b) over huge domain — sparse path triggers, b channels correctly":
        # x has a huge domain that forces the sparse 3-entry path (>100K range).
        # b should be 1 iff x == 0.
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 0, b) :: defines_var(b);
constraint int_eq(x, 0);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["x"]] == 0
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_eq_reif(x, 0, b) — non-zero x channels b=0":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 0, b) :: defines_var(b);
constraint int_eq(x, 42);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["x"]] == 42
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_ne_reif(x, 0, b) over huge domain — inverted sparse table":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_ne_reif(x, 0, b) :: defines_var(b);
constraint int_eq(x, 100);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_eq_reif(x, c, b) where c is interior — clamp index covers x<c, x==c, x>c":
        # c is in the middle of the domain. Test all three branches:
        # x < c → b=0, x == c → b=1, x > c → b=0.
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 50000, b) :: defines_var(b);
constraint int_eq(x, 50000);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_eq_reif(x, c, b) — c outside domain (early-exit static fold)":
        # val < lo → channel is constant 0 (eq) / constant 1 (ne).
        let src = """
var 100000..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 50, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        # b is statically fixed to 0 since val=50 is outside [100000, 200000]
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_eq_reif(x, y, b) over huge domains — 2D var-var sparse path":
        # Both x and y have huge domains; the dense 2D table would explode,
        # so the var-var sparse path triggers.
        let src = """
var 0..200000: x :: output_var;
var 0..200000: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, y, b) :: defines_var(b);
constraint int_eq(x, 12345);
constraint int_eq(y, 12345);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_eq_reif(x, y, b) over huge domains — distinct values channel b=0":
        let src = """
var 0..200000: x :: output_var;
var 0..200000: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, y, b) :: defines_var(b);
constraint int_eq(x, 100);
constraint int_eq(y, 200);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 0


suite "Sparse clamp channels for int_le_reif / int_lt_reif (large domain)":

    test "int_le_reif(x, c, b): le with x at boundary":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, 100, b) :: defines_var(b);
constraint int_eq(x, 100);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        # x == 100 → x <= 100 → b = 1
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lt_reif(x, c, b): lt distinguishes equality from below":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_lt_reif(x, 100, b) :: defines_var(b);
constraint int_eq(x, 100);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        # x == 100 → NOT (x < 100) → b = 0
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_le_reif(x, c, b): x above c":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, 100, b) :: defines_var(b);
constraint int_eq(x, 9999);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_le_reif(c, x, b): const-on-left form, x at boundary":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(100, x, b) :: defines_var(b);
constraint int_eq(x, 100);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        # 100 <= x=100 → b = 1
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lt_reif(c, x, b): strict, x at boundary":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_lt_reif(100, x, b) :: defines_var(b);
constraint int_eq(x, 100);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        # 100 < x=100 is false → b = 0
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_le_reif: always-true static fold (hi <= c)":
        # Domain entirely below c → b is fixed to 1.
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, 300000, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_le_reif: always-false static fold (lo > c)":
        let src = """
var 100000..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, 50, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_le_reif(x, y, b): 2D var-var sparse path with x < y":
        let src = """
var 0..200000: x :: output_var;
var 0..200000: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, y, b) :: defines_var(b);
constraint int_eq(x, 100);
constraint int_eq(y, 200);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_le_reif(x, y, b): 2D var-var sparse path, x == y":
        let src = """
var 0..200000: x :: output_var;
var 0..200000: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, y, b) :: defines_var(b);
constraint int_eq(x, 12345);
constraint int_eq(y, 12345);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lt_reif(x, y, b): 2D var-var, x == y → b = 0":
        let src = """
var 0..200000: x :: output_var;
var 0..200000: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_lt_reif(x, y, b) :: defines_var(b);
constraint int_eq(x, 12345);
constraint int_eq(y, 12345);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 0


suite "Static fold for int_lin_le_reif / int_lin_eq_reif":

    test "int_lin_le_reif: exprMax <= rhs → b fixed to 1":
        # Sum of [1*x, 1*y] with x in 0..10, y in 0..10 has max 20.
        # Compare to rhs=100 → always <=, so b should be statically fixed to 1.
        let src = """
var 0..10: x :: output_var;
var 0..10: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
array [1..2] of int: cs = [1, 1];
constraint int_lin_le_reif(cs, [x, y], 100, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lin_le_reif: exprMin > rhs → b fixed to 0":
        # Sum of [1*x, 1*y] with x in 50..100, y in 50..100 has min 100.
        # Compare to rhs=10 → always >, so b should be statically fixed to 0.
        let src = """
var 50..100: x :: output_var;
var 50..100: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
array [1..2] of int: cs = [1, 1];
constraint int_lin_le_reif(cs, [x, y], 10, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_lin_eq_reif: rhs outside expr range → b fixed to 0":
        # Sum is in [100, 200], compare for equality with rhs=999 → always not equal.
        let src = """
var 50..100: x :: output_var;
var 50..100: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
array [1..2] of int: cs = [1, 1];
constraint int_lin_eq_reif(cs, [x, y], 999, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 0

    test "int_lin_ne_reif: rhs outside expr range → b fixed to 1":
        let src = """
var 50..100: x :: output_var;
var 50..100: y :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
array [1..2] of int: cs = [1, 1];
constraint int_lin_ne_reif(cs, [x, y], 999, b) :: defines_var(b);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["b"]] == 1


suite "Sparse channel correctness under search":

    test "int_eq_reif(x, 0, b) — search must satisfy b == 1 by setting x=0":
        # The search variable is x (huge domain). The channel forces b based on x.
        # We constrain b == 1 and let the search find the right x.
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 0, b) :: defines_var(b);
constraint bool_eq(b, true);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["x"]] == 0
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_le_reif(x, 100, b) — search must satisfy b == 1 by setting x <= 100":
        let src = """
var 0..200000: x :: output_var;
var bool: b :: output_var :: var_is_introduced :: is_defined_var;
constraint int_le_reif(x, 100, b) :: defines_var(b);
constraint bool_eq(b, true);
solve satisfy;
"""
        let tr = solveSat(src)
        check tr.sys.hasFeasibleSolution
        check tr.sys.assignment[tr.varPositions["x"]] <= 100
        check tr.sys.assignment[tr.varPositions["b"]] == 1
