## One-direction implications (cond == c -> T == v) leave T free when the
## condition does not hold. Case analysis must not default a binary T to the
## other value, and an implication table must allow every condition value no
## implication mentions (sdn-chain: "unselected domain -> link off" forced
## every link of a selected domain on, then barred selecting the domain).

import unittest
import std/[tables, sets]
import crusher
import flatzinc/[parser, translator]

suite "One-direction implications":

  test "sel = 0 -> link = 0 alone leaves the links free when sel = 1":
    # Exactly one of two links is on; each needs sel. Defaulting
    # "sel = 1 -> link = 1" would force both on (infeasible).
    let src = """
var 0..1: sel :: output_var;
var 0..1: lnk1 :: output_var;
var 0..1: lnk2 :: output_var;
var bool: off1 :: var_is_introduced :: is_defined_var;
var bool: off2 :: var_is_introduced :: is_defined_var;
var bool: c_sel :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(lnk1, 0, off1) :: defines_var(off1);
constraint int_eq_reif(lnk2, 0, off2) :: defines_var(off2);
constraint int_ne_reif(sel, 0, c_sel) :: defines_var(c_sel);
constraint bool_clause([off1, c_sel], []);
constraint bool_clause([off2, c_sel], []);
constraint int_lin_eq([1, 1], [lnk1, lnk2], 1);
solve satisfy;
"""
    var tr = translate(parseFzn(src))
    check "lnk1" notin tr.channelVarNames
    check "lnk2" notin tr.channelVarNames
    tr.sys.resolve(parallel = false, tabuThreshold = 2000, verbose = false)
    check tr.sys.hasFeasibleSolution
    let a = tr.sys.assignment
    check a[tr.varPositions["sel"]] == 1
    check a[tr.varPositions["lnk1"]] + a[tr.varPositions["lnk2"]] == 1

  test "implication table allows condition values it does not mention":
    # x == 1 -> y == 2 says nothing about x in {2, 3}
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: c1 :: var_is_introduced :: is_defined_var;
var bool: y2 :: var_is_introduced :: is_defined_var;
constraint int_ne_reif(x, 1, c1) :: defines_var(c1);
constraint int_eq_reif(y, 2, y2) :: defines_var(y2);
constraint bool_clause([c1, y2], []);
constraint int_lin_le([-1, 1], [x, y], -1);
solve satisfy;
"""
    var tr = translate(parseFzn(src))
    tr.sys.resolve(parallel = false, tabuThreshold = 2000, verbose = false)
    check tr.sys.hasFeasibleSolution
    let a = tr.sys.assignment
    let (x, y) = (a[tr.varPositions["x"]], a[tr.varPositions["y"]])
    check y < x
    check x != 1 or y == 2
