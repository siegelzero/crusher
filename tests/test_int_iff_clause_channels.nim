## 0/1 integers defined by an equivalence with a clause channel
## (x = 1 <-> exists(...)) become channels, recursive definitions included
## when every recursive path is positive (sdn-chain's domain_path
## reachability matrix). A definition that reaches itself negatively stays a
## search variable: its propagation need not settle.

import unittest
import std/[tables, sets]
import crusher
import flatzinc/[parser, translator]

suite "Int clause-iff channels":

  test "mutually recursive reachability becomes channels and stays consistent":
    # r2 <-> l12 \/ (l32 /\ r3);  r3 <-> l23 /\ r2;  r2 + r3 >= 1
    let src = """
var 0..1: l12 :: output_var;
var 0..1: l23 :: output_var;
var 0..1: l32 :: output_var;
var 0..1: r2 :: output_var;
var 0..1: r3 :: output_var;
var bool: e12 :: var_is_introduced :: is_defined_var;
var bool: e23 :: var_is_introduced :: is_defined_var;
var bool: e32 :: var_is_introduced :: is_defined_var;
var bool: r2e1 :: var_is_introduced :: is_defined_var;
var bool: r2e0 :: var_is_introduced :: is_defined_var;
var bool: r3e1 :: var_is_introduced :: is_defined_var;
var bool: r3e0 :: var_is_introduced :: is_defined_var;
var bool: a32 :: var_is_introduced :: is_defined_var;
var bool: a23 :: var_is_introduced :: is_defined_var;
var bool: s2 :: var_is_introduced :: is_defined_var;
var bool: s3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(l12, 1, e12) :: defines_var(e12);
constraint int_eq_reif(l23, 1, e23) :: defines_var(e23);
constraint int_eq_reif(l32, 1, e32) :: defines_var(e32);
constraint int_eq_reif(r2, 1, r2e1) :: defines_var(r2e1);
constraint int_eq_reif(r2, 0, r2e0) :: defines_var(r2e0);
constraint int_eq_reif(r3, 1, r3e1) :: defines_var(r3e1);
constraint int_eq_reif(r3, 0, r3e0) :: defines_var(r3e0);
constraint array_bool_and([e32, r3e1], a32) :: defines_var(a32);
constraint array_bool_and([e23, r2e1], a23) :: defines_var(a23);
constraint bool_clause_reif([e12, a32], [], s2) :: defines_var(s2);
constraint bool_clause_reif([a23], [], s3) :: defines_var(s3);
constraint bool_clause([r2e1], [s2]);
constraint bool_clause([e12, a32, r2e0], []);
constraint bool_clause([r3e1], [s3]);
constraint bool_clause([a23, r3e0], []);
constraint int_lin_le([-1, -1], [r2, r3], -1);
solve satisfy;
"""
    var tr = translate(parseFzn(src))
    check "r2" in tr.channelVarNames
    check "r3" in tr.channelVarNames
    check "r2" in tr.recursiveIffChannelNames
    check "r3" in tr.recursiveIffChannelNames
    tr.sys.resolve(parallel = false, tabuThreshold = 2000, verbose = false)
    check tr.sys.hasFeasibleSolution
    let a = tr.sys.assignment
    template v(n: string): int = a[tr.varPositions[n]]
    check v("r2") + v("r3") >= 1
    check v("r2") == int(v("l12") == 1 or (v("l32") == 1 and v("r3") == 1))
    check v("r3") == int(v("l23") == 1 and v("r2") == 1)

  test "a definition that reaches itself negatively stays searched":
    # x <-> (y = 0) \/ (z = 1);  y <-> (x = 1): x <-> not x \/ z forces z = 1
    let src = """
var 0..1: x :: output_var;
var 0..1: y :: output_var;
var 0..1: z :: output_var;
var bool: xe1 :: var_is_introduced :: is_defined_var;
var bool: xe0 :: var_is_introduced :: is_defined_var;
var bool: ye1 :: var_is_introduced :: is_defined_var;
var bool: ye0 :: var_is_introduced :: is_defined_var;
var bool: ze1 :: var_is_introduced :: is_defined_var;
var bool: sx :: var_is_introduced :: is_defined_var;
var bool: sy :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, xe1) :: defines_var(xe1);
constraint int_eq_reif(x, 0, xe0) :: defines_var(xe0);
constraint int_eq_reif(y, 1, ye1) :: defines_var(ye1);
constraint int_eq_reif(y, 0, ye0) :: defines_var(ye0);
constraint int_eq_reif(z, 1, ze1) :: defines_var(ze1);
constraint bool_clause_reif([ye0, ze1], [], sx) :: defines_var(sx);
constraint bool_clause_reif([xe1], [], sy) :: defines_var(sy);
constraint bool_clause([xe1], [sx]);
constraint bool_clause([ye0, ze1, xe0], []);
constraint bool_clause([ye1], [sy]);
constraint bool_clause([xe1, ye0], []);
solve satisfy;
"""
    var tr = translate(parseFzn(src))
    check "x" notin tr.recursiveIffChannelNames
    check "y" notin tr.recursiveIffChannelNames
    check not ("x" in tr.channelVarNames and "y" in tr.channelVarNames)
    tr.sys.resolve(parallel = false, tabuThreshold = 2000, verbose = false)
    check tr.sys.hasFeasibleSolution
    let a = tr.sys.assignment
    template v(n: string): int = a[tr.varPositions[n]]
    check v("z") == 1
    check v("x") == 1
    check v("y") == 1
