## End-to-end tests for the value_precede / value_precede_chain decompositions,
## driven through crusher's FlatZinc pipeline with embedded FlatZinc source.
##
## Background (regression): the crusher mznlib previously redefined
## fzn_value_precede_int and fzn_value_precede_chain_int as `true` (no-ops),
## on the assumption that value precedence is only ever symmetry breaking. That
## is wrong — value_precede is a genuine semantic constraint, and stubbing it
## let the solver report assignments that violate it (e.g. value_precede(4,3,x)
## "satisfied" by x = [1,3,1,2], which has a 3 with no preceding 4).
##
## The fix routes value_precede through the standard boolean-chain decomposition
## (int_eq_reif + bool_clause) and decomposes value_precede_chain into pairwise
## value_precede on consecutive chain values. These tests embed the resulting
## FlatZinc shape directly and check the solved assignment actually satisfies the
## constraint.
##
## The decomposition encoded below is: "every occurrence of t must have an
## occurrence of s strictly before it" (equivalent to value_precede(s, t, x)),
## plus a clause forcing t to appear so the constraint actually bites.

import std/[unittest, tables]
import crusher
import flatzinc/[parser, translator]

proc satisfiesValuePrecede(x: seq[int], s, t: int): bool =
  ## value_precede(s, t, x): the first occurrence of s precedes the first
  ## occurrence of t, or t does not occur at all.
  var firstS = -1
  var firstT = -1
  for i, v in x:
    if v == s and firstS == -1: firstS = i
    if v == t and firstT == -1: firstT = i
  if firstT == -1: return true
  return firstS != -1 and firstS < firstT

proc solveX(src: string, names: openArray[string]): seq[int] =
  let model = parseFzn(src)
  var tr = translate(model)
  tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
  result = @[]
  for n in names:
    result.add(tr.sys.assignment[tr.varPositions[n]])

suite "value_precede FlatZinc end-to-end":

  test "value_precede(4, 3, x): a forced 3 must be preceded by a 4":
    # x[1..3] in 1..4. The bool_clause([t2, t3], []) forces a 3 at position 2
    # or 3; value precedence then forces a 4 strictly before it. A no-op
    # decomposition would let the solver leave the 3 with no preceding 4.
    let src = """
var 1..4: x1;
var 1..4: x2;
var 1..4: x3;
var bool: s1 :: is_defined_var;
var bool: s2 :: is_defined_var;
var bool: t2 :: is_defined_var;
var bool: t3 :: is_defined_var;
constraint int_eq_reif(x1, 4, s1) :: defines_var(s1);
constraint int_eq_reif(x2, 4, s2) :: defines_var(s2);
constraint int_eq_reif(x2, 3, t2) :: defines_var(t2);
constraint int_eq_reif(x3, 3, t3) :: defines_var(t3);
constraint int_ne(x1, 3);
constraint bool_clause([s1], [t2]);
constraint bool_clause([s1, s2], [t3]);
constraint bool_clause([t2, t3], []);
solve satisfy;
"""
    let x = solveX(src, ["x1", "x2", "x3"])
    check 3 in x                                  # the 3 was actually forced
    check satisfiesValuePrecede(x, 4, 3)

  test "value_precede_chain([4, 3, 2], x): a forced 2 pulls in 3 then 4":
    # x[1..4] in 1..4. The chain decomposes into value_precede(4,3) AND
    # value_precede(3,2). Forcing a 2 to appear requires a 3 before it, which
    # requires a 4 before that — so any valid solution has 4 ≺ 3 ≺ 2.
    let src = """
var 1..4: x1;
var 1..4: x2;
var 1..4: x3;
var 1..4: x4;
var bool: e4_1 :: is_defined_var;
var bool: e4_2 :: is_defined_var;
var bool: e4_3 :: is_defined_var;
var bool: e3_1 :: is_defined_var;
var bool: e3_2 :: is_defined_var;
var bool: e3_3 :: is_defined_var;
var bool: e3_4 :: is_defined_var;
var bool: e2_2 :: is_defined_var;
var bool: e2_3 :: is_defined_var;
var bool: e2_4 :: is_defined_var;
constraint int_eq_reif(x1, 4, e4_1) :: defines_var(e4_1);
constraint int_eq_reif(x2, 4, e4_2) :: defines_var(e4_2);
constraint int_eq_reif(x3, 4, e4_3) :: defines_var(e4_3);
constraint int_eq_reif(x1, 3, e3_1) :: defines_var(e3_1);
constraint int_eq_reif(x2, 3, e3_2) :: defines_var(e3_2);
constraint int_eq_reif(x3, 3, e3_3) :: defines_var(e3_3);
constraint int_eq_reif(x4, 3, e3_4) :: defines_var(e3_4);
constraint int_eq_reif(x2, 2, e2_2) :: defines_var(e2_2);
constraint int_eq_reif(x3, 2, e2_3) :: defines_var(e2_3);
constraint int_eq_reif(x4, 2, e2_4) :: defines_var(e2_4);
constraint int_ne(x1, 3);
constraint int_ne(x1, 2);
constraint bool_clause([e4_1], [e3_2]);
constraint bool_clause([e4_1, e4_2], [e3_3]);
constraint bool_clause([e4_1, e4_2, e4_3], [e3_4]);
constraint bool_clause([e3_1], [e2_2]);
constraint bool_clause([e3_1, e3_2], [e2_3]);
constraint bool_clause([e3_1, e3_2, e3_3], [e2_4]);
constraint bool_clause([e2_2, e2_3, e2_4], []);
solve satisfy;
"""
    let x = solveX(src, ["x1", "x2", "x3", "x4"])
    check 2 in x                                  # the 2 was actually forced
    check satisfiesValuePrecede(x, 4, 3)
    check satisfiesValuePrecede(x, 3, 2)
