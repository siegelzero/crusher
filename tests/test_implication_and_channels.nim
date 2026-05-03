## Tests for implication-AND channel detection:
## detectImplicationAndChannels recognizes the pattern
##   bool_clause([..., b, ...], [N_1, ..., N_n])  -- LHS → b where
##                                                   LHS = ¬P_others ∧ N's
##   bool2int(b, c)                                -- c sums into a count
##   int_lin_le([1,...,1], [..., c, ...], K)       -- the count constraint
##
## When b's only constraint usages are the clause and the bool2int (degree 2),
## and c's only usages are the bool2int and the int_lin_le, we channel
## b = AND(forcing literals) which removes b from search positions and ties it
## directly to its forcing condition.
##
## int_lin_eq is intentionally rejected: with `Σ b = K` the original may set
## b > LHS to reach K when Σ LHS < K, and forcing b = LHS would lose those
## solutions. Only int_lin_le is sound (rewrite never tightens an upper bound
## into infeasibility).

import unittest
import std/[sequtils, sets]
import flatzinc/[parser, translator]

suite "Implication-AND Channel Detection":

  test "basic b = AND(¬P, N) from 2-pos-1-neg clause + sum":
    ## b's clause has another positive P and one negative N. b is forced up by
    ## ¬P ∧ N. Sum constraint Σ c ≤ 1 makes the count tight. Detector should
    ## channelize b.
    let src = """
var bool: P;
var bool: N;
var bool: b1;
var bool: b2;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
var 0..1: c2 :: var_is_introduced :: is_defined_var;
array [1..2] of var int: cs :: var_is_introduced = [c1, c2];
array [1..2] of int: ones = [1, 1];
constraint bool_clause([P, b1], [N]);
constraint bool_clause([P, b2], [N]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint bool2int(b2, c2) :: defines_var(c2);
constraint int_lin_le(ones, cs, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b1" in tr.channelVarNames
    check "b2" in tr.channelVarNames
    check tr.implicationAndChannelDefs.anyIt(it.targetVar == "b1")
    check tr.implicationAndChannelDefs.anyIt(it.targetVar == "b2")
    let def = tr.implicationAndChannelDefs.filterIt(it.targetVar == "b1")[0]
    check def.clauses.len == 1
    check def.clauses[0].otherPosLits.toHashSet() == ["P"].toHashSet()
    check def.clauses[0].negLits.toHashSet() == ["N"].toHashSet()

  test "multi-positive clause: extra positives appear in AND-target's body":
    ## Clause [b1, P1, P2] with negatives [N1] for b1; clause [b2] [N2] for b2.
    let src = """
var bool: P1;
var bool: P2;
var bool: N1;
var bool: N2;
var bool: b1;
var bool: b2;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
var 0..1: c2 :: var_is_introduced :: is_defined_var;
array [1..2] of var int: cs :: var_is_introduced = [c1, c2];
array [1..2] of int: ones = [1, 1];
constraint bool_clause([P1, P2, b1], [N1]);
constraint bool_clause([b2], [N2]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint bool2int(b2, c2) :: defines_var(c2);
constraint int_lin_le(ones, cs, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b1" in tr.channelVarNames
    check "b2" in tr.channelVarNames
    let def = tr.implicationAndChannelDefs.filterIt(it.targetVar == "b1")[0]
    check def.clauses.len == 1
    check def.clauses[0].otherPosLits.toHashSet() == ["P1", "P2"].toHashSet()
    check def.clauses[0].negLits.toHashSet() == ["N1"].toHashSet()

  test "multi-clause forcer: b channels as OR-of-AND from K bool_clauses":
    ## b appears as positive in two bool_clauses; b is forced if either
    ## clause's body is fully satisfied. Channel as OR over per-clause AND.
    let src = """
var bool: N1;
var bool: N2;
var bool: P;
var bool: b1;
var bool: b2;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
var 0..1: c2 :: var_is_introduced :: is_defined_var;
array [1..2] of var int: cs :: var_is_introduced = [c1, c2];
array [1..2] of int: ones = [1, 1];
constraint bool_clause([b1], [N1]);
constraint bool_clause([P, b1], [N2]);
constraint bool_clause([b2], [P]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint bool2int(b2, c2) :: defines_var(c2);
constraint int_lin_le(ones, cs, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b1" in tr.channelVarNames
    let def = tr.implicationAndChannelDefs.filterIt(it.targetVar == "b1")[0]
    check def.clauses.len == 2

  test "rejects int_lin_eq (unsound when K can exceed Σ LHS)":
    ## Σ c = K with K > Σ LHS allows the original to set b = 1 above LHS to
    ## reach K. The rewrite forces b = LHS, losing those solutions. Detector
    ## must reject int_lin_eq even with positive coefs.
    let src = """
var bool: P1;
var bool: P2;
var bool: N1;
var bool: N2;
var bool: b1;
var bool: b2;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
var 0..1: c2 :: var_is_introduced :: is_defined_var;
array [1..2] of var int: cs :: var_is_introduced = [c1, c2];
array [1..2] of int: ones = [1, 1];
constraint bool_clause([P1, b1], [N1]);
constraint bool_clause([P2, b2], [N2]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint bool2int(b2, c2) :: defines_var(c2);
constraint int_lin_eq(ones, cs, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.implicationAndChannelDefs.anyIt(it.targetVar == "b1")
    check not tr.implicationAndChannelDefs.anyIt(it.targetVar == "b2")

  test "rejects when sum is monotone-down (≥-style)":
    ## With Σ c ≥ K, channeling b to its minimum may make ≥ infeasible where
    ## the original allowed extra b=1. Detector represents ≥ as int_lin_le with
    ## negative coefs; coef = -1 must be rejected.
    let src = """
var bool: N;
var bool: b1;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
array [1..1] of var int: cs :: var_is_introduced = [c1];
array [1..1] of int: negOnes = [-1];
constraint bool_clause([b1], [N]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint int_lin_le(negOnes, cs, -1);  % -c <= -1  ≡  c >= 1
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.implicationAndChannelDefs.anyIt(it.targetVar == "b1")

  test "rejects when b has additional reference outside clause+bool2int":
    ## If b appears in any extra constraint, the rewrite isn't sound — channel
    ## binds b to ¬Q which may break that other constraint. Reject.
    let src = """
var bool: N;
var bool: b1;
var bool: other;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
array [1..1] of var int: cs :: var_is_introduced = [c1];
array [1..1] of int: ones = [1];
constraint bool_clause([b1], [N]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint int_lin_le(ones, cs, 1);
constraint bool_eq(b1, other);   % extra usage of b1
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.implicationAndChannelDefs.anyIt(it.targetVar == "b1")

  test "rejects when c has additional reference outside bool2int+int_lin_le":
    ## c is the bool2int output; if it's also used in an unrelated constraint
    ## (e.g., int_ne(c, 0) below), narrowing b via the channel narrows c, which
    ## could violate that other constraint. Reject.
    let src = """
var bool: N;
var bool: b1;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
array [1..1] of var int: cs :: var_is_introduced = [c1];
array [1..1] of int: ones = [1];
constraint bool_clause([b1], [N]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint int_lin_le(ones, cs, 1);
constraint int_ne(c1, 0);   % extra usage of c1
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.implicationAndChannelDefs.anyIt(it.targetVar == "b1")

  test "channels propagate end-to-end: HRC bp pattern shape":
    let src = """
var bool: P1 :: output_var;
var bool: N1 :: output_var;
var bool: P2 :: output_var;
var bool: N2 :: output_var;
var bool: b1;
var bool: b2;
var 0..1: c1 :: var_is_introduced :: is_defined_var;
var 0..1: c2 :: var_is_introduced :: is_defined_var;
array [1..2] of var int: cs :: var_is_introduced = [c1, c2];
array [1..2] of int: ones = [1, 1];
constraint bool_clause([P1, b1], [N1]);
constraint bool_clause([P2, b2], [N2]);
constraint bool2int(b1, c1) :: defines_var(c1);
constraint bool2int(b2, c2) :: defines_var(c2);
constraint int_lin_le(ones, cs, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b1" in tr.channelVarNames
    check "b2" in tr.channelVarNames
