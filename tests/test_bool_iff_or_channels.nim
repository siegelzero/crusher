## Tests for bool clause iff channels and bool OR channels:
## 1. detectBoolClauseIffChannels: bool_clause([b],[c]) + bool_clause(pos,[b,...]) → b ↔ c
## 2. detectBoolOrChannels: b = c ∨ prev from if-then-else on booleans
## 3. Temporal chain cascading via fixpoint iteration

import unittest
import std/[sequtils, sets, tables, packedsets]
import crusher
import flatzinc/[parser, translator]

suite "Bool Clause Iff Channel Detection":

  test "b ↔ c via two clauses with matching literals":
    ## bool_clause_reif([p,q], [], c) :: defines_var(c) defines c ↔ (p ∨ q).
    ## bool_clause([b], [c]) gives c → b.
    ## bool_clause([p, q], [b]) gives b → (p ∨ q) ↔ c.
    ## Together: b ↔ c.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: p :: var_is_introduced :: is_defined_var;
var bool: q :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, p) :: defines_var(p);
constraint int_eq_reif(y, 1, q) :: defines_var(q);
constraint bool_clause_reif([p, q], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_clause([p, q], [b]);
constraint int_eq(x, 1);
constraint int_eq(y, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # c should be a channel (from reif detection)
    check "c" in tr.channelVarNames
    # b should be detected as iff alias of c
    check "b" in tr.channelVarNames
    check tr.boolEquivAliasDefs.anyIt(it.aliasVar == "b" and it.canonicalVar == "c")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let cVal = tr.sys.assignment[tr.varPositions["c"]]

    # p=1 (x==1), q=0 (y!=1), so c = p ∨ q = 1, b = c = 1
    check cVal == 1
    check bVal == 1

  test "b ↔ c both false when clause is unsatisfied":
    ## Same structure but neither p nor q is true.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: p :: var_is_introduced :: is_defined_var;
var bool: q :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, p) :: defines_var(p);
constraint int_eq_reif(y, 1, q) :: defines_var(q);
constraint bool_clause_reif([p, q], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_clause([p, q], [b]);
constraint int_eq(x, 2);
constraint int_eq(y, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let cVal = tr.sys.assignment[tr.varPositions["c"]]

    # p=0 (x!=1), q=0 (y!=1), so c = 0, b = 0
    check cVal == 0
    check bVal == 0

  test "no iff detection when clause literals do not match":
    ## bool_clause_reif([p, q], [], c) defines c ↔ (p ∨ q).
    ## bool_clause([b], [c]) gives c → b.
    ## bool_clause([p, r], [b]) gives b → (p ∨ r) — different from c's definition.
    ## So b ↔ c cannot be established.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var 1..3: z :: output_var;
var bool: p :: var_is_introduced :: is_defined_var;
var bool: q :: var_is_introduced :: is_defined_var;
var bool: r :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, p) :: defines_var(p);
constraint int_eq_reif(y, 1, q) :: defines_var(q);
constraint int_eq_reif(z, 1, r) :: defines_var(r);
constraint bool_clause_reif([p, q], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_clause([p, r], [b]);
constraint int_eq(x, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # b should NOT be detected as iff alias (literals don't match)
    check not tr.boolEquivAliasDefs.anyIt(it.aliasVar == "b")

  test "iff consumed constraints are in definingConstraints":
    ## Verify that the two bool_clause constraints used for iff detection
    ## are added to definingConstraints.
    ## Uses two positive literals to avoid AND detection consuming the reverse clause.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: p :: var_is_introduced :: is_defined_var;
var bool: q :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, p) :: defines_var(p);
constraint int_eq_reif(y, 1, q) :: defines_var(q);
constraint bool_clause_reif([p, q], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_clause([p, q], [b]);
constraint int_eq(x, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b" in tr.channelVarNames
    # The consumed constraint indices should be in definingConstraints
    for def in tr.boolEquivAliasDefs:
      if def.aliasVar == "b":
        for ci in def.consumedCIs:
          check ci in tr.definingConstraints

suite "Bool OR Channel Detection":

  test "basic bool OR channel: b = c ∨ prev":
    ## Pattern:
    ##   bool_clause_reif([cond], [], c) :: defines_var(c)   -- c ↔ cond
    ##   bool_clause([b], [c])                                -- c → b
    ##   bool_eq_reif(b, prev, eq) :: defines_var(eq)         -- eq ↔ (b = prev)
    ##   bool_clause([eq, cond], [])                           -- eq ∨ cond
    ##
    ## prev is a channel. Result: b = c ∨ prev.
    ## When cond=1: c=1, b=1.
    ## When cond=0: c=0, eq must be 1, so b=prev.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: cond :: var_is_introduced :: is_defined_var;
var bool: prev :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: eq :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, cond) :: defines_var(cond);
constraint int_eq_reif(y, 1, prev) :: defines_var(prev);
constraint bool_clause_reif([cond], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_eq_reif(b, prev, eq) :: defines_var(eq);
constraint bool_clause([eq, cond], []);
constraint int_eq(x, 2);
constraint int_eq(y, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "c" in tr.channelVarNames
    check "prev" in tr.channelVarNames
    check "b" in tr.channelVarNames
    check tr.boolOrChannelDefs.len >= 1
    check tr.boolOrChannelDefs.anyIt(it.targetVar == "b")

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let prevVal = tr.sys.assignment[tr.varPositions["prev"]]
    let cVal = tr.sys.assignment[tr.varPositions["c"]]

    # cond=0 (x!=1), c=0, prev=1 (y==1), so b = 0 ∨ 1 = 1
    check cVal == 0
    check prevVal == 1
    check bVal == 1  # b = c ∨ prev = 0 ∨ 1 = 1

  test "bool OR channel with c=1 forces b=1":
    ## When the condition is true, b is forced to 1 regardless of prev.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: cond :: var_is_introduced :: is_defined_var;
var bool: prev :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: eq :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, cond) :: defines_var(cond);
constraint int_eq_reif(y, 1, prev) :: defines_var(prev);
constraint bool_clause_reif([cond], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_eq_reif(b, prev, eq) :: defines_var(eq);
constraint bool_clause([eq, cond], []);
constraint int_eq(x, 1);
constraint int_eq(y, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let prevVal = tr.sys.assignment[tr.varPositions["prev"]]

    # cond=1 (x==1), c=1, prev=0 (y!=1), so b = 1 ∨ 0 = 1
    check prevVal == 0
    check bVal == 1

  test "bool OR channel with both false":
    ## When both c=0 and prev=0, b should be 0.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: cond :: var_is_introduced :: is_defined_var;
var bool: prev :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: eq :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, cond) :: defines_var(cond);
constraint int_eq_reif(y, 1, prev) :: defines_var(prev);
constraint bool_clause_reif([cond], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_eq_reif(b, prev, eq) :: defines_var(eq);
constraint bool_clause([eq, cond], []);
constraint int_eq(x, 2);
constraint int_eq(y, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]

    # cond=0, c=0, prev=0 (y!=1), so b = 0 ∨ 0 = 0
    check bVal == 0

  test "bool OR consumed constraints are in definingConstraints":
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: cond :: var_is_introduced :: is_defined_var;
var bool: prev :: var_is_introduced :: is_defined_var;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: eq :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, cond) :: defines_var(cond);
constraint int_eq_reif(y, 1, prev) :: defines_var(prev);
constraint bool_clause_reif([cond], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_eq_reif(b, prev, eq) :: defines_var(eq);
constraint bool_clause([eq, cond], []);
constraint int_eq(x, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b" in tr.channelVarNames
    for def in tr.boolOrChannelDefs:
      if def.targetVar == "b":
        for ci in def.consumedCIs:
          check ci in tr.definingConstraints

  test "bool OR temporal chain via fixpoint: b2 = c2 ∨ b1, b1 = c1 ∨ prev":
    ## Two-step temporal chain. b1 = c1 ∨ prev, then b2 = c2 ∨ b1.
    ## b1 must be detected first (as a channel), then b2 uses b1 as its prev.
    ## This requires the fixpoint loop to iterate.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var 1..3: z :: output_var;
var bool: cond1 :: var_is_introduced :: is_defined_var;
var bool: cond2 :: var_is_introduced :: is_defined_var;
var bool: prev :: var_is_introduced :: is_defined_var;
var bool: c1 :: var_is_introduced :: is_defined_var;
var bool: c2 :: var_is_introduced :: is_defined_var;
var bool: eq1 :: var_is_introduced :: is_defined_var;
var bool: eq2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced;
var bool: b2 :: var_is_introduced;
constraint int_eq_reif(x, 1, cond1) :: defines_var(cond1);
constraint int_eq_reif(y, 1, cond2) :: defines_var(cond2);
constraint int_eq_reif(z, 1, prev) :: defines_var(prev);
constraint bool_clause_reif([cond1], [], c1) :: defines_var(c1);
constraint bool_clause_reif([cond2], [], c2) :: defines_var(c2);
constraint bool_clause([b1], [c1]);
constraint bool_eq_reif(b1, prev, eq1) :: defines_var(eq1);
constraint bool_clause([eq1, cond1], []);
constraint bool_clause([b2], [c2]);
constraint bool_eq_reif(b2, b1, eq2) :: defines_var(eq2);
constraint bool_clause([eq2, cond2], []);
constraint int_eq(x, 2);
constraint int_eq(y, 1);
constraint int_eq(z, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Both b1 and b2 should be detected as channels
    check "b1" in tr.channelVarNames
    check "b2" in tr.channelVarNames
    check tr.boolOrChannelDefs.len >= 2

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let prevVal = tr.sys.assignment[tr.varPositions["prev"]]
    let b1Val = tr.sys.assignment[tr.varPositions["b1"]]
    let b2Val = tr.sys.assignment[tr.varPositions["b2"]]

    # cond1=0 (x!=1), c1=0, prev=1 (z==1), b1 = 0 ∨ 1 = 1
    # cond2=1 (y==1), c2=1, b2 = 1 ∨ b1 = 1
    check prevVal == 1
    check b1Val == 1
    check b2Val == 1

  test "no OR detection when prev is not a channel":
    ## prev must be a channel variable for the OR pattern to be detected.
    let src = """
var 1..3: x :: output_var;
var bool: cond :: var_is_introduced :: is_defined_var;
var bool: prev :: var_is_introduced;
var bool: c :: var_is_introduced :: is_defined_var;
var bool: eq :: var_is_introduced :: is_defined_var;
var bool: b :: var_is_introduced;
constraint int_eq_reif(x, 1, cond) :: defines_var(cond);
constraint bool_clause_reif([cond], [], c) :: defines_var(c);
constraint bool_clause([b], [c]);
constraint bool_eq_reif(b, prev, eq) :: defines_var(eq);
constraint bool_clause([eq, cond], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # prev is not a channel, so b should NOT be detected as an OR channel
    check "prev" notin tr.channelVarNames
    check not tr.boolOrChannelDefs.anyIt(it.targetVar == "b")
