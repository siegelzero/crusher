## Tests for forward-backward boolean equivalence channel detection:
## detectForwardBackwardEquivChannels detects B <-> OR(equality conditions)
## from bool_clause(arms, [B]) + bool_clause([ne_reif, B], []) patterns.
## B becomes a channel with a constant {0,1} lookup table.

import unittest
import std/[sequtils, sets, tables, packedsets]
import crusher
import flatzinc/[parser, translator]

proc getObjectiveExpr(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
  elif tr.objectivePos == ObjPosDefinedExpr: tr.objectiveDefExpr
  else: raise newException(ValueError, "No objective")

suite "Forward-Backward Boolean Equivalence Channels":

  test "basic: B <-> (x==2 OR y==1) via AND-wrapped arms":
    ## Forward: bool_clause([and_ab, and_ba], [b])
    ##   and_ab = array_bool_and([h_eq, p_eq_x2])  (p_eq_x2 = x==2)
    ##   and_ba = array_bool_and([h_eq2, p_eq_y1])  (p_eq_y1 = y==1)
    ## Backward: bool_clause([ne_x2, b], [])  (x==2 -> b)
    ##           bool_clause([ne_y1, b], [])  (y==1 -> b)
    ## Result: b = (x==2 OR y==1) as channel
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: output_var;
var bool: h_eq :: var_is_introduced :: is_defined_var;
var bool: h_eq2 :: var_is_introduced :: is_defined_var;
var bool: p_eq_x2 :: var_is_introduced :: is_defined_var;
var bool: p_eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_y1 :: var_is_introduced :: is_defined_var;
var bool: and_ab :: var_is_introduced :: is_defined_var;
var bool: and_ba :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, h_eq) :: defines_var(h_eq);
constraint int_eq_reif(x, 2, p_eq_x2) :: defines_var(p_eq_x2);
constraint int_eq_reif(y, 2, h_eq2) :: defines_var(h_eq2);
constraint int_eq_reif(y, 1, p_eq_y1) :: defines_var(p_eq_y1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint int_ne_reif(y, 1, ne_y1) :: defines_var(ne_y1);
constraint array_bool_and([h_eq, p_eq_x2], and_ab) :: defines_var(and_ab);
constraint array_bool_and([h_eq2, p_eq_y1], and_ba) :: defines_var(and_ba);
constraint bool_clause([and_ab, and_ba], [b]);
constraint bool_clause([ne_x2, b], []);
constraint bool_clause([ne_y1, b], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # b should be detected as a forward-backward equiv channel
    check "b" in tr.channelVarNames
    # Should have generated a case analysis def for b
    check tr.caseAnalysisDefs.anyIt(it.targetVarName == "b")

    # Test with x=2 -> b should be true
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == (if xVal == 2 or yVal == 1: 1 else: 0)

  test "B true when first condition holds":
    ## Fix x=2 -> b must be 1 regardless of y
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: output_var;
var bool: h_eq :: var_is_introduced :: is_defined_var;
var bool: p_eq_x2 :: var_is_introduced :: is_defined_var;
var bool: h_eq2 :: var_is_introduced :: is_defined_var;
var bool: p_eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_y1 :: var_is_introduced :: is_defined_var;
var bool: and_ab :: var_is_introduced :: is_defined_var;
var bool: and_ba :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, h_eq) :: defines_var(h_eq);
constraint int_eq_reif(x, 2, p_eq_x2) :: defines_var(p_eq_x2);
constraint int_eq_reif(y, 2, h_eq2) :: defines_var(h_eq2);
constraint int_eq_reif(y, 1, p_eq_y1) :: defines_var(p_eq_y1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint int_ne_reif(y, 1, ne_y1) :: defines_var(ne_y1);
constraint array_bool_and([h_eq, p_eq_x2], and_ab) :: defines_var(and_ab);
constraint array_bool_and([h_eq2, p_eq_y1], and_ba) :: defines_var(and_ba);
constraint bool_clause([and_ab, and_ba], [b]);
constraint bool_clause([ne_x2, b], []);
constraint bool_clause([ne_y1, b], []);
constraint int_eq(x, 2);
constraint int_eq(y, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 1  # x==2 -> b=1

  test "B false when neither condition holds":
    ## Fix x=3, y=3 -> b must be 0
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: output_var;
var bool: h_eq :: var_is_introduced :: is_defined_var;
var bool: p_eq_x2 :: var_is_introduced :: is_defined_var;
var bool: h_eq2 :: var_is_introduced :: is_defined_var;
var bool: p_eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_y1 :: var_is_introduced :: is_defined_var;
var bool: and_ab :: var_is_introduced :: is_defined_var;
var bool: and_ba :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, h_eq) :: defines_var(h_eq);
constraint int_eq_reif(x, 2, p_eq_x2) :: defines_var(p_eq_x2);
constraint int_eq_reif(y, 2, h_eq2) :: defines_var(h_eq2);
constraint int_eq_reif(y, 1, p_eq_y1) :: defines_var(p_eq_y1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint int_ne_reif(y, 1, ne_y1) :: defines_var(ne_y1);
constraint array_bool_and([h_eq, p_eq_x2], and_ab) :: defines_var(and_ab);
constraint array_bool_and([h_eq2, p_eq_y1], and_ba) :: defines_var(and_ba);
constraint bool_clause([and_ab, and_ba], [b]);
constraint bool_clause([ne_x2, b], []);
constraint bool_clause([ne_y1, b], []);
constraint int_eq(x, 3);
constraint int_eq(y, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 0  # x!=2 and y!=1 -> b=0

  test "direct eq_reif arms (no AND wrapping)":
    ## Forward arms are direct int_eq_reif outputs (not array_bool_and wrapped).
    ## b -> (eq_x2 OR eq_y1), backward: (x==2)->b, (y==1)->b
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: output_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_y1 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_eq_reif(y, 1, eq_y1) :: defines_var(eq_y1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint int_ne_reif(y, 1, ne_y1) :: defines_var(ne_y1);
constraint bool_clause([eq_x2, eq_y1], [b]);
constraint bool_clause([ne_x2, b], []);
constraint bool_clause([ne_y1, b], []);
constraint int_eq(x, 1);
constraint int_eq(y, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 1  # y==1 -> b=1

  test "single-arm forward (B <-> single condition)":
    ## Just one forward arm and one backward condition: B <-> (x==2)
    let src = """
var 1..3: x :: output_var;
var bool: b :: output_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint bool_clause([eq_x2], [b]);
constraint bool_clause([ne_x2, b], []);
constraint int_eq(x, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 1

  test "three-arm forward with three backward conditions":
    ## B <-> (x==1 OR y==2 OR z==3)
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var 1..3: z :: output_var;
var bool: b :: output_var;
var bool: eq_x1 :: var_is_introduced :: is_defined_var;
var bool: eq_y2 :: var_is_introduced :: is_defined_var;
var bool: eq_z3 :: var_is_introduced :: is_defined_var;
var bool: ne_x1 :: var_is_introduced :: is_defined_var;
var bool: ne_y2 :: var_is_introduced :: is_defined_var;
var bool: ne_z3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, eq_x1) :: defines_var(eq_x1);
constraint int_eq_reif(y, 2, eq_y2) :: defines_var(eq_y2);
constraint int_eq_reif(z, 3, eq_z3) :: defines_var(eq_z3);
constraint int_ne_reif(x, 1, ne_x1) :: defines_var(ne_x1);
constraint int_ne_reif(y, 2, ne_y2) :: defines_var(ne_y2);
constraint int_ne_reif(z, 3, ne_z3) :: defines_var(ne_z3);
constraint bool_clause([eq_x1, eq_y2, eq_z3], [b]);
constraint bool_clause([ne_x1, b], []);
constraint bool_clause([ne_y2, b], []);
constraint bool_clause([ne_z3, b], []);
constraint int_eq(x, 2);
constraint int_eq(y, 2);
constraint int_eq(z, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 1  # y==2 -> b=1

  test "three-arm forward all false":
    ## Same three conditions but none met
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var 1..3: z :: output_var;
var bool: b :: output_var;
var bool: eq_x1 :: var_is_introduced :: is_defined_var;
var bool: eq_y2 :: var_is_introduced :: is_defined_var;
var bool: eq_z3 :: var_is_introduced :: is_defined_var;
var bool: ne_x1 :: var_is_introduced :: is_defined_var;
var bool: ne_y2 :: var_is_introduced :: is_defined_var;
var bool: ne_z3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, eq_x1) :: defines_var(eq_x1);
constraint int_eq_reif(y, 2, eq_y2) :: defines_var(eq_y2);
constraint int_eq_reif(z, 3, eq_z3) :: defines_var(eq_z3);
constraint int_ne_reif(x, 1, ne_x1) :: defines_var(ne_x1);
constraint int_ne_reif(y, 2, ne_y2) :: defines_var(ne_y2);
constraint int_ne_reif(z, 3, ne_z3) :: defines_var(ne_z3);
constraint bool_clause([eq_x1, eq_y2, eq_z3], [b]);
constraint bool_clause([ne_x1, b], []);
constraint bool_clause([ne_y2, b], []);
constraint bool_clause([ne_z3, b], []);
constraint int_eq(x, 3);
constraint int_eq(y, 1);
constraint int_eq(z, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 0  # x!=1, y!=2, z!=3 -> b=0

  test "not detected when backward is incomplete":
    ## Forward has 2 arms but only 1 backward condition — should NOT be detected
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: output_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_eq_reif(y, 1, eq_y1) :: defines_var(eq_y1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint bool_clause([eq_x2, eq_y1], [b]);
constraint bool_clause([ne_x2, b], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # b should NOT be a channel (missing backward for y==1)
    check "b" notin tr.channelVarNames

  test "multiple booleans channeled simultaneously":
    ## Two boolean variables b1, b2 each with their own forward/backward pattern
    ## b1 <-> (x==1 OR y==2), b2 <-> (x==2 OR y==1)
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b1 :: output_var;
var bool: b2 :: output_var;
var bool: eq_x1 :: var_is_introduced :: is_defined_var;
var bool: eq_y2 :: var_is_introduced :: is_defined_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x1 :: var_is_introduced :: is_defined_var;
var bool: ne_y2 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_y1 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, eq_x1) :: defines_var(eq_x1);
constraint int_eq_reif(y, 2, eq_y2) :: defines_var(eq_y2);
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_eq_reif(y, 1, eq_y1) :: defines_var(eq_y1);
constraint int_ne_reif(x, 1, ne_x1) :: defines_var(ne_x1);
constraint int_ne_reif(y, 2, ne_y2) :: defines_var(ne_y2);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint int_ne_reif(y, 1, ne_y1) :: defines_var(ne_y1);
constraint bool_clause([eq_x1, eq_y2], [b1]);
constraint bool_clause([ne_x1, b1], []);
constraint bool_clause([ne_y2, b1], []);
constraint bool_clause([eq_x2, eq_y1], [b2]);
constraint bool_clause([ne_x2, b2], []);
constraint bool_clause([ne_y1, b2], []);
constraint int_eq(x, 1);
constraint int_eq(y, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b1" in tr.channelVarNames
    check "b2" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let b1Val = tr.sys.assignment[tr.varPositions["b1"]]
    let b2Val = tr.sys.assignment[tr.varPositions["b2"]]
    check b1Val == 1  # x==1 -> b1=1
    check b2Val == 1  # y==1 -> b2=1

  test "bool2int of channeled bool feeds objective":
    ## b = (x==2 OR y==1) channeled, then bool2int(b, bi), then minimize bi
    ## With x=2 forced, b=1 and bi=1 is forced — objective must be 1.
    let src = """
var 1..3: x :: output_var;
var 1..3: y :: output_var;
var bool: b :: var_is_introduced;
var 0..1: bi :: output_var :: is_defined_var;
var 0..1: obj :: output_var :: is_defined_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: eq_y1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_y1 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_eq_reif(y, 1, eq_y1) :: defines_var(eq_y1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint int_ne_reif(y, 1, ne_y1) :: defines_var(ne_y1);
constraint bool_clause([eq_x2, eq_y1], [b]);
constraint bool_clause([ne_x2, b], []);
constraint bool_clause([ne_y1, b], []);
constraint bool2int(b, bi) :: defines_var(bi);
constraint int_eq(obj, bi) :: defines_var(obj);
constraint int_eq(x, 2);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames

    let objExpr = tr.getObjectiveExpr()
    minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

    let objVal = objExpr.evaluate(tr.sys.assignment)
    check objVal == 1  # x==2 forces b=1, bi=1, obj=1

  test "overlapping conditions on same source variable":
    ## b <-> (x==1 OR x==2) — two backward conditions on the same source variable x
    let src = """
var 1..4: x :: output_var;
var bool: b :: output_var;
var bool: eq_x1 :: var_is_introduced :: is_defined_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_x1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, eq_x1) :: defines_var(eq_x1);
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_ne_reif(x, 1, ne_x1) :: defines_var(ne_x1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint bool_clause([eq_x1, eq_x2], [b]);
constraint bool_clause([ne_x1, b], []);
constraint bool_clause([ne_x2, b], []);
constraint int_eq(x, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 1  # x==2 -> b=1

  test "overlapping conditions same source — false case":
    ## b <-> (x==1 OR x==2), x=3 -> b=0
    let src = """
var 1..4: x :: output_var;
var bool: b :: output_var;
var bool: eq_x1 :: var_is_introduced :: is_defined_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_x1 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 1, eq_x1) :: defines_var(eq_x1);
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_ne_reif(x, 1, ne_x1) :: defines_var(ne_x1);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint bool_clause([eq_x1, eq_x2], [b]);
constraint bool_clause([ne_x1, b], []);
constraint bool_clause([ne_x2, b], []);
constraint int_eq(x, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 0  # x==3 -> b=0

  test "reversed ne_reif order in backward clause":
    ## Backward clause has b first, ne_reif second: bool_clause([b, ne_x2], [])
    let src = """
var 1..3: x :: output_var;
var bool: b :: output_var;
var bool: eq_x2 :: var_is_introduced :: is_defined_var;
var bool: ne_x2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 2, eq_x2) :: defines_var(eq_x2);
constraint int_ne_reif(x, 2, ne_x2) :: defines_var(ne_x2);
constraint bool_clause([eq_x2], [b]);
constraint bool_clause([b, ne_x2], []);
constraint int_eq(x, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "b" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    check bVal == 1

  test "DCMST-like mini tree: edge selection channeled from parent":
    ## 4-node complete graph, even diameter, edge selection b_ij <-> (p[i]==j OR p[j]==i)
    ## Models a miniature DCMST: root=1, p[1]=1, h[1]=0; p[2]=1, h[2]=1; etc.
    ## Edge (1,2): b12 <-> (p1==2 OR p2==1)
    ## With p1=1 (root), p2=1 (parent of 2 is 1): b12 = 1 (edge selected)
    let src = """
var 1..4: p1 :: output_var;
var 1..4: p2 :: output_var;
var 1..4: p3 :: output_var;
var 1..4: p4 :: output_var;
var bool: b12 :: output_var;
var bool: b13 :: output_var;
var bool: b23 :: output_var;
var bool: eq_p1_2 :: var_is_introduced :: is_defined_var;
var bool: eq_p2_1 :: var_is_introduced :: is_defined_var;
var bool: ne_p1_2 :: var_is_introduced :: is_defined_var;
var bool: ne_p2_1 :: var_is_introduced :: is_defined_var;
var bool: eq_p1_3 :: var_is_introduced :: is_defined_var;
var bool: eq_p3_1 :: var_is_introduced :: is_defined_var;
var bool: ne_p1_3 :: var_is_introduced :: is_defined_var;
var bool: ne_p3_1 :: var_is_introduced :: is_defined_var;
var bool: eq_p2_3 :: var_is_introduced :: is_defined_var;
var bool: eq_p3_2 :: var_is_introduced :: is_defined_var;
var bool: ne_p2_3 :: var_is_introduced :: is_defined_var;
var bool: ne_p3_2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(p1, 2, eq_p1_2) :: defines_var(eq_p1_2);
constraint int_eq_reif(p2, 1, eq_p2_1) :: defines_var(eq_p2_1);
constraint int_ne_reif(p1, 2, ne_p1_2) :: defines_var(ne_p1_2);
constraint int_ne_reif(p2, 1, ne_p2_1) :: defines_var(ne_p2_1);
constraint int_eq_reif(p1, 3, eq_p1_3) :: defines_var(eq_p1_3);
constraint int_eq_reif(p3, 1, eq_p3_1) :: defines_var(eq_p3_1);
constraint int_ne_reif(p1, 3, ne_p1_3) :: defines_var(ne_p1_3);
constraint int_ne_reif(p3, 1, ne_p3_1) :: defines_var(ne_p3_1);
constraint int_eq_reif(p2, 3, eq_p2_3) :: defines_var(eq_p2_3);
constraint int_eq_reif(p3, 2, eq_p3_2) :: defines_var(eq_p3_2);
constraint int_ne_reif(p2, 3, ne_p2_3) :: defines_var(ne_p2_3);
constraint int_ne_reif(p3, 2, ne_p3_2) :: defines_var(ne_p3_2);
constraint bool_clause([eq_p1_2, eq_p2_1], [b12]);
constraint bool_clause([ne_p1_2, b12], []);
constraint bool_clause([ne_p2_1, b12], []);
constraint bool_clause([eq_p1_3, eq_p3_1], [b13]);
constraint bool_clause([ne_p1_3, b13], []);
constraint bool_clause([ne_p3_1, b13], []);
constraint bool_clause([eq_p2_3, eq_p3_2], [b23]);
constraint bool_clause([ne_p2_3, b23], []);
constraint bool_clause([ne_p3_2, b23], []);
constraint int_eq(p1, 1);
constraint int_eq(p2, 1);
constraint int_eq(p3, 1);
constraint int_eq(p4, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "b12" in tr.channelVarNames
    check "b13" in tr.channelVarNames
    check "b23" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let b12 = tr.sys.assignment[tr.varPositions["b12"]]
    let b13 = tr.sys.assignment[tr.varPositions["b13"]]
    let b23 = tr.sys.assignment[tr.varPositions["b23"]]

    # p1=1, p2=1, p3=1: edges (1,2)=p2==1->yes, (1,3)=p3==1->yes, (2,3)=neither
    check b12 == 1  # p2==1
    check b13 == 1  # p3==1
    check b23 == 0  # p2!=3 and p3!=2
