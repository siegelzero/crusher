## Tests for conditional counter and conditional element channel detection:
## 1. detectConditionalCounterChannels: run-length counter patterns
##    (if cond then Z=c else Z=prevZ+1) → 2D table channel
## 2. detectConditionalElementChannels: conditional element patterns
##    (if cond then X=table[idx] else X=const) → combined element channel
## 3. inferUnboundedDomains: domain inference for "var int" variables

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]
import crusher
import flatzinc/[parser, translator]

proc getObjectiveExpr(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
  elif tr.objectivePos == ObjPosDefinedExpr: tr.objectiveDefExpr
  else: raise newException(ValueError, "No objective")


suite "Conditional Counter Channel Detection":

  test "basic counter channel: if cond then Z=1 else Z=prevZ+1":
    ## A single conditional counter over 3 positions.
    ## cond[i] indicates a reset; otherwise Z increments from previous.
    ## prevZ domain 1..3, resetVal = 1.
    ## Expected table: cond=0 → Z=prevZ+1, cond=1 → Z=1.
    let src = """
var 1..3: prevZ :: output_var;
var 1..4: Z :: output_var;
var bool: cond :: output_var;
var bool: b_eq :: var_is_introduced :: is_defined_var;
var bool: b_incr :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(Z, 1, b_eq) :: defines_var(b_eq);
constraint int_lin_eq_reif([1,-1],[Z,prevZ],1,b_incr) :: defines_var(b_incr);
constraint bool_clause([b_eq],[cond]);
constraint bool_clause([cond,b_incr],[]);
constraint int_eq(prevZ, 2);
constraint bool_eq(cond, false);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Z should be detected as a conditional counter channel
    check "Z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let zVal = tr.sys.assignment[tr.varPositions["Z"]]
    # cond=false → Z = prevZ + 1 = 2 + 1 = 3
    check zVal == 3

  test "counter channel with cond=true resets to constant":
    ## Same pattern, but cond is true — should reset Z to the constant.
    let src = """
var 1..3: prevZ :: output_var;
var 1..4: Z :: output_var;
var bool: cond :: output_var;
var bool: b_eq :: var_is_introduced :: is_defined_var;
var bool: b_incr :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(Z, 1, b_eq) :: defines_var(b_eq);
constraint int_lin_eq_reif([1,-1],[Z,prevZ],1,b_incr) :: defines_var(b_incr);
constraint bool_clause([b_eq],[cond]);
constraint bool_clause([cond,b_incr],[]);
constraint int_eq(prevZ, 3);
constraint bool_eq(cond, true);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "Z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let zVal = tr.sys.assignment[tr.varPositions["Z"]]
    # cond=true → Z = 1 (reset value)
    check zVal == 1

  test "counter channel with non-unit reset value":
    ## Reset value is 5 instead of 1, prevZ domain 3..6.
    let src = """
var 3..6: prevZ :: output_var;
var 4..7: Z :: output_var;
var bool: cond :: output_var;
var bool: b_eq :: var_is_introduced :: is_defined_var;
var bool: b_incr :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(Z, 5, b_eq) :: defines_var(b_eq);
constraint int_lin_eq_reif([1,-1],[Z,prevZ],1,b_incr) :: defines_var(b_incr);
constraint bool_clause([b_eq],[cond]);
constraint bool_clause([cond,b_incr],[]);
constraint int_eq(prevZ, 6);
constraint bool_eq(cond, false);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "Z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let zVal = tr.sys.assignment[tr.varPositions["Z"]]
    # cond=false → Z = prevZ + 1 = 6 + 1 = 7
    check zVal == 7

  test "multiple counter channels sharing the same condition":
    ## Two counters Z1 and Z2, same cond, different reset values.
    let src = """
var 1..3: prevZ1 :: output_var;
var 1..3: prevZ2 :: output_var;
var 1..4: Z1 :: output_var;
var 1..4: Z2 :: output_var;
var bool: cond :: output_var;
var bool: b_eq1 :: var_is_introduced :: is_defined_var;
var bool: b_incr1 :: var_is_introduced :: is_defined_var;
var bool: b_eq2 :: var_is_introduced :: is_defined_var;
var bool: b_incr2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(Z1, 1, b_eq1) :: defines_var(b_eq1);
constraint int_lin_eq_reif([1,-1],[Z1,prevZ1],1,b_incr1) :: defines_var(b_incr1);
constraint bool_clause([b_eq1],[cond]);
constraint bool_clause([cond,b_incr1],[]);
constraint int_eq_reif(Z2, 2, b_eq2) :: defines_var(b_eq2);
constraint int_lin_eq_reif([1,-1],[Z2,prevZ2],1,b_incr2) :: defines_var(b_incr2);
constraint bool_clause([b_eq2],[cond]);
constraint bool_clause([cond,b_incr2],[]);
constraint int_eq(prevZ1, 2);
constraint int_eq(prevZ2, 1);
constraint bool_eq(cond, false);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "Z1" in tr.channelVarNames
    check "Z2" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let z1Val = tr.sys.assignment[tr.varPositions["Z1"]]
    let z2Val = tr.sys.assignment[tr.varPositions["Z2"]]
    # cond=false → Z1 = prevZ1+1 = 3, Z2 = prevZ2+1 = 2
    check z1Val == 3
    check z2Val == 2

  test "counter channel semantics with free variables":
    ## cond and prevZ are free — verify the if-then-else semantics hold.
    let src = """
var 1..2: prevZ :: output_var;
var 1..3: Z :: output_var;
var bool: cond :: output_var;
var bool: b_eq :: var_is_introduced :: is_defined_var;
var bool: b_incr :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(Z, 1, b_eq) :: defines_var(b_eq);
constraint int_lin_eq_reif([1,-1],[Z,prevZ],1,b_incr) :: defines_var(b_incr);
constraint bool_clause([b_eq],[cond]);
constraint bool_clause([cond,b_incr],[]);
constraint int_eq(Z, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "Z" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let condVal = tr.sys.assignment[tr.varPositions["cond"]]
    let prevZVal = tr.sys.assignment[tr.varPositions["prevZ"]]
    let zVal = tr.sys.assignment[tr.varPositions["Z"]]

    check zVal == 3
    # Z=3 != 1, so cond must be false (not reset), and prevZ+1=3 → prevZ=2
    check condVal == 0  # false
    check prevZVal == 2


suite "Conditional Element Channel Detection":

  test "conditional element semantics — cond=true branch":
    ## When cond is true, X = table[idx]; when false, X = elseConst.
    ## Uses free idx so X is not fully determined by presolve.
    ## Constrains X = elemResult to force cond=true.
    let src = """
var 1..3: idx :: output_var;
var bool: cond :: output_var;
var 0..30: X :: output_var;
var 0..30: elemResult :: var_is_introduced :: is_defined_var;
var bool: b_elem :: var_is_introduced :: is_defined_var;
var bool: b_const :: var_is_introduced :: is_defined_var;
array [1..3] of int: table = [10, 20, 30];
constraint array_int_element(idx, table, elemResult) :: defines_var(elemResult);
constraint int_eq_reif(X, elemResult, b_elem) :: defines_var(b_elem);
constraint int_eq_reif(X, 0, b_const) :: defines_var(b_const);
constraint bool_clause([b_elem],[cond]);
constraint bool_clause([cond, b_const],[]);
constraint int_eq(X, 20);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let condVal = tr.sys.assignment[tr.varPositions["cond"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]
    # X=20 only reachable via table[2]=20, so cond must be true
    check condVal == 1  # true
    check idxVal == 2

  test "conditional element semantics — cond=false branch":
    ## Constrain X = 0 (the else constant) which forces cond=false.
    let src = """
var 1..3: idx :: output_var;
var bool: cond :: output_var;
var 0..30: X :: output_var;
var 0..30: elemResult :: var_is_introduced :: is_defined_var;
var bool: b_elem :: var_is_introduced :: is_defined_var;
var bool: b_const :: var_is_introduced :: is_defined_var;
array [1..3] of int: table = [10, 20, 30];
constraint array_int_element(idx, table, elemResult) :: defines_var(elemResult);
constraint int_eq_reif(X, elemResult, b_elem) :: defines_var(b_elem);
constraint int_eq_reif(X, 0, b_const) :: defines_var(b_const);
constraint bool_clause([b_elem],[cond]);
constraint bool_clause([cond, b_const],[]);
constraint int_eq(X, 0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let condVal = tr.sys.assignment[tr.varPositions["cond"]]
    # X=0 is the else constant, so cond must be false
    check condVal == 0  # false

  test "conditional element with free variables — semantics verification":
    ## Both cond and idx are free. Constrain X to a value only reachable
    ## via the table branch to force cond=true.
    let src = """
var 1..3: idx :: output_var;
var bool: cond :: output_var;
var 0..30: X :: output_var;
var 0..30: elemResult :: var_is_introduced :: is_defined_var;
var bool: b_elem :: var_is_introduced :: is_defined_var;
var bool: b_const :: var_is_introduced :: is_defined_var;
array [1..3] of int: table = [10, 20, 30];
constraint array_int_element(idx, table, elemResult) :: defines_var(elemResult);
constraint int_eq_reif(X, elemResult, b_elem) :: defines_var(b_elem);
constraint int_eq_reif(X, 0, b_const) :: defines_var(b_const);
constraint bool_clause([b_elem],[cond]);
constraint bool_clause([cond, b_const],[]);
constraint int_eq(X, 30);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let condVal = tr.sys.assignment[tr.varPositions["cond"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]

    # X=30 is only reachable via table[3]=30, so cond must be true
    check condVal == 1  # true
    check idxVal == 3

  test "conditional element with optimization":
    ## Minimize X with conditional element. cond is free, idx is free.
    ## table = [5, 3, 7], elseConst = 10.
    ## Optimal: cond=true, idx=2, X=3.
    ## Add allDifferent on another array to keep search space nontrivial.
    let src = """
var 1..3: idx :: output_var;
var bool: cond :: output_var;
var 0..10: X :: output_var;
var 0..10: elemResult :: var_is_introduced :: is_defined_var;
var bool: b_elem :: var_is_introduced :: is_defined_var;
var bool: b_const :: var_is_introduced :: is_defined_var;
var 1..3: y1 :: output_var;
var 1..3: y2 :: output_var;
var 1..3: y3 :: output_var;
array [1..3] of int: table = [5, 3, 7];
constraint array_int_element(idx, table, elemResult) :: defines_var(elemResult);
constraint int_eq_reif(X, elemResult, b_elem) :: defines_var(b_elem);
constraint int_eq_reif(X, 10, b_const) :: defines_var(b_const);
constraint bool_clause([b_elem],[cond]);
constraint bool_clause([cond, b_const],[]);
constraint fzn_all_different_int([y1, y2, y3]);
solve minimize X;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let objExpr = tr.getObjectiveExpr()
    tr.sys.minimize(objExpr, parallel = true, tabuThreshold = 5000,
                    lowerBound = tr.objectiveLoBound,
                    upperBound = tr.objectiveHiBound)

    # min(table) = 3 < elseConst = 10, so optimal X = 3
    let xPos = tr.varPositions.getOrDefault("X", -1)
    if xPos >= 0:
      check tr.sys.assignment[xPos] == 3
    else:
      # X was eliminated as defined var — check objective
      check objExpr.evaluate(tr.sys.bestFeasibleAssignment) == 3

  test "elemResult var is also marked as channel":
    ## The intermediate elemResult variable should be removed from the search space.
    ## Both X and er should be channelized (by either the conditional element
    ## detector or the reification channel system).
    let src = """
var 1..2: idx :: output_var;
var bool: cond :: output_var;
var 0..20: X :: output_var;
var 0..20: er :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
array [1..2] of int: table = [15, 20];
constraint array_int_element(idx, table, er) :: defines_var(er);
constraint int_eq_reif(X, er, b1) :: defines_var(b1);
constraint int_eq_reif(X, 0, b2) :: defines_var(b2);
constraint bool_clause([b1],[cond]);
constraint bool_clause([cond, b2],[]);
constraint bool_eq(cond, true);
constraint int_eq(idx, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # er should be a channel (element defines_var or conditional element detector)
    check "er" in tr.channelVarNames

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # Verify semantics: cond=true, idx=1 → X = table[1] = 15
    let xPos = if "X" in tr.varPositions: tr.varPositions["X"] else: -1
    if xPos >= 0:
      let xVal = tr.sys.assignment[xPos]
      check xVal == 15


suite "Unbounded Domain Inference":

  test "element result domain inferred from constant table":
    ## A "var int" result of array_int_element gets domain from the table values.
    let src = """
var 1..3: idx :: output_var;
var int: result :: output_var;
array [1..3] of int: table = [10, 20, 30];
constraint array_int_element(idx, table, result);
constraint int_eq(idx, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let resultVal = tr.sys.assignment[tr.varPositions["result"]]
    check resultVal == 20

  test "element result domain restricts by index domain":
    ## Only index values 1 and 3 are reachable, so result ∈ {10, 30}.
    let src = """
var {1, 3}: idx :: output_var;
var int: result :: output_var;
array [1..3] of int: table = [10, 20, 30];
constraint array_int_element(idx, table, result);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let resultVal = tr.sys.assignment[tr.varPositions["result"]]
    # result must be one of the reachable values
    check resultVal in [10, 30]

  test "if-then-else reification inference for unbounded var":
    ## X is "var int", appears in exactly 2 complementary int_eq_reif patterns.
    ## Domain should be inferred from the two possible values.
    let src = """
var bool: cond :: output_var;
var int: X :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(X, 42, b1) :: defines_var(b1);
constraint int_eq_reif(X, 99, b2) :: defines_var(b2);
constraint bool_clause([b1],[cond]);
constraint bool_clause([cond, b2],[]);
constraint bool_eq(cond, true);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["X"]]
    # cond=true → X = 42
    check xVal == 42

  test "if-then-else unbounded var with cond=false":
    let src = """
var bool: cond :: output_var;
var int: X :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(X, 42, b1) :: defines_var(b1);
constraint int_eq_reif(X, 99, b2) :: defines_var(b2);
constraint bool_clause([b1],[cond]);
constraint bool_clause([cond, b2],[]);
constraint bool_eq(cond, false);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["X"]]
    # cond=false → X = 99
    check xVal == 99
