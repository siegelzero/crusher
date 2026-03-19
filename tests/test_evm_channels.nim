## Tests for EVM super-compilation improvements:
## - detectConditionalSourceChannels: opcode-conditioned variable-source channels
## - buildValueMapping fix for array_var_int_element
## - Cascade depth limit with lazy fallback
## - Channel binding domain propagation

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, strformat, packedsets]
import crusher
import flatzinc/[parser, translator, output]

suite "Conditional Source Channel Detection":

  test "basic conditional-source detection: 2 opcodes, 2 positions":
    ## Encodes a 1-step stack machine with 2 opcodes and 2 positions.
    ## The source variables must be in a declared array for detection to find them.
    ## Pre values are not fixed — this tests detection, not solving.
    let src = """
var 1..2: op :: output_var;
var 1..5: pre1 :: output_var;
var 1..5: pre2 :: output_var;
var 1..5: post1 :: output_var;
var 1..5: post2 :: output_var;
array [1..2] of var int: pre_arr ::var_is_introduced = [pre1, pre2];
var bool: b_nop1 ::var_is_introduced ::is_defined_var;
var bool: b_nop2 ::var_is_introduced ::is_defined_var;
var bool: b_swap1 ::var_is_introduced ::is_defined_var;
var bool: b_swap2 ::var_is_introduced ::is_defined_var;
var bool: d_nop ::var_is_introduced ::is_defined_var;
var bool: d_swap ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(op, 1, d_nop) :: defines_var(d_nop);
constraint int_eq_reif(op, 2, d_swap) :: defines_var(d_swap);
constraint int_eq_reif(post1, pre1, b_nop1) :: defines_var(b_nop1);
constraint int_eq_reif(post1, pre2, b_swap1) :: defines_var(b_swap1);
constraint int_eq_reif(post2, pre2, b_nop2) :: defines_var(b_nop2);
constraint int_eq_reif(post2, pre1, b_swap2) :: defines_var(b_swap2);
constraint bool_clause([b_nop1], [d_nop]);
constraint bool_clause([b_swap1], [d_swap]);
constraint bool_clause([b_nop2], [d_nop]);
constraint bool_clause([b_swap2], [d_swap]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # post1 and post2 should be detected as conditional-source channels
    check "post1" in tr.channelVarNames
    check "post2" in tr.channelVarNames

  test "conditional-source with array_bool_and grouping":
    ## Opcodes group position equalities via array_bool_and, matching the EVM pattern.
    ## NOP: array_bool_and([b_nop1, b_nop2], g_nop), bool_clause([g_nop], [d_nop])
    ## SWAP: array_bool_and([b_swap1, b_swap2], g_swap), bool_clause([d_nop, g_swap], [d_swap])
    ##
    ## The detector must trace through array_bool_and to discover that b_swap1/b_swap2
    ## are associated with opcode 2.
    let src = """
var 1..2: op :: output_var;
var 1..5: pre1 :: output_var;
var 1..5: pre2 :: output_var;
var 1..5: post1 :: output_var;
var 1..5: post2 :: output_var;
array [1..2] of var int: pre_arr ::var_is_introduced = [pre1, pre2];
var bool: b_nop1 ::var_is_introduced ::is_defined_var;
var bool: b_nop2 ::var_is_introduced ::is_defined_var;
var bool: b_swap1 ::var_is_introduced ::is_defined_var;
var bool: b_swap2 ::var_is_introduced ::is_defined_var;
var bool: d_nop ::var_is_introduced ::is_defined_var;
var bool: d_swap ::var_is_introduced ::is_defined_var;
var bool: g_nop ::var_is_introduced ::is_defined_var;
var bool: g_swap ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(op, 1, d_nop) :: defines_var(d_nop);
constraint int_eq_reif(op, 2, d_swap) :: defines_var(d_swap);
constraint int_eq_reif(post1, pre1, b_nop1) :: defines_var(b_nop1);
constraint int_eq_reif(post1, pre2, b_swap1) :: defines_var(b_swap1);
constraint int_eq_reif(post2, pre2, b_nop2) :: defines_var(b_nop2);
constraint int_eq_reif(post2, pre1, b_swap2) :: defines_var(b_swap2);
constraint array_bool_and([b_nop1, b_nop2], g_nop) :: defines_var(g_nop);
constraint array_bool_and([b_swap1, b_swap2], g_swap) :: defines_var(g_swap);
constraint bool_clause([g_nop], [d_nop]);
constraint bool_clause([d_nop, g_swap], [d_swap]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # post1 and post2 should be detected as conditional-source channels
    check "post1" in tr.channelVarNames
    check "post2" in tr.channelVarNames
    check tr.conditionalSourceDefs.len >= 2


suite "buildValueMapping for array_var_int_element":

  test "array_var_int_element channel resolves through variable array":
    ## array_var_int_element(idx, [a, b, c], result) :: defines_var(result)
    ## idx is a search variable, a/b/c are search variables.
    ## The channel binding should create result as a variable-element channel.
    ## Testing that the buildValueMapping fix allows case-analysis to
    ## resolve through array_var_int_element.
    let src = """
var 1..3: idx :: output_var;
var 1..10: a :: output_var;
var 1..10: b :: output_var;
var 1..10: c :: output_var;
var 1..10: result :: output_var;
array [1..3] of var int: arr ::var_is_introduced = [a, b, c];
constraint array_var_int_element(idx, arr, result) :: defines_var(result);
constraint int_le(result, 10);
constraint int_eq(a, 5);
constraint int_eq(b, 8);
constraint int_eq(c, 3);
constraint int_eq(idx, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # result should be a channel (defines_var on array_var_int_element)
    check "result" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    # idx=2 → result=arr[2]=b=8
    check tr.sys.assignment[tr.varPositions["result"]] == 8


suite "Channel Binding Domain Propagation":

  test "constant-array channel binding restricts domains":
    ## element(x, [10, 20, 30], y) :: defines_var(y)
    ## x in {1,2,3}, y in {1..100}
    ## After propagation: y should be restricted to {10, 20, 30}
    let src = """
var 1..3: x :: output_var;
var 1..100: y :: output_var;
constraint array_int_element(x, [10, 20, 30], y) :: defines_var(y);
constraint int_le(y, 100);
constraint int_eq(x, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Trigger domain reduction
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # After domain reduction, y's domain should be at most {10, 20, 30} (no values outside the array)
    # With x fixed to 2 by presolve, y's domain might be reduced to just {20}
    let yPos = tr.varPositions["y"]
    let yDomain = tr.sys.baseArray.reducedDomain[yPos]
    check yDomain.len <= 3
    check 20 in yDomain
    # No values outside the element array should remain
    for v in yDomain:
      check v in [10, 20, 30]
    check tr.sys.assignment[yPos] == 20

  test "variable-array channel binding restricts target domain":
    ## array_var_int_element(idx, [a, b], result) where a ∈ {1,2}, b ∈ {3,4}
    ## result should be restricted to {1,2,3,4}
    let src = """
var 1..2: idx :: output_var;
var 1..2: a :: output_var;
var 3..4: b :: output_var;
var 1..100: result :: output_var;
array [1..2] of var int: arr ::var_is_introduced = [a, b];
constraint array_var_int_element(idx, arr, result) :: defines_var(result);
constraint int_le(result, 100);
constraint int_eq(idx, 1);
constraint int_eq(a, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let rPos = tr.varPositions["result"]
    let rDomain = tr.sys.baseArray.reducedDomain[rPos]
    # result domain should be restricted to union of a's domain {1,2} and b's domain {3,4}
    check rDomain.len <= 4
    for v in rDomain:
      check v in [1, 2, 3, 4]
    check tr.sys.assignment[rPos] == 2  # idx=1, a=2


suite "Cascade Depth Limit":

  test "deep cascade chain doesn't timeout":
    ## Create a chain of 10 element channels with constraints on the last one.
    ## Validates the cascade infrastructure handles chains correctly.
    var lines: seq[string]
    lines.add("var 1..2: x :: output_var;")
    for i in 1..10:
      lines.add(&"var 1..100: c{i} ::var_is_introduced ::is_defined_var;")
      lines.add(&"constraint array_int_element(x, [{i}, {i+10}], c{i}) :: defines_var(c{i});")
      # Keep channel alive with a constraint
      lines.add(&"constraint int_le(c{i}, 100);")
    lines.add("constraint int_eq(x, 2);")
    lines.add("solve satisfy;")
    let src = lines.join("\n")

    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # x=2, so c[i] = element(2, [i, i+10]) = i+10
    for i in 1..10:
      let pos = tr.varPositions["c" & $i]
      check tr.sys.assignment[pos] == i + 10
