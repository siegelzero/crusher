import unittest
import std/[sequtils, algorithm, sets, tables, strutils]

import crusher
import flatzinc/[parser, translator, output]

suite "FlatZinc Solver - End to End":

  test "solve test_negative_gecode.fzn (all_different + linear)":
    let model = parseFznFile("models/minizinc/test_negative_gecode.fzn")
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    # Get the output array positions
    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    # Verify all_different
    check values.toHashSet.len == values.len

    # Verify sum == -5
    check values.foldl(a + b) == -5

    # Verify strictly increasing for first 3 elements (from int_lin_le constraints on pairs 0-1 and 1-2)
    check values[0] < values[1]
    check values[1] < values[2]

  test "solve cumulative_test_gecode.fzn (cumulative + minimize)":
    let model = parseFznFile("models/minizinc/cumulative_test_gecode.fzn")
    var tr = translate(model)

    let objExpr = tr.getExpr(tr.objectivePos)
    minimize(tr.sys, objExpr,
      parallel = true,
      tabuThreshold = 5000,
      verbose = false
    )

    # Get origin assignments
    let originPositions = tr.arrayPositions["origin"]
    var origins = newSeq[int](originPositions.len)
    for i, pos in originPositions:
      origins[i] = tr.sys.assignment[pos]

    # Durations and heights from the problem
    let durations = @[3, 9, 10, 6, 2]
    let heights = @[1, 2, 1, 1, 3]

    # Get the limit value
    let limitPos = tr.varPositions["limitx"]
    let limit = tr.sys.assignment[limitPos]

    # Verify cumulative constraint: at no time point should total height exceed limit
    var maxEndTime = 0
    for i in 0..<5:
      let endTime = origins[i] + durations[i]
      if endTime > maxEndTime: maxEndTime = endTime

    for t in 1..maxEndTime:
      var totalHeight = 0
      for i in 0..<5:
        if origins[i] <= t and t < origins[i] + durations[i]:
          totalHeight += heights[i]
      check totalHeight <= limit

  test "solve simple satisfaction problem from FZN string":
    # A simple all-different + sum problem
    let src = """
var 1..5: x1;
var 1..5: x2;
var 1..5: x3;
array [1..3] of var int: x:: output_array([1..3]) = [x1,x2,x3];
constraint fzn_all_different_int(x);
constraint int_lin_eq([1,1,1],[x1,x2,x3],6);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["x"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    check values.toHashSet.len == 3  # all different
    check values.foldl(a + b) == 6   # sum = 6
    # Only solution: {1,2,3} in some order
    check values.sorted == @[1, 2, 3]

  test "solve with int_eq and int_ne constraints":
    let src = """
var 1..5: x;
var 1..5: y;
var 1..5: z;
constraint int_eq(x, y);
constraint int_ne(y, z);
constraint int_lin_eq([1,1,1],[x,y,z],7);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]

    check xVal == yVal        # int_eq
    check yVal != zVal        # int_ne
    check xVal + yVal + zVal == 7  # sum = 7

  test "solve with int_plus constraint":
    let src = """
var 1..10: x;
var 1..10: y;
var 1..20: z;
constraint int_plus(x, y, z);
constraint int_eq(z, 15);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let xVal = tr.sys.assignment[tr.varPositions["x"]]
    let yVal = tr.sys.assignment[tr.varPositions["y"]]
    let zVal = tr.sys.assignment[tr.varPositions["z"]]

    check xVal + yVal == zVal
    check zVal == 15

  test "solve with bool2int constraint":
    let src = """
var bool: b;
var 0..1: i;
constraint bool2int(b, i);
constraint int_eq(i, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let bVal = tr.sys.assignment[tr.varPositions["b"]]
    let iVal = tr.sys.assignment[tr.varPositions["i"]]

    check bVal == iVal
    check iVal == 1

  test "solve quasigroup7_gecode_05.fzn (all_different + element)":
    let model = parseFznFile("models/minizinc/2008/quasigroup7/quasigroup7_gecode_05.fzn")
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 20000, verbose = false)

    # Verify the output array forms a valid quasigroup
    let positions = tr.arrayPositions["X_INTRODUCED_16_"]
    var values = newSeq[int](positions.len)
    for i, pos in positions:
      values[i] = tr.sys.assignment[pos]

    # 5x5 Latin square: each row and column should have all different values
    let n = 5
    for row in 0..<n:
      let rowVals = values[row * n ..< (row + 1) * n]
      check rowVals.toHashSet.len == n

    for col in 0..<n:
      var colVals: seq[int]
      for row in 0..<n:
        colVals.add(values[row * n + col])
      check colVals.toHashSet.len == n

  test "output format":
    let src = """
var 1..3: x:: output_var;
var 1..3: y:: output_var;
array [1..2] of var int: arr:: output_array([1..2]) = [x,y];
constraint int_ne(x, y);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let output = tr.formatSolution()
    check "x = " in output
    check "y = " in output
    check "arr = array1d(1..2," in output
