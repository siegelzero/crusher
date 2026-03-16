## Tests for FlatZinc pattern detection of new channel types:
## 1. detectIfThenElseChannels: int_lin_ne_reif + int_eq_reif + bool_clause → 2D table channel
## 2. detectGccCountChannels: variable-count GCC outputs → count-eq channel bindings
## 3. Objective bound tightening for max(max_count - min_count) patterns

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]
import crusher
import flatzinc/[parser, translator, output]

## Helper: get objective expression handling ObjPosDefinedExpr
proc getObjectiveExpr(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0:
    return tr.getExpr(tr.objectivePos)
  elif tr.objectivePos == ObjPosDefinedExpr:
    return tr.objectiveDefExpr
  else:
    raise newException(ValueError, "No objective expression")

suite "FlatZinc If-Then-Else Channel Detection":

  test "multiple if-then-else channels with shared variables":
    ## Two if-then-else patterns sharing the same curr variable.
    ## result1 = if prev1 != curr then curr else 0
    ## result2 = if prev2 != curr then curr else 0
    let src = """
var 1..3: prev1 :: output_var;
var 1..3: prev2 :: output_var;
var 1..3: curr :: output_var;
var 0..3: result1 :: output_var;
var 0..3: result2 :: output_var;
var bool: b_ne1 :: var_is_introduced :: is_defined_var;
var bool: b1_eq1 :: var_is_introduced :: is_defined_var;
var bool: b1_eq0_1 :: var_is_introduced :: is_defined_var;
var bool: b_ne2 :: var_is_introduced :: is_defined_var;
var bool: b2_eq1 :: var_is_introduced :: is_defined_var;
var bool: b2_eq0_2 :: var_is_introduced :: is_defined_var;
constraint int_lin_ne_reif([1,-1],[prev1,curr],0,b_ne1) :: defines_var(b_ne1);
constraint int_eq_reif(result1,curr,b1_eq1) :: defines_var(b1_eq1);
constraint int_eq_reif(result1,0,b1_eq0_1) :: defines_var(b1_eq0_1);
constraint bool_clause([b1_eq1],[b_ne1]);
constraint bool_clause([b_ne1,b1_eq0_1],[]);
constraint int_lin_ne_reif([1,-1],[prev2,curr],0,b_ne2) :: defines_var(b_ne2);
constraint int_eq_reif(result2,curr,b2_eq1) :: defines_var(b2_eq1);
constraint int_eq_reif(result2,0,b2_eq0_2) :: defines_var(b2_eq0_2);
constraint bool_clause([b2_eq1],[b_ne2]);
constraint bool_clause([b_ne2,b2_eq0_2],[]);
constraint int_eq(prev1, 1);
constraint int_eq(prev2, 3);
constraint int_eq(curr, 3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let result1 = tr.sys.assignment[tr.varPositions["result1"]]
    let result2 = tr.sys.assignment[tr.varPositions["result2"]]

    # prev1=1 != curr=3, so result1 = 3
    check result1 == 3
    # prev2=3 == curr=3, so result2 = 0
    check result2 == 0

  test "if-then-else feeds into GCC constraint":
    ## Simulates the Mondoku pattern: if-then-else generates across values,
    ## then a GCC constraint enforces counts on the across array.
    ## Row of 3 cells: puzzle=[1,2,1]
    ## across[i] = if puzzle[i-1] != puzzle[i] then puzzle[i] else 0
    ## across = [1, 2, 0] (first cell always = puzzle[0], second cell boundary, third same as second? No.)
    ## Actually: across[0] = puzzle[0] = 1 (no prev, always group boundary)
    ## across[1] = if puzzle[0]!=puzzle[1] then puzzle[1] else 0 = if 1!=2 then 2 else 0 = 2
    ## across[2] = if puzzle[1]!=puzzle[2] then puzzle[2] else 0 = if 2!=1 then 1 else 0 = 1
    ## across = [1, 2, 1] — each color has exactly one group boundary marker
    ## GCC: across has values {0,1,2} with counts [0, 2, 1]? No...
    ## With 2 colors (1,2) and 3 cells: GCC on across requires each color appears once as a boundary
    ## and 0 appears for non-boundaries.
    let src = """
var 1..2: p1 :: output_var;
var 1..2: p2 :: output_var;
var 1..2: p3 :: output_var;
var 0..2: a2 :: output_var;
var 0..2: a3 :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b1_eq :: var_is_introduced :: is_defined_var;
var bool: b1_eq0 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b2_eq :: var_is_introduced :: is_defined_var;
var bool: b2_eq0 :: var_is_introduced :: is_defined_var;
array [1..3] of var int: across :: var_is_introduced = [p1, a2, a3];
array [1..3] of int: cover = [0, 1, 2];
constraint int_lin_ne_reif([1,-1],[p1,p2],0,b1) :: defines_var(b1);
constraint int_eq_reif(a2,p2,b1_eq) :: defines_var(b1_eq);
constraint int_eq_reif(a2,0,b1_eq0) :: defines_var(b1_eq0);
constraint bool_clause([b1_eq],[b1]);
constraint bool_clause([b1,b1_eq0],[]);
constraint int_lin_ne_reif([1,-1],[p2,p3],0,b2) :: defines_var(b2);
constraint int_eq_reif(a3,p3,b2_eq) :: defines_var(b2_eq);
constraint int_eq_reif(a3,0,b2_eq0) :: defines_var(b2_eq0);
constraint bool_clause([b2_eq],[b2]);
constraint bool_clause([b2,b2_eq0],[]);
constraint fzn_global_cardinality(across,cover,[1,1,1]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let p1 = tr.sys.assignment[tr.varPositions["p1"]]
    let p2 = tr.sys.assignment[tr.varPositions["p2"]]
    let p3 = tr.sys.assignment[tr.varPositions["p3"]]
    let a2 = tr.sys.assignment[tr.varPositions["a2"]]
    let a3 = tr.sys.assignment[tr.varPositions["a3"]]

    # Verify if-then-else semantics
    if p1 != p2:
      check a2 == p2
    else:
      check a2 == 0
    if p2 != p3:
      check a3 == p3
    else:
      check a3 == 0

    # Verify GCC: across = [p1, a2, a3] has each of {0,1,2} exactly once
    let across = @[p1, a2, a3]
    var counts = [0, 0, 0]
    for v in across:
      counts[v] += 1
    check counts[0] == 1
    check counts[1] == 1
    check counts[2] == 1

suite "FlatZinc GCC Count Channel Detection":

  test "variable-count GCC converted to count channels":
    ## GCC with variable count outputs feeding into min/max channels.
    ## The translator should detect this and create countEq channels.
    let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 1..3: x4 :: output_var;
var 1..3: x5 :: output_var;
var 1..3: x6 :: output_var;
array [1..6] of var int: xs :: var_is_introduced = [x1,x2,x3,x4,x5,x6];
array [1..3] of int: cover = [1,2,3];
var 0..6: c1 :: var_is_introduced;
var 0..6: c2 :: var_is_introduced;
var 0..6: c3 :: var_is_introduced;
array [1..3] of var int: counts :: var_is_introduced = [c1,c2,c3];
var 0..6: mn :: var_is_introduced :: is_defined_var;
var 0..6: mx :: var_is_introduced :: is_defined_var;
var -6..6: diff :: var_is_introduced :: is_defined_var;
constraint fzn_global_cardinality(xs,cover,counts);
constraint array_int_minimum(mn,counts) :: defines_var(mn);
constraint array_int_maximum(mx,counts) :: defines_var(mx);
constraint int_lin_eq([1,-1,-1],[mx,mn,diff],0) :: defines_var(diff);
solve minimize diff;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Check that countEq channels were created (3 channels for values 1,2,3)
    check tr.sys.baseArray.countEqChannelBindings.len == 3

    # Check that min/max channels were created
    check tr.sys.baseArray.minMaxChannelBindings.len >= 2

    # Solve
    tr.sys.minimize(tr.getObjectiveExpr(),
                    parallel = true, tabuThreshold = 2000,
                    lowerBound = tr.objectiveLoBound,
                    upperBound = tr.objectiveHiBound)

    # With 6 vars and 3 values, balanced = 2 each, diff = 0
    let positions = tr.arrayPositions["xs"]
    var values: seq[int]
    for pos in positions:
      values.add(tr.sys.assignment[pos])

    var counts = [0, 0, 0, 0]
    for v in values:
      counts[v] += 1

    # Optimal: each value appears exactly 2 times
    check counts[1] == 2
    check counts[2] == 2
    check counts[3] == 2

  test "GCC count channels with fixed-count GCC":
    ## Variable-count GCC for objective + fixed-count GCC for structure.
    ## Like Mondoku: fixed GCC ensures contiguity pattern, variable GCC counts for balance.
    let src = """
var 1..2: x1 :: output_var;
var 1..2: x2 :: output_var;
var 1..2: x3 :: output_var;
var 1..2: x4 :: output_var;
array [1..4] of var int: xs :: var_is_introduced = [x1,x2,x3,x4];
array [1..2] of int: cover = [1,2];
var 0..4: c1 :: var_is_introduced;
var 0..4: c2 :: var_is_introduced;
array [1..2] of var int: counts :: var_is_introduced = [c1,c2];
var 0..4: mn :: var_is_introduced :: is_defined_var;
var 0..4: mx :: var_is_introduced :: is_defined_var;
constraint fzn_global_cardinality(xs,cover,counts);
constraint array_int_minimum(mn,counts) :: defines_var(mn);
constraint array_int_maximum(mx,counts) :: defines_var(mx);
constraint fzn_global_cardinality(xs,[1,2],[2,2]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Variable-count GCC should be consumed as count channels
    check tr.sys.baseArray.countEqChannelBindings.len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["xs"]
    var values: seq[int]
    for pos in positions:
      values.add(tr.sys.assignment[pos])

    var counts = [0, 0, 0]
    for v in values:
      counts[v] += 1

    # Fixed GCC forces exact balance
    check counts[1] == 2
    check counts[2] == 2

  test "GCC count channels: non-pure outputs converted with downstream constraints":
    ## Count outputs used by downstream constraints (e.g., int_le) are still
    ## converted to CountEq channels. The downstream constraints become
    ## channel-dep constraints evaluated through the cascade system.
    let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
array [1..3] of var int: xs :: var_is_introduced = [x1,x2,x3];
array [1..3] of int: cover = [1,2,3];
var 0..3: c1 :: output_var;
var 0..3: c2 :: output_var;
var 0..3: c3 :: output_var;
array [1..3] of var int: counts :: var_is_introduced = [c1,c2,c3];
constraint fzn_global_cardinality(xs,cover,counts);
constraint int_le(c1, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # All 3 count vars are converted to CountEq channels
    check tr.sys.baseArray.countEqChannelBindings.len == 3

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["xs"]
    var values: seq[int]
    for pos in positions:
      values.add(tr.sys.assignment[pos])

    # Verify c1 <= 2
    var count1 = 0
    for v in values:
      if v == 1: inc count1
    check count1 <= 2

  test "GCC count channels: domain-encoded bounds are enforced":
    ## MiniZinc absorbs cnt[p] <= limit[p] into variable domains (e.g., var 0..2
    ## instead of a separate int_le constraint). The translator must generate
    ## explicit atMost constraints to enforce these bounds, since channel positions
    ## don't enforce domain membership during search.
    let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 1..3: x4 :: output_var;
var 1..3: x5 :: output_var;
var 1..3: x6 :: output_var;
array [1..6] of var int: xs :: var_is_introduced = [x1,x2,x3,x4,x5,x6];
array [1..3] of int: cover = [1,2,3];
var 0..2: c1 :: output_var;
var 0..3: c2 :: output_var;
var 0..6: c3 :: output_var;
array [1..3] of var int: counts :: var_is_introduced = [c1,c2,c3];
constraint fzn_global_cardinality(xs,cover,counts);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # All 3 count vars are converted to CountEq channels
    check tr.sys.baseArray.countEqChannelBindings.len == 3

    # Solve multiple times to ensure bounds are consistently enforced
    for trial in 0..<10:
      var tr2 = translate(model)
      tr2.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

      let positions = tr2.arrayPositions["xs"]
      var counts = [0, 0, 0, 0]
      for pos in positions:
        counts[tr2.sys.assignment[pos]] += 1

      # Domain-encoded bound: c1 (count of value 1) <= 2
      check counts[1] <= 2
      # Domain-encoded bound: c2 (count of value 2) <= 3
      check counts[2] <= 3
      # c3 has domain 0..6 which is the full range — no effective bound
      check counts[3] <= 6

  test "GCC count channels: domain-encoded bounds with maximization":
    ## Maximization problem where the optimal depends on domain-encoded
    ## count limits. Without bound enforcement, the solver would place
    ## too many high-value pieces.
    ## 6 cells, value 1 is worth 5 (best), value 2 worth 3, value 3 worth 1.
    ## c1 (count of value 1) domain 0..2: at most 2 of the best piece.
    ## Without limit: all value 1, obj = 30.
    ## With limit: c1=2, c2=4, obj = 5*2 + 3*4 = 22.
    let src = """
var 1..3: x1;
var 1..3: x2;
var 1..3: x3;
var 1..3: x4;
var 1..3: x5;
var 1..3: x6;
array [1..6] of var int: xs :: var_is_introduced = [x1,x2,x3,x4,x5,x6];
array [1..3] of int: cover = [1,2,3];
var 0..2: c1 :: var_is_introduced;
var 0..6: c2 :: var_is_introduced;
var 0..6: c3 :: var_is_introduced;
array [1..3] of var int: counts :: var_is_introduced = [c1,c2,c3];
constraint fzn_global_cardinality(xs,cover,counts);
var int: obj :: output_var;
constraint int_lin_eq([5, 3, 1, -1], [c1, c2, c3, obj], 0);
solve maximize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.sys.baseArray.countEqChannelBindings.len == 3

    let objExpr = tr.getObjectiveExpr()
    tr.sys.maximize(objExpr, parallel = true, tabuThreshold = 5000, verbose = false)

    let positions = tr.arrayPositions["xs"]
    var counts = [0, 0, 0, 0]
    for pos in positions:
      counts[tr.sys.assignment[pos]] += 1

    # Verify domain-encoded limit on value 1 is respected
    check counts[1] <= 2

    # Optimal objective: 5*2 + 3*4 = 22
    let objVal = objExpr.evaluate(tr.sys.assignment)
    check objVal == 22

  test "GCC count channels: lower bound from domain is enforced":
    ## FZN domain can also encode lower bounds (e.g., var 2..4 means
    ## at least 2 of this value). Verify atLeast constraints are generated.
    let src = """
var 1..2: x1 :: output_var;
var 1..2: x2 :: output_var;
var 1..2: x3 :: output_var;
var 1..2: x4 :: output_var;
var 1..2: x5 :: output_var;
var 1..2: x6 :: output_var;
array [1..6] of var int: xs :: var_is_introduced = [x1,x2,x3,x4,x5,x6];
array [1..2] of int: cover = [1,2];
var 2..4: c1 :: output_var;
var 2..4: c2 :: output_var;
array [1..2] of var int: counts :: var_is_introduced = [c1,c2];
constraint fzn_global_cardinality(xs,cover,counts);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.sys.baseArray.countEqChannelBindings.len == 2

    for trial in 0..<10:
      var tr2 = translate(model)
      tr2.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

      let positions = tr2.arrayPositions["xs"]
      var counts = [0, 0, 0]
      for pos in positions:
        counts[tr2.sys.assignment[pos]] += 1

      # Domain-encoded bounds: at least 2 and at most 4 of each value
      check counts[1] >= 2
      check counts[1] <= 4
      check counts[2] >= 2
      check counts[2] <= 4

suite "FlatZinc Objective Bound Tightening":

  test "objective lower bound tightened for max(max-min) pattern":
    ## Objective = max(diff) where diff = max(counts) - min(counts).
    ## Since max >= min, diff >= 0, so objective >= 0.
    ## The translator should tighten objectiveLoBound from the FZN domain min to 0.
    let src = """
var 1..3: x1;
var 1..3: x2;
var 1..3: x3;
var 1..3: x4;
var 1..3: x5;
var 1..3: x6;
array [1..6] of var int: xs :: var_is_introduced = [x1,x2,x3,x4,x5,x6];
array [1..3] of int: cover = [1,2,3];
var 0..6: c1 :: var_is_introduced;
var 0..6: c2 :: var_is_introduced;
var 0..6: c3 :: var_is_introduced;
array [1..3] of var int: counts :: var_is_introduced = [c1,c2,c3];
var 0..6: mn :: var_is_introduced :: is_defined_var;
var 0..6: mx :: var_is_introduced :: is_defined_var;
var -6..6: diff :: var_is_introduced :: is_defined_var;
var -6..6: obj :: var_is_introduced :: is_defined_var;
array [1..1] of var int: diffs :: var_is_introduced = [diff];
constraint fzn_global_cardinality(xs,cover,counts);
constraint array_int_minimum(mn,counts) :: defines_var(mn);
constraint array_int_maximum(mx,counts) :: defines_var(mx);
constraint int_lin_eq([1,-1,-1],[mx,mn,diff],0) :: defines_var(diff);
constraint array_int_maximum(obj,diffs) :: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Objective lower bound should be tightened to 0
    check tr.objectiveLoBound >= 0

  test "objective bound not tightened for non-max-min pattern":
    ## When objective is not max(max-min), don't tighten.
    let src = """
var 1..10: x :: output_var;
var 1..10: y :: output_var;
var -10..10: diff :: output_var :: is_defined_var;
constraint int_lin_eq([1,-1,-1],[x,y,diff],0) :: defines_var(diff);
solve minimize diff;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # No count channels, no max-min pattern — should NOT tighten
    # diff can be negative (x < y), so lb should remain -10
    check tr.objectiveLoBound <= -10 or tr.objectivePos < 0

suite "FlatZinc Combined Pattern Detection":

  test "full Mondoku-like pattern: if-then-else + GCC + count channels + optimization":
    ## Mini Mondoku: 2x2 grid, 2 colors.
    ## Each row/col has one contiguous block per color.
    ## Minimize max imbalance.
    ##
    ## Variables: puzzle[1..4] (2x2 grid row-major)
    ## across[r,c] = if puzzle[r,c-1] != puzzle[r,c] then puzzle[r,c] else 0
    ## GCC on across row: each of {0,1,2} appears specific count
    ## Count channels: count occurrences of each color in each row
    ## Objective: minimize max(max_count_r - min_count_r)
    let src = """
var 1..2: p1 :: output_var;
var 1..2: p2 :: output_var;
var 1..2: p3 :: output_var;
var 1..2: p4 :: output_var;
array [1..2] of int: colors = [1,2];
var 0..2: c1_r1 :: var_is_introduced;
var 0..2: c2_r1 :: var_is_introduced;
array [1..2] of var int: counts_r1 :: var_is_introduced = [c1_r1, c2_r1];
var 0..2: c1_r2 :: var_is_introduced;
var 0..2: c2_r2 :: var_is_introduced;
array [1..2] of var int: counts_r2 :: var_is_introduced = [c1_r2, c2_r2];
var 0..2: mn_r1 :: var_is_introduced :: is_defined_var;
var 0..2: mx_r1 :: var_is_introduced :: is_defined_var;
var -2..2: diff_r1 :: var_is_introduced :: is_defined_var;
var 0..2: mn_r2 :: var_is_introduced :: is_defined_var;
var 0..2: mx_r2 :: var_is_introduced :: is_defined_var;
var -2..2: diff_r2 :: var_is_introduced :: is_defined_var;
var -2..2: obj :: var_is_introduced :: is_defined_var;
array [1..2] of var int: diffs :: var_is_introduced = [diff_r1, diff_r2];
constraint fzn_global_cardinality([p1,p2],colors,counts_r1);
constraint fzn_global_cardinality([p3,p4],colors,counts_r2);
constraint array_int_minimum(mn_r1,counts_r1) :: defines_var(mn_r1);
constraint array_int_maximum(mx_r1,counts_r1) :: defines_var(mx_r1);
constraint int_lin_eq([1,-1,-1],[mx_r1,mn_r1,diff_r1],0) :: defines_var(diff_r1);
constraint array_int_minimum(mn_r2,counts_r2) :: defines_var(mn_r2);
constraint array_int_maximum(mx_r2,counts_r2) :: defines_var(mx_r2);
constraint int_lin_eq([1,-1,-1],[mx_r2,mn_r2,diff_r2],0) :: defines_var(diff_r2);
constraint array_int_maximum(obj,diffs) :: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Verify detection
    check tr.sys.baseArray.countEqChannelBindings.len == 4  # 2 colors × 2 rows
    check tr.sys.baseArray.minMaxChannelBindings.len >= 4   # mn/mx per row + obj
    check tr.objectiveLoBound >= 0  # tightened

    # Solve
    tr.sys.minimize(tr.getObjectiveExpr(),
                    parallel = true, tabuThreshold = 2000,
                    lowerBound = tr.objectiveLoBound,
                    upperBound = tr.objectiveHiBound)

    # With 2 vars per row, 2 colors: balanced = 1 each, diff = 0
    let p1 = tr.sys.assignment[tr.varPositions["p1"]]
    let p2 = tr.sys.assignment[tr.varPositions["p2"]]
    let p3 = tr.sys.assignment[tr.varPositions["p3"]]
    let p4 = tr.sys.assignment[tr.varPositions["p4"]]

    # Each row should have one of each color for optimal balance
    check p1 != p2  # row 1 balanced
    check p3 != p4  # row 2 balanced

suite "FlatZinc Case-Analysis 1-Pos-1-Neg Channel Detection":

  test "conditional size channel via bool_clause([A],[B])":
    ## Encodes: size = if selector==1 then 5 else 0
    ## Uses the 1-positive-1-negative bool_clause pattern:
    ##   int_eq_reif(selector, 1, B) :: defines_var(B)
    ##   int_eq_reif(size, 5, A) :: defines_var(A)
    ##   bool_clause([A], [B])  — selector==1 → size==5
    ## With domain 0..7 (non-binary), default should be 0.
    let src = """
var 1..3: selector :: output_var;
var 0..7: size :: output_var;
var bool: b_eq_sel :: var_is_introduced :: is_defined_var;
var bool: b_eq_size :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(selector, 1, b_eq_sel) :: defines_var(b_eq_sel);
constraint int_eq_reif(size, 5, b_eq_size) :: defines_var(b_eq_size);
constraint bool_clause([b_eq_size], [b_eq_sel]);
constraint int_eq(selector, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let sel = tr.sys.assignment[tr.varPositions["selector"]]
    let sz = tr.sys.assignment[tr.varPositions["size"]]

    check sel == 1
    check sz == 5  # selector==1 → size==5

  test "conditional size defaults to 0 for non-matching selector":
    ## Same pattern but selector is forced to 2 (not 1).
    ## size should default to 0 since the case doesn't match.
    let src = """
var 1..3: selector :: output_var;
var 0..7: size :: output_var;
var bool: b_eq_sel :: var_is_introduced :: is_defined_var;
var bool: b_eq_size :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(selector, 1, b_eq_sel) :: defines_var(b_eq_sel);
constraint int_eq_reif(size, 5, b_eq_size) :: defines_var(b_eq_size);
constraint bool_clause([b_eq_size], [b_eq_sel]);
constraint int_eq(selector, 2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let sel = tr.sys.assignment[tr.varPositions["selector"]]
    let sz = tr.sys.assignment[tr.varPositions["size"]]

    check sel == 2
    check sz == 0  # selector!=1 → size defaults to 0

  test "multiple conditional sizes with same condition variable":
    ## 3 size variables, each activated by a different selector value.
    ## size1 = if sel==1 then 4 else 0
    ## size2 = if sel==2 then 3 else 0
    ## size3 = if sel==1 then 6 else 0
    let src = """
var 1..3: sel :: output_var;
var 0..7: size1 :: output_var;
var 0..7: size2 :: output_var;
var 0..7: size3 :: output_var;
var bool: b_sel1 :: var_is_introduced :: is_defined_var;
var bool: b_sel2 :: var_is_introduced :: is_defined_var;
var bool: b_sz1 :: var_is_introduced :: is_defined_var;
var bool: b_sz2 :: var_is_introduced :: is_defined_var;
var bool: b_sz3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(sel, 1, b_sel1) :: defines_var(b_sel1);
constraint int_eq_reif(sel, 2, b_sel2) :: defines_var(b_sel2);
constraint int_eq_reif(size1, 4, b_sz1) :: defines_var(b_sz1);
constraint int_eq_reif(size2, 3, b_sz2) :: defines_var(b_sz2);
constraint int_eq_reif(size3, 6, b_sz3) :: defines_var(b_sz3);
constraint bool_clause([b_sz1], [b_sel1]);
constraint bool_clause([b_sz2], [b_sel2]);
constraint bool_clause([b_sz3], [b_sel1]);
constraint int_eq(sel, 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let sel = tr.sys.assignment[tr.varPositions["sel"]]
    let s1 = tr.sys.assignment[tr.varPositions["size1"]]
    let s2 = tr.sys.assignment[tr.varPositions["size2"]]
    let s3 = tr.sys.assignment[tr.varPositions["size3"]]

    check sel == 1
    check s1 == 4  # sel==1 → size1==4
    check s2 == 0  # sel!=2 → size2==0
    check s3 == 6  # sel==1 → size3==6
