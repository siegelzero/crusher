## Tests for incremental cascade evaluation in channel-dep penalty computation.
##
## These tests verify the correctness of:
## 1. BFS cascade topology building with diamond patterns
## 2. Incremental cascade evaluation with dirty propagation
## 3. Min/max channels included as dynamic entries in cascade topology
## 4. Forward dependency tracking and cache invalidation
## 5. Optimization correctness with channel-dep constraints
##
## The key optimization: when element external deps change after a move,
## only dirty cascade entries are re-evaluated. Clean entries use cached
## values, with dirty propagation through forward deps when values change.

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]

import crusher
import flatzinc/[parser, translator]

proc getObjectiveExpr(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
  elif tr.objectivePos == ObjPosDefinedExpr: tr.objectiveDefExpr
  else: raise newException(ValueError, "No objective")

suite "Incremental Cascade Evaluation":

  test "min/max channel optimization with element channels":
    ## Tests that optimization works correctly when the objective involves
    ## a min/max channel aggregating element channel results.
    ## This is the core pattern that triggers incremental cascade evaluation:
    ## - search variables feed element channels
    ## - element channels feed into a max channel
    ## - max channel is constrained by the optimization bound
    ##
    ## Pattern: 4 vars x1..x4 in {1..4}, allDifferent.
    ## s_i = element(x_i, [10, 20, 30, 40]) — maps position to "signal" value.
    ## z = max(s_1, ..., s_4). Minimize z.
    ## Since allDifferent forces a permutation, z = max(signals) = 40 always.
    let src = """
var 1..4: x1;
var 1..4: x2;
var 1..4: x3;
var 1..4: x4;
var 10..40: s1:: is_defined_var:: var_is_introduced;
var 10..40: s2:: is_defined_var:: var_is_introduced;
var 10..40: s3:: is_defined_var:: var_is_introduced;
var 10..40: s4:: is_defined_var:: var_is_introduced;
var 10..40: z:: output_var;
array [1..4] of var int: xs:: output_array([1..4]) = [x1, x2, x3, x4];
array [1..4] of int: signals = [10, 20, 30, 40];
constraint gecode_all_different_int(xs);
constraint array_int_element(x1, signals, s1):: defines_var(s1);
constraint array_int_element(x2, signals, s2):: defines_var(s2);
constraint array_int_element(x3, signals, s3):: defines_var(s3);
constraint array_int_element(x4, signals, s4):: defines_var(s4);
constraint array_int_maximum(z, [s1, s2, s3, s4]):: defines_var(z);
solve minimize z;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # z should be a channel (min/max defines_var)
    check "z" in tr.channelVarNames

    # s_i should be channels (element defines_var)
    for name in ["s1", "s2", "s3", "s4"]:
      check name in tr.channelVarNames

    let objExpr = tr.getObjectiveExpr()
    minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

    # Get solution
    var xs: array[4, int]
    for i in 0..3:
      xs[i] = tr.sys.assignment[tr.varPositions["x" & $(i+1)]]

    # Must be a permutation of 1..4
    check xs.toSeq.sorted == @[1, 2, 3, 4]

    # z = max(signals[x1], ..., signals[x4]) = max(10, 20, 30, 40) = 40
    let zVal = objExpr.evaluate(tr.sys.assignment)
    check zVal == 40

  test "min/max optimization where ordering matters":
    ## Tests optimization with a min/max objective where the ordering
    ## of search variables affects the objective value.
    ##
    ## 3 vars x1..x3 in {1..3}, allDifferent (permutation).
    ## Costs: cost[i] = element(x_i, [weights]).
    ## weights vary per position: pos1=[3,1,2], pos2=[1,2,3], pos3=[2,3,1].
    ## z = max(cost1, cost2, cost3). Minimize z.
    ##
    ## Optimal: find permutation minimizing the maximum cost.
    ## With weights [[3,1,2],[1,2,3],[2,3,1]]:
    ##   x=(2,1,3): costs=(1,1,1), z=1
    ##   x=(3,1,2): costs=(2,1,3), z=3
    ##   x=(1,2,3): costs=(3,2,1), z=3
    ##   x=(2,3,1): costs=(1,3,2), z=3
    ## Optimal z=1 when x=(2,1,3).
    let src = """
var 1..3: x1;
var 1..3: x2;
var 1..3: x3;
var 1..3: c1:: is_defined_var:: var_is_introduced;
var 1..3: c2:: is_defined_var:: var_is_introduced;
var 1..3: c3:: is_defined_var:: var_is_introduced;
var 1..3: z:: output_var;
array [1..3] of var int: xs:: output_array([1..3]) = [x1, x2, x3];
array [1..3] of int: w1 = [3, 1, 2];
array [1..3] of int: w2 = [1, 2, 3];
array [1..3] of int: w3 = [2, 3, 1];
constraint gecode_all_different_int(xs);
constraint array_int_element(x1, w1, c1):: defines_var(c1);
constraint array_int_element(x2, w2, c2):: defines_var(c2);
constraint array_int_element(x3, w3, c3):: defines_var(c3);
constraint array_int_maximum(z, [c1, c2, c3]):: defines_var(z);
solve minimize z;
"""
    for trial in 0..<5:
      let model = parseFzn(src)
      var tr = translate(model)

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      var xs: array[3, int]
      for i in 0..2:
        xs[i] = tr.sys.assignment[tr.varPositions["x" & $(i+1)]]
      check xs.toSeq.sorted == @[1, 2, 3]

      let zVal = objExpr.evaluate(tr.sys.assignment)
      # Verify z is the max of the per-position costs
      let w1 = [3, 1, 2]
      let w2 = [1, 2, 3]
      let w3 = [2, 3, 1]
      let c1 = w1[xs[0] - 1]
      let c2 = w2[xs[1] - 1]
      let c3 = w3[xs[2] - 1]
      check zVal == max(c1, max(c2, c3))
      # Optimal z = 1 (x = [2, 1, 3])
      check zVal == 1

  test "minimize max with reification channels":
    ## Tests the full cascade path: search vars → reification channels
    ## (int_le_reif + bool2int) → element channels → min/max channel.
    ## This pattern creates deep cascade chains that exercise incremental
    ## evaluation with dirty propagation.
    ##
    ## Model: 3 vars in {1..3}, allDifferent.
    ## b_ij = (x_i <= j) reified, then summed to get cumulative counts.
    ## z = max(count_at_each_step). Minimize z.
    let src = """
var 1..3: x1;
var 1..3: x2;
var 1..3: x3;
var 0..1: b11:: is_defined_var:: var_is_introduced;
var 0..1: b12:: is_defined_var:: var_is_introduced;
var 0..1: b21:: is_defined_var:: var_is_introduced;
var 0..1: b22:: is_defined_var:: var_is_introduced;
var 0..1: b31:: is_defined_var:: var_is_introduced;
var 0..1: b32:: is_defined_var:: var_is_introduced;
var 0..1: i11:: is_defined_var:: var_is_introduced;
var 0..1: i12:: is_defined_var:: var_is_introduced;
var 0..1: i21:: is_defined_var:: var_is_introduced;
var 0..1: i22:: is_defined_var:: var_is_introduced;
var 0..1: i31:: is_defined_var:: var_is_introduced;
var 0..1: i32:: is_defined_var:: var_is_introduced;
var 0..3: cnt1:: is_defined_var:: var_is_introduced;
var 0..3: cnt2:: is_defined_var:: var_is_introduced;
var 0..3: z:: output_var;
array [1..3] of var int: xs:: output_array([1..3]) = [x1, x2, x3];
constraint gecode_all_different_int(xs);
constraint int_le_reif(x1, 1, b11):: defines_var(b11);
constraint int_le_reif(x1, 2, b12):: defines_var(b12);
constraint int_le_reif(x2, 1, b21):: defines_var(b21);
constraint int_le_reif(x2, 2, b22):: defines_var(b22);
constraint int_le_reif(x3, 1, b31):: defines_var(b31);
constraint int_le_reif(x3, 2, b32):: defines_var(b32);
constraint bool2int(b11, i11):: defines_var(i11);
constraint bool2int(b12, i12):: defines_var(i12);
constraint bool2int(b21, i21):: defines_var(i21);
constraint bool2int(b22, i22):: defines_var(i22);
constraint bool2int(b31, i31):: defines_var(i31);
constraint bool2int(b32, i32):: defines_var(i32);
constraint int_lin_eq([1, -1, -1, -1], [cnt1, i11, i21, i31], 0):: defines_var(cnt1);
constraint int_lin_eq([1, -1, -1, -1], [cnt2, i12, i22, i32], 0):: defines_var(cnt2);
constraint array_int_maximum(z, [cnt1, cnt2]):: defines_var(z);
solve minimize z;
"""
    for trial in 0..<5:
      let model = parseFzn(src)
      var tr = translate(model)

      # Reification vars should be channels
      for name in ["b11", "b12", "b21", "b22", "b31", "b32",
                    "i11", "i12", "i21", "i22", "i31", "i32"]:
        check name in tr.channelVarNames

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      var xs: array[3, int]
      for i in 0..2:
        xs[i] = tr.sys.assignment[tr.varPositions["x" & $(i+1)]]
      check xs.toSeq.sorted == @[1, 2, 3]

      # cnt1 = #{x_i <= 1} = 1 (exactly one var is 1)
      # cnt2 = #{x_i <= 2} = 2 (exactly two vars are <= 2)
      # z = max(1, 2) = 2 for any permutation
      let zVal = objExpr.evaluate(tr.sys.assignment)
      check zVal == 2

  test "cascade with diamond pattern — shared channel dependencies":
    ## Tests cascade topology building when multiple element channels
    ## feed into the same downstream min/max channel, creating a
    ## diamond pattern in the dependency DAG.
    ## The BFS topology must handle this correctly (skip duplicates).
    ##
    ## Pattern:
    ##   x1, x2 → elem1 → max(elem1, elem2)
    ##   x1     → elem2 ↗
    ## elem1 and elem2 both read from x1, creating overlapping paths.
    let src = """
var 1..3: x1;
var 1..3: x2;
var 1..9: e1:: is_defined_var:: var_is_introduced;
var 1..3: e2:: is_defined_var:: var_is_introduced;
var 1..9: z:: output_var;
array [1..3] of int: costs1 = [1, 4, 9];
array [1..3] of int: costs2 = [3, 2, 1];
constraint array_int_element(x1, costs1, e1):: defines_var(e1);
constraint array_int_element(x1, costs2, e2):: defines_var(e2);
constraint array_int_maximum(z, [e1, e2]):: defines_var(z);
constraint int_ne(x1, x2);
solve minimize z;
"""
    for trial in 0..<5:
      let model = parseFzn(src)
      var tr = translate(model)

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      let x1 = tr.sys.assignment[tr.varPositions["x1"]]
      let x2 = tr.sys.assignment[tr.varPositions["x2"]]
      check x1 != x2

      let costs1 = [1, 4, 9]
      let costs2 = [3, 2, 1]
      let e1 = costs1[x1 - 1]
      let e2 = costs2[x1 - 1]
      let zExpected = max(e1, e2)

      let zVal = objExpr.evaluate(tr.sys.assignment)
      check zVal == zExpected

      # Optimal: x1=1 → e1=1, e2=3, z=3; x1=2 → e1=4, e2=2, z=4; x1=3 → e1=9, e2=1, z=9
      # Best is x1=1, z=3
      check zVal == 3
      check x1 == 1

  test "minimize with external deps — multi-variable element channels":
    ## Tests that incremental cascade evaluation correctly handles
    ## external dependencies: element channels whose array entries
    ## reference other search variables (not just the index variable).
    ##
    ## This forces the cascade to have external deps, triggering the
    ## incremental evaluation path with dirty propagation.
    ##
    ## Model: 4 vars, allDifferent. Each var's "cost" depends on what
    ## value the NEXT var has (circular dependency through channels).
    ## cost_i = element(x_{i+1 mod 4}, weights_i)
    ## z = max(costs). Minimize z.
    let src = """
var 1..4: x1;
var 1..4: x2;
var 1..4: x3;
var 1..4: x4;
var 1..4: c1:: is_defined_var:: var_is_introduced;
var 1..4: c2:: is_defined_var:: var_is_introduced;
var 1..4: c3:: is_defined_var:: var_is_introduced;
var 1..4: c4:: is_defined_var:: var_is_introduced;
var 1..4: z:: output_var;
array [1..4] of var int: xs:: output_array([1..4]) = [x1, x2, x3, x4];
array [1..4] of int: w1 = [4, 1, 2, 3];
array [1..4] of int: w2 = [2, 3, 4, 1];
array [1..4] of int: w3 = [1, 4, 3, 2];
array [1..4] of int: w4 = [3, 2, 1, 4];
constraint gecode_all_different_int(xs);
constraint array_int_element(x2, w1, c1):: defines_var(c1);
constraint array_int_element(x3, w2, c2):: defines_var(c2);
constraint array_int_element(x4, w3, c3):: defines_var(c3);
constraint array_int_element(x1, w4, c4):: defines_var(c4);
constraint array_int_maximum(z, [c1, c2, c3, c4]):: defines_var(z);
solve minimize z;
"""
    for trial in 0..<3:
      let model = parseFzn(src)
      var tr = translate(model)

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      var xs: array[4, int]
      for i in 0..3:
        xs[i] = tr.sys.assignment[tr.varPositions["x" & $(i+1)]]
      check xs.toSeq.sorted == @[1, 2, 3, 4]

      let w1 = [4, 1, 2, 3]
      let w2 = [2, 3, 4, 1]
      let w3 = [1, 4, 3, 2]
      let w4 = [3, 2, 1, 4]
      let c1 = w1[xs[1] - 1]
      let c2 = w2[xs[2] - 1]
      let c3 = w3[xs[3] - 1]
      let c4 = w4[xs[0] - 1]
      let zExpected = max(max(c1, c2), max(c3, c4))

      let zVal = objExpr.evaluate(tr.sys.assignment)
      check zVal == zExpected

      # Verify optimality: brute force check all 24 permutations
      var bestZ = high(int)
      for a in 1..4:
        for b in 1..4:
          if b == a: continue
          for c in 1..4:
            if c == a or c == b: continue
            let d = 10 - a - b - c  # remaining value
            let tc1 = w1[b - 1]
            let tc2 = w2[c - 1]
            let tc3 = w3[d - 1]
            let tc4 = w4[a - 1]
            let tz = max(max(tc1, tc2), max(tc3, tc4))
            bestZ = min(bestZ, tz)
      check zVal == bestZ

  test "minimize min channel — aggregation direction":
    ## Tests with array_int_minimum instead of maximum.
    ## Ensures cascade evaluation works for both min and max channels.
    let src = """
var 1..3: x1;
var 1..3: x2;
var 1..3: x3;
var 1..10: c1:: is_defined_var:: var_is_introduced;
var 1..10: c2:: is_defined_var:: var_is_introduced;
var 1..10: c3:: is_defined_var:: var_is_introduced;
var 1..10: z:: output_var;
array [1..3] of var int: xs:: output_array([1..3]) = [x1, x2, x3];
array [1..3] of int: w1 = [5, 1, 3];
array [1..3] of int: w2 = [2, 4, 6];
array [1..3] of int: w3 = [7, 3, 1];
constraint gecode_all_different_int(xs);
constraint array_int_element(x1, w1, c1):: defines_var(c1);
constraint array_int_element(x2, w2, c2):: defines_var(c2);
constraint array_int_element(x3, w3, c3):: defines_var(c3);
constraint array_int_minimum(z, [c1, c2, c3]):: defines_var(z);
solve maximize z;
"""
    for trial in 0..<5:
      let model = parseFzn(src)
      var tr = translate(model)

      let objExpr = tr.getObjectiveExpr()
      maximize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      var xs: array[3, int]
      for i in 0..2:
        xs[i] = tr.sys.assignment[tr.varPositions["x" & $(i+1)]]
      check xs.toSeq.sorted == @[1, 2, 3]

      let w1 = [5, 1, 3]
      let w2 = [2, 4, 6]
      let w3 = [7, 3, 1]
      let c1 = w1[xs[0] - 1]
      let c2 = w2[xs[1] - 1]
      let c3 = w3[xs[2] - 1]
      let zExpected = min(c1, min(c2, c3))
      let zVal = objExpr.evaluate(tr.sys.assignment)
      check zVal == zExpected

      # Brute force optimal
      var bestZ = low(int)
      for a in 1..3:
        for b in 1..3:
          if b == a: continue
          let c = 6 - a - b
          let tc1 = w1[a - 1]
          let tc2 = w2[b - 1]
          let tc3 = w3[c - 1]
          let tz = min(tc1, min(tc2, tc3))
          bestZ = max(bestZ, tz)
      check zVal == bestZ

  test "cascade cache correctness across multiple optimization rounds":
    ## Tests that incremental cascade caches are correctly invalidated
    ## across multiple optimization rounds (binary search tightens bounds
    ## each round, changing the constraint and thus the channel-dep
    ## penalty landscape).
    ##
    ## Uses a 5-var permutation with weighted max objective to force
    ## multiple binary search iterations.
    let src = """
var 1..5: x1;
var 1..5: x2;
var 1..5: x3;
var 1..5: x4;
var 1..5: x5;
var 1..25: c1:: is_defined_var:: var_is_introduced;
var 1..25: c2:: is_defined_var:: var_is_introduced;
var 1..25: c3:: is_defined_var:: var_is_introduced;
var 1..25: c4:: is_defined_var:: var_is_introduced;
var 1..25: c5:: is_defined_var:: var_is_introduced;
var 1..25: z:: output_var;
array [1..5] of var int: xs:: output_array([1..5]) = [x1, x2, x3, x4, x5];
array [1..5] of int: w1 = [10, 3, 7, 1, 5];
array [1..5] of int: w2 = [2, 8, 4, 6, 9];
array [1..5] of int: w3 = [5, 1, 9, 3, 7];
array [1..5] of int: w4 = [8, 6, 2, 7, 4];
array [1..5] of int: w5 = [4, 9, 6, 5, 1];
constraint gecode_all_different_int(xs);
constraint array_int_element(x1, w1, c1):: defines_var(c1);
constraint array_int_element(x2, w2, c2):: defines_var(c2);
constraint array_int_element(x3, w3, c3):: defines_var(c3);
constraint array_int_element(x4, w4, c4):: defines_var(c4);
constraint array_int_element(x5, w5, c5):: defines_var(c5);
constraint array_int_maximum(z, [c1, c2, c3, c4, c5]):: defines_var(z);
solve minimize z;
"""
    for trial in 0..<3:
      let model = parseFzn(src)
      var tr = translate(model)

      let objExpr = tr.getObjectiveExpr()
      minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
               lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

      var xs: array[5, int]
      for i in 0..4:
        xs[i] = tr.sys.assignment[tr.varPositions["x" & $(i+1)]]
      check xs.toSeq.sorted == @[1, 2, 3, 4, 5]

      let weights = [@[10, 3, 7, 1, 5], @[2, 8, 4, 6, 9],
                      @[5, 1, 9, 3, 7], @[8, 6, 2, 7, 4],
                      @[4, 9, 6, 5, 1]]
      var costs: array[5, int]
      for i in 0..4:
        costs[i] = weights[i][xs[i] - 1]
      let zVal = objExpr.evaluate(tr.sys.assignment)
      check zVal == costs.max

      # Brute force: enumerate all 120 permutations
      var bestZ = high(int)
      var perm = @[1, 2, 3, 4, 5]
      while true:
        var maxCost = 0
        for i in 0..4:
          maxCost = max(maxCost, weights[i][perm[i] - 1])
        bestZ = min(bestZ, maxCost)
        if not perm.nextPermutation:
          break
      check zVal == bestZ
