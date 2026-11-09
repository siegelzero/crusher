## Tests for the native optional-task disjunctive (crusher_disjunctive_opt):
## MultiMachineNoOverlap fixed blocks / ignored machine / shared machine
## positions, and the FlatZinc translation (grouped per allocation variable,
## and the per-constraint fallback).

import unittest
import std/[tables, sets]
import crusher
import constraints/multiMachineNoOverlap
import flatzinc/[parser, translator]

proc overlaps(s1, d1, s2, d2: int): bool = s1 < s2 + d2 and s2 < s1 + d1

suite "MultiMachineNoOverlap extensions":

  test "fixed blocks count as busy time on their machine only":
    # Task 0 on machine 1 (pos 1), start pos 0. Machine 1 is busy on [10, 15).
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0], machinePositions = @[1], fixedMachines = @[-1],
      durations = @[5], numMachineValues = 3, maxTime = 30,
      fixedBlocks = @[newSeq[(int, int)](), @[(10, 5)], newSeq[(int, int)]()])
    c.initialize(@[12, 1])            # [12,17) vs [10,15): 3 units overlap
    check c.cost == 3
    check c.moveDelta(0, 12, 20) == -3
    check c.moveDelta(1, 1, 2) == -3  # moving to machine 2 clears it
    c.updatePosition(0, 0)
    check c.cost == 0
    # Batch evaluation agrees with moveDelta, including the block
    let dom = @[0, 6, 8, 10, 14, 20]
    let batch = c.batchMovePenalty(0, 0, dom)
    for i, v in dom:
      check batch[i] == c.moveDelta(0, 0, v)

  test "ignored machine value is unconstrained":
    # Presence bools as the machine: 1 = present, 0 = absent (ignored).
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1], machinePositions = @[2, 3], fixedMachines = @[-1, -1],
      durations = @[4, 4], numMachineValues = 2, maxTime = 20, ignoreMachine = 0)
    c.initialize(@[0, 2, 1, 1])       # both present, [0,4) vs [2,6): overlap 2
    check c.cost == 2
    check c.moveDelta(3, 1, 0) == -2  # making task 1 absent removes it
    c.updatePosition(3, 0)
    check c.cost == 0
    check c.moveDelta(1, 2, 0) == 0   # absent task: start moves are free
    check c.batchMovePenalty(1, 2, @[0, 1, 2]) == @[0, 0, 0]

  test "tasks sharing a machine position move together":
    # Tasks 0 and 1 share machine position 3 (same-allocation group); task 2
    # has its own machine position 4. Starts at positions 0..2.
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1, 2], machinePositions = @[3, 3, 4],
      fixedMachines = @[-1, -1, -1], durations = @[3, 3, 3],
      numMachineValues = 3, maxTime = 20)
    var a = @[0, 10, 1, 1, 2]         # tasks 0,1 on machine 1; task 2 on machine 2 at [1,4)
    c.initialize(a)
    check c.cost == 0
    # Moving the shared position to machine 2 brings task 0 onto task 2: overlap 2
    let d = c.moveDelta(3, 1, 2)
    check d == 2
    c.updatePosition(3, 2)
    check c.cost == 2
    check c.currentMachines[0] == 2 and c.currentMachines[1] == 2

suite "crusher_disjunctive_opt translation":

  test "per-team optional disjunctives are grouped by allocation variable":
    # Three tasks, two teams. Opt encoding as MiniZinc emits it: deopt alias
    # x_i_m, presence o_i_m <-> (alloc_i == m), o -> x == start, ¬o -> x == 0.
    # Team 1 also has a fixed unavailability block [0, 4).
    var src = "var 1..2: a1 :: output_var;\nvar 1..2: a2 :: output_var;\nvar 1..2: a3 :: output_var;\n"
    src &= "var 0..10: s1 :: output_var;\nvar 0..10: s2 :: output_var;\nvar 0..10: s3 :: output_var;\n"
    var body = ""
    for m in 1..2:
      var xs, os: seq[string]
      for i in 1..3:
        let x = "x" & $i & "_" & $m
        let o = "o" & $i & "_" & $m
        let r = "r" & $i & "_" & $m
        let e = "e" & $i & "_" & $m
        let z = "z" & $i & "_" & $m
        src &= "var 0..10: " & x & ";\nvar bool: " & o & ";\n"
        src &= "var bool: " & r & " :: is_defined_var;\nvar bool: " & e & " :: is_defined_var;\nvar bool: " & z & " :: is_defined_var;\n"
        body &= "constraint int_eq_reif(a" & $i & "," & $m & "," & r & ") :: defines_var(" & r & ");\n"
        body &= "constraint bool_clause([" & r & "],[" & o & "]);\nconstraint bool_clause([" & o & "],[" & r & "]);\n"
        body &= "constraint int_eq_reif(" & x & ",s" & $i & "," & e & ") :: defines_var(" & e & ");\n"
        body &= "constraint bool_clause([" & e & "],[" & r & "]);\n"
        body &= "constraint int_eq_reif(" & x & ",0," & z & ") :: defines_var(" & z & ");\n"
        body &= "constraint bool_clause([" & o & "," & z & "],[]);\n"
        xs.add(x); os.add(o)
      var sArr = "["
      var oArr = "["
      var dArr = "["
      for i in 0..<3:
        sArr &= xs[i] & ","; oArr &= os[i] & ","; dArr &= "4,"
      if m == 1:
        sArr &= "0]"; oArr &= "true]"; dArr &= "4]"
      else:
        sArr[^1] = ']'; oArr[^1] = ']'; dArr[^1] = ']'
      body &= "constraint crusher_disjunctive_opt(" & sArr & "," & oArr & "," & dArr & ");\n"
    src &= body & "solve satisfy;\n"
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.multiMachineNoOverlapInfos.len == 1
    tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
    check tr.sys.hasFeasibleSolution
    var al, st: seq[int]
    for i in 1..3:
      al.add tr.sys.assignment[tr.varPositions["a" & $i]]
      st.add tr.sys.assignment[tr.varPositions["s" & $i]]
    for i in 0..<3:
      if al[i] == 1: check not overlaps(st[i], 4, 0, 4)   # team 1 calendar block
      for j in i+1..<3:
        if al[i] == al[j]: check not overlaps(st[i], 4, st[j], 4)

  test "fallback: presence literals that are plain bools":
    let src = """
var 0..12: s1 :: output_var;
var 0..12: s2 :: output_var;
var 0..12: s3 :: output_var;
var bool: p1 :: output_var;
var bool: p2 :: output_var;
var bool: p3 :: output_var;
constraint bool_clause([p1],[]);
constraint bool_clause([p2],[]);
constraint bool_clause([p3],[]);
constraint crusher_disjunctive_opt([s1,s2,s3,2],[p1,p2,p3,true],[3,3,3,2]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.multiMachineNoOverlapInfos.len == 0
    tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
    check tr.sys.hasFeasibleSolution
    var st: seq[int]
    for n in ["s1", "s2", "s3"]: st.add tr.sys.assignment[tr.varPositions[n]]
    # All present (forced): pairwise disjoint and clear of the block [2, 4)
    for i in 0..<3:
      check not overlaps(st[i], 3, 2, 2)
      for j in i+1..<3:
        check not overlaps(st[i], 3, st[j], 3)

proc objExprOf(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
  else: tr.objectiveDefExpr

suite "Objective dominant term":

  test "lexicographic weight is detected and optimized":
    # obj = 100*v + r with v + r >= 4: optimum v = 1, r = 3 (obj 103)
    let src = """
var 1..5: v :: output_var;
var 0..9: r :: output_var;
var 0..1000: obj :: output_var :: is_defined_var;
constraint int_lin_le([-1, -1], [v, r], -4);
constraint int_lin_eq([100, 1, -1], [v, r, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.sys.objectiveDominant.active
    check tr.sys.objectiveDominant.weight == 100
    let objExpr = tr.objExprOf()
    minimize(tr.sys, objExpr, parallel = false, tabuThreshold = 2000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)
    check tr.sys.assignment[tr.varPositions["v"]] == 1
    check objExpr.evaluate(tr.sys.assignment) == 103

  test "comparable weights are not treated as dominant":
    let src = """
var 1..5: v :: output_var;
var 0..9: r :: output_var;
var 0..1000: obj :: output_var :: is_defined_var;
constraint int_lin_eq([3, 1, -1], [v, r, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.sys.objectiveDominant.active
