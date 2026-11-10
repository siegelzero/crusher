## Tests for optional-task disjunctives with variable durations (saeling):
## MultiMachineNoOverlap duration positions and incremental updates, the
## FlatZinc translation of crusher_disjunctive_opt with variable durations
## (per constraint and grouped into allocation families, including unload
## starts tied to their task through int_lin_eq_reif), and CPM presolve
## soundness for precedences `s1 + d <= s2` with a variable d.

import unittest
import std/[random, tables, strutils]
import crusher
import constraints/multiMachineNoOverlap
import flatzinc/[parser, translator]

proc overlaps(s1, d1, s2, d2: int): bool = s1 < s2 + d2 and s2 < s1 + d1

suite "MultiMachineNoOverlap variable durations":

  test "incremental cost and moveDelta match a full recompute":
    # Tasks 0..5: starts at positions 0..5, machines at 6..11 (tasks 4 and 5
    # share position 11), durations: tasks 0..2 variable at 12..14, the
    # others constant. Machine 0 is ignored; machine 2 has a fixed block.
    var rng = initRand(7)
    let n = 6
    var starts, machines, durPos, fixed: seq[int]
    for t in 0..<n:
      starts.add(t)
      machines.add(if t == 5: 11 else: 6 + t)
      fixed.add(-1)
      durPos.add(if t < 3: 12 + t else: -1)
    let c = newMultiMachineNoOverlapConstraint[int](
      starts, machines, fixed, durations = @[0, 0, 0, 3, 4, 2],
      numMachineValues = 4, maxTime = 40,
      fixedBlocks = @[newSeq[(int, int)](), newSeq[(int, int)](), @[(5, 4)], newSeq[(int, int)]()],
      ignoreMachine = 0, durPositions = durPos)
    var a = newSeq[int](15)
    proc randomValue(p: int): int =
      if p < 6: rng.rand(0..20)
      elif p < 12: rng.rand(0..3)
      else: rng.rand(0..6)
    for p in 0..<15: a[p] = randomValue(p)
    c.initialize(a)
    proc fullCost(): int =
      let f = newMultiMachineNoOverlapConstraint[int](
        starts, machines, fixed, durations = @[0, 0, 0, 3, 4, 2],
        numMachineValues = 4, maxTime = 40,
        fixedBlocks = @[newSeq[(int, int)](), newSeq[(int, int)](), @[(5, 4)], newSeq[(int, int)]()],
        ignoreMachine = 0, durPositions = durPos)
      f.initialize(a)
      f.cost
    check c.cost == fullCost()
    for step in 0..<2000:
      var p = rng.rand(0..14)
      if p == 10: p = 11   # position 10 belongs to no task
      let v = randomValue(p)
      let before = c.cost
      let predicted = c.moveDelta(p, a[p], v)
      a[p] = v
      c.updatePosition(p, v)
      check c.cost - before == predicted
      check c.cost == fullCost()
      if c.cost != fullCost(): break

  test "batch start evaluation uses the current duration":
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1], machinePositions = @[-1, -1], fixedMachines = @[1, 1],
      durations = @[0, 3], numMachineValues = 2, maxTime = 30,
      durPositions = @[2, -1])
    c.initialize(@[0, 10, 5])         # [0,5) and [10,13)
    check c.cost == 0
    c.updatePosition(2, 12)           # [0,12) now overlaps [10,13) by 2
    check c.cost == 2
    let dom = @[0, 1, 2, 9, 13, 20]
    let batch = c.batchMovePenalty(0, 0, dom)
    for i, v in dom:
      check batch[i] == c.moveDelta(0, 0, v)

suite "crusher_disjunctive_opt with variable durations":

  test "per-constraint translation constrains variable lengths":
    let src = """
var 0..8: s1 :: output_var;
var 0..8: s2 :: output_var;
var 2..5: d1 :: output_var;
var 2..5: d2 :: output_var;
constraint int_lin_le([-1],[d1],-4);
constraint int_lin_le([-1],[d2],-4);
constraint crusher_disjunctive_opt([s1,s2],[true,true],[d1,d2]);
solve satisfy;
"""
    for trial in 0..4:
      var tr = translate(parseFzn(src))
      tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
      check tr.sys.hasFeasibleSolution
      let asg = tr.sys.assignment
      let s1 = asg[tr.varPositions["s1"]]
      let s2 = asg[tr.varPositions["s2"]]
      let d1 = asg[tr.varPositions["d1"]]
      let d2 = asg[tr.varPositions["d2"]]
      check d1 >= 4 and d2 >= 4
      check not overlaps(s1, d1, s2, d2)

  proc familySrc(): string =
    ## Two tasks; machine family over a_i (duration D_i), worker family over
    ## w_i (load [s_i, s_i+1)) and u_i (unload [s_i+D_i-1, s_i+D_i)). The
    ## unload alias is tied to its start by int_lin_eq_reif, as MiniZinc
    ## emits for `StartLCU + DurLCU - DurUnload`. Everything is forced onto
    ## one machine and one worker.
    var decl = ""
    var body = ""
    for i in 1..2:
      decl &= "var 1..2: a" & $i & " :: output_var;\nvar 1..2: w" & $i & " :: output_var;\n"
      decl &= "var 1..2: u" & $i & " :: output_var;\nvar 0..20: s" & $i & " :: output_var;\n"
      decl &= "var 3..6: D" & $i & " :: output_var;\n"
    body &= "constraint int_lin_eq([1,-1],[a1,a2],0);\n"
    body &= "constraint int_lin_eq([1,-1],[w1,w2],0);\nconstraint int_lin_eq([1,-1],[w1,u1],0);\n"
    body &= "constraint int_lin_eq([1,-1],[w1,u2],0);\n"
    proc optElem(alloc: string, m: int, tag: string, startEq: string): (string, string) =
      ## Declares the deopt alias x and presence o for one element.
      let x = "x" & tag
      let o = "o" & tag
      let r = "r" & tag
      let e = "e" & tag
      let z = "z" & tag
      decl &= "var -1..30: " & x & ";\nvar bool: " & o & ";\n"
      decl &= "var bool: " & r & " :: is_defined_var;\nvar bool: " & e & " :: is_defined_var;\nvar bool: " & z & " :: is_defined_var;\n"
      body &= "constraint int_eq_reif(" & alloc & "," & $m & "," & r & ") :: defines_var(" & r & ");\n"
      body &= "constraint bool_clause([" & r & "],[" & o & "]);\nconstraint bool_clause([" & o & "],[" & r & "]);\n"
      body &= startEq.replace("$X", x).replace("$E", e)
      body &= "constraint bool_clause([" & e & "],[" & r & "]);\n"
      body &= "constraint int_eq_reif(" & x & ",0," & z & ") :: defines_var(" & z & ");\n"
      body &= "constraint bool_clause([" & o & "," & z & "],[]);\n"
      (x, o)
    for m in 1..2:
      var xs, os: seq[string]
      for i in 1..2:
        let (x, o) = optElem("a" & $i, m, "m" & $i & "_" & $m,
          "constraint int_eq_reif($X,s" & $i & ",$E) :: defines_var($E);\n")
        xs.add x; os.add o
      body &= "constraint crusher_disjunctive_opt([" & xs[0] & "," & xs[1] & "],[" & os[0] & "," &
              os[1] & "],[D1,D2]);\n"
    for w in 1..2:
      var xs, os: seq[string]
      for i in 1..2:
        let (x, o) = optElem("w" & $i, w, "l" & $i & "_" & $w,
          "constraint int_eq_reif($X,s" & $i & ",$E) :: defines_var($E);\n")
        xs.add x; os.add o
      for i in 1..2:
        let (x, o) = optElem("u" & $i, w, "u" & $i & "_" & $w,
          "constraint int_lin_eq_reif([1,-1,-1],[$X,D" & $i & ",s" & $i & "],-1,$E) :: defines_var($E);\n")
        xs.add x; os.add o
      body &= "constraint crusher_disjunctive_opt([" & xs.join(",") & "],[" & os.join(",") &
              "],[1,1,1,1]);\n"
    decl & body & "solve satisfy;\n"

  test "machine and worker families are grouped separately":
    let tr = translate(parseFzn(familySrc()))
    check tr.multiMachineNoOverlapInfos.len == 2
    var nMMNO = 0
    for c in tr.sys.baseArray.constraints:
      if c.stateType == MultiMachineNoOverlapType: inc nMMNO
    check nMMNO == 2

  test "grouped solutions respect machine and worker no-overlap":
    for trial in 0..4:
      var tr = translate(parseFzn(familySrc()))
      tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
      check tr.sys.hasFeasibleSolution
      let asg = tr.sys.assignment
      var s, d: seq[int]
      for i in 1..2:
        s.add asg[tr.varPositions["s" & $i]]
        d.add asg[tr.varPositions["D" & $i]]
      check not overlaps(s[0], d[0], s[1], d[1])
      # Worker intervals: loads and unloads of both tasks are pairwise disjoint
      var iv: seq[(int, int)]
      for i in 0..1:
        iv.add((s[i], 1))
        iv.add((s[i] + d[i] - 1, 1))
      for x in 0..<iv.len:
        for y in x+1..<iv.len:
          check not overlaps(iv[x][0], iv[x][1], iv[y][0], iv[y][1])

suite "CPM presolve with variable durations":

  test "a variable duration is never subtracted at its maximum":
    ## s1 + d <= s2 with d >= c + 8: d is the target of another edge, which
    ## used to make CPM take d for the start and s1 for the duration, and
    ## the backward pass then subtracted max(s1) and declared infeasibility.
    let src = """
var 0..20: s1 :: output_var;
var 0..20: s2 :: output_var;
var 0..30: d :: output_var;
var 1..5: c :: output_var;
constraint int_lin_le([-1,1],[d,c],-8);
constraint int_lin_le([1,1,-1],[s1,d,s2],0);
solve satisfy;
"""
    var tr = translate(parseFzn(src))
    # s1 can still be as late as 20 - min(d) = 11
    check 11 in tr.sys.baseArray.domain[tr.varPositions["s1"]]
    tr.sys.resolve(parallel = false, tabuThreshold = 2000, verbose = false)
    check tr.sys.hasFeasibleSolution
    let asg = tr.sys.assignment
    let s1 = asg[tr.varPositions["s1"]]
    let s2 = asg[tr.varPositions["s2"]]
    let d = asg[tr.varPositions["d"]]
    let cv = asg[tr.varPositions["c"]]
    check cv + 8 <= d
    check s1 + d <= s2
