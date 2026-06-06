## Regression tests for set_intersect / set_union with a CONSTANT result set.
##
## all_disjoint(x) decomposes (via the MiniZinc library) into a series of
##   constraint set_intersect(x[i], x[j], 1..0);
## i.e. "the intersection of these two set variables must equal the empty set".
## The FlatZinc translator previously `discard`ed any set_intersect/set_union
## whose result argument was a constant set, so disjointness was silently
## dropped and the solver happily returned overlapping sets (e.g.
##   x = [2..3, {}, 2..2]  -- 2 appears in both x[1] and x[3]).
##
## These tests pin the fix: a constant-result intersection/union is enforced
## element-wise. We check the total system penalty directly on crafted
## assignments so the tests are fully deterministic.

import unittest
import std/[sequtils, tables]
import crusher
import flatzinc/[parser, translator]

proc totalPenalty(tr: var FznTranslator, assignment: seq[int]): int =
  ## Initialize every constraint with `assignment` and sum their penalties.
  tr.sys.initialize(assignment)
  for c in tr.sys.baseArray.constraints:
    result += c.penalty()

proc setElem(asg: var seq[int], info: SetVarInfo, elem, val: int) =
  ## Set the membership bool for `elem` of a set variable to `val` (0/1).
  asg[info.positions[elem - info.lo]] = val

suite "FlatZinc set_intersect / set_union with constant result":

  test "set_intersect(A, B, 1..0) enforces disjointness (all_disjoint core)":
    let src = """
var set of 1..3: A;
var set of 1..3: B;
array [1..2] of var set of int: x:: output_array([1..2]) = [A,B];
constraint set_intersect(A,B,1..0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    let aInfo = tr.setVarBoolPositions["A"]
    let bInfo = tr.setVarBoolPositions["B"]

    template freshAssignment: seq[int] = newSeq[int](tr.sys.baseArray.len)

    # Overlap at element 1 → must be penalized.
    var overlap = freshAssignment
    setElem(overlap, aInfo, 1, 1)
    setElem(overlap, bInfo, 1, 1)
    check totalPenalty(tr, overlap) > 0

    # Overlap at element 2 with larger sets A={1,2}, B={2,3} → penalized.
    var overlap2 = freshAssignment
    setElem(overlap2, aInfo, 1, 1); setElem(overlap2, aInfo, 2, 1)
    setElem(overlap2, bInfo, 2, 1); setElem(overlap2, bInfo, 3, 1)
    check totalPenalty(tr, overlap2) > 0

    # Disjoint A={1}, B={2} → no penalty.
    var disjoint = freshAssignment
    setElem(disjoint, aInfo, 1, 1)
    setElem(disjoint, bInfo, 2, 1)
    check totalPenalty(tr, disjoint) == 0

    # Both empty → trivially disjoint, no penalty.
    var empty = freshAssignment
    check totalPenalty(tr, empty) == 0

  test "set_intersect(A, B, 1..0) is solvable and yields disjoint sets":
    # Force both sets non-empty via cardinality vars with domain >= 1, then
    # confirm the solver respects disjointness.
    let src = """
var set of 1..2: A;
var set of 1..2: B;
var 1..2: ca;
var 1..2: cb;
array [1..2] of var set of int: x:: output_array([1..2]) = [A,B];
constraint set_card(A, ca);
constraint set_card(B, cb);
constraint set_intersect(A,B,1..0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let aInfo = tr.setVarBoolPositions["A"]
    let bInfo = tr.setVarBoolPositions["B"]
    let asg = tr.sys.assignment

    var aSet, bSet: seq[int]
    for e in aInfo.lo..aInfo.hi:
      if asg[aInfo.positions[e - aInfo.lo]] == 1: aSet.add(e)
      if asg[bInfo.positions[e - bInfo.lo]] == 1: bSet.add(e)

    check aSet.len >= 1            # non-empty (card >= 1)
    check bSet.len >= 1
    # Disjoint: no shared element.
    for e in aSet:
      check e notin bSet

  test "set_union(A, B, {1,2,3}) enforces full coverage":
    let src = """
var set of 1..3: A;
var set of 1..3: B;
array [1..2] of var set of int: x:: output_array([1..2]) = [A,B];
constraint set_union(A,B,1..3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    let aInfo = tr.setVarBoolPositions["A"]
    let bInfo = tr.setVarBoolPositions["B"]

    template freshAssignment: seq[int] = newSeq[int](tr.sys.baseArray.len)

    # Union {1} ∪ {2} = {1,2} ≠ {1,2,3} → element 3 missing → penalized.
    var partial = freshAssignment
    setElem(partial, aInfo, 1, 1)
    setElem(partial, bInfo, 2, 1)
    check totalPenalty(tr, partial) > 0

    # Union {1,2} ∪ {3} = {1,2,3} → full coverage, no penalty.
    var full = freshAssignment
    setElem(full, aInfo, 1, 1); setElem(full, aInfo, 2, 1)
    setElem(full, bInfo, 3, 1)
    check totalPenalty(tr, full) == 0
