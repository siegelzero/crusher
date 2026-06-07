## Regression: maximizing card(x intersect y), where the cardinality variable is
## the optimisation objective.
##
## MiniZinc compiles `maximize card(x intersect y)` to
##   set_intersect(x, y, c) :: defines_var(c);  set_card(c, n);  maximize n;
## The SetIntersectCard fusion detected this and (a) emitted only a penalty bound
## on |x∩y| — never computing n — and (b) dropped even that bound as "tautological"
## when n's upper bound exceeded the universe overlap. n was left disconnected, so
## the solver reported card 3 (impossible — the overlap of {1,2,3} and {2,3,4} is
## at most 2) for an assignment whose real intersection was empty, and MiniZinc
## rejected the non-improving / incorrect objective.
##
## The refcount guard couldn't catch this: the objective is referenced in the
## solve item, not in any constraint's args. The fix excludes the objective
## variable from the fusion, routing through the general set_intersect + set_card
## decomposition, which channels n = Σ c.bools correctly.

import unittest
import std/[sets, tables]
import crusher
import flatzinc/[parser, translator]

proc objectiveExpr(tr: FznTranslator): AlgebraicExpression[int] =
  if tr.objectivePos >= 0:
    return tr.getExpr(tr.objectivePos)
  elif tr.objectivePos == ObjPosDefinedExpr:
    return tr.objectiveDefExpr
  else:
    raise newException(ValueError, "no objective expression")

proc setMembers(tr: FznTranslator, asg: seq[int], setName: string): HashSet[int] =
  ## Concrete members of a decomposed set variable under `asg`.
  let info = tr.setVarBoolPositions[setName]
  for i, pos in info.positions:
    if asg[pos] == 1:
      result.incl(info.lo + i)

proc countSetIntersectCard(tr: FznTranslator): int =
  for c in tr.sys.baseArray.constraints:
    if c.stateType == SetIntersectCardType:
      inc result

suite "SetIntersectCard as objective":

  test "maximize card(x intersect y) reports the true intersection cardinality":
    let src = """
var set of 1..3: x;
var set of 2..4: y;
var set of 1..4: c :: var_is_introduced :: is_defined_var;
var 0..4: n :: var_is_introduced;
constraint set_card(c, n);
constraint set_intersect(x, y, c) :: defines_var(c);
solve maximize n;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # The fusion must NOT fire: the cardinality variable is the objective, so it
    # is channeled through the general set decomposition instead.
    check countSetIntersectCard(tr) == 0

    let objExpr = tr.objectiveExpr()
    maximize(tr.sys, objExpr, parallel = true, tabuThreshold = 5000,
             lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)

    let asg = tr.sys.assignment
    let trueCard = (setMembers(tr, asg, "x") * setMembers(tr, asg, "y")).len
    let reportedObj = objExpr.evaluate(asg)

    # The reported objective must equal the actual intersection cardinality
    # (the bug reported a value with no relation to x and y)...
    check reportedObj == trueCard
    # ...and reach the true maximum of 2 (x∩y ⊆ {2,3}).
    check reportedObj == 2

  test "non-objective cardinality bound still fuses into a SetIntersectCard constraint":
    # Same shape but n is a bounded throwaway (|x∩y| ≤ 1), not the objective. The
    # fusion's O(1) penalty constraint should still be emitted, and an assignment
    # with two shared elements must be penalised.
    let src = """
var set of 1..3: x;
var set of 2..4: y;
var set of 1..4: c :: var_is_introduced :: is_defined_var;
var 0..1: n :: var_is_introduced;
constraint set_card(c, n);
constraint set_intersect(x, y, c) :: defines_var(c);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check countSetIntersectCard(tr) == 1

    # Force x = y = {2,3}: |x∩y| = 2 > 1, so the fused constraint is violated.
    var asg = newSeq[int](tr.sys.baseArray.len)
    let xi = tr.setVarBoolPositions["x"]
    let yi = tr.setVarBoolPositions["y"]
    asg[xi.positions[2 - xi.lo]] = 1
    asg[xi.positions[3 - xi.lo]] = 1
    asg[yi.positions[2 - yi.lo]] = 1
    asg[yi.positions[3 - yi.lo]] = 1
    tr.sys.initialize(asg)
    var penalty = 0
    for c in tr.sys.baseArray.constraints:
      penalty += c.penalty()
    check penalty > 0
