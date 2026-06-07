## Regression tests for functional-dependency table channels whose dependent
## variable has a domain tightened BELOW the table's value range.
##
## Reproduces the `suite/wcsp.mzn` failure: in a Weighted CSP each `ocosts2[j]`
## is functionally determined by `(p[x], p[y])` through a full extensional table,
## but its domain is tightened (by the `objective <= top-1` bound) below the
## forbidden "top" cost. The translator used to filter table tuples by the
## DEPENDENT column's domain, dropping the high-cost rows and silently filling
## those keys with `tuples[0]`'s cost. The channel then reported a falsely-low
## cost for forbidden assignments, so the solver returned infeasible solutions
## with a bogus objective.
##
## The fix: build the functional channel from the full table (filtering only on
## KEY columns, never the dependent one) and reset the dependent variable's
## domain to the values the channel can actually produce.

import unittest
import std/[tables]

import crusher
import flatzinc/[parser, translator]

proc channelValueAt(tr: FznTranslator, channelPos: int,
                    keyAsg: Table[int, int]): int =
  ## Evaluate the element channel bound to `channelPos` for the given (sparse)
  ## key assignment, returning the dependent value the channel looks up.
  for b in tr.sys.baseArray.channelBindings:
    if b.channelPosition == channelPos:
      let idx = b.indexExpression.evaluate(keyAsg)
      doAssert idx >= 0 and idx < b.arrayElements.len,
        "channel index " & $idx & " out of range " & $b.arrayElements.len
      let elem = b.arrayElements[idx]
      doAssert elem.isConstant, "expected constant lookup element"
      return elem.constantValue
  raise newException(ValueError, "no element channel binding for position " & $channelPos)

suite "Table functional-dependency channel — dependent values outside a tightened domain":

  # A full 3x3 cost table over keys (x, y), each in 0..2. The cell (2,2) is the
  # forbidden "top" with cost 9, which lies outside c's declared domain 0..5.
  # Costs repeat (lots of 1s) so neither `c` alone nor (c,x)/(c,y) form a unique
  # key — exactly as in the WCSP, only the (x,y) pair is functional. Both x=2 and
  # y=2 keep support from in-domain cells ((2,0)->2 and (0,2)->2), so the (2,2)
  # combination stays reachable even though its own cost is out of c's domain —
  # mirroring how a shared `p[i]` value survives per-variable propagation.
  const grid = "[1,0,0, 1,0,1, 2,0,2,  1,1,0, 3,1,1, 1,1,2,  2,2,0, 1,2,1, 9,2,2]"

  test "binary table keeps the top cost for the forbidden key (unannotated)":
    let src = """
var 0..2: x :: output_var;
var 0..2: y :: output_var;
var 0..5: c :: output_var;
constraint fzn_table_int([c, x, y], """ & grid & """);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    let cPos = tr.varPositions["c"]
    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]

    # c is functionally determined by (x, y): it must become a derived channel,
    # while x and y stay searched.
    check tr.sys.baseArray.channelPositions.contains(cPos)
    check not tr.sys.baseArray.channelPositions.contains(xPos)
    check not tr.sys.baseArray.channelPositions.contains(yPos)

    # The channel's domain must include the top cost 9, outside the declared 0..5.
    check 9 in tr.sys.baseArray.domain[cPos]

    # Every key must look up its TRUE cost — especially the forbidden (2,2) -> 9,
    # not a gap default.
    check channelValueAt(tr, cPos, {xPos: 0, yPos: 0}.toTable) == 1
    check channelValueAt(tr, cPos, {xPos: 0, yPos: 2}.toTable) == 2
    check channelValueAt(tr, cPos, {xPos: 1, yPos: 1}.toTable) == 3
    check channelValueAt(tr, cPos, {xPos: 2, yPos: 0}.toTable) == 2
    check channelValueAt(tr, cPos, {xPos: 2, yPos: 2}.toTable) == 9

  test "binary table keeps the top cost with a defines_var annotation":
    # MiniZinc sometimes annotates the functional column; this drives the
    # annotation-guided composite-key path instead of the search over keys.
    let src = """
var 0..2: x :: output_var;
var 0..2: y :: output_var;
var 0..5: c :: output_var;
constraint fzn_table_int([c, x, y], """ & grid & """) :: defines_var(c);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    let cPos = tr.varPositions["c"]
    let xPos = tr.varPositions["x"]
    let yPos = tr.varPositions["y"]

    check tr.sys.baseArray.channelPositions.contains(cPos)
    check 9 in tr.sys.baseArray.domain[cPos]
    check channelValueAt(tr, cPos, {xPos: 2, yPos: 2}.toTable) == 9
    check channelValueAt(tr, cPos, {xPos: 0, yPos: 0}.toTable) == 1
