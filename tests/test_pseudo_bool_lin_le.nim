import unittest
import std/[sequtils, tables, packedsets]

import crusher
import constraints/[stateful, types, pseudoBoolLinLe]
import flatzinc/[parser, translator]

suite "PseudoBoolLinLe constraint":

  test "basic moveDelta correctness":
    # sum(2*x0 - 1*x1 + 3*x2) <= 3
    let c = newPseudoBoolLinLeConstraint[int](@[0, 1, 2], @[2, -1, 3], 3)
    var assignment = @[1, 0, 1]  # sum = 2*1 + -1*0 + 3*1 = 5, cost = max(0, 5-3) = 2
    c.initialize(assignment)
    check c.cost == 2
    check c.currentSum == 5

    # Flip x0 from 1 to 0: sum goes from 5 to 3, cost 2 -> 0, delta = -2
    check c.moveDelta(0, 1, 0) == -2

    # Flip x1 from 0 to 1: sum goes from 5 to 4, cost 2 -> 1, delta = -1
    check c.moveDelta(1, 0, 1) == -1

    # Flip x2 from 1 to 0: sum goes from 5 to 2, cost 2 -> 0, delta = -2
    check c.moveDelta(2, 1, 0) == -2

  test "updatePosition maintains state":
    let c = newPseudoBoolLinLeConstraint[int](@[0, 1], @[1, -1], 0)
    var assignment = @[0, 0]  # sum = 0, cost = 0
    c.initialize(assignment)
    check c.cost == 0
    check c.currentSum == 0

    # Set x0 = 1: sum = 1, cost = max(0, 1-0) = 1
    c.updatePosition(0, 1)
    check c.cost == 1
    check c.currentSum == 1

    # Set x1 = 1: sum = 1 + (-1) = 0, cost = 0
    c.updatePosition(1, 1)
    check c.cost == 0
    check c.currentSum == 0

  test "getAffectedPositions slack-based optimization":
    # sum(1*x0 + 1*x1 + 1*x2) <= 2, maxAbsCoeff = 1
    let c = newPseudoBoolLinLeConstraint[int](@[0, 1, 2], @[1, 1, 1], 2)
    var assignment = @[0, 0, 0]  # sum = 0, slack = 2 >= maxAbsCoeff(1)
    c.initialize(assignment)
    check c.cost == 0

    # Move within high slack: sum 0 -> 1, slack was 2, now 1 — both >= maxAbsCoeff(1)
    c.updatePosition(0, 1)
    check c.cost == 0
    check c.getAffectedPositions().len == 0  # slack still >= maxAbsCoeff

    # Move to tight: sum 1 -> 2, slack was 1, now 0 — 0 < maxAbsCoeff(1)
    c.updatePosition(1, 1)
    check c.cost == 0
    check c.getAffectedPositions().len == 3  # boundary region, must broadcast

  test "batchMovePenalty matches individual moveDelta":
    let c = newPseudoBoolLinLeConstraint[int](@[0, 1, 2], @[2, -3, 1], 1)
    var assignment = @[1, 0, 0]  # sum = 2, cost = 1
    c.initialize(assignment)
    check c.cost == 1

    let domain = @[0, 1]
    let batch = c.batchMovePenalty(0, 1, domain)
    check batch[0] == c.moveDelta(0, 1, 0)  # flip to 0
    check batch[1] == 0  # keep at 1

    let batch1 = c.batchMovePenalty(1, 0, domain)
    check batch1[0] == 0  # keep at 0
    check batch1[1] == c.moveDelta(1, 0, 1)  # flip to 1

  test "deepCopy produces independent state":
    let c = newPseudoBoolLinLeConstraint[int](@[0, 1], @[1, 1], 1)
    var assignment = @[1, 1]  # sum = 2, cost = 1
    c.initialize(assignment)
    check c.cost == 1

    let copy = c.deepCopy()
    copy.initialize(assignment)
    check copy.cost == 1

    # Modify original, copy should be unaffected after re-initialization
    c.updatePosition(0, 0)
    check c.cost == 0
    check copy.cost == 1

suite "PseudoBoolLinLe translator integration":

  test "mixed-coefficient binary int_lin_le emits PseudoBoolLinLeType":
    # sum(1*x + -1*y + 1*z) <= 1 on binary vars
    let src = """
var 0..1: x;
var 0..1: y;
var 0..1: z;
constraint int_lin_le([1,-1,1],[x,y,z],1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    var nPB = 0
    for c in tr.sys.baseArray.constraints:
      if c.stateType == PseudoBoolLinLeType:
        inc nPB
    check nPB == 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let vx = tr.sys.assignment[tr.varPositions["x"]]
    let vy = tr.sys.assignment[tr.varPositions["y"]]
    let vz = tr.sys.assignment[tr.varPositions["z"]]
    check vx - vy + vz <= 1

  test "pure +1 coefficients still emit AtMostType (not PseudoBoolLinLe)":
    let src = """
var 0..1: a;
var 0..1: b;
var 0..1: c;
constraint int_lin_le([1,1,1],[a,b,c],1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    var nAtMost = 0
    var nPB = 0
    for c in tr.sys.baseArray.constraints:
      if c.stateType == AtMostType: inc nAtMost
      if c.stateType == PseudoBoolLinLeType: inc nPB
    check nAtMost >= 1
    check nPB == 0

  test "fixed binary vars excluded from PseudoBoolLinLe (adjusted rhs)":
    # x is fixed to 1 by domain, so int_lin_le(2*x + 1*y - 1*z, 2)
    # becomes PseudoBoolLinLe(y, z; coeffs=[1,-1]; rhs=2-2=0)
    let src = """
var 1..1: x;
var 0..1: y;
var 0..1: z;
constraint int_lin_le([2,1,-1],[x,y,z],2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    var nPB = 0
    for c in tr.sys.baseArray.constraints:
      if c.stateType == PseudoBoolLinLeType:
        inc nPB
        # rhs should be adjusted: 2 - 2*1 = 0
        check c.pseudoBoolLinLeState.rhs == 0
    check nPB == 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    let vy = tr.sys.assignment[tr.varPositions["y"]]
    let vz = tr.sys.assignment[tr.varPositions["z"]]
    check vy - vz <= 0  # y <= z

  test "non-binary vars fall through to RelationalType":
    let src = """
var 0..5: x;
var 0..1: y;
constraint int_lin_le([1,-1],[x,y],2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    var nPB = 0
    var nRel = 0
    for c in tr.sys.baseArray.constraints:
      if c.stateType == PseudoBoolLinLeType: inc nPB
      if c.stateType == RelationalType: inc nRel
    check nPB == 0
    check nRel >= 1

suite "Early tautological detection for int_lin_le_reif":

  test "always-satisfied reif fixes indicator to 1":
    # int_lin_le_reif([1],[x],10,b) where x in {0,1}
    # exprMax = 1 <= 10, so b is always 1
    let src = """
var 0..1: x;
var 0..1: b :: is_defined_var;
constraint int_lin_le_reif([1],[x],10,b) :: defines_var(b);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let bPos = tr.varPositions["b"]
    let bDom = tr.sys.baseArray.domain[bPos]
    check bDom.len == 1
    check bDom[0] == 1

  test "never-satisfied reif fixes indicator to 0":
    # int_lin_le_reif([1,1],[x,y],-1,b) where x,y in {0,1}
    # exprMin = 0 > -1, so b is always 0
    let src = """
var 0..1: x;
var 0..1: y;
var 0..1: b :: is_defined_var;
constraint int_lin_le_reif([1,1],[x,y],-1,b) :: defines_var(b);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let bPos = tr.varPositions["b"]
    let bDom = tr.sys.baseArray.domain[bPos]
    check bDom.len == 1
    check bDom[0] == 0

  test "non-tautological reif still creates channel binding":
    # int_lin_le_reif([1,1],[x,y],1,b) where x,y in {0,1}
    # exprMin=0, exprMax=2, rhs=1 — not always-satisfied or always-violated
    let src = """
var 0..1: x;
var 0..1: y;
var 0..1: b :: is_defined_var;
constraint int_lin_le_reif([1,1],[x,y],1,b) :: defines_var(b);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let bPos = tr.varPositions["b"]
    let bDom = tr.sys.baseArray.domain[bPos]
    # Not fixed — should have domain {0,1}
    check bDom.len == 2

suite "Binary linear domain reduction":

  test "variable fixed when coefficient exceeds slack":
    # int_lin_le([10, 1, 1], [x, y, z], 5) with x,y,z in {0,1}
    # sumNeg = 0 (no negative coefficients)
    # For x: minSum when x=1 = 10 + 0 = 10 > 5, so x must be 0
    let src = """
var 0..1: x :: output_var;
var 0..1: y :: output_var;
var 0..1: z :: output_var;
constraint int_lin_le([10,1,1],[x,y,z],5);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let xPos = tr.varPositions["x"]
    let xDom = tr.sys.baseArray.domain[xPos]
    # x should be fixed to 0 by domain reduction
    check xDom.len == 1
    check xDom[0] == 0

  test "BNN-like problem end-to-end":
    # Small BNN-like problem: 4 binary inputs, 2 reified neurons, minimize actions
    # neuron1: b1 <-> (x1 + x2 - x3 - x4 <= 0)  →  int_lin_le_reif
    # neuron2: b2 <-> (-x1 + x2 + x3 - x4 <= 0)  →  int_lin_le_reif
    # constraint: b1 + b2 >= 1  →  int_lin_le([-1,-1],[b1,b2],-1)
    # objective: minimize x1 + x2 + x3 + x4
    let src = """
var 0..1: x1;
var 0..1: x2;
var 0..1: x3;
var 0..1: x4;
var 0..1: b1 :: is_defined_var;
var 0..1: b2 :: is_defined_var;
var 0..4: obj :: output_var;
array [1..7] of var int: out :: output_array([1..7]) = [x1,x2,x3,x4,b1,b2,obj];
constraint int_lin_le_reif([1,1,-1,-1],[x1,x2,x3,x4],0,b1) :: defines_var(b1);
constraint int_lin_le_reif([-1,1,1,-1],[x1,x2,x3,x4],0,b2) :: defines_var(b2);
constraint int_lin_le([-1,-1],[b1,b2],-1);
constraint int_lin_eq([1,1,1,1,-1],[x1,x2,x3,x4,obj],0) :: defines_var(obj);
solve :: int_search([x1,x2,x3,x4],input_order,indomain_min,complete) minimize obj;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let x1 = tr.sys.assignment[tr.varPositions["x1"]]
    let x2 = tr.sys.assignment[tr.varPositions["x2"]]
    let x3 = tr.sys.assignment[tr.varPositions["x3"]]
    let x4 = tr.sys.assignment[tr.varPositions["x4"]]
    let b1 = tr.sys.assignment[tr.varPositions["b1"]]
    let b2 = tr.sys.assignment[tr.varPositions["b2"]]

    # Check reification correctness
    let neuron1 = x1 + x2 - x3 - x4
    check (b1 == 1) == (neuron1 <= 0)
    let neuron2 = -x1 + x2 + x3 - x4
    check (b2 == 1) == (neuron2 <= 0)

    # Check constraint: at least one neuron fires
    check b1 + b2 >= 1
