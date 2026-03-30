## Tests for reservoir constraint detection, domain reduction, and solving.

import std/[unittest, tables, packedsets, sequtils, algorithm]
import crusher
import flatzinc/[parser, translator]
import constraints/[stateful, types, reservoir]

suite "Reservoir Constraint":

  test "reservoir pattern detection: basic upper+lower pair":
    # Reservoir pattern: 3 tasks with consumption [2, -1, 1], maxDiff=3
    # act_leq_act[j,i] = (start[j] <= start[i]) encoded as:
    #   int_lin_le_reif([1,-1], [start_j, start_i], 0, b_ji) :: defines_var(b_ji)
    #   bool2int(b_ji, z_ji) :: defines_var(z_ji)
    # Upper bound: int_lin_le([2,-1,1], [z_0_i, z_1_i, z_2_i], 3)
    # Lower bound: int_lin_le([-2,1,-1], [z_0_i, z_1_i, z_2_i], 3)
    # For event point i=1 (self-consumption=-1 folded into RHS):
    #   upper rhs = 3 - (-1) = 4, lower rhs = 3 + (-1) = 2
    #   upper coeffs: [2, 1] (tasks 0 and 2 relative to event point 1)
    #   lower coeffs: [-2, -1]
    let src = """
var 0..20: s0;
var 0..20: s1;
var 0..20: s2;
array [1..2] of int: c12 = [1, -1];
var bool: b01 :: is_defined_var;
var bool: b21 :: is_defined_var;
var 0..1: z01 :: is_defined_var;
var 0..1: z21 :: is_defined_var;
constraint int_lin_le_reif(c12, [s0, s1], 0, b01) :: defines_var(b01);
constraint int_lin_le_reif(c12, [s2, s1], 0, b21) :: defines_var(b21);
constraint bool2int(b01, z01) :: defines_var(z01);
constraint bool2int(b21, z21) :: defines_var(z21);
constraint int_lin_le([2, 1], [z01, z21], 4);
constraint int_lin_le([-2, -1], [z01, z21], 2);
constraint bool_clause([b01, b21], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should detect 1 reservoir constraint
    check tr.reservoirPatternInfos.len == 1
    let info = tr.reservoirPatternInfos[0]
    check info.taskVarNames.len == 3  # s0, s1, s2
    check info.maxDiff == 3

    # Reservoir constraint should be in the system
    var hasReservoir = false
    for c in tr.sys.baseArray.constraints:
      if c.stateType == ReservoirType:
        hasReservoir = true
        break
    check hasReservoir

  test "reservoir constraint penalty computation":
    # Direct unit test of the constraint penalty
    # Tasks at positions 0, 1, 2 with consumption [3, -2, 1], maxDiff=2
    var rc = newReservoirConstraint[int](@[0, 1, 2], @[3, -2, 1], 2)
    var assignment = @[5, 3, 10]  # start times: task1=5, task0=3, task2=10
    rc.initialize(assignment)

    # Sorted by start: task1(3, consumption=-2), task0(5, consumption=3), task2(10, consumption=1)
    # Prefix sums: -2, 1, 2
    # Violations: max(0, |-2|-2)=0, max(0,|1|-2)=0, max(0,|2|-2)=0
    check rc.cost == 0

    # Move task0 to start=1 (before task1):
    # Sorted: task0(1, 3), task1(3, -2), task2(10, 1)
    # Prefix sums: 3, 1, 2
    # Violations: max(0, 3-2)=1, 0, 0
    let delta = rc.moveDelta(0, 5, 1)
    check delta == 1

  test "reservoir constraint: tasks reorder correctly":
    # 4 tasks, consumption = [1, -1, 1, -1], maxDiff = 1
    var rc = newReservoirConstraint[int](@[0, 1, 2, 3], @[1, -1, 1, -1], 1)
    # Start times: interleaved +1 -1 → balance stays in [-1, 1]
    # task0=0, task1=1, task2=2, task3=3
    var assignment = @[0, 1, 2, 3]
    rc.initialize(assignment)
    # Sorted: task0(0,+1), task1(1,-1), task2(2,+1), task3(3,-1)
    # Prefix: 1, 0, 1, 0 → all within [-1,1]
    check rc.cost == 0

    # Move task3 to position 0 → sorted: task3(0,-1), task0(0,+1), task1(1,-1), task2(2,+1)
    # Prefix: -1, 0, -1, 0 → all within [-1,1]
    check rc.moveDelta(3, 3, 0) == 0

    # Move task1 to 5 → sorted: task0(0,+1), task2(2,+1), task1(5,-1), task3(3,-1)
    # Wait, that's task3(3,-1) before task1(5,-1):
    # Prefix: 1, 2, 1, 0 → violation at prefix=2: 2-1=1
    check rc.moveDelta(1, 1, 5) == 1

  test "reservoir constraint updatePosition":
    var rc = newReservoirConstraint[int](@[0, 1, 2], @[2, -1, -1], 1)
    var assignment = @[0, 1, 2]
    rc.initialize(assignment)
    # Sorted: task0(0, +2), task1(1, -1), task2(2, -1)
    # Prefix: 2, 1, 0 → violations: (2-1)=1, (1-1)=0, 0 → cost=1
    check rc.cost == 1

    # Move task0 to the end
    rc.updatePosition(0, 5)
    # Sorted: task1(1, -1), task2(2, -1), task0(5, +2)
    # Prefix: -1, -2, 0 → violations: 0, (2-1)=1, 0 → cost=1
    check rc.cost == 1

  test "reservoir constraint deepCopy":
    var rc = newReservoirConstraint[int](@[0, 1], @[1, -1], 1)
    var assignment = @[0, 5]
    rc.initialize(assignment)
    check rc.cost == 0

    var rc2 = rc.deepCopy()
    rc2.initialize(assignment)
    check rc2.cost == 0

    # Modify original, copy should be independent
    rc.updatePosition(0, 10)
    check rc2.cost == 0  # unchanged

  test "reservoir constraint batchMovePenalty":
    var rc = newReservoirConstraint[int](@[0, 1, 2], @[2, -1, -1], 2)
    var assignment = @[0, 1, 2]
    rc.initialize(assignment)
    # Sorted: task0(0, +2), task1(1, -1), task2(2, -1)
    # Prefix: 2, 1, 0 → all within [-2, 2] → cost=0
    check rc.cost == 0

    let domain = @[0, 1, 2, 3, 4, 5]
    let deltas = rc.batchMovePenalty(0, 0, domain)

    # Verify batch matches individual moveDelta
    for i, v in domain:
      let expected = rc.moveDelta(0, 0, v)
      check deltas[i] == expected

  test "reservoir solving: feasible ordering exists":
    # 3 tasks with consumption [5, -3, -2], maxDiff = 5
    # Valid ordering: task0 first → prefix 5 (ok), then task1 → 2, then task2 → 0
    # Invalid ordering: task1 first → -3, task2 → -5, task0 → 0 (prefix -5 violates if maxDiff < 5)
    let src = """
var 0..10: s0;
var 0..10: s1;
var 0..10: s2;
array [1..2] of int: c12 = [1, -1];
var bool: b00 :: is_defined_var;
var bool: b10 :: is_defined_var;
var bool: b20 :: is_defined_var;
var 0..1: z00 :: is_defined_var;
var 0..1: z10 :: is_defined_var;
var 0..1: z20 :: is_defined_var;
var bool: b01 :: is_defined_var;
var bool: b11 :: is_defined_var;
var bool: b21 :: is_defined_var;
var 0..1: z01 :: is_defined_var;
var 0..1: z11 :: is_defined_var;
var 0..1: z21 :: is_defined_var;
var bool: b02 :: is_defined_var;
var bool: b12 :: is_defined_var;
var bool: b22 :: is_defined_var;
var 0..1: z02 :: is_defined_var;
var 0..1: z12 :: is_defined_var;
var 0..1: z22 :: is_defined_var;
constraint int_lin_le_reif(c12, [s0, s0], 0, b00) :: defines_var(b00);
constraint int_lin_le_reif(c12, [s1, s0], 0, b10) :: defines_var(b10);
constraint int_lin_le_reif(c12, [s2, s0], 0, b20) :: defines_var(b20);
constraint int_lin_le_reif(c12, [s0, s1], 0, b01) :: defines_var(b01);
constraint int_lin_le_reif(c12, [s1, s1], 0, b11) :: defines_var(b11);
constraint int_lin_le_reif(c12, [s2, s1], 0, b21) :: defines_var(b21);
constraint int_lin_le_reif(c12, [s0, s2], 0, b02) :: defines_var(b02);
constraint int_lin_le_reif(c12, [s1, s2], 0, b12) :: defines_var(b12);
constraint int_lin_le_reif(c12, [s2, s2], 0, b22) :: defines_var(b22);
constraint bool2int(b00, z00) :: defines_var(z00);
constraint bool2int(b10, z10) :: defines_var(z10);
constraint bool2int(b20, z20) :: defines_var(z20);
constraint bool2int(b01, z01) :: defines_var(z01);
constraint bool2int(b11, z11) :: defines_var(z11);
constraint bool2int(b21, z21) :: defines_var(z21);
constraint bool2int(b02, z02) :: defines_var(z02);
constraint bool2int(b12, z12) :: defines_var(z12);
constraint bool2int(b22, z22) :: defines_var(z22);
constraint int_lin_le([5, -3, -2], [z00, z10, z20], 5);
constraint int_lin_le([-5, 3, 2], [z00, z10, z20], 5);
constraint int_lin_le([5, -3, -2], [z01, z11, z21], 8);
constraint int_lin_le([-5, 3, 2], [z01, z11, z21], 2);
constraint int_lin_le([5, -3, -2], [z02, z12, z22], 7);
constraint int_lin_le([-5, 3, 2], [z02, z12, z22], 3);
constraint bool_clause([b00, b01], []);
constraint bool_clause([b00, b02], []);
constraint bool_clause([b01, b02], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should detect reservoir
    check tr.reservoirPatternInfos.len >= 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    # Verify the ordering satisfies the reservoir constraint
    let v0 = tr.sys.assignment[tr.varPositions["s0"]]
    let v1 = tr.sys.assignment[tr.varPositions["s1"]]
    let v2 = tr.sys.assignment[tr.varPositions["s2"]]

    # Check reservoir constraint manually: sort by start, check prefix sums
    var tasks = @[(start: v0, cons: 5), (start: v1, cons: -3), (start: v2, cons: -2)]
    tasks.sort(proc(a, b: tuple[start: int, cons: int]): int = cmp(a.start, b.start))
    var prefix = 0
    for t in tasks:
      prefix += t.cons
      check abs(prefix) <= 5

suite "Conditional Separation Domain Reduction":

  test "conditional separation pattern detection":
    # Pattern: assign → (start ≤ 5 ∨ start ≥ 10)
    #   int_le_reif(start, 5, sep_before) :: defines_var(sep_before)
    #   int_le_reif(10, start, sep_after) :: defines_var(sep_after)
    #   bool_clause([sep_before, sep_after], [assign])
    let src = """
var 0..20: start;
var bool: assign;
var bool: sep_before :: is_defined_var;
var bool: sep_after :: is_defined_var;
constraint int_le_reif(start, 5, sep_before) :: defines_var(sep_before);
constraint int_le_reif(10, start, sep_after) :: defines_var(sep_after);
constraint bool_clause([sep_before, sep_after], [assign]);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Should detect the conditional separation pattern
    check tr.conditionalSeparationInfos.len == 1
    check tr.conditionalSeparationInfos[0].lo == 5
    check tr.conditionalSeparationInfos[0].hi == 10
    check tr.conditionalSeparationInfos[0].varName == "start"
    check tr.conditionalSeparationInfos[0].guardName == "assign"

  test "conditional separation domain reduction with forced guard":
    # Same pattern but guard is forced to 1 → domain should exclude (5, 10)
    let src = """
var 0..20: start :: output_var;
var bool: assign;
var bool: sep_before :: is_defined_var;
var bool: sep_after :: is_defined_var;
constraint int_le_reif(start, 5, sep_before) :: defines_var(sep_before);
constraint int_le_reif(10, start, sep_after) :: defines_var(sep_after);
constraint bool_clause([sep_before, sep_after], [assign]);
constraint bool_eq(assign, true);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.conditionalSeparationInfos.len == 1

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let startVal = tr.sys.assignment[tr.varPositions["start"]]
    # start must be ≤ 5 or ≥ 10
    check (startVal <= 5 or startVal >= 10)

  test "conditional separation: multiple windows":
    # Two unavailability windows on the same variable
    let src = """
var 0..30: start :: output_var;
var bool: g1;
var bool: g2;
var bool: sb1 :: is_defined_var;
var bool: sa1 :: is_defined_var;
var bool: sb2 :: is_defined_var;
var bool: sa2 :: is_defined_var;
constraint int_le_reif(start, 5, sb1) :: defines_var(sb1);
constraint int_le_reif(10, start, sa1) :: defines_var(sa1);
constraint bool_clause([sb1, sa1], [g1]);
constraint int_le_reif(start, 15, sb2) :: defines_var(sb2);
constraint int_le_reif(20, start, sa2) :: defines_var(sa2);
constraint bool_clause([sb2, sa2], [g2]);
constraint bool_eq(g1, true);
constraint bool_eq(g2, true);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.conditionalSeparationInfos.len == 2

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let startVal = tr.sys.assignment[tr.varPositions["start"]]
    # Must satisfy both windows: start ≤ 5 or start ≥ 10, AND start ≤ 15 or start ≥ 20
    check (startVal <= 5 or startVal >= 10)
    check (startVal <= 15 or startVal >= 20)

suite "Presolve Cardinality Forcing":

  test "all-ones cardinality: fixes variables when nUnfixed == rhs":
    # int_lin_eq([1,1,1], [x1, x2, x3], 3) with x_i in {0,1}
    # and x1 fixed to 0 by another constraint → rhs becomes 3-0=3, nUnfixed=2?
    # Actually: no fixation, all 3 unfixed, rhs=3 → all must be 1
    let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_lin_eq([1,1,1],[x1,x2,x3],3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    check tr.sys.assignment[tr.varPositions["x1"]] == 1
    check tr.sys.assignment[tr.varPositions["x2"]] == 1
    check tr.sys.assignment[tr.varPositions["x3"]] == 1

  test "all-ones cardinality: partial fixing propagates":
    # x1 fixed to 1, x2+x3+x4 must sum to 2, each in {0,1}
    # With 3 unfixed and rhs=2, not all forced.
    # But x1 fixed to 0 → x2+x3 must sum to 2 → both forced to 1
    let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_eq(x1, 0);
constraint int_lin_eq([1,1,1],[x1,x2,x3],2);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    check tr.sys.assignment[tr.varPositions["x1"]] == 0
    check tr.sys.assignment[tr.varPositions["x2"]] == 1
    check tr.sys.assignment[tr.varPositions["x3"]] == 1

  test "all-ones cardinality with parameter coefficient array":
    # Same as above but coefficients come from a parameter array
    let src = """
array [1..3] of int: ones = [1, 1, 1];
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_lin_eq(ones,[x1,x2,x3],3);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    check tr.sys.assignment[tr.varPositions["x1"]] == 1
    check tr.sys.assignment[tr.varPositions["x2"]] == 1
    check tr.sys.assignment[tr.varPositions["x3"]] == 1
