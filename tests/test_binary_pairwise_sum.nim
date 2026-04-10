import std/[tables, unittest]
import crusher
import expressions/binaryPairwiseSum
import flatzinc/[parser, translator]

suite "BinaryPairwiseSumExpression Tests":

    test "Basic evaluate — quadratic only":
        # 3 pairs: (0,1,10), (0,2,20), (1,2,30), constant=5
        let pairs = @[
            (posA: 0, posB: 1, coeff: 10),
            (posA: 0, posB: 2, coeff: 20),
            (posA: 1, posB: 2, coeff: 30),
        ]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=5)

        # All 1: 5 + 10*1*1 + 20*1*1 + 30*1*1 = 65
        check expr.evaluate(@[1, 1, 1]) == 65

        # All 0: 5 + 0 = 5
        check expr.evaluate(@[0, 0, 0]) == 5

        # Only pos 0 = 1: 5 + 0 + 0 + 0 = 5 (no partner is 1)
        check expr.evaluate(@[1, 0, 0]) == 5

        # pos 0,1 = 1: 5 + 10*1*1 = 15
        check expr.evaluate(@[1, 1, 0]) == 15

    test "Evaluate — mixed quadratic and linear":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let linear = @[(pos: 2, coeff: 5)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, linear, constant=3)

        # pos0=1,pos1=1,pos2=1: 3 + 10*1*1 + 5*1 = 18
        check expr.evaluate(@[1, 1, 1]) == 18

        # pos0=0,pos1=0,pos2=1: 3 + 0 + 5*1 = 8
        check expr.evaluate(@[0, 0, 1]) == 8

        # pos0=1,pos1=0,pos2=0: 3 + 0 + 0 = 3
        check expr.evaluate(@[1, 0, 0]) == 3

    test "Linear terms with non-binary values":
        let linear = @[(pos: 0, coeff: 3), (pos: 1, coeff: -2)]
        let expr = newBinaryPairwiseSumExpression[int](@[], linear, constant=10)

        # 10 + 3*5 + (-2)*3 = 10 + 15 - 6 = 19
        check expr.evaluate(@[5, 3]) == 19

    test "Initialize and getValue":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let linear = @[(pos: 2, coeff: 5)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, linear, constant=0)

        expr.initialize(@[1, 1, 1])
        check expr.value == 15  # 10 + 5

        expr.initialize(@[0, 1, 0])
        check expr.value == 0  # 0 + 0

    test "updatePosition — quadratic term activated":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=0)

        expr.initialize(@[0, 1])
        check expr.value == 0  # 0*1 = 0

        # Flip pos 0: 0→1
        expr.updatePosition(0, 1)
        check expr.value == 10  # 1*1 = 1 → coeff 10

    test "updatePosition — quadratic term deactivated":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=0)

        expr.initialize(@[1, 1])
        check expr.value == 10

        # Flip pos 1: 1→0
        expr.updatePosition(1, 0)
        check expr.value == 0

    test "updatePosition — linear term":
        let linear = @[(pos: 0, coeff: 7)]
        let expr = newBinaryPairwiseSumExpression[int](@[], linear, constant=0)

        expr.initialize(@[0])
        check expr.value == 0

        expr.updatePosition(0, 1)
        check expr.value == 7

        expr.updatePosition(0, 3)
        check expr.value == 21

    test "moveDelta matches full recomputation":
        let pairs = @[
            (posA: 0, posB: 1, coeff: 10),
            (posA: 0, posB: 2, coeff: 20),
            (posA: 1, posB: 2, coeff: 30),
        ]
        let linear = @[(pos: 0, coeff: 5)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, linear, constant=3)

        expr.initialize(@[1, 0, 1])
        # Value: 3 + 0 + 20*1 + 0 + 5*1 = 28
        check expr.value == 28

        # moveDelta: flip pos 1: 0→1
        let delta1 = expr.moveDelta(1, 0, 1)
        # After: 3 + 10 + 20 + 30 + 5 = 68, delta = 68-28 = 40
        check delta1 == 40

        # moveDelta: flip pos 0: 1→0
        let delta2 = expr.moveDelta(0, 1, 0)
        # After: 3 + 0 + 0 + 0 + 0 = 3, delta = 3-28 = -25
        check delta2 == -25

    test "moveDelta with non-binary values":
        let pairs = @[(posA: 0, posB: 1, coeff: 3)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=0)

        expr.initialize(@[2, 5])
        check expr.value == 30  # 3*2*5

        # Change pos 0: 2→4, delta = 3*5*(4-2) = 30
        let delta = expr.moveDelta(0, 2, 4)
        check delta == 30

    test "moveDelta on position not in any term":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=0)

        expr.initialize(@[1, 1, 5])
        check expr.moveDelta(2, 5, 9) == 0

    test "Self-pairs folded into linear":
        # posA==posB means coeff * x^2; for binary x, x^2=x → becomes linear
        let pairs = @[
            (posA: 0, posB: 0, coeff: 100),  # self-pair
            (posA: 0, posB: 1, coeff: 10),
        ]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=5)

        # Self-pair becomes linear term: 100*x0
        check expr.pairs.len == 1
        check expr.linearTerms.len == 1

        expr.initialize(@[1, 1])
        # 5 + 100*1 + 10*1*1 = 115
        check expr.value == 115

        expr.initialize(@[1, 0])
        # 5 + 100*1 + 0 = 105
        check expr.value == 105

        expr.initialize(@[0, 0])
        # 5 + 0 + 0 = 5
        check expr.value == 5

    test "deepCopy independence":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newBinaryPairwiseSumExpression[int](pairs, constant=5)

        expr.initialize(@[1, 1])
        check expr.value == 15

        let copy = expr.deepCopy()
        check copy.value == 15

        # Modify original
        expr.updatePosition(0, 0)
        check expr.value == 5

        # Copy should be unaffected
        check copy.value == 15

    test "Integration: minimize binary pairwise sum":
        # 4 binary variables, minimize sum of all pairwise products
        # Minimum is when at most 1 variable is 1
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(@[0, 1])

        # Must have at least 2 variables set to 1
        sys.addConstraint(x[0] + x[1] + x[2] + x[3] >= 2)

        let pairs = @[
            (posA: 0, posB: 1, coeff: 10),
            (posA: 0, posB: 2, coeff: 20),
            (posA: 0, posB: 3, coeff: 30),
            (posA: 1, posB: 2, coeff: 40),
            (posA: 1, posB: 3, coeff: 50),
            (posA: 2, posB: 3, coeff: 60),
        ]
        let obj = newBinaryPairwiseSumExpression[int](pairs, constant=0)

        minimize(sys, obj, parallel=true, tabuThreshold=1000)

        obj.initialize(sys.assignment)
        # With exactly 2 variables set to 1, minimum pair is (0,1) with coeff 10
        check obj.value == 10
        echo "Minimize BPS: ", x.assignment, " obj=", obj.value

    test "Integration: maximize binary pairwise sum":
        # 4 binary variables, maximize pairwise products
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(@[0, 1])

        # Must have at most 3 variables set to 1
        sys.addConstraint(x[0] + x[1] + x[2] + x[3] <= 3)

        let pairs = @[
            (posA: 0, posB: 1, coeff: 1),
            (posA: 0, posB: 2, coeff: 1),
            (posA: 0, posB: 3, coeff: 1),
            (posA: 1, posB: 2, coeff: 1),
            (posA: 1, posB: 3, coeff: 1),
            (posA: 2, posB: 3, coeff: 1),
        ]
        let obj = newBinaryPairwiseSumExpression[int](pairs, constant=0)

        maximize(sys, obj, parallel=true, tabuThreshold=1000)

        obj.initialize(sys.assignment)
        # With 3 variables set to 1: C(3,2)=3 pairs
        check obj.value == 3
        echo "Maximize BPS: ", x.assignment, " obj=", obj.value

    test "Mixed quadratic + linear integration":
        # 3 binary vars: minimize 100*x0*x1 + 50*x0*x2 + 10*x0 + 20*x1
        # With constraint x0+x1+x2 >= 2
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(@[0, 1])
        sys.addConstraint(x[0] + x[1] + x[2] >= 2)

        let pairs = @[
            (posA: 0, posB: 1, coeff: 100),
            (posA: 0, posB: 2, coeff: 50),
        ]
        let linear = @[(pos: 0, coeff: 10), (pos: 1, coeff: 20)]
        let obj = newBinaryPairwiseSumExpression[int](pairs, linear, constant=0)

        minimize(sys, obj, parallel=true, tabuThreshold=1000)

        obj.initialize(sys.assignment)
        # Best: x0=0, x1=1, x2=1 → 0 + 0 + 0 + 20 = 20
        check obj.value == 20
        echo "Mixed BPS: ", x.assignment, " obj=", obj.value


suite "BinaryPairwiseSum Translator Detection":

    test "detect quadratic objective from conditional pairwise costs":
        ## Pattern: objective = sum of (ETA_ij * visit_i * visit_j)
        ## Decomposed as: int_eq_reif(cost, C, b) + bool_clause([b],[cond1,cond2])
        ##                + int_eq_reif(visit_i, 1, cond_i)
        let src = """
var 0..1: v1 :: output_var;
var 0..1: v2 :: output_var;
var 0..1: v3 :: output_var;
var 0..10: cost12 :: var_is_introduced;
var 0..20: cost13 :: var_is_introduced;
var 0..30: cost23 :: var_is_introduced;
var bool: b_v1 :: var_is_introduced :: is_defined_var;
var bool: b_v2 :: var_is_introduced :: is_defined_var;
var bool: b_v3 :: var_is_introduced :: is_defined_var;
var bool: eq12 :: var_is_introduced :: is_defined_var;
var bool: eq12z :: var_is_introduced :: is_defined_var;
var bool: eq13 :: var_is_introduced :: is_defined_var;
var bool: eq13z :: var_is_introduced :: is_defined_var;
var bool: eq23 :: var_is_introduced :: is_defined_var;
var bool: eq23z :: var_is_introduced :: is_defined_var;
var 0..60: obj :: is_defined_var;
constraint int_eq_reif(v1, 1, b_v1) :: defines_var(b_v1);
constraint int_eq_reif(v2, 1, b_v2) :: defines_var(b_v2);
constraint int_eq_reif(v3, 1, b_v3) :: defines_var(b_v3);
constraint int_eq_reif(cost12, 10, eq12) :: defines_var(eq12);
constraint int_eq_reif(cost12, 0, eq12z) :: defines_var(eq12z);
constraint bool_clause([eq12], [b_v1, b_v2]);
constraint bool_clause([b_v1, eq12z], []);
constraint int_eq_reif(cost13, 20, eq13) :: defines_var(eq13);
constraint int_eq_reif(cost13, 0, eq13z) :: defines_var(eq13z);
constraint bool_clause([eq13], [b_v1, b_v3]);
constraint bool_clause([b_v1, eq13z], []);
constraint int_eq_reif(cost23, 30, eq23) :: defines_var(eq23);
constraint int_eq_reif(cost23, 0, eq23z) :: defines_var(eq23z);
constraint bool_clause([eq23], [b_v2, b_v3]);
constraint bool_clause([b_v2, eq23z], []);
constraint int_lin_eq([1,1,1,-1], [cost12, cost13, cost23, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.binaryPairwiseSumObjName == "obj"
        check tr.binaryPairwiseSumPairs.len == 3
        check tr.binaryPairwiseSumLinearTerms.len == 0
        check tr.binaryPairwiseSumRemainingTerms.len == 0
        check tr.objectivePos == ObjPosBinaryPairwiseSum

        # Verify the expression was built
        check tr.binaryPairwiseSumExpr.pairs.len == 3

        # Solve: minimize obj with no other constraints
        # Best: all 0 → obj = 0
        minimize(tr.sys, tr.binaryPairwiseSumExpr,
                 parallel=true, tabuThreshold=1000)
        tr.binaryPairwiseSumExpr.initialize(tr.sys.assignment)
        check tr.binaryPairwiseSumExpr.value == 0

    test "detect mixed linear + quadratic from single and double conditions":
        ## Single condition (1 neg literal) → linear term
        ## Double condition (2 neg literals) → quadratic term
        let src = """
var 0..1: v1 :: output_var;
var 0..1: v2 :: output_var;
var 0..5: cost_lin :: var_is_introduced;
var 0..10: cost_quad :: var_is_introduced;
var bool: b_v1 :: var_is_introduced :: is_defined_var;
var bool: b_v2 :: var_is_introduced :: is_defined_var;
var bool: eql :: var_is_introduced :: is_defined_var;
var bool: eqlz :: var_is_introduced :: is_defined_var;
var bool: eqq :: var_is_introduced :: is_defined_var;
var bool: eqqz :: var_is_introduced :: is_defined_var;
var 0..15: obj :: is_defined_var;
constraint int_eq_reif(v1, 1, b_v1) :: defines_var(b_v1);
constraint int_eq_reif(v2, 1, b_v2) :: defines_var(b_v2);
constraint int_eq_reif(cost_lin, 5, eql) :: defines_var(eql);
constraint int_eq_reif(cost_lin, 0, eqlz) :: defines_var(eqlz);
constraint bool_clause([eql], [b_v1]);
constraint bool_clause([b_v1, eqlz], []);
constraint int_eq_reif(cost_quad, 10, eqq) :: defines_var(eqq);
constraint int_eq_reif(cost_quad, 0, eqqz) :: defines_var(eqqz);
constraint bool_clause([eqq], [b_v1, b_v2]);
constraint bool_clause([b_v1, eqqz], []);
constraint int_lin_eq([1,1,-1], [cost_lin, cost_quad, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.binaryPairwiseSumObjName == "obj"
        check tr.binaryPairwiseSumPairs.len == 1    # 1 quadratic
        check tr.binaryPairwiseSumLinearTerms.len == 1  # 1 linear
        check tr.objectivePos == ObjPosBinaryPairwiseSum

        # Solve: minimize with no extra constraints → all 0
        minimize(tr.sys, tr.binaryPairwiseSumExpr,
                 parallel=true, tabuThreshold=1000)
        tr.binaryPairwiseSumExpr.initialize(tr.sys.assignment)
        # Best with no constraints: all 0 → obj=0
        check tr.binaryPairwiseSumExpr.value == 0

    test "non-composable terms kept as remaining":
        ## Mix of composable and non-composable terms in the objective
        ## Non-composable: variable with no eq_reif chain (plain variable)
        let src = """
var 0..1: v1 :: output_var;
var 0..1: v2 :: output_var;
var 0..1: v3 :: output_var;
var 0..10: cost12 :: var_is_introduced;
var 0..20: cost13 :: var_is_introduced;
var 1..10: other :: output_var;
var bool: b_v1 :: var_is_introduced :: is_defined_var;
var bool: b_v2 :: var_is_introduced :: is_defined_var;
var bool: b_v3 :: var_is_introduced :: is_defined_var;
var bool: eq12 :: var_is_introduced :: is_defined_var;
var bool: ez12 :: var_is_introduced :: is_defined_var;
var bool: eq13 :: var_is_introduced :: is_defined_var;
var bool: ez13 :: var_is_introduced :: is_defined_var;
var 0..40: obj :: is_defined_var;
constraint int_eq_reif(v1, 1, b_v1) :: defines_var(b_v1);
constraint int_eq_reif(v2, 1, b_v2) :: defines_var(b_v2);
constraint int_eq_reif(v3, 1, b_v3) :: defines_var(b_v3);
constraint int_eq_reif(cost12, 10, eq12) :: defines_var(eq12);
constraint int_eq_reif(cost12, 0, ez12) :: defines_var(ez12);
constraint bool_clause([eq12], [b_v1, b_v2]);
constraint bool_clause([b_v1, ez12], []);
constraint int_eq_reif(cost13, 20, eq13) :: defines_var(eq13);
constraint int_eq_reif(cost13, 0, ez13) :: defines_var(ez13);
constraint bool_clause([eq13], [b_v1, b_v3]);
constraint bool_clause([b_v1, ez13], []);
constraint int_lin_eq([1,1,1,-1], [cost12, cost13, other, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.binaryPairwiseSumObjName == "obj"
        check tr.binaryPairwiseSumPairs.len == 2          # cost12, cost13 composed
        check tr.binaryPairwiseSumRemainingTerms.len == 1  # other kept as remaining


suite "Binary Partition Detection":

    test "detect exactly-one constraint":
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_lin_eq([1,1,1], [x1,x2,x3], 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.binaryPartitions.len == 1
        check tr.binaryPartitions[0].varNames.len == 3

        # Solve: exactly one must be 1
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        var count = 0
        for vn in ["x1", "x2", "x3"]:
            if tr.sys.assignment[tr.varPositions[vn]] == 1:
                inc count
        check count == 1

    test "detect multiple partition groups":
        let src = """
var 0..1: a1 :: output_var;
var 0..1: a2 :: output_var;
var 0..1: b1 :: output_var;
var 0..1: b2 :: output_var;
var 0..1: b3 :: output_var;
constraint int_lin_eq([1,1], [a1,a2], 1);
constraint int_lin_eq([1,1,1], [b1,b2,b3], 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.binaryPartitions.len == 2

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        var countA = 0
        for vn in ["a1", "a2"]:
            if tr.sys.assignment[tr.varPositions[vn]] == 1: inc countA
        check countA == 1

        var countB = 0
        for vn in ["b1", "b2", "b3"]:
            if tr.sys.assignment[tr.varPositions[vn]] == 1: inc countB
        check countB == 1

    test "non-binary vars not detected as partition":
        let src = """
var 0..2: x1 :: output_var;
var 0..2: x2 :: output_var;
constraint int_lin_eq([1,1], [x1,x2], 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # x1,x2 have domain 0..2, not binary → should NOT be detected
        check tr.binaryPartitions.len == 0

    test "defines_var constraint not detected as partition":
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: is_defined_var;
constraint int_lin_eq([1,1,-1], [x1,x2,x3], 0) :: defines_var(x3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # This is a defines_var constraint, not a partition
        check tr.binaryPartitions.len == 0

    test "partition with pairwise sum objective — end to end":
        ## Combines partition detection with BPS objective.
        ## 3 binary vars per group, 2 groups.
        ## Objective: pairwise cost between groups.
        let src = """
var 0..1: a1 :: output_var;
var 0..1: a2 :: output_var;
var 0..1: b1 :: output_var;
var 0..1: b2 :: output_var;
var 0..20: c_a1b1 :: var_is_introduced;
var 0..30: c_a1b2 :: var_is_introduced;
var 0..40: c_a2b1 :: var_is_introduced;
var 0..50: c_a2b2 :: var_is_introduced;
var bool: r_a1 :: var_is_introduced :: is_defined_var;
var bool: r_a2 :: var_is_introduced :: is_defined_var;
var bool: r_b1 :: var_is_introduced :: is_defined_var;
var bool: r_b2 :: var_is_introduced :: is_defined_var;
var bool: eq_a1b1 :: var_is_introduced :: is_defined_var;
var bool: ez_a1b1 :: var_is_introduced :: is_defined_var;
var bool: eq_a1b2 :: var_is_introduced :: is_defined_var;
var bool: ez_a1b2 :: var_is_introduced :: is_defined_var;
var bool: eq_a2b1 :: var_is_introduced :: is_defined_var;
var bool: ez_a2b1 :: var_is_introduced :: is_defined_var;
var bool: eq_a2b2 :: var_is_introduced :: is_defined_var;
var bool: ez_a2b2 :: var_is_introduced :: is_defined_var;
var 0..140: obj :: is_defined_var;
constraint int_lin_eq([1,1], [a1,a2], 1);
constraint int_lin_eq([1,1], [b1,b2], 1);
constraint int_eq_reif(a1, 1, r_a1) :: defines_var(r_a1);
constraint int_eq_reif(a2, 1, r_a2) :: defines_var(r_a2);
constraint int_eq_reif(b1, 1, r_b1) :: defines_var(r_b1);
constraint int_eq_reif(b2, 1, r_b2) :: defines_var(r_b2);
constraint int_eq_reif(c_a1b1, 20, eq_a1b1) :: defines_var(eq_a1b1);
constraint int_eq_reif(c_a1b1, 0, ez_a1b1) :: defines_var(ez_a1b1);
constraint bool_clause([eq_a1b1], [r_a1, r_b1]);
constraint bool_clause([r_a1, ez_a1b1], []);
constraint int_eq_reif(c_a1b2, 30, eq_a1b2) :: defines_var(eq_a1b2);
constraint int_eq_reif(c_a1b2, 0, ez_a1b2) :: defines_var(ez_a1b2);
constraint bool_clause([eq_a1b2], [r_a1, r_b2]);
constraint bool_clause([r_a1, ez_a1b2], []);
constraint int_eq_reif(c_a2b1, 40, eq_a2b1) :: defines_var(eq_a2b1);
constraint int_eq_reif(c_a2b1, 0, ez_a2b1) :: defines_var(ez_a2b1);
constraint bool_clause([eq_a2b1], [r_a2, r_b1]);
constraint bool_clause([r_a2, ez_a2b1], []);
constraint int_eq_reif(c_a2b2, 50, eq_a2b2) :: defines_var(eq_a2b2);
constraint int_eq_reif(c_a2b2, 0, ez_a2b2) :: defines_var(ez_a2b2);
constraint bool_clause([eq_a2b2], [r_a2, r_b2]);
constraint bool_clause([r_a2, ez_a2b2], []);
constraint int_lin_eq([1,1,1,1,-1], [c_a1b1, c_a1b2, c_a2b1, c_a2b2, obj], 0) :: defines_var(obj);
solve minimize obj;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Both patterns detected
        check tr.binaryPartitions.len == 2
        check tr.binaryPairwiseSumObjName == "obj"
        check tr.binaryPairwiseSumPairs.len == 4
        check tr.objectivePos == ObjPosBinaryPairwiseSum

        # Solve: partition says exactly one a_i=1 and one b_j=1
        # So exactly one of the 4 cost terms is active
        # Minimum cost is min(20, 30, 40, 50) = 20 (a1=1, b1=1)
        minimize(tr.sys, tr.binaryPairwiseSumExpr,
                 parallel=true, tabuThreshold=5000,
                 lowerBound=tr.objectiveLoBound,
                 upperBound=tr.objectiveHiBound)

        tr.binaryPairwiseSumExpr.initialize(tr.sys.assignment)
        check tr.binaryPairwiseSumExpr.value == 20
        echo "Partition+BPS result: obj=", tr.binaryPairwiseSumExpr.value

    test "binary partition domain reduction — singleton propagation":
        ## When one member is forced to 1 via a separate constraint,
        ## the partition plus that constraint should be solvable trivially.
        let src = """
var 0..1: x1 :: output_var;
var 0..1: x2 :: output_var;
var 0..1: x3 :: output_var;
constraint int_lin_eq([1,1,1], [x1,x2,x3], 1);
constraint int_eq(x1, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.binaryPartitions.len == 1
        # x1 is forced to 1 by int_eq, so x2 and x3 should be 0
        tr.sys.resolve(parallel = true, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["x1"]] == 1
        check tr.sys.assignment[tr.varPositions["x2"]] == 0
        check tr.sys.assignment[tr.varPositions["x3"]] == 0
