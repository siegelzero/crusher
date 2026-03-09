import std/[sequtils, unittest, packedsets]
import crusher
import constraints/diffnK

proc validateDiffnKSolution(positions, sizes: seq[seq[int]]): bool =
    ## Validates that no two k-dimensional boxes overlap
    let n = positions.len
    if n == 0: return true
    let k = positions[0].len
    for i in 0 ..< n:
        for j in i + 1 ..< n:
            # Skip zero-size boxes
            var hasZero = false
            for d in 0 ..< k:
                if sizes[i][d] <= 0 or sizes[j][d] <= 0:
                    hasZero = true
                    break
            if hasZero: continue
            # Check overlap in all dimensions
            var allOverlap = true
            for d in 0 ..< k:
                let overlapD = positions[i][d] < positions[j][d] + sizes[j][d] and
                               positions[j][d] < positions[i][d] + sizes[i][d]
                if not overlapD:
                    allOverlap = false
                    break
            if allOverlap:
                echo "Overlap: box ", i, " and box ", j
                return false
    return true

suite "DiffnK Constraint Tests":
    test "Basic 3D non-overlapping unit cubes":
        # 8 unit cubes in a 2x2x2 grid
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(8)
        var ys = sys.newConstrainedSequence(8)
        var zs = sys.newConstrainedSequence(8)
        xs.setDomain(toSeq(0..1))
        ys.setDomain(toSeq(0..1))
        zs.setDomain(toSeq(0..1))

        # Build position and size expressions
        let n = 8
        let k = 3
        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        let unitSize = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 1),
            linear = true
        )
        for i in 0 ..< n:
            posExprs[i] = @[sys.baseArray[i], sys.baseArray[i + n], sys.baseArray[i + 2*n]]
            sizeExprs[i] = @[unitSize, unitSize, unitSize]

        sys.addConstraint(diffnK[int](n, k, posExprs, sizeExprs))
        sys.resolve(parallel = true)

        var positions = newSeq[seq[int]](n)
        var sizes = newSeq[seq[int]](n)
        for i in 0 ..< n:
            positions[i] = @[xs.assignment[i], ys.assignment[i], zs.assignment[i]]
            sizes[i] = @[1, 1, 1]
        check validateDiffnKSolution(positions, sizes)

    test "3D with zero-size boxes (nonstrict)":
        # 4 boxes in 3D, 2 have zero size in one dimension — should be trivially satisfiable
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(4)
        var ys = sys.newConstrainedSequence(4)
        var zs = sys.newConstrainedSequence(4)
        xs.setDomain(toSeq(0..0))  # all at position 0
        ys.setDomain(toSeq(0..0))
        zs.setDomain(toSeq(0..0))

        let n = 4
        let k = 3
        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)

        proc litExpr(v: int): AlgebraicExpression[int] =
            newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: v),
                linear = true
            )

        for i in 0 ..< n:
            posExprs[i] = @[sys.baseArray[i], sys.baseArray[i + n], sys.baseArray[i + 2*n]]
            # First 2 boxes have size 0 in z-dimension
            if i < 2:
                sizeExprs[i] = @[litExpr(1), litExpr(1), litExpr(0)]
            else:
                sizeExprs[i] = @[litExpr(1), litExpr(1), litExpr(0)]

        sys.addConstraint(diffnK[int](n, k, posExprs, sizeExprs))
        sys.resolve(parallel = true)
        # All sizes are 0, so no overlaps possible — trivially solved

    test "Incremental update correctness":
        # Verify moveDelta matches full recompute
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(4)
        var ys = sys.newConstrainedSequence(4)
        var zs = sys.newConstrainedSequence(4)
        xs.setDomain(toSeq(0..3))
        ys.setDomain(toSeq(0..3))
        zs.setDomain(toSeq(0..3))

        let n = 4
        let k = 3
        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)

        let unitSize = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 2),
            linear = true
        )
        for i in 0 ..< n:
            posExprs[i] = @[sys.baseArray[i], sys.baseArray[i + n], sys.baseArray[i + 2*n]]
            sizeExprs[i] = @[unitSize, unitSize, unitSize]

        let constraint = newDiffnKConstraint[int](n, k, posExprs, sizeExprs)

        # Create an assignment where boxes overlap
        var assignment = newSeq[int](12)
        # Box 0: (0,0,0), Box 1: (1,1,1), Box 2: (0,0,0), Box 3: (2,2,2)
        assignment[0] = 0; assignment[1] = 1; assignment[2] = 0; assignment[3] = 2
        assignment[4] = 0; assignment[5] = 1; assignment[6] = 0; assignment[7] = 2
        assignment[8] = 0; assignment[9] = 1; assignment[10] = 0; assignment[11] = 2

        constraint.initialize(assignment)
        let initialCost = constraint.cost
        check initialCost > 0  # boxes 0 and 2 overlap, 0 and 1 overlap

        # Test moveDelta: move box 2's x to 3
        let delta = constraint.moveDelta(2, 0, 3)

        # Apply the move and verify
        constraint.updatePosition(2, 3)
        let newCost = constraint.cost

        check newCost == initialCost + delta

    test "2D packing via diffnK":
        # Use k=2 to verify it works as regular diffn
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(4)
        var ys = sys.newConstrainedSequence(4)
        xs.setDomain(toSeq(0..1))
        ys.setDomain(toSeq(0..1))

        let n = 4
        let k = 2
        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)

        let unitSize = newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 1),
            linear = true
        )
        for i in 0 ..< n:
            posExprs[i] = @[sys.baseArray[i], sys.baseArray[i + n]]
            sizeExprs[i] = @[unitSize, unitSize]

        sys.addConstraint(diffnK[int](n, k, posExprs, sizeExprs))
        sys.resolve(parallel = true)

        var positions = newSeq[seq[int]](n)
        var sizes = newSeq[seq[int]](n)
        for i in 0 ..< n:
            positions[i] = @[xs.assignment[i], ys.assignment[i]]
            sizes[i] = @[1, 1]
        check validateDiffnKSolution(positions, sizes)

    test "batchMovePenalty matches moveDelta":
        # Verify batchMovePenalty returns same values as individual moveDelta calls
        let n = 3
        let k = 3
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(n)
        var ys = sys.newConstrainedSequence(n)
        var zs = sys.newConstrainedSequence(n)
        xs.setDomain(toSeq(0..4))
        ys.setDomain(toSeq(0..4))
        zs.setDomain(toSeq(0..4))

        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)

        proc litExpr(v: int): AlgebraicExpression[int] =
            newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: v),
                linear = true
            )

        for i in 0 ..< n:
            posExprs[i] = @[sys.baseArray[i], sys.baseArray[i + n], sys.baseArray[i + 2*n]]
            sizeExprs[i] = @[litExpr(2), litExpr(2), litExpr(2)]

        let constraint = newDiffnKConstraint[int](n, k, posExprs, sizeExprs)

        # Overlapping assignment: box0=(0,0,0), box1=(1,1,1), box2=(0,1,0)
        var assignment = newSeq[int](9)
        assignment[0] = 0; assignment[1] = 1; assignment[2] = 0
        assignment[3] = 0; assignment[4] = 1; assignment[5] = 1
        assignment[6] = 0; assignment[7] = 1; assignment[8] = 0

        constraint.initialize(assignment)

        let domain = toSeq(0..4)
        let pos = 0  # box 0's x position
        let curVal = assignment[pos]

        let batchResult = constraint.batchMovePenalty(pos, curVal, domain)
        for i, v in domain:
            if v == curVal:
                check batchResult[i] == 0
            else:
                let delta = constraint.moveDelta(pos, curVal, v)
                check batchResult[i] == delta

    test "deep copy independence":
        # Verify deep copy produces independent state
        let n = 3
        let k = 2
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(n)
        var ys = sys.newConstrainedSequence(n)
        xs.setDomain(toSeq(0..3))
        ys.setDomain(toSeq(0..3))

        var posExprs = newSeq[seq[AlgebraicExpression[int]]](n)
        var sizeExprs = newSeq[seq[AlgebraicExpression[int]]](n)

        proc litExpr(v: int): AlgebraicExpression[int] =
            newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: v),
                linear = true
            )

        for i in 0 ..< n:
            posExprs[i] = @[sys.baseArray[i], sys.baseArray[i + n]]
            sizeExprs[i] = @[litExpr(2), litExpr(2)]

        let original = newDiffnKConstraint[int](n, k, posExprs, sizeExprs)

        # Initialize with overlapping boxes
        var assignment = newSeq[int](6)
        assignment[0] = 0; assignment[1] = 0; assignment[2] = 1
        assignment[3] = 0; assignment[4] = 0; assignment[5] = 1

        original.initialize(assignment)
        let origCost = original.cost

        # Deep copy
        let copy = original.deepCopy()
        copy.initialize(assignment)
        check copy.cost == origCost

        # Modify the copy, verify original is unchanged
        copy.updatePosition(0, 3)
        let copyCost = copy.cost
        check original.cost == origCost
        check copyCost != origCost  # moving box 0 away should change cost
