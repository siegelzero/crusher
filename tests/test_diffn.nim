import std/[sequtils, unittest]
import crusher

proc validateDiffnSolution(xs, ys, dxs, dys: seq[int]): bool =
    ## Validates that no two rectangles overlap
    let n = xs.len
    for i in 0 ..< n:
        for j in i + 1 ..< n:
            # Skip zero-size rectangles
            if dxs[i] <= 0 or dys[i] <= 0 or dxs[j] <= 0 or dys[j] <= 0:
                continue
            let overlapX = xs[i] < xs[j] + dxs[j] and xs[j] < xs[i] + dxs[i]
            let overlapY = ys[i] < ys[j] + dys[j] and ys[j] < ys[i] + dys[i]
            if overlapX and overlapY:
                echo "Overlap: rect ", i, " (", xs[i], ",", ys[i], ",", dxs[i], ",", dys[i],
                     ") and rect ", j, " (", xs[j], ",", ys[j], ",", dxs[j], ",", dys[j], ")"
                return false
    return true

suite "Diffn Constraint Tests":
    test "Basic non-overlapping rectangles":
        # 4 unit squares on a 2x2 grid — must place without overlap
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(4)
        var ys = sys.newConstrainedSequence(4)
        xs.setDomain(toSeq(0..1))
        ys.setDomain(toSeq(0..1))

        # Fixed 1x1 sizes as literal expressions
        let dxExprs = (0..3).mapIt(newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 1),
            linear = true
        ))
        let dyExprs = (0..3).mapIt(newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: 1),
            linear = true
        ))

        # x and y expressions from positions
        let xExprs = (0..3).mapIt(sys.baseArray[it])
        let yExprs = (4..7).mapIt(sys.baseArray[it])

        sys.addConstraint(diffn[int](xExprs, yExprs, dxExprs, dyExprs))

        sys.resolve(parallel = true)

        let xSol = xs.assignment
        let ySol = ys.assignment
        check validateDiffnSolution(xSol, ySol, @[1, 1, 1, 1], @[1, 1, 1, 1])

    test "Rectangles with different sizes":
        # 3 rectangles: 2x1, 1x2, 1x1 on a 3x3 grid
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(3)
        var ys = sys.newConstrainedSequence(3)
        xs.setDomain(toSeq(0..2))
        ys.setDomain(toSeq(0..2))

        let widths = @[2, 1, 1]
        let heights = @[1, 2, 1]

        let dxExprs = widths.mapIt(newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: it),
            linear = true
        ))
        let dyExprs = heights.mapIt(newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: it),
            linear = true
        ))

        let xExprs = (0..2).mapIt(sys.baseArray[it])
        let yExprs = (3..5).mapIt(sys.baseArray[it])

        sys.addConstraint(diffn[int](xExprs, yExprs, dxExprs, dyExprs))

        sys.resolve(parallel = true)

        let xSol = xs.assignment
        let ySol = ys.assignment
        check validateDiffnSolution(xSol, ySol, widths, heights)

    test "Tight packing of rectangles":
        # 2 rectangles: 3x1 and 3x1, must stack in a 3x2 area
        var sys = initConstraintSystem[int]()
        var xs = sys.newConstrainedSequence(2)
        var ys = sys.newConstrainedSequence(2)
        xs.setDomain(toSeq(0..2))
        ys.setDomain(toSeq(0..1))

        let widths = @[3, 3]
        let heights = @[1, 1]

        let dxExprs = widths.mapIt(newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: it),
            linear = true
        ))
        let dyExprs = heights.mapIt(newAlgebraicExpression[int](
            positions = initPackedSet[int](),
            node = ExpressionNode[int](kind: LiteralNode, value: it),
            linear = true
        ))

        let xExprs = (0..1).mapIt(sys.baseArray[it])
        let yExprs = (2..3).mapIt(sys.baseArray[it])

        sys.addConstraint(diffn[int](xExprs, yExprs, dxExprs, dyExprs))

        sys.resolve(parallel = true)

        let xSol = xs.assignment
        let ySol = ys.assignment
        check validateDiffnSolution(xSol, ySol, widths, heights)
