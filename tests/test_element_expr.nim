import std/unittest
import crusher

suite "Expression-based Element Constraint Tests":
    test "Basic expression-based element with computed index":
        # Test expression-based element constraint
        var sys = initConstraintSystem[int]()

        # Create a 3x3 grid (flat: 9 cells)
        var grid = sys.newConstrainedSequence(9)
        grid.setDomain([0, 1, 2, 3])

        # Position variables X and Y
        var X = sys.newConstrainedVariable()
        var Y = sys.newConstrainedVariable()
        X.setDomain([0, 1, 2])
        Y.setDomain([0, 1, 2])

        # Compute index as Y * 3 + X
        let indexExpr = Y * 3 + X

        # Value variable
        var V = sys.newConstrainedVariable()
        V.setDomain([1, 2, 3])

        # Expression-based element: grid[Y*3 + X] = V
        sys.addConstraint(elementExpr(indexExpr, grid, V))

        # Also constrain X=1, Y=1 (so index = 4)
        sys.addConstraint(X == 1)
        sys.addConstraint(Y == 1)

        # And V = 2
        sys.addConstraint(V == 2)

        sys.resolve(verbose = false)

        echo "X = ", X.assignment()
        echo "Y = ", Y.assignment()
        echo "V = ", V.assignment()
        echo "grid[4] = ", grid.assignment[4]

        # Verify: grid[4] should equal V = 2
        check grid.assignment[4] == 2

    test "Expression-based element with linear index":
        # Test Y * W + X pattern (common in grid problems)
        var sys = initConstraintSystem[int]()

        # 2x3 grid as flat array (6 cells)
        let W = 3
        var grid = sys.newConstrainedSequence(6)
        grid.setDomain([0, 1, 2, 3, 4, 5])

        # Position variables
        var X = sys.newConstrainedVariable()
        var Y = sys.newConstrainedVariable()
        X.setDomain([0, 1, 2])  # columns
        Y.setDomain([0, 1])     # rows

        # Compute index as Y * W + X
        let indexExpr = Y * W + X

        # Value that should be at the computed position
        var V = sys.newConstrainedVariable()
        V.setDomain([0, 1, 2, 3, 4, 5])

        # Expression-based element: grid[Y*W + X] = V
        sys.addConstraint(elementExpr(indexExpr, grid, V))

        # Constrain: we want position (1, 1) which is index = 1*3 + 1 = 4
        sys.addConstraint(X == 1)
        sys.addConstraint(Y == 1)
        sys.addConstraint(V == 4)  # V should match the index we expect

        sys.resolve(verbose = false)

        let xVal = X.assignment()
        let yVal = Y.assignment()
        let vVal = V.assignment()
        let computedIndex = yVal * W + xVal

        echo "X = ", xVal, ", Y = ", yVal, ", V = ", vVal
        echo "Computed index = ", computedIndex
        echo "grid[", computedIndex, "] = ", grid.assignment[computedIndex]

        # Verify: grid at computed index should equal V
        check computedIndex == 4
        check grid.assignment[computedIndex] == vVal

    test "Expression-based element with constant array (shape lookup)":
        # This mimics Picat's matrix_element(Shape, Rr, Cf, V) for shape lookup
        var sys = initConstraintSystem[int]()

        # A 3x3 shape as flat constant array (like a heptomino piece)
        # Shape:
        #   1 1 1
        #   1 1 0
        #   1 0 0
        let flatShape = @[1, 1, 1, 1, 1, 0, 1, 0, 0]

        # Row and column variables (transformed coordinates)
        var Rr = sys.newConstrainedVariable()
        var Cf = sys.newConstrainedVariable()
        Rr.setDomain([0, 1, 2])
        Cf.setDomain([0, 1, 2])

        # Result variable V = Shape[Rr * 3 + Cf]
        var V = sys.newConstrainedVariable()
        V.setDomain([0, 1])

        # Compute index as Rr * 3 + Cf
        let indexExpr = Rr * 3 + Cf

        # Expression-based element with constant array: flatShape[Rr*3 + Cf] = V
        sys.addConstraint(elementExpr(indexExpr, flatShape, V))

        # Test case 1: Rr=0, Cf=0 -> index=0 -> V should be 1
        sys.addConstraint(Rr == 0)
        sys.addConstraint(Cf == 0)

        sys.resolve(verbose = false)

        echo "Rr = ", Rr.assignment(), ", Cf = ", Cf.assignment()
        echo "V = ", V.assignment(), " (expected 1 since Shape[0,0] = 1)"

        check V.assignment() == 1

    test "Expression-based element with constant array - empty cell":
        var sys = initConstraintSystem[int]()

        # Same shape
        let flatShape = @[1, 1, 1, 1, 1, 0, 1, 0, 0]

        var Rr = sys.newConstrainedVariable()
        var Cf = sys.newConstrainedVariable()
        Rr.setDomain([0, 1, 2])
        Cf.setDomain([0, 1, 2])

        var V = sys.newConstrainedVariable()
        V.setDomain([0, 1])

        let indexExpr = Rr * 3 + Cf
        sys.addConstraint(elementExpr(indexExpr, flatShape, V))

        # Test: Rr=1, Cf=2 -> index=5 -> V should be 0 (empty cell)
        sys.addConstraint(Rr == 1)
        sys.addConstraint(Cf == 2)
        # Also force V to what it should be
        sys.addConstraint(V == 0)

        sys.resolve(verbose = false)

        echo "Rr = ", Rr.assignment(), ", Cf = ", Cf.assignment()
        echo "V = ", V.assignment(), " (expected 0 since Shape[1,2] = 0)"

        check V.assignment() == 0

    test "Expression-based element with constant array - find V":
        # Let solver find V given fixed position
        var sys = initConstraintSystem[int]()

        # Simpler: array of [10, 20, 30]
        let arr = @[10, 20, 30]

        var idx = sys.newConstrainedVariable()
        idx.setDomain([0, 1, 2])

        var V = sys.newConstrainedVariable()
        V.setDomain([10, 20, 30])

        # Simple index variable (not computed)
        sys.addConstraint(elementExpr(idx, arr, V))

        # Fix index to 1 -> V should be 20
        sys.addConstraint(idx == 1)

        sys.resolve(verbose = false)

        echo "idx = ", idx.assignment(), ", V = ", V.assignment()
        check V.assignment() == 20
