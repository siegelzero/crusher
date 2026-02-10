import std/[sequtils, sets, unittest]
import crusher

suite "Scatter Search Tests":
    test "Simple AllDifferent":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(5)
        x.setDomain(toSeq(1..5))
        sys.addConstraint(allDifferent(x))

        sys.scatterResolve(poolSize = 6, iterations = 3, tabuThreshold = 1000,
                           relinkThreshold = 500, verbose = false)

        let solution = x.assignment
        check solution.len == 5
        check solution.toHashSet.len == 5
        for v in solution:
            check v >= 1 and v <= 5

    test "4x4 N-Queens":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(0..<4))

        var terms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<4:
            terms.add(x[i])
        sys.addConstraint(allDifferent(terms))

        terms.reset()
        for i in 0..<4:
            terms.add(x[i] - i)
        sys.addConstraint(allDifferent(terms))

        terms.reset()
        for i in 0..<4:
            terms.add(x[i] + i)
        sys.addConstraint(allDifferent(terms))

        sys.scatterResolve(poolSize = 6, iterations = 3, tabuThreshold = 2000,
                           relinkThreshold = 1000, verbose = false)

        let solution = x.assignment
        check solution.len == 4
        # Validate no column conflicts
        check solution.toHashSet.len == 4
        # Validate no diagonal conflicts
        var mainDiags = initHashSet[int]()
        var antiDiags = initHashSet[int]()
        for i, col in solution:
            mainDiags.incl(col - i)
            antiDiags.incl(col + i)
        check mainDiags.len == 4
        check antiDiags.len == 4

    test "4x4 Magic Square":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedMatrix(4, 4)
        let target = 4 * (4 * 4 + 1) div 2  # = 34

        for row in X.rows():
            sys.addConstraint(row.foldl(a + b) == target)
        for col in X.columns():
            sys.addConstraint(col.foldl(a + b) == target)

        var terms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<4:
            terms.add(X[i, i])
        sys.addConstraint(terms.foldl(a + b) == target)

        terms = @[]
        for i in 0..<4:
            terms.add(X[i, 4 - i - 1])
        sys.addConstraint(terms.foldl(a + b) == target)

        sys.addConstraint(allDifferent(X))
        X.setDomain(toSeq(1..16))

        sys.scatterResolve(poolSize = 8, iterations = 5, tabuThreshold = 5000,
                           relinkThreshold = 2000, verbose = false)

        let solution = X.assignment
        check solution.len == 4
        for row in solution:
            check row.len == 4
        # Check all values used
        var allVals = initHashSet[int]()
        for row in solution:
            for v in row:
                allVals.incl(v)
        check allVals.len == 16
        # Check row sums
        for row in solution:
            check row.foldl(a + b, 0) == target
