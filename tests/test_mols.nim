import std/[sequtils, strutils, sets, unittest]
import crusher

proc validateMOLS(X: seq[seq[int]], Y: seq[seq[int]], n: int): bool =
    ## Validates that X and Y form a pair of Mutually Orthogonal Latin Squares

    # Check dimensions
    if X.len != n or Y.len != n:
        echo "❌ Invalid matrix dimensions"
        return false

    for i in 0..<n:
        if X[i].len != n or Y[i].len != n:
            echo "❌ Invalid row length in row ", i
            return false

    # Validate that both X and Y are Latin squares
    proc validateLatinSquare(matrix: seq[seq[int]]): bool =
        # Check that each row contains all values 0..<n exactly once
        for i, row in matrix:
            let rowSet = row.toHashSet()
            let expectedSet = toSeq(0..<n).toHashSet()
            if rowSet != expectedSet:
                echo "❌ Row ", i, " does not contain all values 0..<", n, ": ", row
                return false

        # Check that each column contains all values 0..<n exactly once
        for j in 0..<n:
            var colSet = initHashSet[int]()
            for i in 0..<n:
                colSet.incl(matrix[i][j])
            let expectedSet = toSeq(0..<n).toHashSet()
            if colSet != expectedSet:
                echo "❌ Column ", j, " does not contain all values 0..<", n
                return false

        return true

    if not validateLatinSquare(X):
        echo "❌ X is not a valid Latin square"
        return false

    if not validateLatinSquare(Y):
        echo "❌ Y is not a valid Latin square"
        return false

    # Check canonical form constraints
    # X: first row and column should be 0,1,2,...
    for i in 0..<n:
        if X[0][i] != i:
            echo "❌ X first row should be 0,1,2,... but X[0][", i, "] = ", X[0][i]
            return false
        if X[i][0] != i:
            echo "❌ X first column should be 0,1,2,... but X[", i, "][0] = ", X[i][0]
            return false

    # Y: first row should be 0,1,2,...
    for i in 0..<n:
        if Y[0][i] != i:
            echo "❌ Y first row should be 0,1,2,... but Y[0][", i, "] = ", Y[0][i]
            return false

    # Y: first column constraints (Y[i][0] <= i+1 and Y[i][0] != i for i >= 1)
    for i in 1..<n:
        if Y[i][0] > i + 1:
            echo "❌ Y[", i, "][0] = ", Y[i][0], " should be <= ", i + 1
            return false
        if Y[i][0] == i:
            echo "❌ Y[", i, "][0] = ", Y[i][0], " should not equal ", i
            return false

    # Check mutual orthogonality: all pairs (X[i][j], Y[i][j]) should be distinct
    var pairSet = initHashSet[(int, int)]()
    for i in 0..<n:
        for j in 0..<n:
            let pair = (X[i][j], Y[i][j])
            if pair in pairSet:
                echo "❌ Duplicate pair found: (", pair[0], ", ", pair[1], ") at position (", i, ", ", j, ")"
                return false
            pairSet.incl(pair)

    # Should have exactly n*n distinct pairs
    if pairSet.len != n * n:
        echo "❌ Expected ", n * n, " distinct pairs, but got ", pairSet.len
        return false

    return true

proc solveMOLS(n: int, parallel: bool = false): (seq[seq[int]], seq[seq[int]]) =
    ## Solves MOLS problem for given n, returns (X, Y) matrices
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    var Y = sys.newConstrainedMatrix(n, n)

    # Set up each of X and Y to be latin squares
    # Set domain of each entry to 0..<n
    X.setDomain(toSeq(0..<n))
    Y.setDomain(toSeq(0..<n))

    # Each row has to be a permutation of 0, 1, .., n
    for row in X.rows():
        sys.addConstraint(allDifferent(row))

    for row in Y.rows():
        sys.addConstraint(allDifferent(row))

    # Each col has to be a permutation of 0, 1, .., n
    for col in X.columns():
        sys.addConstraint(allDifferent(col))

    for col in Y.columns():
        sys.addConstraint(allDifferent(col))

    # First row in order 0 1 2... in first square
    for i in 0..<n:
        sys.addConstraint(X[0, i] == i)
        sys.addConstraint(X[i, 0] == i)

    # First col in order 0 1 2... in both squares
    for i in 0..<n:
        sys.addConstraint(Y[0, i] == i)

    for i in 1..<n:
        sys.addConstraint(Y[i, 0] <= i + 1)
        sys.addConstraint(Y[i, 0] != i)

    # Mutual orthogonality condition
    var pairs: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<n:
        for j in 0..<n:
            pairs.add(X[i, j] + n*Y[i, j])
    sys.addConstraint(allDifferent(pairs))

    # Solve with specified mode
    sys.resolve(10000, parallel=parallel, verbose=false)

    return (X.assignment(), Y.assignment())

suite "MOLS (Mutually Orthogonal Latin Squares) Tests":
    test "4x4 MOLS generation with parallel search":
        let (X, Y) = solveMOLS(4, parallel=true)

        echo "✓ Found MOLS solution with parallel search:"
        echo "X matrix:"
        for row in X:
            echo "  ", row
        echo "Y matrix:"
        for row in Y:
            echo "  ", row

        check validateMOLS(X, Y, 4)

    test "3x3 MOLS generation with parallel search":
        let (X, Y) = solveMOLS(3, parallel=true)

        echo "✓ Found MOLS solution with parallel search:"
        echo "X matrix:"
        for row in X:
            echo "  ", row
        echo "Y matrix:"
        for row in Y:
            echo "  ", row

        check validateMOLS(X, Y, 3)

    test "Compare parallel vs sequential for 4x4 MOLS":
        # Test both methods find valid solutions
        let (X_parallel, Y_parallel) = solveMOLS(4, parallel=true)
        let (X_sequential, Y_sequential) = solveMOLS(4, parallel=false)

        echo "✓ Parallel solution found"
        echo "✓ Sequential solution found"

        # Both should be valid MOLS
        check validateMOLS(X_parallel, Y_parallel, 4)
        check validateMOLS(X_sequential, Y_sequential, 4)