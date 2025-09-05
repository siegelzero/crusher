import std/[sequtils, strutils, sets]
import crusher

proc validateMagicSquare(matrix: seq[seq[int]], n: int): bool =
    ## Validates that the given matrix is a valid n×n magic square

    let target = n * (n * n + 1) div 2
    echo "🎯 Expected magic sum: ", target

    # Check dimensions
    if matrix.len != n:
        echo "❌ Invalid number of rows: expected ", n, ", got ", matrix.len
        return false

    for i, row in matrix:
        if row.len != n:
            echo "❌ Invalid number of columns in row ", i, ": expected ", n, ", got ", row.len
            return false

    # Check that all values are in range 1..n²
    var allValues = initHashSet[int]()
    for i, row in matrix:
        for j, val in row:
            if val < 1 or val > n * n:
                echo "❌ Invalid value at [", i, ",", j, "]: ", val, " (expected 1..", n*n, ")"
                return false
            allValues.incl(val)

    # Check that all values 1..n² are used exactly once
    let expectedValues = toSeq(1..n*n).toHashSet()
    if allValues != expectedValues:
        echo "❌ Not all values 1..", n*n, " are used exactly once"
        return false

    # Check row sums
    for i, row in matrix:
        let rowSum = row.foldl(a + b, 0)
        if rowSum != target:
            echo "❌ Row ", i, " sum is ", rowSum, ", expected ", target
            return false

    # Check column sums
    for j in 0..<n:
        var colSum = 0
        for i in 0..<n:
            colSum += matrix[i][j]
        if colSum != target:
            echo "❌ Column ", j, " sum is ", colSum, ", expected ", target
            return false

    # Check main diagonal sum
    var diag1Sum = 0
    for i in 0..<n:
        diag1Sum += matrix[i][i]
    if diag1Sum != target:
        echo "❌ Main diagonal sum is ", diag1Sum, ", expected ", target
        return false

    # Check anti-diagonal sum
    var diag2Sum = 0
    for i in 0..<n:
        diag2Sum += matrix[i][n - i - 1]
    if diag2Sum != target:
        echo "❌ Anti-diagonal sum is ", diag2Sum, ", expected ", target
        return false

    echo "✅ All magic square properties verified"
    return true

proc testMagicSquareFoldl4x4(): bool =
    ## Test solving a 4×4 magic square using foldl constraints and validate the solution
    echo "🧪 Testing 4×4 Magic Square generation (foldl constraints)..."

    # Create constraint system (based on models/magicSquare.nim)
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(4, 4)

    let target = 4 * (4 * 4 + 1) div 2  # = 34

    # Row sums == target (using foldl)
    for row in X.rows():
        sys.addConstraint(row.foldl(a + b) == target)

    # Col sums == target (using foldl)
    for col in X.columns():
        sys.addConstraint(col.foldl(a + b) == target)

    # Main diagonal
    var terms: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<4:
        terms.add(X[i, i])
    sys.addConstraint(terms.foldl(a + b) == target)

    # Anti-diagonal
    terms = @[]
    for i in 0..<4:
        terms.add(X[i, 4 - i - 1])
    sys.addConstraint(terms.foldl(a + b) == target)

    # All entries must be distinct
    sys.addConstraint(allDifferent(X))
    X.setDomain(toSeq(1..16))

    # Solve the constraint system
    echo "⚡ Solving constraint system..."
    sys.resolve()

    # Extract solution matrix
    let solution = X.assignment

    # Display solution
    echo "📋 Solution found:"
    for i, row in solution:
        echo "   ", row.mapIt($it).join("  ")

    # Validate the solution
    echo "✅ Validating solution..."
    return validateMagicSquare(solution, 4)

proc testMagicSquareLC4x4(): bool =
    ## Test solving a 4×4 magic square using linear combination constraints and validate the solution
    echo "🧪 Testing 4×4 Magic Square generation (Linear Combination constraints)..."

    # Create constraint system (based on models/magicSquareLC.nim)
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(4, 4)

    let target = 4 * (4 * 4 + 1) div 2  # = 34

    # Row sums == target (using sum - Linear Combination)
    for row in X.rows():
        sys.addConstraint(sum(row) == target)

    # Col sums == target (using sum - Linear Combination)
    for col in X.columns():
        sys.addConstraint(sum(col) == target)

    # Main diagonal
    var terms: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<4:
        terms.add(X[i, i])
    sys.addConstraint(sum(terms) == target)

    # Anti-diagonal
    terms = @[]
    for i in 0..<4:
        terms.add(X[i, 4 - i - 1])
    sys.addConstraint(sum(terms) == target)

    # All entries must be distinct
    sys.addConstraint(allDifferent(X))
    X.setDomain(toSeq(1..16))

    # Solve the constraint system
    echo "⚡ Solving constraint system..."
    sys.resolve()

    # Extract solution matrix
    let solution = X.assignment

    # Display solution
    echo "📋 Solution found:"
    for i, row in solution:
        echo "   ", row.mapIt($it).join("  ")

    # Validate the solution
    echo "✅ Validating solution..."
    return validateMagicSquare(solution, 4)

proc main() =
    echo "🚀 Starting Magic Square Tests"
    echo "==============================="

    var allSuccess = true

    echo ""
    echo "📋 Test 1/2: Magic Square (foldl constraints)"
    echo "=============================================="
    let foldlSuccess = testMagicSquareFoldl4x4()
    if not foldlSuccess:
        allSuccess = false

    echo ""
    echo "📋 Test 2/2: Magic Square (Linear Combination constraints)"
    echo "=========================================================="
    let lcSuccess = testMagicSquareLC4x4()
    if not lcSuccess:
        allSuccess = false

    echo ""
    if allSuccess:
        echo "✅ All magic square tests passed!"
        quit(0)
    else:
        echo "❌ Some magic square tests failed!"
        quit(1)

when isMainModule:
    main()