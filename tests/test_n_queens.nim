import std/[sequtils, strutils, sets, unittest]
import crusher

proc validateNQueensSolution(solution: seq[int], n: int): bool =
    ## Validates that the given solution is a valid n-queens solution
    ## where solution[i] represents the column position of the queen in row i

    # Check dimensions
    if solution.len != n:
        echo "❌ Invalid solution length: expected ", n, ", got ", solution.len
        return false

    # Check that all values are in valid range [0, n-1]
    for i, col in solution:
        if col < 0 or col >= n:
            echo "❌ Invalid column value at row ", i, ": ", col, " (expected 0..", n-1, ")"
            return false

    # Check column conflicts: no two queens in same column
    var usedColumns = initHashSet[int]()
    for i, col in solution:
        if col in usedColumns:
            echo "❌ Column conflict: queens at rows ", usedColumns, " and ", i, " both in column ", col
            return false
        usedColumns.incl(col)

    # Check main diagonal conflicts: no two queens on same main diagonal
    # Two queens are on same main diagonal if solution[i] - i == solution[j] - j
    var usedMainDiagonals = initHashSet[int]()
    for i, col in solution:
        let diagonalId = col - i
        if diagonalId in usedMainDiagonals:
            echo "❌ Main diagonal conflict: queen at row ", i, " conflicts with previous queen (diagonal ", diagonalId, ")"
            return false
        usedMainDiagonals.incl(diagonalId)

    # Check anti-diagonal conflicts: no two queens on same anti-diagonal  
    # Two queens are on same anti-diagonal if solution[i] + i == solution[j] + j
    var usedAntiDiagonals = initHashSet[int]()
    for i, col in solution:
        let diagonalId = col + i
        if diagonalId in usedAntiDiagonals:
            echo "❌ Anti-diagonal conflict: queen at row ", i, " conflicts with previous queen (diagonal ", diagonalId, ")"
            return false
        usedAntiDiagonals.incl(diagonalId)

    return true

suite "N-Queens Tests":
    test "4x4 N-Queens (expression-based constraints)":
        # Create constraint system (based on models/nQueens.nim)
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(0..<4))

        # Column constraint: no two queens in same column
        # Uses simple variable references - will be optimized to position-based
        var terms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<4:
            terms.add(x[i])
        sys.addConstraint(allDifferent(terms))

        # Main diagonal constraint: no two queens on same main diagonal
        # Uses expression-based constraints with x[i] - i
        terms.reset()
        for i in 0..<4:
            terms.add(x[i] - i)
        sys.addConstraint(allDifferent(terms))

        # Anti-diagonal constraint: no two queens on same anti-diagonal
        # Uses expression-based constraints with x[i] + i  
        terms.reset()
        for i in 0..<4:
            terms.add(x[i] + i)
        sys.addConstraint(allDifferent(terms))

        # Solve the constraint system
        sys.resolve()

        # Extract solution and validate
        let solution = x.assignment
        check validateNQueensSolution(solution, 4)