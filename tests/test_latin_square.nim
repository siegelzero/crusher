import std/[sequtils, strutils, sets, unittest]
import crusher

proc validateLatinSquare(matrix: seq[seq[int]], n: int): bool =
    ## Validates that the given matrix is a valid n×n latin square
    
    # Check dimensions
    if matrix.len != n:
        echo "❌ Invalid number of rows: expected ", n, ", got ", matrix.len
        return false
        
    for i, row in matrix:
        if row.len != n:
            echo "❌ Invalid number of columns in row ", i, ": expected ", n, ", got ", row.len
            return false
    
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
    
    # Check canonical first row and column (as per the model)
    let expectedFirstRow = toSeq(0..<n)
    if matrix[0] != expectedFirstRow:
        echo "❌ First row should be ", expectedFirstRow, ", got ", matrix[0]
        return false
        
    for i in 0..<n:
        if matrix[i][0] != i:
            echo "❌ First column should be in order 0,1,2..., but matrix[", i, "][0] = ", matrix[i][0]
            return false
    
    return true

suite "Latin Square Tests":
    test "4x4 Latin Square generation":
        # Create constraint system (based on models/latinSquare.nim)
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedMatrix(4, 4)
        X.setDomain(toSeq(0..<4))

        # Add constraints
        for row in X.rows():
            sys.addConstraint(allDifferent(row))

        for col in X.columns():
            sys.addConstraint(allDifferent(col))

        # First row in order 0 1 2 3
        for i in 0..<4:
            sys.addConstraint(X[0, i] == i)

        # First col in order 0 1 2 3
        for i in 0..<4:
            sys.addConstraint(X[i, 0] == i)

        # Solve the constraint system
        sys.resolve()

        # Extract solution matrix using the assignment method on ConstrainedMatrix
        let solution = X.assignment

        # Validate the solution
        check validateLatinSquare(solution, 4)