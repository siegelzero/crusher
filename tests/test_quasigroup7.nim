import unittest
import std/[sequtils, sets, strutils, os, tables]

import crusher
import flatzinc/[parser, translator, output]

proc validateQuasigroup7(matrix: seq[seq[int]], n: int): bool =
    ## Validates that the given n×n matrix satisfies quasigroup7 constraints:
    ## 1. Latin square (each value 0..n-1 appears once per row and column)
    ## 2. Idempotent: matrix[i,i] == i
    ## 3. Axiom 7: matrix[i, matrix[j,i]] == matrix[matrix[j,i], j]

    # Check dimensions
    if matrix.len != n:
        echo "Invalid number of rows: expected ", n, ", got ", matrix.len
        return false
    for i, row in matrix:
        if row.len != n:
            echo "Invalid number of columns in row ", i
            return false

    # Check Latin square: each row and column has all values 0..n-1
    let expected = toSeq(0..<n).toHashSet()
    for i in 0..<n:
        if matrix[i].toHashSet() != expected:
            echo "Row ", i, " doesn't contain all values: ", matrix[i]
            return false
        var col = initHashSet[int]()
        for j in 0..<n:
            col.incl(matrix[j][i])
        if col != expected:
            echo "Column ", i, " doesn't contain all values"
            return false

    # Check idempotent: matrix[i,i] == i
    for i in 0..<n:
        if matrix[i][i] != i:
            echo "Not idempotent at [", i, ",", i, "]: expected ", i, ", got ", matrix[i][i]
            return false

    # Check axiom 7: matrix[i, matrix[j,i]] == matrix[matrix[j,i], j]
    for i in 0..<n:
        for j in 0..<n:
            let ji = matrix[j][i]
            let lhs = matrix[i][ji]
            let rhs = matrix[ji][j]
            if lhs != rhs:
                echo "Axiom 7 violated at i=", i, " j=", j,
                     ": matrix[", i, ",", ji, "]=", lhs,
                     " != matrix[", ji, ",", j, "]=", rhs
                return false

    return true

suite "Quasigroup7 Tests":

    test "quasigroup7 n=5 via FlatZinc pipeline":
        # Compile with MiniZinc
        let fznPath = "/tmp/qg7_test_5.fzn"
        let mznPath = "minizinc_challenge/2008/quasigroup7/quasigroup7.mzn"
        let solverPath = os.getCurrentDir() / "minizinc"

        let cmd = "MZN_SOLVER_PATH=" & solverPath &
                  " minizinc --compile --solver crusher" &
                  " -D \"n=5\" " & mznPath & " -o " & fznPath & " 2>/dev/null"
        let exitCode = execShellCmd(cmd)
        check exitCode == 0

        # Parse and translate
        let model = parseFznFile(fznPath)
        var tr = translate(model)

        # Verify matrix element detection happened (matrixInfos populated)
        var hasMatrixInfo = false
        for k, v in tr.matrixInfos:
            hasMatrixInfo = true
            break
        check hasMatrixInfo

        # Solve
        tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

        # Extract solution as 5x5 matrix
        let n = 5
        # Find the output array
        check tr.outputArrays.len > 0
        let oa = tr.outputArrays[0]
        let positions = tr.arrayPositions[oa.name]
        check positions.len == n * n

        var flat = newSeq[int](n * n)
        for i, pos in positions:
            flat[i] = tr.sys.assignment[pos]

        var matrix = newSeq[seq[int]](n)
        for i in 0..<n:
            matrix[i] = flat[i * n ..< (i + 1) * n]

        check validateQuasigroup7(matrix, n)

    test "quasigroup7 n=5 native API":
        let n = 5
        var sys = initConstraintSystem[int]()
        var qg = sys.newConstrainedMatrix(n, n)
        qg.setDomain(toSeq(0..<n))

        # All rows different
        for row in qg.rows():
            sys.addConstraint(allDifferent(row))

        # All columns different
        for col in qg.columns():
            sys.addConstraint(allDifferent(col))

        # Idempotent: qg[i,i] = i
        for i in 0..<n:
            sys.addConstraint(qg[i, i] == i)

        # Axiom 7: qg[i, qg[j,i]] = qg[qg[j,i], j]
        # Use the native matrixElement API with ConstrainedMatrix
        for i in 0..<n:
            for j in 0..<n:
                # qg[j,i] is a variable expression
                let jiExpr = qg[j, i]

                # LHS: qg[i, qg[j,i]] — row=i (constant), col=qg[j,i] (variable)
                let lhsVar = sys.newConstrainedVariable()
                lhsVar.setDomain(toSeq(0..<n))
                sys.addConstraint(matrixElement(qg, i, jiExpr, lhsVar.value))

                # RHS: qg[qg[j,i], j] — row=qg[j,i] (variable), col=j (constant)
                let rhsVar = sys.newConstrainedVariable()
                rhsVar.setDomain(toSeq(0..<n))
                sys.addConstraint(matrixElement(qg, jiExpr, j, rhsVar.value))

                # LHS == RHS
                sys.addConstraint(lhsVar == rhsVar)

        # Implied constraint: qg[i, n-1] + 2 >= i
        for i in 0..<n:
            sys.addConstraint(qg[i, n - 1] >= i - 2)

        sys.resolve(parallel = true, tabuThreshold = 20000, verbose = false)

        # Extract solution
        let assignment = qg.assignment
        check validateQuasigroup7(assignment, n)
