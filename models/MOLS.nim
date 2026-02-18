import std/[os, sequtils, strutils]

import crusher


proc MOLSSystem*(n: int) =
    # Mutually Orthogonal Latin Squares
    # Uses matrixElement formulation: Z[i, X[i,j]] == Y[i,j]
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    var Y = sys.newConstrainedMatrix(n, n)
    var Z = sys.newConstrainedMatrix(n, n)

    X.setDomain(toSeq(0..<n))
    Y.setDomain(toSeq(0..<n))
    Z.setDomain(toSeq(0..<n))

    # X, Y, Z are all Latin squares
    for row in X.rows():
        sys.addConstraint(allDifferent(row))
    for row in Y.rows():
        sys.addConstraint(allDifferent(row))
    for row in Z.rows():
        sys.addConstraint(allDifferent(row))
    for col in X.columns():
        sys.addConstraint(allDifferent(col))
    for col in Y.columns():
        sys.addConstraint(allDifferent(col))
    for col in Z.columns():
        sys.addConstraint(allDifferent(col))

    # Symmetry breaking
    for i in 0..<n:
        sys.addConstraint(X[0, i] == i)
        sys.addConstraint(X[i, 0] == i)
        sys.addConstraint(Y[0, i] == i)
    for i in 1..<n:
        sys.addConstraint(Y[i, 0] <= i + 1)
        sys.addConstraint(Y[i, 0] != i)

    # Orthogonality via matrixElement: Z[i, X[i,j]] == Y[i,j]
    for i in 0..<n:
        for j in 0..<n:
            sys.addConstraint(matrixElement(Z, i, X[i, j], Y[i, j]))

    sys.resolve(10000, parallel=true, verbose=false)

    for row in X.assignment():
        echo row

    echo ""

    for row in Y.assignment():
        echo row


when isMainModule:
    let n = parseInt(paramStr(1))
    MOLSSystem(n)
