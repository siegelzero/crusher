import std/[os, sequtils, strutils]

import crusher


proc MOLSSystem*(n: int) =
    # Mutually Orthogonal Latin Squares
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

    sys.resolve(10000, parallel=true, verbose=false)

    for row in X.assignment():
        echo row

    echo ""

    for row in Y.assignment():
        echo row


when isMainModule:
    let n = parseInt(paramStr(1))
    MOLSSystem(n)
