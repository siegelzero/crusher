import std/[os, sequtils, strutils]

import crusher


proc latinSquare*(n: int) =
    # Latin Squares
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    X.setDomain(toSeq(0..<n))

    for row in X.rows():
        sys.addConstraint(allDifferent(row))

    for col in X.columns():
        sys.addConstraint(allDifferent(col))

    # First row in order 0 1 2...
    for i in 0..<n:
        sys.addConstraint(X[0, i] == i)

    # First col in order 0 1 2...
    for i in 0..<n:
        sys.addConstraint(X[i, 0] == i)

    sys.resolve(parallel=true, verbose=true)

    echo X


when isMainModule:
    let n = parseInt(paramStr(1))
    latinSquare(n)
