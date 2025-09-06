import std/[os, sequtils, strutils]

import crusher


proc magicSquare*(n: int) =
    # Magic Squares
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)

    let target = n*(n*n + 1) div 2

    # Row sums == target
    for row in X.rows():
        sys.addConstraint(row.foldl(a + b) == target)

    # Col sums == target
    for col in X.columns():
        sys.addConstraint(col.foldl(a + b) == target)

    # Diagonals
    var terms: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<n:
        terms.add(X[i, i])
    sys.addConstraint(terms.foldl(a + b) == target)

    terms = @[]
    for i in 0..<n:
        terms.add(X[i, n - i - 1])
    sys.addConstraint(terms.foldl(a + b) == target)

    # All entries in square must be distinct
    sys.addConstraint(allDifferent(X))
    X.setDomain(toSeq(1..n*n))

    sys.resolve()
    echo X


when isMainModule:
    let n = parseInt(paramStr(1))
    magicSquare(n)