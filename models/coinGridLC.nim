import std/[os, sequtils, strutils]
import crusher


proc coingrid*(n, c: int) =
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    X.setDomain(toSeq 0..1)

    for column in X.columns():
        sys.addConstraint(sum(column) == c)

    for row in X.rows():
        sys.addConstraint(sum(row) == c)

    var objectiveTerms: seq[AlgebraicExpression[int]]
    for i in 0..<n:
        for j in 0..<n:
            if i != j:
                objectiveTerms.add(X[i, j]*(i - j)*(i - j))

    let objective = sum(objectiveTerms)
    sys.minimize(objective, parallel=true, verbose=true)


when isMainModule:
    let n = parseInt(paramStr(1))
    let c = parseInt(paramStr(2))
    coingrid(n, c)
