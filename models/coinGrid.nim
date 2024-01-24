import std/[os, sequtils, strutils]
import crusher


proc coingrid*(n, c: int) =
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    X.setDomain(toSeq 0..1)

    for column in X.columns():
        sys.addConstraint(linearCombinationEq(column, c))
    
    for row in X.rows():
        sys.addConstraint(linearCombinationEq(row, c))
    
    var objectiveTerms: seq[Expression[int]]
    for i in 0..<n:
        for j in 0..<n:
            if i != j:
                objectiveTerms.add(X[i, j]*(i - j)*(i - j))

    let objective = foldl(objectiveTerms, a + b)
    sys.minimize(objective)

    # doAssert assignment == @[0, 1, 1, 0, 0]
    # doAssert objective.evaluate(assignment) == 17


when isMainModule:
    let n = parseInt(paramStr(1))
    let c = parseInt(paramStr(2))
    coingrid(n, c)