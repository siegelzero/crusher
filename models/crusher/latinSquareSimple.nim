import std/[os, sequtils, strutils]

import crusher


proc latinSquareSimple*(n: int) =
    # Latin Squares without symmetry breaking
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    X.setDomain(toSeq(1..n))  # Use 1-based domain like FlatZinc

    for row in X.rows():
        sys.addConstraint(allDifferent(row))
    
    for col in X.columns():
        sys.addConstraint(allDifferent(col))
        
    # No symmetry breaking constraints - just the all-different constraints

    sys.resolve()

    echo X


when isMainModule:
    let n = parseInt(paramStr(1))
    latinSquareSimple(n)