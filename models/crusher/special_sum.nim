import std/sequtils

import crusher


proc specialSum*(N: int, terms: int) =
    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(terms)
    x.setDomain(toSeq(1..N))
    
    # Add constraint that sum equals N (using efficient linear combination)
    sys.addConstraint(sum(x) == N)
    
    # Add constraints that each variable is divisible by 2 or 5
    # Using gcd(x[i], 10) > 1 which is equivalent but more efficient than OR
    for i in 0..<terms:
        sys.addConstraint(commonFactor(x[i], 10))
    
    # Add constraint that values are in increasing order
    let increasingConstraints = increasing(x)
    for constraint in increasingConstraints:
        sys.addConstraint(constraint)
    
    sys.resolve()
    
    echo "Solution found:"
    for i in 0..<terms:
        echo "x", i+1, " = ", x.assignment[i]
    
    let sum = x.assignment[0..<terms].foldl(a + b)
    echo "Sum = ", sum


when isMainModule:
    import std/[os, strutils]
    let N = if paramCount() > 0: parseInt(paramStr(1)) else: 100
    let numTerms = if paramCount() > 1: parseInt(paramStr(2)) else: 5
    specialSum(N, numTerms)
