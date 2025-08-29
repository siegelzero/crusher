import std/[os, sequtils, strutils, tables]

import crusher

proc testGlobalCardinality*() =
    # Simple test: 4 variables where exactly 2 should be value 1, and 2 should be value 2
    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(4)
    x.setDomain(toSeq(1..2))  # Domain: {1, 2}

    # Create cardinality constraint: exactly 2 ones and 2 twos
    let cardinalities = {1: 2, 2: 2}.toTable
    sys.addConstraint(globalCardinality(x, cardinalities))

    echo "Testing GlobalCardinality constraint:"
    echo "4 variables with domain {1, 2}"
    echo "Cardinalities: 1 appears 2 times, 2 appears 2 times"
    
    sys.resolve()
    echo "Solution: ", x
    
    # Verify the solution
    let solution = x.assignment
    var counts = {1: 0, 2: 0}.toTable
    for val in solution:
        counts[val] += 1
    
    echo "Actual counts:"
    for val, count in counts.pairs:
        echo "  Value ", val, ": ", count, " times"

when isMainModule:
    testGlobalCardinality()