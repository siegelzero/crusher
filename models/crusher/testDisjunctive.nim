import std/[os, sequtils, strformat]

import crusher

proc testDisjunctive*() =
    # Test disjunctive (OR) constraints
    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(3)
    x.setDomain(toSeq(1..10))
    
    # Test constraint: (x[0] < 3) OR (x[1] > 7)
    # This should allow solutions where either:
    # - x[0] is 1 or 2, OR
    # - x[1] is 8, 9, or 10
    let constraint1 = x[0] < 3
    let constraint2 = x[1] > 7
    let disjunctiveConstraint = constraint1 or constraint2
    
    sys.addConstraint(disjunctiveConstraint)
    
    # Add another constraint to make it more interesting
    sys.addConstraint(x[2] == 5)
    
    echo "Testing disjunctive constraint: (x[0] < 3) OR (x[1] > 7)"
    echo "With additional constraint: x[2] == 5"
    
    sys.resolve()
    
    if sys.assignment.len > 0:
        echo fmt"Solution found: x = [{x.assignment[0]}, {x.assignment[1]}, {x.assignment[2]}]"
        
        # Verify the disjunctive constraint
        let x0_less_3 = x.assignment[0] < 3
        let x1_greater_7 = x.assignment[1] > 7
        let disjunctive_satisfied = x0_less_3 or x1_greater_7
        
        echo fmt"x[0] < 3: {x0_less_3} (x[0] = {x.assignment[0]})"
        echo fmt"x[1] > 7: {x1_greater_7} (x[1] = {x.assignment[1]})"
        echo fmt"Disjunctive constraint satisfied: {disjunctive_satisfied}"
        echo fmt"x[2] == 5: {x.assignment[2] == 5}"
    else:
        echo "No solution found"

proc testConjunctive*() =
    # Test conjunctive (AND) constraints  
    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(2)
    x.setDomain(toSeq(1..10))
    
    # Test constraint: (x[0] > 3) AND (x[1] < 8)
    let constraint1 = x[0] > 3
    let constraint2 = x[1] < 8
    let conjunctiveConstraint = constraint1 and constraint2
    
    sys.addConstraint(conjunctiveConstraint)
    
    echo "\nTesting conjunctive constraint: (x[0] > 3) AND (x[1] < 8)"
    
    sys.resolve()
    
    if sys.assignment.len > 0:
        echo fmt"Solution found: x = [{x.assignment[0]}, {x.assignment[1]}]"
        
        # Verify the conjunctive constraint
        let x0_greater_3 = x.assignment[0] > 3
        let x1_less_8 = x.assignment[1] < 8
        let conjunctive_satisfied = x0_greater_3 and x1_less_8
        
        echo fmt"x[0] > 3: {x0_greater_3} (x[0] = {x.assignment[0]})"
        echo fmt"x[1] < 8: {x1_less_8} (x[1] = {x.assignment[1]})"
        echo fmt"Conjunctive constraint satisfied: {conjunctive_satisfied}"
    else:
        echo "No solution found"

when isMainModule:
    testDisjunctive()
    testConjunctive()