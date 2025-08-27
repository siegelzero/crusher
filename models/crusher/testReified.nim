import std/[os, sequtils, strformat, tables]

import crusher

proc testReified*() =
    # Test reified constraints: boolean variables that are true iff constraints hold
    var sys = initConstraintSystem[int]()
    
    # Create integer variables
    var x = sys.newConstrainedSequence(2)
    x.setDomain(toSeq(1..10))
    
    # Create boolean variables (domain [0, 1] following FlatZinc conventions)
    var b = sys.newConstrainedSequence(3) 
    b.setDomain([0, 1])
    
    # Test reified equality: b[0] ↔ (x[0] == x[1])
    # This means b[0] is true (1) iff x[0] equals x[1]
    sys.addConstraint(reifyEq(b[0], x[0], x[1]))
    
    # Test reified inequality: b[1] ↔ (x[0] > 5)
    # This means b[1] is true (1) iff x[0] is greater than 5
    sys.addConstraint(reifyGt(b[1], x[0], 5))
    
    # Test general reified constraint: b[2] ↔ (x[0] + x[1] <= 12)
    # This means b[2] is true (1) iff the sum of x[0] and x[1] is at most 12
    let sumConstraint = x[0] + x[1] <= 12
    sys.addConstraint(reify(b[2], sumConstraint))
    
    # Force at least one boolean to be true for interesting solutions
    sys.addConstraint(b[0] + b[1] + b[2] >= 1)
    
    echo "Testing reified constraints:"
    echo "b[0] ↔ (x[0] == x[1])     # b[0] true iff x[0] equals x[1]"
    echo "b[1] ↔ (x[0] > 5)         # b[1] true iff x[0] greater than 5"
    echo "b[2] ↔ (x[0] + x[1] <= 12) # b[2] true iff sum at most 12"
    echo "At least one boolean must be true"
    echo ""
    
    sys.resolve()
    
    if sys.assignment.len > 0:
        let x0 = x.assignment[0]
        let x1 = x.assignment[1]
        let b0 = b.assignment[0]
        let b1 = b.assignment[1] 
        let b2 = b.assignment[2]
        
        echo fmt"Solution found:"
        echo fmt"x = [{x0}, {x1}]"
        echo fmt"b = [{b0}, {b1}, {b2}]"
        echo ""
        
        # Verify the reified constraints
        let x0_eq_x1 = (x0 == x1)
        let x0_gt_5 = (x0 > 5)
        let sum_le_12 = (x0 + x1 <= 12)
        
        echo "Verification:"
        echo fmt"x[0] == x[1]: {x0_eq_x1} -> b[0] should be {(if x0_eq_x1: 1 else: 0)}, actual: {b0}"
        echo fmt"x[0] > 5: {x0_gt_5} -> b[1] should be {(if x0_gt_5: 1 else: 0)}, actual: {b1}"  
        echo fmt"x[0] + x[1] <= 12: {sum_le_12} -> b[2] should be {(if sum_le_12: 1 else: 0)}, actual: {b2}"
        
        # Verify correctness
        let correct0 = (b0 == (if x0_eq_x1: 1 else: 0))
        let correct1 = (b1 == (if x0_gt_5: 1 else: 0))  
        let correct2 = (b2 == (if sum_le_12: 1 else: 0))
        
        echo fmt"All reified constraints satisfied: {correct0 and correct1 and correct2}"
    else:
        echo "No solution found"

proc testReifiedChoice*() =
    # Simpler example: Use reified constraints for implication
    var sys = initConstraintSystem[int]()
    
    var x = sys.newConstrainedSequence(2)
    x.setDomain(toSeq(1..10))
    
    var isLarge = sys.newConstrainedSequence(1)
    isLarge.setDomain([0, 1])  # Boolean variable
    
    # isLarge is true iff x[0] > 5
    sys.addConstraint(reifyGt(isLarge[0], x[0], 5))
    
    # If x[0] is large, then x[1] must be small (≤ 3)
    # This is: isLarge[0] == 1 -> x[1] <= 3
    # Equivalent to: not isLarge[0] or x[1] <= 3
    let isLargeTrue = isLarge[0] == 1
    let x1Small = x[1] <= 3
    sys.addConstraint(not isLargeTrue or x1Small)
    
    echo "\nTesting reified implication:"
    echo "isLarge ↔ (x[0] > 5)"
    echo "isLarge -> (x[1] <= 3)  # If x[0] is large, x[1] must be small"
    echo ""
    
    sys.resolve()
    
    if sys.assignment.len > 0:
        let x0 = x.assignment[0]
        let x1 = x.assignment[1]
        let large = isLarge.assignment[0]
        
        echo fmt"Solution found:"
        echo fmt"x = [{x0}, {x1}]"
        echo fmt"isLarge = {large}"
        
        let x0_gt_5 = (x0 > 5)
        let implication_satisfied = (large == 0) or (x1 <= 3)
        
        echo fmt"x[0] > 5: {x0_gt_5} -> isLarge should be {(if x0_gt_5: 1 else: 0)}, actual: {large}"
        echo fmt"Implication (isLarge -> x[1] <= 3): {implication_satisfied}"
        echo fmt"All constraints satisfied: {(large == (if x0_gt_5: 1 else: 0)) and implication_satisfied}"
    else:
        echo "No solution found"

proc testReifiedLinear*() =
    # Test reified linear constraints with LinearCombination
    var sys = initConstraintSystem[int]()
    
    # Create integer variables
    var x = sys.newConstrainedSequence(3)
    x.setDomain(toSeq(1..10))
    
    # Create boolean variable
    var b = sys.newConstrainedSequence(1)
    b.setDomain([0, 1])
    
    # Create a LinearCombination: 2*x[0] + 3*x[1] - x[2]
    var coeffs = initTable[int, int]()
    coeffs[x[0].node.position] = 2
    coeffs[x[1].node.position] = 3  
    coeffs[x[2].node.position] = -1
    let linearComb = newLinearCombination(coeffs, 0)  # 2*x[0] + 3*x[1] - x[2] + 0
    
    # Test reified linear equality: b[0] ↔ (2*x[0] + 3*x[1] - x[2] == 5)
    sys.addConstraint(reifyLinEq(b[0], linearComb, 5))
    
    # Add some bounds to make it solvable
    sys.addConstraint(x[0] >= 1)
    sys.addConstraint(x[1] >= 1)
    sys.addConstraint(x[2] >= 1)
    sys.addConstraint(x[0] <= 5)
    sys.addConstraint(x[1] <= 5)
    sys.addConstraint(x[2] <= 8)
    
    echo "\nTesting reified linear constraint:"
    echo "b[0] ↔ (2*x[0] + 3*x[1] - x[2] == 5)"
    echo "With bounds: 1 ≤ x[i] ≤ 5 for i=0,1 and 1 ≤ x[2] ≤ 8"
    echo ""
    
    sys.resolve()
    
    if sys.assignment.len > 0:
        let x0 = x.assignment[0]
        let x1 = x.assignment[1]
        let x2 = x.assignment[2]
        let b0 = b.assignment[0]
        
        echo fmt"Solution found:"
        echo fmt"x = [{x0}, {x1}, {x2}]"
        echo fmt"b = [{b0}]"
        echo ""
        
        # Verify the reified linear constraint
        let linearValue = 2*x0 + 3*x1 - x2
        let linearSatisfied = (linearValue == 5)
        
        echo fmt"Linear combination value: 2*{x0} + 3*{x1} - {x2} = {linearValue}"
        echo fmt"Linear constraint (== 5): {linearSatisfied}"
        echo fmt"Boolean variable b[0]: {b0}"
        echo fmt"Reified constraint satisfied: {(b0 == 1 and linearSatisfied) or (b0 == 0 and not linearSatisfied)}"
    else:
        echo "No solution found"

when isMainModule:
    testReified()
    testReifiedChoice()
    testReifiedLinear()