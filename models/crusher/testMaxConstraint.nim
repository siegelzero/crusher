import std/sequtils
import ../../src/crusher

# Test model for MaxConstraint functionality
# Find values such that max constraints are satisfied

proc testMaxConstraint() =
    echo "Testing MaxConstraint functionality..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(1..10))  # Domain 1 to 10
    
    # Create max constraint: max(vars) == 7
    let maxExpr = max(vars)
    sys.addConstraint(maxExpr == 7)
    
    echo "Constraint system created with max(vars) == 7"
    echo "Domain: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "vars = ", solution
    echo "max(vars) = ", max(solution)
    
    # Verify the constraint is satisfied
    let actualMax = max(solution)
    if actualMax == 7:
        echo "✓ Constraint satisfied: max(vars) = ", actualMax
    else:
        echo "✗ Constraint violated: max(vars) = ", actualMax, " ≠ 7"

proc testMaxConstraintGreaterEqual() =
    echo "\nTesting MaxConstraint with >= operator..."
    
    var sys = initConstraintSystem[int]()
    
    # Create four variables
    var vars = sys.newConstrainedSequence(4) 
    vars.setDomain(toSeq(3..8))  # Domain 3 to 8
    
    # Create max constraint: max(vars) >= 6
    let maxExpr = max(vars)
    sys.addConstraint(maxExpr >= 6)
    
    echo "Constraint system created with max(vars) >= 6"
    echo "Domain: [3, 4, 5, 6, 7, 8]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "vars = ", solution
    echo "max(vars) = ", max(solution)
    
    # Verify the constraint is satisfied
    let actualMax = max(solution)
    if actualMax >= 6:
        echo "✓ Constraint satisfied: max(vars) = ", actualMax, " >= 6"
    else:
        echo "✗ Constraint violated: max(vars) = ", actualMax, " < 6"

proc testMaxConstraintExpressions() =
    echo "\nTesting MaxConstraint with expressions..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(1..6))  # Domain 1 to 6
    
    # Create expressions: x+2, y*3, z-1
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x + 2, y * 3, z - 1]
    
    # Create max constraint: max(x+2, y*3, z-1) <= 12
    let maxExpr = max(expressions)
    sys.addConstraint(maxExpr <= 12)
    
    echo "Constraint system created with max(x+2, y*3, z-1) <= 12"
    echo "Domain for x,y,z: [1, 2, 3, 4, 5, 6]"
    echo "Expression values: x+2 in [3,8], y*3 in [3,18], z-1 in [0,5]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Calculate expression values
    let expr1 = solution[0] + 2  # x + 2
    let expr2 = solution[1] * 3  # y * 3  
    let expr3 = solution[2] - 1  # z - 1
    
    echo "Expression values: x+2 =", expr1, ", y*3 =", expr2, ", z-1 =", expr3
    let actualMax = max([expr1, expr2, expr3])
    echo "max(x+2, y*3, z-1) =", actualMax
    
    # Verify the constraint is satisfied
    if actualMax <= 12:
        echo "✓ Constraint satisfied: max =", actualMax, " <= 12"
    else:
        echo "✗ Constraint violated: max =", actualMax, " > 12"

proc testMaxConstraintExpressionsEquality() =
    echo "\nTesting MaxConstraint with expressions and equality..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(2..8))  # Domain 2 to 8
    
    # Create expressions: x*2, y+3, z-2
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x * 2, y + 3, z - 2]
    
    # Create max constraint: max(x*2, y+3, z-2) == 10
    let maxExpr = max(expressions)
    sys.addConstraint(maxExpr == 10)
    
    echo "Constraint system created with max(x*2, y+3, z-2) == 10"
    echo "Domain for x,y,z: [2, 3, 4, 5, 6, 7, 8]"
    echo "Expression values: x*2 in [4,16], y+3 in [5,11], z-2 in [0,6]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Calculate expression values
    let expr1 = solution[0] * 2  # x * 2
    let expr2 = solution[1] + 3  # y + 3  
    let expr3 = solution[2] - 2  # z - 2
    
    echo "Expression values: x*2 =", expr1, ", y+3 =", expr2, ", z-2 =", expr3
    let actualMax = max([expr1, expr2, expr3])
    echo "max(x*2, y+3, z-2) =", actualMax
    
    # Verify the constraint is satisfied
    if actualMax == 10:
        echo "✓ Constraint satisfied: max =", actualMax, " == 10"
    else:
        echo "✗ Constraint violated: max =", actualMax, " ≠ 10"

proc testMinMaxConstraintsCombined() =
    echo "\nTesting combined Min and Max constraints..."
    
    var sys = initConstraintSystem[int]()
    
    # Create four variables w, x, y, z
    var vars = sys.newConstrainedSequence(4)
    vars.setDomain(toSeq(3..9))  # Domain 3 to 9
    
    # Create min and max constraints on the same variables
    # min(vars) >= 4 AND max(vars) <= 7
    let minExpr = min(vars)
    let maxExpr = max(vars)
    sys.addConstraint(minExpr >= 4)
    sys.addConstraint(maxExpr <= 7)
    
    echo "Constraint system created with min(vars) >= 4 AND max(vars) <= 7"
    echo "Domain: [3, 4, 5, 6, 7, 8, 9]"
    echo "Looking for solution where all values are between 4 and 7..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "vars = ", solution
    
    let actualMin = min(solution)
    let actualMax = max(solution)
    echo "min(vars) = ", actualMin, ", max(vars) = ", actualMax
    
    # Verify both constraints are satisfied
    let minSatisfied = actualMin >= 4
    let maxSatisfied = actualMax <= 7
    
    if minSatisfied and maxSatisfied:
        echo "✓ Both constraints satisfied: min =", actualMin, " >= 4 AND max =", actualMax, " <= 7"
    else:
        if not minSatisfied:
            echo "✗ Min constraint violated: min =", actualMin, " < 4"
        if not maxSatisfied:
            echo "✗ Max constraint violated: max =", actualMax, " > 7"

when isMainModule:
    testMaxConstraint()
    testMaxConstraintGreaterEqual() 
    testMaxConstraintExpressions()
    testMaxConstraintExpressionsEquality()
    testMinMaxConstraintsCombined()