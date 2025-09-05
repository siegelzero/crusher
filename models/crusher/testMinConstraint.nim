import std/sequtils
import ../../src/crusher

# Test model for MinConstraint functionality
# Find values for x, y, z such that min(x, y, z) == 5

proc testMinConstraint() =
    echo "Testing MinConstraint functionality..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(1..10))  # Domain 1 to 10
    
    # Create min constraint: min(vars) == 5
    let minExpr = min(vars)
    sys.addConstraint(minExpr == 5)
    
    echo "Constraint system created with min(vars) == 5"
    echo "Domain: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "vars = ", solution
    echo "min(vars) = ", min(solution)
    
    # Verify the constraint is satisfied
    let actualMin = min(solution)
    if actualMin == 5:
        echo "✓ Constraint satisfied: min(vars) = ", actualMin
    else:
        echo "✗ Constraint violated: min(vars) = ", actualMin, " ≠ 5"

proc testMinConstraintLessEqual() =
    echo "\nTesting MinConstraint with <= operator..."
    
    var sys = initConstraintSystem[int]()
    
    # Create four variables
    var vars = sys.newConstrainedSequence(4) 
    vars.setDomain(toSeq(5..12))  # Domain 5 to 12
    
    # Create min constraint: min(vars) <= 7
    let minExpr = min(vars)
    sys.addConstraint(minExpr <= 7)
    
    echo "Constraint system created with min(vars) <= 7"
    echo "Domain: [5, 6, 7, 8, 9, 10, 11, 12]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "vars = ", solution
    echo "min(vars) = ", min(solution)
    
    # Verify the constraint is satisfied
    let actualMin = min(solution)
    if actualMin <= 7:
        echo "✓ Constraint satisfied: min(vars) = ", actualMin, " <= 7"
    else:
        echo "✗ Constraint violated: min(vars) = ", actualMin, " > 7"

proc testMinConstraintExpressions() =
    echo "\nTesting MinConstraint with expressions..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(1..6))  # Domain 1 to 6
    
    # Create expressions: x+1, y*2, z-1
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x + 1, y * 2, z - 1]
    
    # Create min constraint: min(x+1, y*2, z-1) >= 4
    let minExpr = min(expressions)
    sys.addConstraint(minExpr >= 4)
    
    echo "Constraint system created with min(x+1, y*2, z-1) >= 4"
    echo "Domain for x,y,z: [1, 2, 3, 4, 5, 6]"
    echo "Expression values: x+1 in [2,7], y*2 in [2,12], z-1 in [0,5]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Calculate expression values
    let expr1 = solution[0] + 1  # x + 1
    let expr2 = solution[1] * 2  # y * 2  
    let expr3 = solution[2] - 1  # z - 1
    
    echo "Expression values: x+1 =", expr1, ", y*2 =", expr2, ", z-1 =", expr3
    let actualMin = min([expr1, expr2, expr3])
    echo "min(x+1, y*2, z-1) =", actualMin
    
    # Verify the constraint is satisfied
    if actualMin >= 4:
        echo "✓ Constraint satisfied: min =", actualMin, " >= 4"
    else:
        echo "✗ Constraint violated: min =", actualMin, " < 4"

proc testMinConstraintExpressionsEquality() =
    echo "\nTesting MinConstraint with expressions and equality..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(2..8))  # Domain 2 to 8
    
    # Create expressions: x-1, y+2, z*2
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x - 1, y + 2, z * 2]
    
    # Create min constraint: min(x-1, y+2, z*2) == 6
    let minExpr = min(expressions)
    sys.addConstraint(minExpr == 6)
    
    echo "Constraint system created with min(x-1, y+2, z*2) == 6"
    echo "Domain for x,y,z: [2, 3, 4, 5, 6, 7, 8]"
    echo "Expression values: x-1 in [1,7], y+2 in [4,10], z*2 in [4,16]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Calculate expression values
    let expr1 = solution[0] - 1  # x - 1
    let expr2 = solution[1] + 2  # y + 2  
    let expr3 = solution[2] * 2  # z * 2
    
    echo "Expression values: x-1 =", expr1, ", y+2 =", expr2, ", z*2 =", expr3
    let actualMin = min([expr1, expr2, expr3])
    echo "min(x-1, y+2, z*2) =", actualMin
    
    # Verify the constraint is satisfied
    if actualMin == 6:
        echo "✓ Constraint satisfied: min =", actualMin, " == 6"
    else:
        echo "✗ Constraint violated: min =", actualMin, " ≠ 6"

when isMainModule:
    testMinConstraint()
    testMinConstraintLessEqual() 
    testMinConstraintExpressions()
    testMinConstraintExpressionsEquality()