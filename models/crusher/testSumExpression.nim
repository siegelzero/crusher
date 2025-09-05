import std/sequtils
import ../../src/crusher

# Test model for SumExpression functionality
# Test both position-based and expression-based sum constraints

proc testSumPositionBased() =
    echo "Testing SumExpression with position-based (simple variables)..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(1..8))  # Domain 1 to 8
    
    # Create simple variable expressions 
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x, y, z]
    
    # Create sum constraint: sum(x, y, z) == 12
    let sumExpr = sum(expressions)
    sys.addConstraint(sumExpr == 12)
    
    echo "Constraint system created with sum(x, y, z) == 12"
    echo "Domain: [1, 2, 3, 4, 5, 6, 7, 8]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Verify the constraint is satisfied
    let actualSum = solution[0] + solution[1] + solution[2]
    echo "sum(x, y, z) =", actualSum
    
    if actualSum == 12:
        echo "✓ Constraint satisfied: sum =", actualSum, " == 12"
    else:
        echo "✗ Constraint violated: sum =", actualSum, " ≠ 12"

proc testSumExpressionBased() =
    echo "\nTesting SumExpression with expression-based (complex expressions)..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(1..6))  # Domain 1 to 6
    
    # Create complex expressions: x+2, y*2, z-1
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x + 2, y * 2, z - 1]
    
    # Create sum constraint: sum(x+2, y*2, z-1) <= 15
    let sumExpr = sum(expressions)
    sys.addConstraint(sumExpr <= 15)
    
    echo "Constraint system created with sum(x+2, y*2, z-1) <= 15"
    echo "Domain for x,y,z: [1, 2, 3, 4, 5, 6]"
    echo "Expression values: x+2 in [3,8], y*2 in [2,12], z-1 in [0,5]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Calculate expression values
    let expr1 = solution[0] + 2  # x + 2
    let expr2 = solution[1] * 2  # y * 2  
    let expr3 = solution[2] - 1  # z - 1
    
    echo "Expression values: x+2 =", expr1, ", y*2 =", expr2, ", z-1 =", expr3
    let actualSum = expr1 + expr2 + expr3
    echo "sum(x+2, y*2, z-1) =", actualSum
    
    # Verify the constraint is satisfied
    if actualSum <= 15:
        echo "✓ Constraint satisfied: sum =", actualSum, " <= 15"
    else:
        echo "✗ Constraint violated: sum =", actualSum, " > 15"

proc testSumExpressionEquality() =
    echo "\nTesting SumExpression with expressions and equality..."
    
    var sys = initConstraintSystem[int]()
    
    # Create three variables x, y, z
    var vars = sys.newConstrainedSequence(3)
    vars.setDomain(toSeq(2..7))  # Domain 2 to 7
    
    # Create expressions: x-1, y+1, z*2
    let x = vars[0]
    let y = vars[1] 
    let z = vars[2]
    let expressions = @[x - 1, y + 1, z * 2]
    
    # Create sum constraint: sum(x-1, y+1, z*2) == 18
    let sumExpr = sum(expressions)
    sys.addConstraint(sumExpr == 18)
    
    echo "Constraint system created with sum(x-1, y+1, z*2) == 18"
    echo "Domain for x,y,z: [2, 3, 4, 5, 6, 7]"
    echo "Expression values: x-1 in [1,6], y+1 in [3,8], z*2 in [4,14]"
    echo "Looking for solution..."
    
    sys.resolve()
    
    let solution = vars.assignment()
    echo "Solution found:"
    echo "x =", solution[0], ", y =", solution[1], ", z =", solution[2]
    
    # Calculate expression values
    let expr1 = solution[0] - 1  # x - 1
    let expr2 = solution[1] + 1  # y + 1  
    let expr3 = solution[2] * 2  # z * 2
    
    echo "Expression values: x-1 =", expr1, ", y+1 =", expr2, ", z*2 =", expr3
    let actualSum = expr1 + expr2 + expr3
    echo "sum(x-1, y+1, z*2) =", actualSum
    
    # Verify the constraint is satisfied
    if actualSum == 18:
        echo "✓ Constraint satisfied: sum =", actualSum, " == 18"
    else:
        echo "✗ Constraint violated: sum =", actualSum, " ≠ 18"

when isMainModule:
    testSumPositionBased()
    testSumExpressionBased()
    testSumExpressionEquality()