import std/[sequtils, unittest, tables]
import crusher

suite "Linear Constraint Tests":
    test "Position-based vs Expression-based Linear Constraints":
        # Create constraint system
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..5))

        # Position-based constraint: simple sum using RefNodes
        # This should be optimized to position-based mode
        var simpleTerms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<3:
            simpleTerms.add(x[i])  # RefNodes only -> position-based optimization
        sys.addConstraint(sum(simpleTerms) == 9)

        # Expression-based constraint: multi-variable summands  
        # This should trigger expression-based mode due to complex terms
        var complexTerms: seq[AlgebraicExpression[int]] = @[]
        complexTerms.add(x[0] + x[1])    # Multi-variable term: positions {0,1}
        complexTerms.add(x[1] - x[2])    # Multi-variable term: positions {1,2}
        complexTerms.add(2 * x[0])       # Single variable with coefficient
        sys.addConstraint(sum(complexTerms) <= 12)

        # Solve the constraint system
        sys.resolve()

        # Extract and validate solution
        let solution = x.assignment
        
        # Validate position-based constraint: x[0] + x[1] + x[2] == 9
        let sumCheck = solution[0] + solution[1] + solution[2]
        check sumCheck == 9
        
        # Validate expression-based constraint: (x[0] + x[1]) + (x[1] - x[2]) + (2*x[0]) <= 12
        let complexSum = (solution[0] + solution[1]) + (solution[1] - solution[2]) + (2 * solution[0])
        check complexSum <= 12

    test "Direct SumExpression Constructor Tests":
        # Test the direct SumExpression constructors
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3) 
        x.setDomain(toSeq(0..5))

        # Position-based: unit coefficients using position array
        let positionBased = newSumExpression[int]([0, 1, 2])  # All coefficients = 1
        sys.addConstraint(positionBased == 9)

        # Expression-based: custom coefficients using coefficient table
        var coeffs = initTable[int, int]()
        coeffs[0] = 3   # 3*x[0]
        coeffs[1] = 1   # 1*x[1] 
        coeffs[2] = -1  # -1*x[2]
        let coefficientBased = newSumExpression[int](coeffs, 0)  # No constant term
        sys.addConstraint(coefficientBased <= 12)

        # Solve the constraint system
        sys.resolve()

        # Extract and validate solution
        let solution = x.assignment
        
        # Validate constraints
        check solution[0] + solution[1] + solution[2] == 9
        check 3 * solution[0] + solution[1] - solution[2] <= 12