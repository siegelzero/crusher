import std/[sequtils, unittest, tables]
import crusher

suite "Min/Max Constraint Tests":
    test "Min Constraint with Constant Target - Position-based":
        # Test min constraint with simple variable references (position-based optimization)
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..10))

        # Create min constraint: min(x[0], x[1], x[2]) == 3
        var terms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<3:
            terms.add(x[i])  # RefNodes only -> position-based optimization
        sys.addConstraint(min(terms) == 3)

        # Add additional constraints to ensure we get a valid solution
        sys.addConstraint(x[0] >= 3)
        sys.addConstraint(x[1] >= 3)
        sys.addConstraint(x[2] >= 3)

        sys.resolve()
        let solution = x.assignment

        # Verify min constraint: at least one variable should be 3
        let actualMin = min([solution[0], solution[1], solution[2]])
        check actualMin == 3

        # Verify all variables are >= 3
        check solution[0] >= 3
        check solution[1] >= 3
        check solution[2] >= 3

    test "Max Constraint with Constant Target - Position-based":
        # Test max constraint with simple variable references
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..8))

        # Create max constraint: max(x[0], x[1], x[2]) == 6
        var terms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<3:
            terms.add(x[i])
        sys.addConstraint(max(terms) == 6)

        # Add constraints to ensure we get a valid solution
        sys.addConstraint(x[0] <= 6)
        sys.addConstraint(x[1] <= 6)
        sys.addConstraint(x[2] <= 6)

        sys.resolve()
        let solution = x.assignment

        # Verify max constraint: at least one variable should be 6
        let actualMax = max([solution[0], solution[1], solution[2]])
        check actualMax == 6

        # Verify all variables are <= 6
        check solution[0] <= 6
        check solution[1] <= 6
        check solution[2] <= 6

    test "Min Constraint with Constant Target - Expression-based":
        # Test min constraint with complex expressions (expression-based mode)
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(0..10))

        # Create complex expressions for min constraint
        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])    # Multi-variable term
        terms.add(x[1] - x[2])    # Multi-variable term
        terms.add(2 * x[3])       # Single variable with coefficient

        # min(x[0]+x[1], x[1]-x[2], 2*x[3]) == 4
        sys.addConstraint(min(terms) == 4)

        # Add constraints to ensure valid solution space
        sys.addConstraint(x[0] >= 1)
        sys.addConstraint(x[1] >= 3)
        sys.addConstraint(x[2] >= 0)
        sys.addConstraint(x[3] >= 2)

        sys.resolve()
        let solution = x.assignment

        # Verify min constraint
        let term1 = solution[0] + solution[1]
        let term2 = solution[1] - solution[2]
        let term3 = 2 * solution[3]
        let actualMin = min([term1, term2, term3])
        check actualMin == 4

    test "Max Constraint with Constant Target - Expression-based":
        # Test max constraint with complex expressions
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(0..8))

        # Create complex expressions for max constraint
        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])    # Multi-variable term
        terms.add(x[1] + x[2])    # Multi-variable term
        terms.add(3 * x[3])       # Single variable with coefficient

        # max(x[0]+x[1], x[1]+x[2], 3*x[3]) == 10
        sys.addConstraint(max(terms) == 10)

        # Add constraints to ensure valid solution space
        sys.addConstraint(x[0] <= 5)
        sys.addConstraint(x[1] <= 5)
        sys.addConstraint(x[2] <= 5)
        sys.addConstraint(x[3] <= 3)

        sys.resolve()
        let solution = x.assignment

        # Verify max constraint
        let term1 = solution[0] + solution[1]
        let term2 = solution[1] + solution[2]
        let term3 = 3 * solution[3]
        let actualMax = max([term1, term2, term3])
        check actualMax == 10

    test "Min Constraint with Variable Target":
        # Test min constraint where the target is another variable
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..8))

        # Simple case: min(x[0], x[1]) == x[2]
        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0])
        terms.add(x[1])
        sys.addConstraint(min(terms) == x[2])

        # Fix values to ensure deterministic result
        sys.addConstraint(x[0] == 5)  # Higher value
        sys.addConstraint(x[1] == 3)  # Lower value (will be the minimum)

        sys.resolve()
        let solution = x.assignment

        # Verify the constraint: x[2] should equal min(x[0], x[1]) = min(5, 3) = 3
        let expectedMin = min([solution[0], solution[1]])
        check solution[2] == expectedMin
        check solution[0] == 5
        check solution[1] == 3
        check solution[2] == 3

    test "Max Constraint with Variable Target":
        # Test max constraint where the target is another variable
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..8))

        # Simple case: max(x[0], x[1]) == x[2]
        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0])
        terms.add(x[1])
        sys.addConstraint(max(terms) == x[2])

        # Fix values to ensure deterministic result
        sys.addConstraint(x[0] == 3)  # Lower value
        sys.addConstraint(x[1] == 7)  # Higher value (will be the maximum)

        sys.resolve()
        let solution = x.assignment

        # Verify the constraint: x[2] should equal max(x[0], x[1]) = max(3, 7) = 7
        let expectedMax = max([solution[0], solution[1]])
        check solution[2] == expectedMax
        check solution[0] == 3
        check solution[1] == 7
        check solution[2] == 7

    test "Combined Min/Max Constraints":
        # Test combining min and max constraints in the same problem
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(7)  # Add one more variable for auxiliary
        x.setDomain(toSeq(1..10))

        # Fix specific values to ensure deterministic behavior
        sys.addConstraint(x[0] == 3)  # Lower value
        sys.addConstraint(x[1] == 5)  # Higher value
        sys.addConstraint(x[2] == 6)  # Will be used for max constraint
        sys.addConstraint(x[3] == 4)  # Lower value for max constraint
        sys.addConstraint(x[4] == 8)  # Higher value for min constraint
        sys.addConstraint(x[5] == 2)  # Lower value for min constraint

        # Constraint 1: min(x[0], x[1]) == 3 (should be satisfied: min(3,5) = 3)
        var minTerms: seq[AlgebraicExpression[int]] = @[]
        minTerms.add(x[0])
        minTerms.add(x[1])
        sys.addConstraint(min(minTerms) == 3)

        # Constraint 2: max(x[2], x[3]) == 6 (should be satisfied: max(6,4) = 6)
        var maxTerms: seq[AlgebraicExpression[int]] = @[]
        maxTerms.add(x[2])
        maxTerms.add(x[3])
        sys.addConstraint(max(maxTerms) == 6)

        # Constraint 3: Variable target constraints
        # min(x[4], x[5]) == x[6] should give x[6] = min(8,2) = 2
        # max(x[0], x[1]) == x[6] should give x[6] = max(3,5) = 5
        # But this creates a conflict! Let's use separate aux variables

        var minTerms2: seq[AlgebraicExpression[int]] = @[]
        minTerms2.add(x[4])
        minTerms2.add(x[5])
        sys.addConstraint(min(minTerms2) == x[6])  # x[6] should be 2

        # Since we can't have both constraints on x[6], let's verify just the min constraint

        sys.resolve()
        let solution = x.assignment

        # Verify all fixed values
        check solution[0] == 3
        check solution[1] == 5
        check solution[2] == 6
        check solution[3] == 4
        check solution[4] == 8
        check solution[5] == 2

        # Verify constraint 1: min(x[0], x[1]) == 3
        let actualMin1 = min([solution[0], solution[1]])
        check actualMin1 == 3

        # Verify constraint 2: max(x[2], x[3]) == 6
        let actualMax1 = max([solution[2], solution[3]])
        check actualMax1 == 6

        # Verify constraint 3: min(x[4], x[5]) == x[6] should give x[6] = 2
        let actualMin2 = min([solution[4], solution[5]])
        check actualMin2 == solution[6]
        check solution[6] == 2

    test "Min/Max with Inequality Relations":
        # Test min/max constraints with != relationship
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..6))

        # min(x[0], x[1]) <= 3
        var minTerms: seq[AlgebraicExpression[int]] = @[]
        minTerms.add(x[0])
        minTerms.add(x[1])
        sys.addConstraint(min(minTerms) <= 3)

        # max(x[2], x[3]) >= 4
        var maxTerms: seq[AlgebraicExpression[int]] = @[]
        maxTerms.add(x[2])
        maxTerms.add(x[3])
        sys.addConstraint(max(maxTerms) >= 4)

        sys.resolve()
        let solution = x.assignment

        # Verify constraints
        let actualMin = min([solution[0], solution[1]])
        let actualMax = max([solution[2], solution[3]])

        check actualMin <= 3
        check actualMax >= 4