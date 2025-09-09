import std/[sequtils, unittest, algorithm]
import crusher

proc validateIncreasing[T](values: seq[T]): bool =
    ## Validates that the given sequence is in non-decreasing order
    for i in 0..<(values.len - 1):
        if values[i] > values[i + 1]:
            return false
    return true


suite "Increasing Constraint Tests":

    test "Basic increasing constraint - already increasing":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(5)

        # Set domain
        X.setDomain(toSeq(1..10))

        # Add increasing constraint
        sys.addConstraint(increasing(X))

        # setting max at 5 should force order 1, 2, 3, 4, 5
        sys.addConstraint(max(X) == 5)

        sys.resolve()

        # check that assignment is increasing
        let assignment = X.assignment
        check(validateIncreasing(assignment))

    test "Increasing constraint - all equal values":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        # Set domain
        X.setDomain(toSeq(1..5))

        # Add increasing constraint
        sys.addConstraint(increasing(X))

        # Force all values to be 3 (non-strict increasing allows this)
        for i in 0..<4:
            sys.addConstraint(X[i] == 3)

        sys.resolve()

        # Check that all values are equal (which satisfies increasing)
        let assignment = X.assignment
        check(validateIncreasing(assignment))
        check(assignment == @[3, 3, 3, 3])

    test "Increasing constraint - mixed equal and increasing":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(6)

        # Set domain
        X.setDomain(toSeq(1..10))

        # Add increasing constraint
        sys.addConstraint(increasing(X))

        # Force specific pattern: 2, 2, 5, 5, 8, 8
        sys.addConstraint(X[0] == 2)
        sys.addConstraint(X[1] == 2)
        sys.addConstraint(X[2] == 5)
        sys.addConstraint(X[3] == 5)
        sys.addConstraint(X[4] == 8)
        sys.addConstraint(X[5] == 8)

        sys.resolve()

        # Check that assignment follows the pattern
        let assignment = X.assignment
        check(validateIncreasing(assignment))
        check(assignment == @[2, 2, 5, 5, 8, 8])

    test "Increasing constraint - expression based":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        # Set domain
        X.setDomain(toSeq(1..10))

        # Create expressions: X[0] + 1, X[1], X[2] - 1, X[3]
        let expr1 = X[0] + 1
        let expr2 = X[1]
        let expr3 = X[2] - 1
        let expr4 = X[3]

        # Add increasing constraint on expressions
        sys.addConstraint(increasing[int](@[expr1, expr2, expr3, expr4]))

        # Force specific values: [1, 3, 4, 5]
        # This should make expressions [2, 3, 3, 5] which is increasing
        sys.addConstraint(X[0] == 1)
        sys.addConstraint(X[1] == 3)
        sys.addConstraint(X[2] == 4)
        sys.addConstraint(X[3] == 5)

        sys.resolve()

        # Check expression values are increasing
        let assignment = X.assignment
        let evalExpr1 = expr1.evaluate(assignment)
        let evalExpr2 = expr2.evaluate(assignment)
        let evalExpr3 = expr3.evaluate(assignment)
        let evalExpr4 = expr4.evaluate(assignment)
        let expressionValues = @[evalExpr1, evalExpr2, evalExpr3, evalExpr4]

        check(validateIncreasing(expressionValues))
        check(expressionValues == @[2, 3, 3, 5])

    test "Increasing constraint - impossible sequence should fail":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        # Set domain
        X.setDomain(toSeq(1..10))

        # Add increasing constraint
        sys.addConstraint(increasing(X))

        # Force values that violate increasing: 5 > 3 at positions 0,1
        sys.addConstraint(X[0] == 5)
        sys.addConstraint(X[1] == 3)
        sys.addConstraint(X[2] == 7)

        # This should fail to resolve due to the constraint violation
        try:
            sys.resolve()
            check(false)  # Should not reach here due to constraint violation
        except CatchableError:
            check(true)  # Expected to fail

    test "Increasing constraint - strict increasing pattern":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(5)

        # Set domain
        X.setDomain(toSeq(1..10))

        # Add increasing constraint
        sys.addConstraint(increasing(X))

        # Also add allDifferent to make it strictly increasing
        sys.addConstraint(allDifferent(X))

        # Constrain max to 5 to force 1,2,3,4,5
        sys.addConstraint(max(X) == 5)

        sys.resolve()

        let assignment = X.assignment
        check(validateIncreasing(assignment))
        check(assignment == @[1, 2, 3, 4, 5])  # Should be strictly increasing

    test "Increasing constraint - non-contiguous positions":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(10)

        # Set domain for all positions
        X.setDomain(toSeq(1..10))

        # Apply increasing constraint only to positions [1, 3, 5, 7, 9]
        sys.addConstraint(increasing[int]([1, 3, 5, 7, 9]))

        # Force specific values for the constrained positions
        sys.addConstraint(X[1] == 2)  # pos 1
        sys.addConstraint(X[3] == 4)  # pos 3
        sys.addConstraint(X[5] == 4)  # pos 5 (equal is OK)
        sys.addConstraint(X[7] == 6)  # pos 7
        sys.addConstraint(X[9] == 8)  # pos 9

        # Set other positions to any values
        sys.addConstraint(X[0] == 9)
        sys.addConstraint(X[2] == 1)
        sys.addConstraint(X[4] == 7)
        sys.addConstraint(X[6] == 3)
        sys.addConstraint(X[8] == 5)

        sys.resolve()

        let assignment = X.assignment
        # Check the constrained positions are increasing: [2, 4, 4, 6, 8]
        let constrainedValues = @[assignment[1], assignment[3], assignment[5], assignment[7], assignment[9]]
        check(validateIncreasing(constrainedValues))
        check(constrainedValues == @[2, 4, 4, 6, 8])

        # Check that other positions have the forced values (no increasing constraint)
        check(assignment[0] == 9)  # Can be any value
        check(assignment[2] == 1)  # Can be any value
        check(assignment[4] == 7)  # Can be any value

    test "Increasing constraint - matrix columns":
        var sys = initConstraintSystem[int]()
        var M = sys.newConstrainedMatrix(3, 3)

        # Set domain
        M.setDomain(toSeq(1..9))

        # Apply increasing constraint to each column
        for col in M.columns():
            sys.addConstraint(increasing(col))

        # Force specific values to test
        sys.addConstraint(M[0, 0] == 1) # Column 0: 1, 3, 5
        sys.addConstraint(M[1, 0] == 3)
        sys.addConstraint(M[2, 0] == 5)

        sys.addConstraint(M[0, 1] == 2) # Column 1: 2, 2, 4
        sys.addConstraint(M[1, 1] == 2)
        sys.addConstraint(M[2, 1] == 4)

        sys.addConstraint(M[0, 2] == 6) # Column 2: 6, 7, 9
        sys.addConstraint(M[1, 2] == 7)
        sys.addConstraint(M[2, 2] == 9)

        sys.resolve()

        let assignment = M.assignment
        # Check each column is increasing
        for j in 0..<3:
            let column = @[assignment[0][j], assignment[1][j], assignment[2][j]]
            check(validateIncreasing(column))

        # Verify specific expected values
        check(assignment == @[@[1, 2, 6], @[3, 2, 7], @[5, 4, 9]])
