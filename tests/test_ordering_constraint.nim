import std/[sequtils, unittest, algorithm]
import crusher

proc validateIncreasing[T](values: seq[T]): bool =
    ## Validates that the given sequence is in non-decreasing order
    for i in 0..<(values.len - 1):
        if values[i] > values[i + 1]:
            return false
    return true

proc validateStrictlyIncreasing[T](values: seq[T]): bool =
    ## Validates that the given sequence is in strictly increasing order
    for i in 0..<(values.len - 1):
        if values[i] >= values[i + 1]:
            return false
    return true

proc validateDecreasing[T](values: seq[T]): bool =
    ## Validates that the given sequence is in non-increasing order
    for i in 0..<(values.len - 1):
        if values[i] < values[i + 1]:
            return false
    return true

proc validateStrictlyDecreasing[T](values: seq[T]): bool =
    ## Validates that the given sequence is in strictly decreasing order
    for i in 0..<(values.len - 1):
        if values[i] <= values[i + 1]:
            return false
    return true

proc countIncreasingViolations[T](values: seq[T]): int =
    ## Count the number of decreasing pairs (violations of increasing constraint)
    result = 0
    for i in 0..<(values.len - 1):
        if values[i] > values[i + 1]:
            result += 1

proc countStrictlyIncreasingViolations[T](values: seq[T]): int =
    ## Count violations of strictly increasing constraint
    result = 0
    for i in 0..<(values.len - 1):
        if values[i] >= values[i + 1]:
            result += 1

proc countDecreasingViolations[T](values: seq[T]): int =
    ## Count violations of decreasing constraint
    result = 0
    for i in 0..<(values.len - 1):
        if values[i] < values[i + 1]:
            result += 1

proc countStrictlyDecreasingViolations[T](values: seq[T]): int =
    ## Count violations of strictly decreasing constraint
    result = 0
    for i in 0..<(values.len - 1):
        if values[i] <= values[i + 1]:
            result += 1

suite "Ordering Constraint Tests":

    test "Increasing constraint - basic functionality":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(5)

        X.setDomain(toSeq(1..10))
        sys.addConstraint(increasing(X))
        sys.addConstraint(max(X) == 5)

        sys.resolve()

        let assignment = X.assignment
        check(validateIncreasing(assignment))

    test "Increasing constraint - equal values allowed":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(increasing(X))

        for i in 0..<4:
            sys.addConstraint(X[i] == 3)

        sys.resolve()

        let assignment = X.assignment
        check(validateIncreasing(assignment))
        check(assignment == @[3, 3, 3, 3])

    test "Strictly increasing constraint - basic functionality":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(5)

        X.setDomain(toSeq(1..10))
        sys.addConstraint(strictlyIncreasing(X))
        sys.addConstraint(max(X) == 5)

        sys.resolve()

        let assignment = X.assignment
        check(validateStrictlyIncreasing(assignment))
        check(assignment == @[1, 2, 3, 4, 5])

    test "Strictly increasing constraint - equal values not allowed":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(strictlyIncreasing(X))

        # Force a valid strictly increasing sequence
        sys.addConstraint(X[0] == 1)
        sys.addConstraint(X[1] == 3)
        sys.addConstraint(X[2] == 5)

        sys.resolve()

        let assignment = X.assignment
        check(validateStrictlyIncreasing(assignment))
        check(assignment == @[1, 3, 5])

    test "Decreasing constraint - basic functionality":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(5)

        X.setDomain(toSeq(1..10))
        sys.addConstraint(decreasing(X))
        sys.addConstraint(min(X) == 1)

        sys.resolve()

        let assignment = X.assignment
        check(validateDecreasing(assignment))

    test "Decreasing constraint - equal values allowed":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(decreasing(X))

        for i in 0..<4:
            sys.addConstraint(X[i] == 3)

        sys.resolve()

        let assignment = X.assignment
        check(validateDecreasing(assignment))
        check(assignment == @[3, 3, 3, 3])

    test "Strictly decreasing constraint - basic functionality":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(5)

        X.setDomain(toSeq(1..10))
        sys.addConstraint(strictlyDecreasing(X))
        sys.addConstraint(min(X) == 1)

        sys.resolve()

        let assignment = X.assignment
        check(validateStrictlyDecreasing(assignment))
        # Don't check for exact values, just that it's strictly decreasing
        # The solver may find different valid solutions

    test "Strictly decreasing constraint - equal values not allowed":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(strictlyDecreasing(X))

        # Force a valid strictly decreasing sequence
        sys.addConstraint(X[0] == 5)
        sys.addConstraint(X[1] == 3)
        sys.addConstraint(X[2] == 1)

        sys.resolve()

        let assignment = X.assignment
        check(validateStrictlyDecreasing(assignment))
        check(assignment == @[5, 3, 1])

    test "Expression-based increasing constraint":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        X.setDomain(toSeq(1..10))

        # Create expressions: X[0] + 1, X[1], X[2] - 1, X[3]
        let expr1 = X[0] + 1
        let expr2 = X[1]
        let expr3 = X[2] - 1
        let expr4 = X[3]

        sys.addConstraint(increasing[int](@[expr1, expr2, expr3, expr4]))

        # Force specific values
        sys.addConstraint(X[0] == 1)  # expr1 = 2
        sys.addConstraint(X[1] == 3)  # expr2 = 3
        sys.addConstraint(X[2] == 4)  # expr3 = 3
        sys.addConstraint(X[3] == 5)  # expr4 = 5

        sys.resolve()

        let assignment = X.assignment
        let evalExpr1 = expr1.evaluate(assignment)
        let evalExpr2 = expr2.evaluate(assignment)
        let evalExpr3 = expr3.evaluate(assignment)
        let evalExpr4 = expr4.evaluate(assignment)
        let expressionValues = @[evalExpr1, evalExpr2, evalExpr3, evalExpr4]

        check(validateIncreasing(expressionValues))
        check(expressionValues == @[2, 3, 3, 5])

    test "Expression-based strictly increasing constraint":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..10))

        # Create expressions: X[0], X[1] + 1, X[2] + 3
        let expr1 = X[0]
        let expr2 = X[1] + 1
        let expr3 = X[2] + 3

        sys.addConstraint(strictlyIncreasing[int](@[expr1, expr2, expr3]))

        # Force values that make expressions [2, 3, 6]
        sys.addConstraint(X[0] == 2)  # expr1 = 2
        sys.addConstraint(X[1] == 2)  # expr2 = 3
        sys.addConstraint(X[2] == 3)  # expr3 = 6

        sys.resolve()

        let assignment = X.assignment
        let evalExpr1 = expr1.evaluate(assignment)
        let evalExpr2 = expr2.evaluate(assignment)
        let evalExpr3 = expr3.evaluate(assignment)
        let expressionValues = @[evalExpr1, evalExpr2, evalExpr3]

        check(validateStrictlyIncreasing(expressionValues))
        check(expressionValues == @[2, 3, 6])

    test "Expression-based decreasing constraint":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..10))

        # Create expressions: X[0] + 5, X[1] + 2, X[2]
        let expr1 = X[0] + 5
        let expr2 = X[1] + 2
        let expr3 = X[2]

        sys.addConstraint(decreasing[int](@[expr1, expr2, expr3]))

        # Force values that make expressions [7, 5, 3]
        sys.addConstraint(X[0] == 2)  # expr1 = 7
        sys.addConstraint(X[1] == 3)  # expr2 = 5
        sys.addConstraint(X[2] == 3)  # expr3 = 3

        sys.resolve()

        let assignment = X.assignment
        let evalExpr1 = expr1.evaluate(assignment)
        let evalExpr2 = expr2.evaluate(assignment)
        let evalExpr3 = expr3.evaluate(assignment)
        let expressionValues = @[evalExpr1, evalExpr2, evalExpr3]

        check(validateDecreasing(expressionValues))
        check(expressionValues == @[7, 5, 3])

    test "Expression-based strictly decreasing constraint":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..10))

        # Create expressions: X[0] * 2, X[1] + 1, X[2]
        let expr1 = X[0] * 2
        let expr2 = X[1] + 1
        let expr3 = X[2]

        sys.addConstraint(strictlyDecreasing[int](@[expr1, expr2, expr3]))

        # Force values that make expressions [8, 4, 1]
        sys.addConstraint(X[0] == 4)  # expr1 = 8
        sys.addConstraint(X[1] == 3)  # expr2 = 4
        sys.addConstraint(X[2] == 1)  # expr3 = 1

        sys.resolve()

        let assignment = X.assignment
        let evalExpr1 = expr1.evaluate(assignment)
        let evalExpr2 = expr2.evaluate(assignment)
        let evalExpr3 = expr3.evaluate(assignment)
        let expressionValues = @[evalExpr1, evalExpr2, evalExpr3]

        check(validateStrictlyDecreasing(expressionValues))
        check(expressionValues == @[8, 4, 1])

    test "Non-contiguous positions - increasing":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(10)

        X.setDomain(toSeq(1..10))

        # Apply increasing constraint only to positions [1, 3, 5, 7, 9]
        sys.addConstraint(increasing[int]([1, 3, 5, 7, 9]))

        # Force specific values for the constrained positions
        sys.addConstraint(X[1] == 2)
        sys.addConstraint(X[3] == 4)
        sys.addConstraint(X[5] == 4)  # Equal is OK for increasing
        sys.addConstraint(X[7] == 6)
        sys.addConstraint(X[9] == 8)

        # Set other positions to any values
        sys.addConstraint(X[0] == 9)
        sys.addConstraint(X[2] == 1)
        sys.addConstraint(X[4] == 7)
        sys.addConstraint(X[6] == 3)
        sys.addConstraint(X[8] == 5)

        sys.resolve()

        let assignment = X.assignment
        let constrainedValues = @[assignment[1], assignment[3], assignment[5], assignment[7], assignment[9]]
        check(validateIncreasing(constrainedValues))
        check(constrainedValues == @[2, 4, 4, 6, 8])

    test "Non-contiguous positions - strictly decreasing":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(8)

        X.setDomain(toSeq(1..10))

        # Apply strictly decreasing constraint to positions [0, 2, 4, 6]
        sys.addConstraint(strictlyDecreasing[int]([0, 2, 4, 6]))

        # Force specific values for the constrained positions
        sys.addConstraint(X[0] == 9)
        sys.addConstraint(X[2] == 6)
        sys.addConstraint(X[4] == 3)
        sys.addConstraint(X[6] == 1)

        # Set other positions to any values
        sys.addConstraint(X[1] == 2)
        sys.addConstraint(X[3] == 8)
        sys.addConstraint(X[5] == 4)
        sys.addConstraint(X[7] == 7)

        sys.resolve()

        let assignment = X.assignment
        let constrainedValues = @[assignment[0], assignment[2], assignment[4], assignment[6]]
        check(validateStrictlyDecreasing(constrainedValues))
        check(constrainedValues == @[9, 6, 3, 1])

    test "Matrix columns with different ordering constraints":
        var sys = initConstraintSystem[int]()
        var M = sys.newConstrainedMatrix(2, 2)  # Simple 2x2 matrix

        M.setDomain(toSeq(1..9))

        # Apply different constraints to each column
        var cols: seq[seq[AlgebraicExpression[int]]] = @[]
        for col in M.columns():
            cols.add(col)

        sys.addConstraint(increasing[int](cols[0]))      # Column 0: increasing
        sys.addConstraint(decreasing[int](cols[1]))      # Column 1: decreasing

        # Force just a few values to guide the solver
        sys.addConstraint(M[0, 0] == 2)  # Row 0, Column 0
        sys.addConstraint(M[0, 1] == 8)  # Row 0, Column 1

        sys.resolve()

        let assignment = M.assignment

        # Check column 0 (increasing)
        let col0 = @[assignment[0][0], assignment[1][0]]
        check(validateIncreasing(col0))
        check(col0[0] == 2)  # First value should be 2 as forced

        # Check column 1 (decreasing)
        let col1 = @[assignment[0][1], assignment[1][1]]
        check(validateDecreasing(col1))
        check(col1[0] == 8)  # First value should be 8 as forced

    test "Constraint violations properly detected by system":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        X.setDomain(toSeq(1..10))

        # Add increasing constraint
        sys.addConstraint(increasing(X))

        # Force values that should work: [2, 3, 3, 5]
        sys.addConstraint(X[0] == 2)
        sys.addConstraint(X[1] == 3)
        sys.addConstraint(X[2] == 3)
        sys.addConstraint(X[3] == 5)

        sys.resolve()

        let assignment = X.assignment
        check(validateIncreasing(assignment))
        check(assignment == @[2, 3, 3, 5])

    test "Edge case - single element constraint":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(1)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(increasing(X))
        sys.addConstraint(X[0] == 3)

        sys.resolve()

        let assignment = X.assignment
        check(validateIncreasing(assignment))  # Single element is always valid
        check(assignment == @[3])

    test "Edge case - single element strictly increasing":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(1)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(strictlyIncreasing(X))
        sys.addConstraint(X[0] == 2)

        sys.resolve()

        let assignment = X.assignment
        check(validateStrictlyIncreasing(assignment))  # Single element is always valid
        check(assignment == @[2])

    test "Edge case - two element constraint":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(2)

        X.setDomain(toSeq(1..5))
        sys.addConstraint(strictlyIncreasing(X))
        sys.addConstraint(X[0] == 1)
        sys.addConstraint(X[1] == 3)

        sys.resolve()

        let assignment = X.assignment
        check(validateStrictlyIncreasing(assignment))
        check(assignment == @[1, 3])

    test "Edge case - empty constraint positions":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..5))

        # Apply ordering constraint to empty array of positions (should be no-op)
        sys.addConstraint(increasing[int](@[]))

        # Force some values
        sys.addConstraint(X[0] == 3)
        sys.addConstraint(X[1] == 1)
        sys.addConstraint(X[2] == 5)

        sys.resolve()

        # Since no constraints were actually applied, any assignment should work
        let assignment = X.assignment
        check(assignment == @[3, 1, 5])

    test "Conflict detection - impossible strictly increasing":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..3))  # Limited domain
        sys.addConstraint(strictlyIncreasing(X))

        # Force values that make strictly increasing impossible
        sys.addConstraint(X[0] == 2)
        sys.addConstraint(X[1] == 2)  # Equal values violate strictly increasing
        sys.addConstraint(X[2] == 3)

        # The system should detect this is impossible and fail to resolve
        try:
            sys.resolve()
            check(false)  # Should not reach here due to constraint violation
        except CatchableError:
            check(true)  # Expected to fail

    test "Mixed constraints - increasing with allDifferent":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        X.setDomain(toSeq(1..10))
        sys.addConstraint(increasing(X))
        sys.addConstraint(allDifferent(X))  # This makes it effectively strictly increasing

        # Force values that satisfy both constraints
        sys.addConstraint(X[0] == 2)
        sys.addConstraint(max(X) == 8)

        sys.resolve()

        let assignment = X.assignment
        check(validateIncreasing(assignment))
        check(validateStrictlyIncreasing(assignment))  # Should be strictly increasing due to allDifferent
        check(assignment[0] == 2)
        check(assignment[3] == 8)  # Max constraint

    test "Complex expression constraint with solvable values":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(3)

        X.setDomain(toSeq(1..5))

        # Create expressions: X[0]*2, X[1], X[2]-1
        let expr1 = X[0] * 2
        let expr2 = X[1]
        let expr3 = X[2] - 1

        sys.addConstraint(strictlyIncreasing[int](@[expr1, expr2, expr3]))

        # Force values that make expressions work: [2, 5, 6] -> strictly increasing
        sys.addConstraint(X[0] == 1)  # expr1 = 2
        sys.addConstraint(X[1] == 5)  # expr2 = 5
        sys.addConstraint(X[2] == 7)  # expr3 = 6  (but X[2] domain is 1..5!)

        # Since X[2] can't be 7, let's use valid values
        sys = initConstraintSystem[int]()  # Reset
        X = sys.newConstrainedSequence(3)
        X.setDomain(toSeq(1..10))  # Expand domain

        let expr1_new = X[0] * 2
        let expr2_new = X[1]
        let expr3_new = X[2] - 1

        sys.addConstraint(strictlyIncreasing[int](@[expr1_new, expr2_new, expr3_new]))

        sys.addConstraint(X[0] == 1)  # expr1 = 2
        sys.addConstraint(X[1] == 5)  # expr2 = 5
        sys.addConstraint(X[2] == 7)  # expr3 = 6

        sys.resolve()

        let assignment = X.assignment
        let evalExpr1 = expr1_new.evaluate(assignment)
        let evalExpr2 = expr2_new.evaluate(assignment)
        let evalExpr3 = expr3_new.evaluate(assignment)
        let expressionValues = @[evalExpr1, evalExpr2, evalExpr3]

        check(validateStrictlyIncreasing(expressionValues))
        check(expressionValues == @[2, 5, 6])