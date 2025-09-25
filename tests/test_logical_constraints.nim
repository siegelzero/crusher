import std/[sequtils, unittest]
import crusher

suite "Logical Constraint Tests":
    test "Basic logical AND constraint with resolve":
        # Create a simple constraint system
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        # Set domains
        x.setDomain([1, 2, 3, 4, 5])
        y.setDomain([1, 2, 3, 4, 5])

        # Create basic constraints: x > 2 AND y < 4
        let c1 = x > 2  # x > 2
        let c2 = y < 4  # y < 4
        let andConstraint = c1 and c2

        # Add the logical constraint to the system
        sys.addConstraint(andConstraint)

        # Solve the constraint system
        try:
            sys.resolve(verbose=false)

            # Check that the solution satisfies both constraints
            let assignment = sys.assignment
            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found solution: x=", xVal, ", y=", yVal

            # Verify the solution
            check xVal > 2
            check yVal < 4

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for x > 2 AND y < 4"
            check false

    test "Logical OR constraint with resolve":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        # Set narrow domains to test OR constraint
        x.setDomain([1, 5])  # x can only be 1 or 5
        y.setDomain([1, 5])  # y can only be 1 or 5

        # Create constraints: x == 5 OR y == 5 (at least one must be 5)
        let c1 = x == 5
        let c2 = y == 5
        let orConstraint = c1 or c2

        sys.addConstraint(orConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found solution: x=", xVal, ", y=", yVal

            # At least one should be 5
            check (xVal == 5 or yVal == 5)

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for x == 5 OR y == 5"
            check false

    test "Logical XOR constraint":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2])
        y.setDomain([1, 2])

        # Create XOR constraint: exactly one of x==1 or y==1 should be true
        let c1 = x == 1
        let c2 = y == 1
        let xorConstraint = c1 xor c2

        sys.addConstraint(xorConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found XOR solution: x=", xVal, ", y=", yVal

            # Exactly one should be 1
            let firstTrue = (xVal == 1)
            let secondTrue = (yVal == 1)
            check (firstTrue and not secondTrue) or (not firstTrue and secondTrue)

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for XOR constraint"
            check false

    test "Arrow operator -> for implies":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])

        # Test the -> operator: if x == 1 then y == 2
        let impliesConstraint = (x == 1) -> (y == 2)

        sys.addConstraint(impliesConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found solution with -> operator: x=", xVal, ", y=", yVal

            # If x is 1, then y must be 2. Otherwise, any value is okay.
            if xVal == 1:
                check yVal == 2

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for (x == 1) -> (y == 2)"
            check false

    test "Double arrow operator <-> for iff":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2])
        y.setDomain([1, 2])

        # Test the <-> operator: x == 1 if and only if y == 1
        let iffConstraint = (x == 1) <-> (y == 1)

        sys.addConstraint(iffConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found solution with <-> operator: x=", xVal, ", y=", yVal

            # Both must be 1 or both must be 2
            check (xVal == 1 and yVal == 1) or (xVal == 2 and yVal == 2)

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for (x == 1) <-> (y == 1)"
            check false

    test "Legacy implies function syntax":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])

        # If x == 1 then y == 2 using legacy function syntax
        let precondition = x == 1
        let postcondition = y == 2
        let impliesConstraint = implies(precondition, postcondition)

        sys.addConstraint(impliesConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found solution with legacy implies: x=", xVal, ", y=", yVal

            # If x is 1, then y must be 2. Otherwise, any value is okay.
            if xVal == 1:
                check yVal == 2

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for legacy implies"
            check false

    test "Complex nested logical constraint":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()
        var z = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])
        z.setDomain([1, 2, 3])

        # (x > 1 AND y < 3) OR z == 2
        let c1 = x > 1
        let c2 = y < 3
        let c3 = z == 2
        let complexConstraint = (c1 and c2) or c3

        sys.addConstraint(complexConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()
            let zVal = z.assignment()

            echo "Found solution: x=", xVal, ", y=", yVal, ", z=", zVal

            # Either (x > 1 AND y < 3) OR z == 2 must be true
            let leftSide = (xVal > 1 and yVal < 3)
            let rightSide = (zVal == 2)
            check (leftSide or rightSide)

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for complex logical constraint"
            check false

    test "Complex expression with intuitive operators":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()
        var z = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])
        z.setDomain([1, 2, 3])

        # Complex logical expression using intuitive operators:
        # (x > 1) -> (y == 2) and (y == 2) <-> (z == 3)
        let complexConstraint = ((x > 1) -> (y == 2)) and ((y == 2) <-> (z == 3))

        sys.addConstraint(complexConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()
            let zVal = z.assignment()

            echo "Found solution with complex operators: x=", xVal, ", y=", yVal, ", z=", zVal

            # Verify the logical relationships
            let implies_satisfied = (xVal <= 1) or (yVal == 2)  # (x > 1) -> (y == 2)
            let iff_satisfied = (yVal == 2) == (zVal == 3)      # (y == 2) <-> (z == 3)

            check implies_satisfied and iff_satisfied

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for complex logical expression"
            check false

    test "Logical constraint with stateful constraints":
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)
        var x = sys.newConstrainedVariable()

        sequence.setDomain([1, 2, 3, 4, 5])
        x.setDomain([1, 2, 3, 4, 5])

        # Mix algebraic and stateful constraints
        let algebraicConstraint = x > 3
        let statefulConstraint = sequence.sum() == 6
        let mixedLogical = algebraicConstraint and statefulConstraint

        sys.addConstraint(mixedLogical)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let seqVals = sequence.assignment()
            let sumVal = seqVals.foldl(a + b, 0)

            echo "Found solution: x=", xVal, ", sequence=", seqVals

            # Both constraints must be satisfied
            check xVal > 3
            check sumVal == 6

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for mixed logical constraint"
            check false

    test "Mixed old and new syntax should work":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])

        # Mix old implies() function and new -> operator
        let constraint1 = implies(x == 1, y == 2)  # Old syntax
        let constraint2 = (x == 2) -> (y == 3)     # New syntax

        let mixedConstraint = constraint1 or constraint2

        sys.addConstraint(mixedConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found solution with mixed syntax: x=", xVal, ", y=", yVal

            # At least one implication should be satisfied
            let first_satisfied = (xVal != 1) or (yVal == 2)
            let second_satisfied = (xVal != 2) or (yVal == 3)

            check first_satisfied or second_satisfied

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for mixed syntax"
            check false

    test "NOT operator with logical combinations":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])

        let c1 = x == 1
        let c2 = y == 2

        # Test NOT with AND: not(c1 and c2)
        let notAndConstraint = not (c1 and c2)

        sys.addConstraint(notAndConstraint)

        try:
            sys.resolve(verbose=false)

            let xVal = x.assignment()
            let yVal = y.assignment()

            echo "Found NOT solution: x=", xVal, ", y=", yVal

            # NOT(c1 AND c2) means at least one of c1 or c2 should be false
            check not (xVal == 1 and yVal == 2)

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for NOT constraint"
            check false

    test "All different except 0 constraint using logical operators":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedSequence(4)

        # Domain includes 0 (which can be repeated) and other values (which must be unique)
        X.setDomain([0, 1, 2])

        # Create all_different_except_0 constraint using mixed algebraic and stateful approach:
        # For all pairs (i,j) where i < j: (X[i] != 0) and (X[j] != 0) implies X[i] != X[j]
        for i in 0..<4:
            for j in (i+1)..<4:
                sys.addConstraint(((X[i] != 0) and (X[j] != 0)) -> X[i] != X[j])

        try:
            sys.resolve(verbose=false)

            let assignment = X.assignment()
            echo "Found all_different_except_0 solution: ", assignment

            # Verify the constraint: all non-zero values should be unique
            var nonzeroValues: seq[int] = @[]
            for val in assignment:
                if val != 0:
                    nonzeroValues.add(val)

            # Check that all non-zero values are unique
            for i in 0..<nonzeroValues.len:
                for j in (i+1)..<nonzeroValues.len:
                    check nonzeroValues[i] != nonzeroValues[j]

            echo "Verification passed: All non-zero values are unique"

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for all_different_except_0"
            check false

    test "Complex logical constraint with sum, min, and max expressions":
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(10)  # 10 variables

        # Set a domain that allows for interesting solutions
        sequence.setDomain([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20])

        # Complex constraint: sum(X) = 100 AND one of these patterns must hold:
        # Pattern 1: (min(X) == 1 AND max(X) == 20)  - wide range
        # Pattern 2: (min(X) == 5 AND max(X) == 15)  - medium range
        # Pattern 3: (min(X) == 8 AND max(X) == 12)  - narrow range

        # First constraint: sum must equal 100
        let sumConstraint = sequence.sum() == 100  # StatefulConstraint

        # Pattern constraints (all AlgebraicConstraints that will be auto-converted)
        let pattern1 = (sequence.min() == 1) and (sequence.max() == 20)   # Wide range
        let pattern2 = (sequence.min() == 5) and (sequence.max() == 15)   # Medium range
        let pattern3 = (sequence.min() == 8) and (sequence.max() == 12)   # Narrow range

        # Combined pattern constraint: at least one pattern must be satisfied
        let patternConstraint = pattern1 or pattern2 or pattern3  # AlgebraicConstraint

        # Final constraint: sum AND pattern constraints (mixed types, auto-conversion)
        let finalConstraint = sumConstraint and patternConstraint

        sys.addConstraint(finalConstraint)

        try:
            sys.resolve(verbose=false)

            let assignment = sequence.assignment()
            let sumVal = assignment.foldl(a + b, 0)
            let minVal = assignment.min()
            let maxVal = assignment.max()

            echo "Found complex constraint solution:"
            echo "  Sequence: ", assignment
            echo "  Sum: ", sumVal
            echo "  Min: ", minVal
            echo "  Max: ", maxVal

            # Verify the sum constraint
            check sumVal == 100

            # Verify at least one pattern is satisfied
            let pattern1Satisfied = (minVal == 1 and maxVal == 20)
            let pattern2Satisfied = (minVal == 5 and maxVal == 15)
            let pattern3Satisfied = (minVal == 8 and maxVal == 12)

            check (pattern1Satisfied or pattern2Satisfied or pattern3Satisfied)

            # Report which pattern was satisfied
            if pattern1Satisfied:
                echo "  Pattern satisfied: Wide range (min=1, max=20)"
            elif pattern2Satisfied:
                echo "  Pattern satisfied: Medium range (min=5, max=15)"
            elif pattern3Satisfied:
                echo "  Pattern satisfied: Narrow range (min=8, max=12)"

        except NoSolutionFoundError:
            echo "Failed: Should have found a solution for complex sum/min/max constraint"
            check false
