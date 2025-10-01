import std/[sequtils, unittest]
import crusher

suite "Intuitive Boolean Operator Syntax":
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

    test "Complex expression with intuitive operators":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()
        var z = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])
        z.setDomain([1, 2, 3])

        # Complex boolean expression using intuitive operators:
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
            echo "Failed: Should have found a solution for complex boolean expression"
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