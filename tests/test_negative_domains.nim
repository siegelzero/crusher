import std/[sequtils, tables, unittest]
import ../src/crusher

suite "Negative Domain Support Tests":
    test "Simple negative domain - basic constraints":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)

        # Test negative domain
        x.setDomain(toSeq((-5)..5))

        # Add basic constraints
        sys.addConstraint(x[0] == -2)
        sys.addConstraint(x[1] == 3)
        sys.addConstraint(x[2] == -1)

        sys.resolve()
        let assignment = x.assignment()

        check assignment[0] == -2
        check assignment[1] == 3
        check assignment[2] == -1

    test "Negative domain - AllDifferent constraint":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)

        # Test with mixed negative/positive domain
        x.setDomain(toSeq((-3)..0))

        # All different constraint should work with negatives
        sys.addConstraint(allDifferent(x))

        sys.resolve()
        let assignment = x.assignment()

        # Check that all values are different and within domain
        for i in 0..<4:
            check assignment[i] >= -3
            check assignment[i] <= 0

        # Check uniqueness
        var seen: Table[int, bool]
        for val in assignment:
            check val notin seen
            seen[val] = true

    test "Large negative range":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(5)

        # Test with large negative numbers
        x.setDomain(toSeq((-1000)..(-996)))

        sys.addConstraint(allDifferent(x))

        sys.resolve()
        let assignment = x.assignment()

        # Verify all values in range and different
        for i in 0..<5:
            check assignment[i] >= -1000
            check assignment[i] <= -996

        var seen: Table[int, bool]
        for val in assignment:
            check val notin seen
            seen[val] = true

    test "Mixed domain with negative sum constraint":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)

        # Domain includes negatives, zero, and positives
        x.setDomain(toSeq((-5)..5))

        # Sum constraint that requires negative total
        sys.addConstraint(x[0] + x[1] + x[2] == -6)
        sys.addConstraint(allDifferent(x))

        sys.resolve()
        let assignment = x.assignment()

        check assignment[0] + assignment[1] + assignment[2] == -6

        # Check uniqueness
        var seen: Table[int, bool]
        for val in assignment:
            check val notin seen
            seen[val] = true

    test "Matrix with negative domains":
        var sys = initConstraintSystem[int]()
        var X = sys.newConstrainedMatrix(2, 2)

        # Use negative domain for matrix
        X.setDomain(toSeq((-2)..1))

        # All different across entire matrix
        sys.addConstraint(allDifferent(X))

        sys.resolve()
        let assignment = X.assignment()

        # Flatten matrix to check uniqueness
        var allValues: seq[int]
        for row in assignment:
            for val in row:
                allValues.add(val)
                check val >= -2
                check val <= 1

        var seen: Table[int, bool]
        for val in allValues:
            check val notin seen
            seen[val] = true

    test "Sparse negative domain":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)

        # Non-contiguous domain with negative values
        x.setDomain(@[-10, -5, -1, 2, 7])

        sys.addConstraint(allDifferent(x))

        sys.resolve()
        let assignment = x.assignment()

        # Check all values are from the specified domain
        let validDomain = @[-10, -5, -1, 2, 7]
        for val in assignment:
            check val in validDomain

        # Check uniqueness
        var seen: Table[int, bool]
        for val in assignment:
            check val notin seen
            seen[val] = true