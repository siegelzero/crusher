import std/[sequtils, strutils, sets, unittest]
import crusher

suite "Global Cardinality Constraint Tests":

    test "Basic global cardinality with exact counts":
        # Test a simple case: values should appear exactly the specified number of times
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(5)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add global cardinality constraint: value 1 appears 2 times, value 2 appears 2 times, value 3 appears 1 time
        let constraint = globalCardinality[int]([0, 1, 2, 3, 4], [1, 2, 3], [2, 2, 1])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of each value
        var counts = [0, 0, 0, 0]  # counts[0] unused, counts[1-3] for values 1-3
        for val in assignment:
            if val >= 1 and val <= 3:
                counts[val] += 1

        # Verify exact counts
        check counts[1] == 2  # value 1 appears 2 times
        check counts[2] == 2  # value 2 appears 2 times
        check counts[3] == 1  # value 3 appears 1 time

    test "Global cardinality with bounded counts":
        # Test bounded variant: each value should appear within specified bounds
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(6)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add bounded global cardinality constraint:
        # value 1 appears 1-3 times, value 2 appears 2-3 times, value 3 appears 0-2 times
        let constraint = globalCardinalityBounded[int]([0, 1, 2, 3, 4, 5], [1, 2, 3], [1, 2, 0], [3, 3, 2])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of each value
        var counts = [0, 0, 0, 0]  # counts[0] unused, counts[1-3] for values 1-3
        for val in assignment:
            if val >= 1 and val <= 3:
                counts[val] += 1

        # Verify bounds are respected
        check counts[1] >= 1 and counts[1] <= 3  # value 1 within bounds 1-3
        check counts[2] >= 2 and counts[2] <= 3  # value 2 within bounds 2-3
        check counts[3] >= 0 and counts[3] <= 2  # value 3 within bounds 0-2

    test "Global cardinality with small domains":
        # Test with very constrained domains
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains - all variables must be 1
        sequence.setDomain(toSeq(1..1))

        # Add constraint: value 1 appears exactly 4 times
        let constraint = globalCardinality[int]([0, 1, 2, 3], [1], [4])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment
        check assignment == @[1, 1, 1, 1]

    test "Global cardinality with expression-based constraint":
        # Test global cardinality constraint applied to algebraic expressions
        var sys = initConstraintSystem[int]()
        var matrix = sys.newConstrainedMatrix(2, 2)  # 2x2 matrix

        # Set domains
        matrix.setDomain(toSeq(1..4))

        # Create expressions for row sums
        var rowSumExpressions: seq[AlgebraicExpression[int]] = @[]
        for row in matrix.rows():
            rowSumExpressions.add(row.foldl(a + b))

        # Add global cardinality constraint on row sums: sum 3 appears 1 time, sum 5 appears 1 time
        let constraint = globalCardinality[int](rowSumExpressions, [3, 5], [1, 1])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = matrix.assignment
        let row1SumValue = assignment[0][0] + assignment[0][1]
        let row2SumValue = assignment[1][0] + assignment[1][1]

        # Check that we have exactly one sum of 3 and one sum of 5
        let sums = @[row1SumValue, row2SumValue]
        check (sums.count(3) == 1 and sums.count(5) == 1)

    test "Multiple global cardinality constraints":
        # Test system with multiple global cardinality constraints
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(6)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add first constraint: in positions 0-2, value 1 appears 2 times, value 2 appears 1 time
        let constraint1 = globalCardinality[int]([0, 1, 2], [1, 2], [2, 1])
        sys.addConstraint(constraint1)

        # Add second constraint: in positions 3-5, value 2 appears 2 times, value 3 appears 1 time
        let constraint2 = globalCardinality[int]([3, 4, 5], [2, 3], [2, 1])
        sys.addConstraint(constraint2)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Check first constraint (positions 0-2)
        var counts1 = [0, 0, 0, 0]
        for i in 0..2:
            if assignment[i] >= 1 and assignment[i] <= 3:
                counts1[assignment[i]] += 1
        check counts1[1] == 2 and counts1[2] == 1

        # Check second constraint (positions 3-5)
        var counts2 = [0, 0, 0, 0]
        for i in 3..5:
            if assignment[i] >= 1 and assignment[i] <= 3:
                counts2[assignment[i]] += 1
        check counts2[2] == 2 and counts2[3] == 1

    test "Global cardinality with zero counts":
        # Test constraint where some values should appear 0 times
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        sequence.setDomain(toSeq(1..3))

        # Constraint: value 1 appears 3 times, value 2 appears 0 times, value 3 appears 0 times
        let constraint = globalCardinality[int]([0, 1, 2], [1, 2, 3], [3, 0, 0])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment
        check assignment == @[1, 1, 1]  # All values should be 1

    test "Global cardinality combined with allDifferent":
        # Test global cardinality working with other constraints
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        sequence.setDomain(toSeq(1..4))

        # Add allDifferent constraint (all values must be different)
        var terms: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<4:
            terms.add(sequence[i])
        sys.addConstraint(allDifferent(terms))

        # Add global cardinality constraint: each value 1,2,3,4 appears exactly 1 time
        let constraint = globalCardinality[int]([0, 1, 2, 3], [1, 2, 3, 4], [1, 1, 1, 1])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Verify all different
        check assignment.toHashSet().card == 4

        # Verify each value appears exactly once
        var counts = [0, 0, 0, 0, 0]  # counts[0] unused, counts[1-4] for values 1-4
        for val in assignment:
            if val >= 1 and val <= 4:
                counts[val] += 1

        for i in 1..4:
            check counts[i] == 1