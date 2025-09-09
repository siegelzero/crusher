import std/[sequtils, unittest]
import crusher

suite "Sequence Constraint Tests":

    test "Basic position-based sequence constraint - satisfied":
        # Test basic sequence constraint that is satisfied
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(6)

        # Set domains - values 1, 2
        seq.setDomain(toSeq(1..2))

        # Sequence constraint: in any 3 consecutive positions, at least 1 and at most 2 values from {2}
        let constraint = sequence[int]([0, 1, 2, 3, 4, 5], 1, 2, 3, [2])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = seq.assignment

        # Manually verify the constraint is satisfied
        # Check all windows of size 3
        for i in 0..(assignment.len - 3):
            var countInSet = 0
            for j in 0..<3:
                if assignment[i + j] == 2:
                    countInSet += 1

            check countInSet >= 1  # at least 1
            check countInSet <= 2  # at most 2

        echo "Assignment: ", assignment

    test "Position-based sequence constraint - boundary case":
        # Test sequence constraint at boundary conditions
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(4)

        # Set domains
        seq.setDomain(toSeq(1..3))

        # Sequence constraint: in any 2 consecutive positions, exactly 1 value from {3}
        let constraint = sequence[int]([0, 1, 2, 3], 1, 1, 2, [3])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = seq.assignment

        # Check all windows of size 2 have exactly 1 occurrence of value 3
        for i in 0..(assignment.len - 2):
            var countInSet = 0
            for j in 0..<2:
                if assignment[i + j] == 3:
                    countInSet += 1
            check countInSet == 1  # exactly 1

        echo "Boundary case - Assignment: ", assignment

    test "Position-based sequence constraint with violations":
        # Test constraint cost calculation when violated
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(4)

        seq.setDomain(toSeq(1..2))

        # Create a constraint that should have violations initially
        let constraint = sequence[int]([0, 1, 2, 3], 2, 2, 3, [2])

        # Initialize with an assignment that violates the constraint
        let assignment = @[1, 1, 1, 1]  # No 2s, but need exactly 2 in each window of 3
        constraint.initialize(assignment)

        # Each window of 3 has 0 occurrences of 2, but needs 2, so cost = 2 per window
        # Windows: [1,1,1], [1,1,1] - 2 windows, each with cost 2
        check constraint.penalty() == 4
        echo "Violation cost (no 2s, need 2 per window): ", constraint.penalty()

        # Test with partial satisfaction
        let assignment2 = @[2, 1, 1, 1]  # First window has 1 occurrence of 2, needs 2
        constraint.initialize(assignment2)

        # Windows: [2,1,1] (cost 1), [1,1,1] (cost 2) - total cost 3
        check constraint.penalty() == 3
        echo "Partial violation cost: ", constraint.penalty()

        # Test with full satisfaction
        let assignment3 = @[2, 2, 1, 2]  # Each window should have exactly 2 occurrences of 2
        constraint.initialize(assignment3)

        # Windows: [2,2,1] (2 occurrences - satisfied), [2,1,2] (2 occurrences - satisfied)
        check constraint.penalty() == 0
        echo "Full satisfaction cost: ", constraint.penalty()

    test "Sequence constraint with different window sizes":
        # Test sequence constraint with varied window sizes
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(5)

        seq.setDomain(toSeq(1..3))

        # Sequence constraint with window size 4: at least 2 values from {1, 2}
        let constraint = sequence[int]([0, 1, 2, 3, 4], 2, 4, 4, [1, 2])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = seq.assignment

        # Check all windows of size 4
        for i in 0..(assignment.len - 4):
            var countInSet = 0
            for j in 0..<4:
                if assignment[i + j] in [1, 2]:
                    countInSet += 1
            check countInSet >= 2  # at least 2
            check countInSet <= 4  # at most 4

        echo "Different window size - Assignment: ", assignment

    test "Sequence constraint with multiple constraints":
        # Test sequence constraint combined with other constraints
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(5)

        seq.setDomain(toSeq(1..3))

        # Add sequence constraint
        let seqConstraint = sequence[int]([0, 1, 2, 3, 4], 1, 2, 3, [3])
        sys.addConstraint(seqConstraint)

        # Add atleast constraint to ensure we use multiple values
        let atLeastConstraint = atLeast[int]([0, 1, 2, 3, 4], 1, 2)
        sys.addConstraint(atLeastConstraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = seq.assignment

        # Verify sequence constraint
        for i in 0..(assignment.len - 3):
            var countInSet = 0
            for j in 0..<3:
                if assignment[i + j] == 3:
                    countInSet += 1
            check countInSet >= 1
            check countInSet <= 2

        # Verify atleast constraint (at least 2 occurrences of value 1)
        var count1 = 0
        for val in assignment:
            if val == 1:
                count1 += 1
        check count1 >= 2

        echo "Multiple constraints - Assignment: ", assignment

    test "Sequence constraint moveDelta functionality":
        # Test that moveDelta correctly predicts cost changes
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(4)

        seq.setDomain(toSeq(1..3))

        let constraint = sequence[int]([0, 1, 2, 3], 1, 1, 2, [2])

        # Initialize with an assignment
        let initialAssignment = @[1, 2, 1, 1]  # Windows: [1,2], [2,1], [1,1] - first 2 satisfied, last violated
        constraint.initialize(initialAssignment)

        let initialCost = constraint.penalty()

        # Test moving position 3 from 1 to 2 (should improve cost)
        let delta = constraint.moveDelta(3, 1, 2)

        # Apply the move and check actual cost change
        constraint.updatePosition(3, 2)
        let newCost = constraint.penalty()

        # Verify delta prediction matches actual change
        check newCost - initialCost == delta
        echo "Move delta test - Initial cost: ", initialCost, ", Delta: ", delta, ", New cost: ", newCost

    test "Sequence constraint with empty target set":
        # Test constraint with empty target set
        var constraint = sequence[int]([0, 1, 2], 0, 0, 2, [])  # No values in target set

        # Initialize with assignment
        let assignment = @[1, 2, 3]
        constraint.initialize(assignment)

        # Should have no violations since no values should be in empty set
        check constraint.penalty() == 0
        echo "Empty target set test - Cost: ", constraint.penalty()

    test "Sequence constraint updatePosition functionality":
        # Test incremental updates work correctly
        var constraint = sequence[int]([0, 1, 2, 3], 1, 2, 3, [2])

        # Initialize with assignment
        let assignment = @[1, 1, 1, 1]  # No 2s, each window needs at least 1
        constraint.initialize(assignment)

        let initialCost = constraint.penalty()

        # Update position 1 from 1 to 2
        constraint.updatePosition(1, 2)

        # This should reduce violations in windows that include position 1
        check constraint.penalty() < initialCost
        echo "Update test - Initial cost: ", initialCost, ", New cost: ", constraint.penalty()

    test "Sequence constraint edge case - single window":
        # Test with sequence length equal to window size
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(3)

        seq.setDomain(toSeq(1..2))

        # Window size equals sequence length
        let constraint = sequence[int]([0, 1, 2], 1, 2, 3, [2])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = seq.assignment

        # Only one window to check
        var countInSet = 0
        for val in assignment:
            if val == 2:
                countInSet += 1

        check countInSet >= 1  # at least 1
        check countInSet <= 2  # at most 2

        echo "Single window test - Assignment: ", assignment

    test "Sequence constraint with large target set":
        # Test sequence constraint with most values in target set
        var sys = initConstraintSystem[int]()
        var seq = sys.newConstrainedSequence(4)

        seq.setDomain(toSeq(1..4))

        # Target set contains most values
        let constraint = sequence[int]([0, 1, 2, 3], 2, 3, 3, [1, 2, 3])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = seq.assignment

        # Check all windows of size 3
        for i in 0..(assignment.len - 3):
            var countInSet = 0
            for j in 0..<3:
                if assignment[i + j] in [1, 2, 3]:
                    countInSet += 1
            check countInSet >= 2  # at least 2
            check countInSet <= 3  # at most 3

        echo "Large target set - Assignment: ", assignment