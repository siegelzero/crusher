import std/[sequtils, unittest]
import crusher

suite "AtLeast Constraint Tests":

    test "Basic position-based atleast constraint - satisfied":
        # Test basic atleast constraint with positions that is satisfied
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(5)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add atleast constraint: at least 2 occurrences of value 1
        let constraint = atLeast[int]([0, 1, 2, 3, 4], 1, 2)
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of value 1
        var count = 0
        for val in assignment:
            if val == 1:
                count += 1

        # Verify constraint is satisfied
        check count >= 2
        echo "Assignment: ", assignment, " (count of 1s: ", count, ")"

    test "Basic position-based atleast constraint - boundary case":
        # Test atleast constraint with exact minimum requirement
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        # Set domains - force all variables to be 1
        sequence.setDomain(toSeq(1..1))

        # Add atleast constraint: at least 3 occurrences of value 1
        let constraint = atLeast[int]([0, 1, 2], 1, 3)
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of value 1
        var count = 0
        for val in assignment:
            if val == 1:
                count += 1

        # Verify constraint is satisfied with exact count
        check count == 3
        check assignment == @[1, 1, 1]

    test "Position-based atleast constraint - over-satisfied":
        # Test atleast constraint that can be over-satisfied
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(6)

        # Set domains to allow multiple values
        sequence.setDomain(toSeq(1..2))

        # Add atleast constraint: at least 2 occurrences of value 1
        let constraint = atLeast[int]([0, 1, 2, 3, 4, 5], 1, 2)
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of value 1
        var count = 0
        for val in assignment:
            if val == 1:
                count += 1

        # Verify constraint is satisfied (could have more than 2)
        check count >= 2
        echo "Over-satisfied case - Assignment: ", assignment, " (count of 1s: ", count, ")"

    test "Position-based atleast constraint with different target value":
        # Test atleast constraint with target value other than 1
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains
        sequence.setDomain(toSeq(2..4))

        # Add atleast constraint: at least 2 occurrences of value 3
        let constraint = atLeast[int]([0, 1, 2, 3], 3, 2)
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of value 3
        var count = 0
        for val in assignment:
            if val == 3:
                count += 1

        # Verify constraint is satisfied
        check count >= 2
        echo "Different target value - Assignment: ", assignment, " (count of 3s: ", count, ")"

    test "Position-based atleast constraint - minimum requirement":
        # Test atleast constraint with minimum possible satisfying assignment
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add atleast constraint: at least 2 occurrences of value 2
        let constraint = atLeast[int]([0, 1, 2, 3], 2, 2)
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of value 2
        var count = 0
        for val in assignment:
            if val == 2:
                count += 1

        # Verify constraint is satisfied with at least minimum requirement
        check count >= 2
        echo "Minimum requirement - Assignment: ", assignment, " (count of 2s: ", count, ")"

    test "AtLeast constraint with multiple constraints":
        # Test atleast constraint combined with other constraints
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(5)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add atleast constraint: at least 2 occurrences of value 1
        let atLeastConstraint = atLeast[int]([0, 1, 2, 3, 4], 1, 2)
        sys.addConstraint(atLeastConstraint)

        # Add another atleast constraint: at least 1 occurrence of value 3
        let atLeastConstraint2 = atLeast[int]([0, 1, 2, 3, 4], 3, 1)
        sys.addConstraint(atLeastConstraint2)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of both target values
        var count1 = 0
        var count3 = 0
        for val in assignment:
            if val == 1:
                count1 += 1
            elif val == 3:
                count3 += 1

        # Verify both constraints are satisfied
        check count1 >= 2
        check count3 >= 1
        echo "Multiple constraints - Assignment: ", assignment, " (1s: ", count1, ", 3s: ", count3, ")"

    test "AtLeast constraint cost calculation":
        # Test that the constraint correctly calculates cost when violated
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        # Set up domains that might not satisfy the constraint
        sequence.setDomain(toSeq(2..3))

        # Add atleast constraint: at least 2 occurrences of value 1 (which may not be possible)
        let constraint = atLeast[int]([0, 1, 2], 1, 2)
        sys.addConstraint(constraint)

        # Initialize the constraint manually to test cost calculation
        let assignment = @[2, 3, 2]
        constraint.initialize(assignment)

        # The constraint should have positive cost since no 1s are present but we need 2
        check constraint.penalty() > 0
        echo "Cost with no 1s (need 2): ", constraint.penalty()

        # Test with partial satisfaction
        let assignment2 = @[1, 3, 2]
        constraint.initialize(assignment2)

        # The constraint should have cost 1 since we have 1 occurrence but need 2
        check constraint.penalty() == 1
        echo "Cost with 1 occurrence (need 2): ", constraint.penalty()

        # Test with full satisfaction
        let assignment3 = @[1, 1, 2]
        constraint.initialize(assignment3)

        # The constraint should have cost 0 since we have 2 occurrences and need 2
        check constraint.penalty() == 0
        echo "Cost with 2 occurrences (need 2): ", constraint.penalty()

    test "AtLeast constraint with negative domains":
        # Test atleast constraint with negative values in domain
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains with negative values
        sequence.setDomain(toSeq(-2..1))

        # Add atleast constraint: at least 2 occurrences of value -1
        let constraint = atLeast[int]([0, 1, 2, 3], -1, 2)
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Count occurrences of value -1
        var count = 0
        for val in assignment:
            if val == -1:
                count += 1

        # Verify constraint is satisfied
        check count >= 2
        echo "Negative domain - Assignment: ", assignment, " (count of -1s: ", count, ")"

    test "AtLeast constraint moveDelta functionality":
        # Test that moveDelta correctly predicts cost changes
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        sequence.setDomain(toSeq(1..3))

        let constraint = atLeast[int]([0, 1, 2], 2, 2)
        sys.addConstraint(constraint)

        # Initialize with an assignment that doesn't satisfy the constraint
        let initialAssignment = @[1, 3, 3]  # Only 1 occurrence of value 2, need 2
        constraint.initialize(initialAssignment)

        let initialCost = constraint.penalty()

        # Test moving position 1 from 3 to 2 (should improve cost)
        let delta = constraint.atLeastState.moveDelta(1, 3, 2)

        # Apply the move and check actual cost change
        constraint.updatePosition(1, 2)
        let newCost = constraint.penalty()

        # Verify delta prediction matches actual change
        check newCost - initialCost == delta
        echo "Move delta test - Initial cost: ", initialCost, ", Delta: ", delta, ", New cost: ", newCost