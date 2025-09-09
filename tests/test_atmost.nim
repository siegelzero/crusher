import std/[sequtils, unittest]
import crusher

suite "AtMost Constraint Tests":

    test "Basic position-based atmost constraint - satisfied":
        # Test basic atmost constraint with positions that is satisfied
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(5)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add atmost constraint: at most 2 occurrences of value 1
        let constraint = atMost[int]([0, 1, 2, 3, 4], 1, 2)
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
        check count <= 2
        echo "Assignment: ", assignment, " (count of 1s: ", count, ")"

    test "Basic position-based atmost constraint - boundary case":
        # Test atmost constraint with exact maximum requirement
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        # Set domains - force all variables to be 1
        sequence.setDomain(toSeq(1..1))

        # Add atmost constraint: at most 3 occurrences of value 1
        let constraint = atMost[int]([0, 1, 2], 1, 3)
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
        check count <= 3
        check assignment == @[1, 1, 1]

    test "Position-based atmost constraint - under-satisfied":
        # Test atmost constraint that is under-satisfied (which is fine)
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(6)

        # Set domains to allow multiple values
        sequence.setDomain(toSeq(1..2))

        # Add atmost constraint: at most 4 occurrences of value 1
        let constraint = atMost[int]([0, 1, 2, 3, 4, 5], 1, 4)
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

        # Verify constraint is satisfied (could have fewer than 4)
        check count <= 4
        echo "Under-satisfied case - Assignment: ", assignment, " (count of 1s: ", count, ")"

    test "Position-based atmost constraint with different target value":
        # Test atmost constraint with target value other than 1
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains
        sequence.setDomain(toSeq(2..4))

        # Add atmost constraint: at most 2 occurrences of value 3
        let constraint = atMost[int]([0, 1, 2, 3], 3, 2)
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
        check count <= 2
        echo "Different target value - Assignment: ", assignment, " (count of 3s: ", count, ")"

    test "Position-based atmost constraint - maximum requirement":
        # Test atmost constraint with maximum possible satisfying assignment
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add atmost constraint: at most 2 occurrences of value 2
        let constraint = atMost[int]([0, 1, 2, 3], 2, 2)
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

        # Verify constraint is satisfied with at most maximum requirement
        check count <= 2
        echo "Maximum requirement - Assignment: ", assignment, " (count of 2s: ", count, ")"

    test "AtMost constraint with multiple constraints":
        # Test atmost constraint combined with other constraints
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(5)

        # Set domains
        sequence.setDomain(toSeq(1..3))

        # Add atmost constraint: at most 2 occurrences of value 1
        let atMostConstraint = atMost[int]([0, 1, 2, 3, 4], 1, 2)
        sys.addConstraint(atMostConstraint)

        # Add another atmost constraint: at most 3 occurrences of value 3
        let atMostConstraint2 = atMost[int]([0, 1, 2, 3, 4], 3, 3)
        sys.addConstraint(atMostConstraint2)

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
        check count1 <= 2
        check count3 <= 3
        echo "Multiple constraints - Assignment: ", assignment, " (1s: ", count1, ", 3s: ", count3, ")"

    test "AtMost constraint cost calculation":
        # Test that the constraint correctly calculates cost when violated
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        # Set up domains that allow the constraint to be violated
        sequence.setDomain(toSeq(1..3))

        # Add atmost constraint: at most 1 occurrence of value 1
        let constraint = atMost[int]([0, 1, 2], 1, 1)
        sys.addConstraint(constraint)

        # Initialize the constraint manually to test cost calculation
        let assignment = @[2, 3, 2]  # No 1s present - should have cost 0
        constraint.initialize(assignment)

        # The constraint should have zero cost since no 1s are present
        check constraint.penalty() == 0
        echo "Cost with no 1s (max 1): ", constraint.penalty()

        # Test with exact satisfaction
        let assignment2 = @[1, 3, 2]  # 1 occurrence of 1 - should have cost 0
        constraint.initialize(assignment2)

        # The constraint should have cost 0 since we have 1 occurrence and max is 1
        check constraint.penalty() == 0
        echo "Cost with 1 occurrence (max 1): ", constraint.penalty()

        # Test with violation
        let assignment3 = @[1, 1, 2]  # 2 occurrences of 1 - should have cost 1
        constraint.initialize(assignment3)

        # The constraint should have cost 1 since we have 2 occurrences but max is 1
        check constraint.penalty() == 1
        echo "Cost with 2 occurrences (max 1): ", constraint.penalty()

        # Test with larger violation
        let assignment4 = @[1, 1, 1]  # 3 occurrences of 1 - should have cost 2
        constraint.initialize(assignment4)

        # The constraint should have cost 2 since we have 3 occurrences but max is 1
        check constraint.penalty() == 2
        echo "Cost with 3 occurrences (max 1): ", constraint.penalty()

    test "AtMost constraint with negative domains":
        # Test atmost constraint with negative values in domain
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains with negative values
        sequence.setDomain(toSeq(-2..1))

        # Add atmost constraint: at most 2 occurrences of value -1
        let constraint = atMost[int]([0, 1, 2, 3], -1, 2)
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
        check count <= 2
        echo "Negative domain - Assignment: ", assignment, " (count of -1s: ", count, ")"

    test "AtMost constraint moveDelta functionality":
        # Test that moveDelta correctly predicts cost changes
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        sequence.setDomain(toSeq(1..3))

        let constraint = atMost[int]([0, 1, 2], 2, 1)  # at most 1 occurrence of value 2
        sys.addConstraint(constraint)

        # Initialize with an assignment that violates the constraint
        let initialAssignment = @[2, 2, 3]  # 2 occurrences of value 2, max is 1
        constraint.initialize(initialAssignment)

        let initialCost = constraint.penalty()
        check initialCost == 1  # Should have cost 1 (2 - 1 = 1)

        # Test moving position 1 from 2 to 3 (should improve cost)
        let delta = constraint.atMostState.moveDelta(1, 2, 3)

        # Apply the move and check actual cost change
        constraint.updatePosition(1, 3)
        let newCost = constraint.penalty()

        # Verify delta prediction matches actual change
        check newCost - initialCost == delta
        check newCost == 0  # Should now be satisfied with 1 occurrence
        echo "Move delta test - Initial cost: ", initialCost, ", Delta: ", delta, ", New cost: ", newCost

    test "AtMost constraint with zero maximum":
        # Test atmost constraint that forbids all occurrences
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        # Set domains
        sequence.setDomain(toSeq(2..4))

        # Add atmost constraint: at most 0 occurrences of value 1 (forbid value 1)
        let constraint = atMost[int]([0, 1, 2], 1, 0)
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

        # Verify constraint is satisfied (no occurrences of 1)
        check count == 0
        echo "Zero maximum - Assignment: ", assignment, " (count of 1s: ", count, ")"

    test "AtMost constraint violation handling":
        # Test atmost constraint that will definitely be violated with current domains
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains to only allow value 1
        sequence.setDomain(toSeq(1..1))

        # Add atmost constraint: at most 2 occurrences of value 1 (but we have 4 positions)
        let constraint = atMost[int]([0, 1, 2, 3], 1, 2)
        sys.addConstraint(constraint)

        # Initialize manually to test violation cost
        let assignment = @[1, 1, 1, 1]  # 4 occurrences but max is 2
        constraint.initialize(assignment)

        # Should have cost 2 (4 - 2 = 2)
        check constraint.penalty() == 2
        echo "Violation handling - Cost with 4 occurrences (max 2): ", constraint.penalty()