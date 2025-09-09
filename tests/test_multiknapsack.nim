import std/[sequtils, unittest]
import crusher

suite "Multiknapsack Constraint Tests":

    test "Basic position-based multiknapsack constraint - satisfied":
        # Test basic multiknapsack constraint that is satisfied
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        # Set domains - values 1, 2, 3
        sequence.setDomain(toSeq(1..3))

        # Weights: [2, 3, 1, 2] for positions [0, 1, 2, 3]
        # Capacities: value 1 -> capacity 4, value 2 -> capacity 5, value 3 -> capacity 3
        let constraint = multiknapsack[int]([0, 1, 2, 3], [2, 3, 1, 2], [(1, 4), (2, 5), (3, 3)])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Manually verify the constraint is satisfied
        var loads = [0, 0, 0, 0]  # loads for values 0, 1, 2, 3 (index = value)
        let weights = [2, 3, 1, 2]
        let capacities = [0, 4, 5, 3]  # capacities for values 0, 1, 2, 3

        for i in 0..<assignment.len:
            if assignment[i] >= 1 and assignment[i] <= 3:
                loads[assignment[i]] += weights[i]

        # Check that no value exceeds its capacity
        for value in 1..3:
            check loads[value] <= capacities[value]

        echo "Assignment: ", assignment
        echo "Loads: value 1=", loads[1], " (≤4), value 2=", loads[2], " (≤5), value 3=", loads[3], " (≤3)"

    test "Position-based multiknapsack constraint - boundary case":
        # Test multiknapsack constraint at capacity boundaries
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        # Set domains
        sequence.setDomain(toSeq(1..2))

        # Weights: [3, 2, 1] for positions [0, 1, 2]
        # Capacities: value 1 -> capacity 3, value 2 -> capacity 3
        # If all assigned to value 1: 3+2+1=6 > 3 (violates)
        # Need to distribute between values 1 and 2
        let constraint = multiknapsack[int]([0, 1, 2], [3, 2, 1], [(1, 3), (2, 3)])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Calculate actual loads
        var load1, load2 = 0
        let weights = [3, 2, 1]

        for i in 0..<assignment.len:
            if assignment[i] == 1:
                load1 += weights[i]
            elif assignment[i] == 2:
                load2 += weights[i]

        # Verify capacities are respected
        check load1 <= 3
        check load2 <= 3

        echo "Boundary case - Assignment: ", assignment
        echo "Load 1: ", load1, " (≤3), Load 2: ", load2, " (≤3)"

    test "Position-based multiknapsack constraint with over-capacity":
        # Test constraint cost calculation when over capacity
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        sequence.setDomain(toSeq(1..2))

        # Create a constraint that should have violations initially
        let constraint = multiknapsack[int]([0, 1, 2], [3, 3, 3], [(1, 5), (2, 5)])

        # Initialize with an assignment that violates the constraint
        let assignment = @[1, 1, 1]  # All assigned to value 1, total weight = 9 > capacity 5
        constraint.initialize(assignment)

        # The constraint should have positive cost (over-capacity = 9 - 5 = 4)
        check constraint.penalty() == 4
        echo "Over-capacity cost (9-5): ", constraint.penalty()

        # Test with partial violation
        let assignment2 = @[1, 1, 2]  # Two to value 1 (weight 6 > 5), one to value 2 (weight 3 ≤ 5)
        constraint.initialize(assignment2)

        # The constraint should have cost 1 (over-capacity for value 1 = 6 - 5 = 1)
        check constraint.penalty() == 1
        echo "Partial over-capacity cost (6-5): ", constraint.penalty()

        # Test with no violations
        let assignment3 = @[1, 2, 2]  # One to value 1 (weight 3 ≤ 5), two to value 2 (weight 6 > 5)
        constraint.initialize(assignment3)

        # The constraint should have cost 1 (over-capacity for value 2 = 6 - 5 = 1)
        check constraint.penalty() == 1
        echo "Different over-capacity cost: ", constraint.penalty()

    test "Multiknapsack constraint with different weights":
        # Test multiknapsack with varied weights
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(5)

        sequence.setDomain(toSeq(1..3))

        # Different weights for each position
        let constraint = multiknapsack[int]([0, 1, 2, 3, 4], [1, 2, 3, 4, 5], [(1, 10), (2, 8), (3, 6)])
        sys.addConstraint(constraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Calculate loads
        var loads = [0, 0, 0, 0]  # for values 0, 1, 2, 3
        let weights = [1, 2, 3, 4, 5]

        for i in 0..<assignment.len:
            if assignment[i] >= 1 and assignment[i] <= 3:
                loads[assignment[i]] += weights[i]

        # Verify no over-capacity
        check loads[1] <= 10
        check loads[2] <= 8
        check loads[3] <= 6

        echo "Different weights - Assignment: ", assignment
        echo "Loads: ", loads[1], ", ", loads[2], ", ", loads[3]

    test "Multiknapsack constraint with multiple constraints":
        # Test multiknapsack combined with other constraints
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(4)

        sequence.setDomain(toSeq(1..3))

        # Add multiknapsack constraint
        let mkConstraint = multiknapsack[int]([0, 1, 2, 3], [2, 2, 2, 2], [(1, 4), (2, 4), (3, 4)])
        sys.addConstraint(mkConstraint)

        # Add atleast constraint to ensure we use multiple values
        let atLeastConstraint = atLeast[int]([0, 1, 2, 3], 1, 1)
        sys.addConstraint(atLeastConstraint)

        # Solve the constraint system
        sys.resolve()

        # Extract solution and verify
        let assignment = sequence.assignment

        # Verify multiknapsack constraint
        var loads = [0, 0, 0, 0]
        let weights = [2, 2, 2, 2]

        for i in 0..<assignment.len:
            if assignment[i] >= 1 and assignment[i] <= 3:
                loads[assignment[i]] += weights[i]

        for value in 1..3:
            check loads[value] <= 4

        # Verify atleast constraint (at least one occurrence of value 1)
        var count1 = 0
        for val in assignment:
            if val == 1:
                count1 += 1
        check count1 >= 1

        echo "Multiple constraints - Assignment: ", assignment

    test "Multiknapsack constraint moveDelta functionality":
        # Test that moveDelta correctly predicts cost changes
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(3)

        sequence.setDomain(toSeq(1..3))

        let constraint = multiknapsack[int]([0, 1, 2], [3, 2, 1], [(1, 4), (2, 3), (3, 2)])

        # Initialize with an assignment
        let initialAssignment = @[1, 1, 2]  # Load 1: 5 > 4, Load 2: 1 ≤ 3
        constraint.initialize(initialAssignment)

        let initialCost = constraint.penalty()

        # Test moving position 2 from 2 to 1 (should worsen cost)
        let delta = constraint.moveDelta(2, 2, 1)

        # Apply the move and check actual cost change
        constraint.updatePosition(2, 1)
        let newCost = constraint.penalty()

        # Verify delta prediction matches actual change
        check newCost - initialCost == delta
        echo "Move delta test - Initial cost: ", initialCost, ", Delta: ", delta, ", New cost: ", newCost

    test "Multiknapsack constraint with zero capacities":
        # Test edge case with zero capacity values
        var sys = initConstraintSystem[int]()
        var sequence = sys.newConstrainedSequence(2)

        sequence.setDomain(toSeq(1..3))

        # Value 1 has zero capacity - any assignment to it should cause violation
        let constraint = multiknapsack[int]([0, 1], [1, 1], [(1, 0), (2, 5), (3, 5)])

        # Test with assignment to zero-capacity value
        let assignment = @[1, 2]  # Position 0 assigned to value 1 (capacity 0)
        constraint.initialize(assignment)

        # Should have cost equal to the weight assigned to value 1
        check constraint.penalty() == 1
        echo "Zero capacity test - Cost: ", constraint.penalty()

    test "Multiknapsack constraint updatePosition functionality":
        # Test incremental updates work correctly
        var constraint = multiknapsack[int]([0, 1, 2], [2, 3, 1], [(1, 5), (2, 4)])

        # Initialize with assignment
        let assignment = @[1, 1, 2]  # Load 1: 5, Load 2: 1
        constraint.initialize(assignment)

        let initialCost = constraint.penalty()

        # Update position 1 from 1 to 2
        constraint.updatePosition(1, 2)

        # Manually calculate expected loads after update
        # New assignment: [1, 2, 2] -> Load 1: 2, Load 2: 4
        # Both within capacity, so cost should be 0
        check constraint.penalty() == 0
        echo "Update test - Initial cost: ", initialCost, ", New cost: ", constraint.penalty()