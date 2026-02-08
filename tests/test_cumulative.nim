import std/[sequtils, strutils, sets, unittest, tables]
import crusher

proc validateCumulativeSolution[T](origins: seq[T], durations: seq[T], heights: seq[T], limit: T): bool =
    ## Validates that the cumulative constraint is satisfied
    ## Returns true if at all time points, resource usage <= limit

    # Build resource profile
    var resourceProfile = initTable[T, T]()

    for i in 0..<origins.len:
        let origin = origins[i]
        let duration = durations[i]
        let height = heights[i]

        # Add resource usage for this task's time span
        for t in origin ..< (origin + duration):
            let currentUsage = resourceProfile.getOrDefault(t, T(0))
            resourceProfile[t] = currentUsage + height

    # Check that all time points are within limit
    for time, usage in resourceProfile.pairs:
        if usage > limit:
            echo "❌ Resource overload at time ", time, ": usage=", usage, ", limit=", limit
            return false

    return true

suite "Cumulative Constraint Tests":
    test "Basic cumulative constraint (from MiniZinc example)":
        # Example from Global Constraints Catalogue
        # Tasks with specific durations and resource heights
        # Should find valid start times that don't exceed limit

        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(5)
        origins.setDomain(toSeq(1..20))

        let durations = @[3, 9, 10, 6, 2]
        let heights = @[1, 2, 1, 1, 3]
        let limit = 8

        # Add cumulative constraint
        sys.addConstraint(cumulative[int]([0, 1, 2, 3, 4], durations, heights, limit))

        # Solve
        sys.resolve()

        # Extract and validate solution
        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

    test "Tight cumulative constraint (minimal limit)":
        # Test with a very tight resource limit
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(3)
        origins.setDomain(toSeq(1..10))

        let durations = @[3, 3, 3]
        let heights = @[2, 2, 2]
        let limit = 4  # Can only run 2 tasks simultaneously

        sys.addConstraint(cumulative[int]([0, 1, 2], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

    test "Simple non-overlapping tasks":
        # Two tasks that should be scheduled sequentially
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(2)
        origins.setDomain(toSeq(1..10))

        let durations = @[3, 3]
        let heights = @[5, 5]
        let limit = 5  # Can only run one task at a time

        sys.addConstraint(cumulative[int]([0, 1], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

        # Tasks should not overlap
        let task1End = solution[0] + durations[0]
        let task2Start = solution[1]
        let task2End = solution[1] + durations[1]
        let task1Start = solution[0]

        # Check no overlap
        check (task1End <= task2Start or task2End <= task1Start)

    test "Multiple tasks with varying heights":
        # More realistic scheduling scenario
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(4)
        origins.setDomain(toSeq(1..15))

        let durations = @[4, 3, 5, 2]
        let heights = @[3, 2, 4, 1]
        let limit = 6

        sys.addConstraint(cumulative[int]([0, 1, 2, 3], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

    test "Expression-based cumulative constraint":
        # Test with algebraic expressions for origin times
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        # Origins are expressions: x[0], x[1]+1, x[2]+2
        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0])
        originExprs.add(x[1] + 1)
        originExprs.add(x[2] + 2)

        let durations = @[2, 3, 2]
        let heights = @[3, 2, 3]
        let limit = 5

        sys.addConstraint(cumulative[int](originExprs, durations, heights, limit))

        sys.resolve()

        # Evaluate actual origins from expressions
        let assignment = x.assignment
        let actualOrigins = @[
            assignment[0],
            assignment[1] + 1,
            assignment[2] + 2
        ]

        check validateCumulativeSolution(actualOrigins, durations, heights, limit)

    test "Single task (trivial case)":
        # Single task should always be satisfiable
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(1)
        origins.setDomain(toSeq(1..10))

        let durations = @[5]
        let heights = @[3]
        let limit = 3

        sys.addConstraint(cumulative[int]([0], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

    test "Zero height tasks":
        # Tasks with zero resource consumption
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(3)
        origins.setDomain(toSeq(1..10))

        let durations = @[3, 3, 3]
        let heights = @[0, 0, 0]  # No resource usage
        let limit = 1

        sys.addConstraint(cumulative[int]([0, 1, 2], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

    test "Global Constraints Catalogue Example 1 (verified)":
        # Example from https://sofdem.github.io/gccat/gccat/Ccumulative.html
        # This is the canonical example with known valid solution
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(5)
        origins.setDomain(toSeq(1..20))

        let durations = @[3, 9, 10, 6, 2]
        let heights = @[1, 2, 1, 1, 3]
        let limit = 8

        sys.addConstraint(cumulative[int]([0, 1, 2, 3, 4], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

        # The known valid solution from the example is:
        # origins = [1, 2, 3, 6, 7] (but solver may find different valid solution)
        echo "  Found solution: origins = ", solution

    test "Global Constraints Catalogue Example 2 (non-ground)":
        # More challenging example with tighter constraints
        # From Figure 5.96.2 with variable domains
        var sys = initConstraintSystem[int]()
        var origins = sys.newConstrainedSequence(4)
        origins.setDomain(toSeq(1..8))  # All origins in range [1,8]

        # Using middle values from the variable ranges
        let durations = @[4, 6, 4, 2]  # Task durations
        let heights = @[4, 3, 2, 3]     # Resource demands (using middle of ranges)
        let limit = 5                   # Tight resource limit

        sys.addConstraint(cumulative[int]([0, 1, 2, 3], durations, heights, limit))

        sys.resolve()

        let solution = origins.assignment
        check validateCumulativeSolution(solution, durations, heights, limit)

        echo "  Found solution for tight constraint: origins = ", solution

    test "Schedule1 optimization (SICStus Prolog / Beldiceanu & Contejean 94)":
        ## Cumulative scheduling optimization problem
        ## Original source: https://www.hakank.org/picat/schedule1.pi
        ## From SICStus Prolog documentation
        ##
        ## 7 tasks with known optimal makespan of 23
        ## Task Duration Resource
        ##  t1    16       2
        ##  t2     6       9
        ##  t3    13       3
        ##  t4     7       7
        ##  t5     5      10
        ##  t6    18       1
        ##  t7     4      11

        const
            NumTasks = 7
            Capacity = 13
            Durations = @[16, 6, 13, 7, 5, 18, 4]
            Resources = @[2, 9, 3, 7, 10, 1, 11]
            OptimalMakespan = 23

        var sys = initConstraintSystem[int]()

        # Start times for each task (domain 1..30 as in original model)
        var startTimes = sys.newConstrainedSequence(NumTasks)
        startTimes.setDomain(toSeq(1..30))

        # Create algebraic expressions for cumulative constraint
        var startExpressions: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<NumTasks:
            startExpressions.add(startTimes[i])

        # Cumulative constraint
        sys.addConstraint(cumulative[int](startExpressions, Durations, Resources, Capacity))

        # Create end time expressions and minimize makespan
        var endExpressions: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<NumTasks:
            endExpressions.add(startTimes[i] + Durations[i])

        let makespan = max(endExpressions)

        # Optimize
        sys.minimize(makespan, parallel=true, verbose=false, multiplier=20)

        # Validate solution
        let solution = startTimes.assignment
        check validateCumulativeSolution(solution, Durations, Resources, Capacity)

        # Calculate actual makespan
        var actualMakespan = 0
        for i in 0..<NumTasks:
            actualMakespan = max(actualMakespan, solution[i] + Durations[i])

        echo "  Found makespan: ", actualMakespan, " (optimal: ", OptimalMakespan, ")"
        echo "  Start times: ", solution

        check actualMakespan == OptimalMakespan
