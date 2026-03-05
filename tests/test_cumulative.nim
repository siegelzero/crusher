import std/[sequtils, strutils, sets, unittest, tables]
import crusher
import constraints/cumulative

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
        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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

        sys.resolve(parallel=true)

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
        sys.minimize(makespan, parallel=true, verbose=false,
                     populationSize=10, tabuThreshold=100)

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

    test "Variable limit - basic":
        # The limit is a decision variable; solver must find a feasible assignment
        # for both task origins and the limit value
        var sys = initConstraintSystem[int]()

        # 3 tasks + 1 limit variable
        var origins = sys.newConstrainedSequence(3)
        origins.setDomain(toSeq(1..15))
        var limitVar = sys.newConstrainedVariable()
        limitVar.setDomain(toSeq(3..10))

        let durations = @[3, 4, 2]
        let heights = @[2, 3, 2]

        # limitVar is at position 3 (after origins 0,1,2)
        sys.addConstraint(cumulative[int]([0, 1, 2], durations, heights,
                                          limit = 10, limitPosition = 3))

        sys.resolve(parallel=true)

        let solution = origins.assignment
        let assignedLimit = limitVar.assignment
        check validateCumulativeSolution(solution, durations, heights, assignedLimit)

    test "Variable limit - optimization (minimize limit)":
        # Minimize the resource capacity needed to schedule all tasks
        var sys = initConstraintSystem[int]()

        var origins = sys.newConstrainedSequence(3)
        origins.setDomain(toSeq(1..20))
        var limitVar = sys.newConstrainedVariable()
        limitVar.setDomain(toSeq(1..10))

        # 3 tasks: each height=3, duration=5
        # With 3 tasks in domain 1..20, they can be spread out to avoid overlap
        # Minimum possible limit = 3 (one task at a time)
        let durations = @[5, 5, 5]
        let heights = @[3, 3, 3]

        sys.addConstraint(cumulative[int]([0, 1, 2], durations, heights,
                                          limit = 10, limitPosition = 3))

        sys.minimize(AlgebraicExpression[int](limitVar), parallel=true, verbose=false,
                     populationSize=10, tabuThreshold=100)

        let solution = origins.assignment
        let assignedLimit = limitVar.assignment
        check validateCumulativeSolution(solution, durations, heights, assignedLimit)

        # With enough time domain, tasks can be sequential -> limit = 3
        echo "  Variable limit optimized to: ", assignedLimit
        check assignedLimit == 3

    test "Variable limit - expression-based origins":
        # Combine variable limit with expression-based origin times
        var sys = initConstraintSystem[int]()

        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..12))
        var limitVar = sys.newConstrainedVariable()
        limitVar.setDomain(toSeq(4..10))

        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0])
        originExprs.add(x[1] + 1)
        originExprs.add(x[2] + 2)

        let durations = @[2, 3, 2]
        let heights = @[3, 2, 3]

        # limitVar is at position 3
        sys.addConstraint(cumulative[int](originExprs, durations, heights,
                                          limit = 10, limitPosition = 3))

        sys.resolve(parallel=true)

        let assignment = x.assignment
        let assignedLimit = limitVar.assignment
        let actualOrigins = @[
            assignment[0],
            assignment[1] + 1,
            assignment[2] + 2
        ]
        check validateCumulativeSolution(actualOrigins, durations, heights, assignedLimit)

suite "ExpressionBased Cumulative batchMovePenalty":
    test "Single-task batchMovePenalty matches moveDelta":
        # Create an ExpressionBased cumulative with one task per position
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..20))

        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0])
        originExprs.add(x[1] + 2)
        originExprs.add(x[2])

        let durations = @[4, 3, 5]
        let heights = @[2, 3, 2]
        let limit = 5

        let cumul = newCumulativeConstraint[int](originExprs, durations, heights, limit, maxTime = 30)

        # Initialize with a known assignment
        var assignment = newSeq[int](3)
        assignment[0] = 5
        assignment[1] = 10
        assignment[2] = 0
        cumul.initialize(assignment)

        # For each position, verify batchMovePenalty matches individual moveDelta
        let domain = toSeq(0..20)
        for pos in 0..2:
            let currentVal = assignment[pos]
            let batchResult = cumul.batchMovePenalty(pos, currentVal, domain)

            for i, v in domain:
                let expected = cumul.moveDelta(pos, currentVal, v)
                check batchResult[i] == expected

    test "Multi-task batchMovePenalty matches moveDelta":
        # Create an ExpressionBased cumulative where one position affects multiple tasks
        # x[0] appears in origins of task 0 and task 1
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..15))

        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0])           # task 0: origin = x[0]
        originExprs.add(x[0] + x[1])    # task 1: origin = x[0] + x[1] (shares x[0])
        originExprs.add(x[2])           # task 2: origin = x[2]

        let durations = @[3, 2, 4]
        let heights = @[2, 3, 1]
        let limit = 5

        let cumul = newCumulativeConstraint[int](originExprs, durations, heights, limit, maxTime = 30)

        var assignment = newSeq[int](3)
        assignment[0] = 2
        assignment[1] = 5
        assignment[2] = 10
        cumul.initialize(assignment)

        # Position 0 affects both task 0 and task 1 — multi-task path
        let domain = toSeq(0..15)
        let currentVal = assignment[0]
        let batchResult = cumul.batchMovePenalty(0, currentVal, domain)

        for i, v in domain:
            let expected = cumul.moveDelta(0, currentVal, v)
            if batchResult[i] != expected:
                echo "  Mismatch at pos=0, value=", v, ": batch=", batchResult[i], " moveDelta=", expected
            check batchResult[i] == expected

    test "Multi-task shared position solving":
        # End-to-end test where x[0] is shared between two task origins
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..20))

        # Task origins: x[0], x[0]+x[1], x[2]
        # x[0] appears in two origins — tests multi-task handling
        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0])
        originExprs.add(x[0] + x[1])
        originExprs.add(x[2])

        let durations = @[3, 4, 5]
        let heights = @[3, 3, 3]
        let limit = 3  # Only one task at a time

        sys.addConstraint(cumulative[int](originExprs, durations, heights, limit))

        sys.resolve(parallel=true)

        let assignment = x.assignment
        let actualOrigins = @[
            assignment[0],
            assignment[0] + assignment[1],
            assignment[2]
        ]
        check validateCumulativeSolution(actualOrigins, durations, heights, limit)

    test "Expression-based moveDelta correctness":
        # Verify the optimized (hash-table-free) moveDelta produces correct results
        # by comparing against manually computed penalties
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(2)
        x.setDomain(toSeq(0..10))

        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0] + 1)  # task 0: origin = x[0] + 1
        originExprs.add(x[1])      # task 1: origin = x[1]

        let durations = @[3, 3]
        let heights = @[4, 4]
        let limit = 4  # Only one task at a time

        let cumul = newCumulativeConstraint[int](originExprs, durations, heights, limit, maxTime = 20)

        # Place tasks so they overlap: task0 at t=3..6, task1 at t=4..7
        var assignment = newSeq[int](2)
        assignment[0] = 2  # origin = 2+1 = 3
        assignment[1] = 4  # origin = 4
        cumul.initialize(assignment)

        # Overlap at t=4,5 => overuse = 4 at each => cost = 8
        check cumul.cost == 8

        # Move x[0] to 7 => origin = 8 => task0 at t=8..10, no overlap with task1 (t=4..6)
        let delta = cumul.moveDelta(0, 2, 7)
        check delta == -8  # removing all overlap

        # Move x[0] to 1 => origin = 2 => task0 at t=2..4, overlap at t=4 only
        let delta2 = cumul.moveDelta(0, 2, 1)
        check delta2 == -4  # overlap reduced from 2 points to 1 point

    test "batchMovePenalty with non-origin position returns zeros":
        # Position not in any origin expression should return all zeros
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        var originExprs: seq[AlgebraicExpression[int]] = @[]
        originExprs.add(x[0])
        originExprs.add(x[1])
        # x[2] is NOT used in any origin expression

        let durations = @[3, 3]
        let heights = @[2, 2]
        let limit = 3

        let cumul = newCumulativeConstraint[int](originExprs, durations, heights, limit, maxTime = 20)

        var assignment = newSeq[int](3)
        assignment[0] = 1
        assignment[1] = 5
        assignment[2] = 7
        cumul.initialize(assignment)

        # Position 2 is not in expressionsAtPosition, so batchMovePenalty should return zeros
        let domain = toSeq(0..10)
        let batchResult = cumul.batchMovePenalty(2, assignment[2], domain)
        for i in 0..<domain.len:
            check batchResult[i] == 0
