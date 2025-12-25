import std/[unittest, sequtils, tables, sets]
import ../src/crusher

suite "RelationalConstraint Tests":

    test "Sum-to-Sum equality constraint":
        # Test: sum([x[0], x[1]]) == sum([x[2], x[3]])
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 4)

        # Set domains
        sequence.setDomain([1, 2, 3, 4, 5])

        # Create two sum expressions
        let leftSum = sum([sequence[0], sequence[1]])
        let rightSum = sum([sequence[2], sequence[3]])

        # Add the relational constraint: leftSum == rightSum
        system.addConstraint(leftSum == rightSum)

        # Solve
        system.resolve()
        let values = sequence.assignment
        let leftTotal = values[0] + values[1]
        let rightTotal = values[2] + values[3]
        check leftTotal == rightTotal

    test "Min-to-Max inequality constraint":
        # Test: min([x[0], x[1]]) <= max([x[2], x[3]])
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 4)

        # Set domains
        sequence.setDomain([1, 2, 3, 4, 5])

        # Create min and max expressions
        let minExpr = min([sequence[0], sequence[1]])
        let maxExpr = max([sequence[2], sequence[3]])

        # Add the relational constraint: minExpr <= maxExpr
        system.addConstraint(minExpr <= maxExpr)

        # Solve
        system.resolve()
        let values = sequence.assignment
        let minVal = min(values[0], values[1])
        let maxVal = max(values[2], values[3])
        check minVal <= maxVal

    test "Mixed Sum and Algebraic expression":
        # Test: sum([x[0], x[1]]) == (x[2] + 2*x[3])
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 4)

        # Set domains
        sequence.setDomain([1, 2, 3, 4, 5])

        # Create sum expression and algebraic expression
        let leftSum = sum([sequence[0], sequence[1]])
        let rightAlgebraic = sequence[2] + 2 * sequence[3]

        # Add the relational constraint
        system.addConstraint(leftSum == rightAlgebraic)

        # Solve
        system.resolve()
        let values = sequence.assignment
        let leftTotal = values[0] + values[1]
        let rightTotal = values[2] + 2 * values[3]
        check leftTotal == rightTotal

    test "Complex multi-expression constraint":
        # Test: sum([x[0], x[1], x[2]]) > min([x[3], x[4]])
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 5)

        # Set domains
        sequence.setDomain([1, 2, 3, 4, 5])

        # Create expressions
        let sumExpr = sum([sequence[0], sequence[1], sequence[2]])
        let minExpr = min([sequence[3], sequence[4]])

        # Add the relational constraint
        system.addConstraint(sumExpr > minExpr)

        # Solve
        system.resolve()
        let values = sequence.assignment
        let sumVal = values[0] + values[1] + values[2]
        let minVal = min(values[3], values[4])
        check sumVal > minVal

    test "Chained constraints with multiple expressions":
        # Test multiple relational constraints working together
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 6)

        # Set domains
        sequence.setDomain([1, 2, 3, 4, 5, 6])

        # Create expressions
        let sum1 = sum([sequence[0], sequence[1]])
        let sum2 = sum([sequence[2], sequence[3]])
        let maxExpr = max([sequence[4], sequence[5]])

        # Add multiple relational constraints that are satisfiable
        system.addConstraint(sum1 == sum2)        # sum1 must equal sum2
        system.addConstraint(sum1 <= maxExpr)     # sum1 must be less than or equal to max

        # Solve
        system.resolve()
        let values = sequence.assignment
        let s1 = values[0] + values[1]
        let s2 = values[2] + values[3]
        let maxVal = max(values[4], values[5])
        check s1 == s2
        check s1 <= maxVal

    test "Single element min/max expressions":
        # Test edge case: min/max with only one element
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 3)

        # Set domains
        sequence.setDomain([1, 2, 3, 4, 5])

        # Create single-element expressions
        let singleMin = min([sequence[0]])
        let singleMax = max([sequence[1]])

        # Add constraints
        system.addConstraint(singleMin == sequence[2])
        system.addConstraint(singleMax >= 3)

        # Solve
        system.resolve()
        let values = sequence.assignment
        check values[0] == values[2]  # singleMin == sequence[2]
        check values[1] >= 3          # singleMax >= 3

    test "Negative domain relational constraints":
        # Test relational constraints with negative values
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 4)

        # Set negative domain
        sequence.setDomain([-5, -3, -1, 0, 1, 3, 5])

        # Create expressions
        let sumExpr = sum([sequence[0], sequence[1]])
        let minExpr = min([sequence[2], sequence[3]])

        # Add constraint: sum must be greater than min
        system.addConstraint(sumExpr > minExpr)

        # Solve
        system.resolve()
        let values = sequence.assignment
        let sumVal = values[0] + values[1]
        let minVal = min(values[2], values[3])
        check sumVal > minVal

    test "Zero-valued expressions with allDifferent":
        # Test constraint with zero sum and allDifferent - should use each domain value exactly once
        let system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 5)

        # Set symmetric domain around zero
        sequence.setDomain([-2, -1, 0, 1, 2])

        # Create sum that should equal zero
        let sumExpr = sum([sequence[0], sequence[1], sequence[2], sequence[3], sequence[4]])

        # Add constraints: sum equals zero AND all values different
        system.addConstraint(sumExpr == 0)
        system.addConstraint(allDifferent[int]([0, 1, 2, 3, 4]))

        # Solve
        system.resolve()
        let values = sequence.assignment
        let totalSum = values[0] + values[1] + values[2] + values[3] + values[4]
        check totalSum == 0

        # Verify all values are different (should use each domain value exactly once)
        let usedValues = values.toHashSet()
        check usedValues.len == 5  # All values should be unique
        check usedValues == [-2, -1, 0, 1, 2].toHashSet()  # Should be exactly the domain

    test "Bus scheduling optimization (Taha, Introduction to Operations Research)":
        ## Bus scheduling problem from Taha, page 58
        ## Source: https://www.hakank.org/picat/bus_schedule.pi
        ##
        ## Schedule buses across 6 time slots, each bus works 2 consecutive slots.
        ## Minimize total buses while meeting demand at each slot.
        ## Optimal solution: 26 buses

        const
            TimeSlots = 6
            Demands = [8, 10, 7, 12, 4, 4]
            OptimalBuses = 26
            MaxBusesPerSlot = 45

        var sys = initConstraintSystem[int]()

        # X[i] = number of buses starting at time slot i
        var X = sys.newConstrainedSequence(TimeSlots)
        X.setDomain(toSeq(0..MaxBusesPerSlot))

        # Coverage constraints: X[i] + X[i+1] >= Demands[i]
        for i in 0..<(TimeSlots - 1):
            sys.addConstraint(X[i] + X[i + 1] >= Demands[i])

        # Cyclic constraint: X[5] + X[0] == Demands[5]
        sys.addConstraint(X[TimeSlots - 1] + X[0] == Demands[TimeSlots - 1])

        # Minimize total buses
        var busExprs: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<TimeSlots:
            busExprs.add(X[i])
        let totalBuses = sum(busExprs)

        sys.minimize(totalBuses, parallel=true, verbose=false)

        let solution = X.assignment
        var total = 0
        for i in 0..<TimeSlots:
            total += solution[i]

        # Verify coverage constraints
        for i in 0..<(TimeSlots - 1):
            check solution[i] + solution[i + 1] >= Demands[i]
        check solution[TimeSlots - 1] + solution[0] == Demands[TimeSlots - 1]

        echo "  Bus schedule: ", solution, " (total: ", total, ")"
        check total == OptimalBuses