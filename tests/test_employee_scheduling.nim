## Employee Scheduling Test
## =========================
##
## Tests the employee scheduling problem from hakank.org/picat.
## This provides coverage for:
## - AtLeast/AtMost constraints for value counting
## - Implication constraints (->)
## - Optimization with abs() in objective

import std/[unittest]
import crusher

const
    NumPeople = 5
    NumDays = 7
    # Off=0 so that sum(X[p]) = total shift points directly
    Off = 0
    Morning = 1
    Midday = 2
    Evening = 3

proc solveEmployeeScheduling(): int =
    ## Returns the Z value (sum of abs differences of points)
    var sys = initConstraintSystem[int]()

    # X[p][d] = shift for person p on day d
    var X: array[NumPeople, ConstrainedSequence[int]]
    for p in 0..<NumPeople:
        X[p] = sys.newConstrainedSequence(NumDays)
        X[p].setDomain(@[Off, Morning, Midday, Evening])

    # At least one manager per shift per day
    for d in 0..<NumDays:
        for s in [Morning, Midday, Evening]:
            var dayExprs: seq[AlgebraicExpression[int]] = @[]
            for p in 0..<NumPeople:
                dayExprs.add(X[p][d])
            sys.addConstraint(atLeast(dayExprs, s, 1))

    # Each manager gets exactly two days off
    for p in 0..<NumPeople:
        var personExprs: seq[AlgebraicExpression[int]] = @[]
        for d in 0..<NumDays:
            personExprs.add(X[p][d])
        sys.addConstraint(atLeast(personExprs, Off, 2))
        sys.addConstraint(atMost(personExprs, Off, 2))

    # Evening => not morning next day
    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            let nextDay = (d + 1) mod NumDays
            sys.addConstraint((X[p][d] == Evening) -> (X[p][nextDay] != Morning))

    # Objective: minimize Z = sum of |Points[p1] - Points[p2]|
    # Since Off=0, points[p] = X[p][0] + X[p][1] + ... + X[p][6]
    var personSums: array[NumPeople, AlgebraicExpression[int]]
    for p in 0..<NumPeople:
        var s = X[p][0]
        for d in 1..<NumDays:
            s = s + X[p][d]
        personSums[p] = s

    var absDiffTerms: seq[AlgebraicExpression[int]] = @[]
    for p1 in 0..<NumPeople:
        for p2 in (p1+1)..<NumPeople:
            absDiffTerms.add(abs(personSums[p1] - personSums[p2]))

    let zObjective = sum(absDiffTerms)

    sys.minimize(zObjective, verbose=false, parallel=true,
                 tabuThreshold=1000, scatterThreshold=3)

    # Calculate actual Z from solution
    var pointsVals: array[NumPeople, int]
    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            pointsVals[p] += X[p].assignment[d]

    var z = 0
    for p1 in 0..<NumPeople:
        for p2 in (p1+1)..<NumPeople:
            z += abs(pointsVals[p1] - pointsVals[p2])

    # Verify all constraints satisfied
    for d in 0..<NumDays:
        for s in [Morning, Midday, Evening]:
            var count = 0
            for p in 0..<NumPeople:
                if X[p].assignment[d] == s:
                    count += 1
            assert count >= 1, "Shift coverage violated"

    for p in 0..<NumPeople:
        var offCount = 0
        for d in 0..<NumDays:
            if X[p].assignment[d] == Off:
                offCount += 1
        assert offCount == 2, "Days off constraint violated"

    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            let nextDay = (d + 1) mod NumDays
            if X[p].assignment[d] == Evening:
                assert X[p].assignment[nextDay] != Morning, "Evening->morning violated"

    return z

suite "Employee Scheduling Tests":

    test "Find optimal fair schedule (Z=0)":
        # Run solver - optimal is Z=0 where all managers have 10 points
        let z = solveEmployeeScheduling()
        echo "Found Z = ", z
        check z == 0

    test "Reification with biconditional channeling":
        var sys = initConstraintSystem[int]()

        var x = sys.newConstrainedVariable()
        x.setDomain(@[1, 2, 3])

        var b1 = sys.newConstrainedVariable()
        var b2 = sys.newConstrainedVariable()
        var b3 = sys.newConstrainedVariable()
        b1.setDomain(@[0, 1])
        b2.setDomain(@[0, 1])
        b3.setDomain(@[0, 1])

        sys.addConstraint((b1 == 1) <-> (x == 1))
        sys.addConstraint((b2 == 1) <-> (x == 2))
        sys.addConstraint((b3 == 1) <-> (x == 3))

        sys.addConstraint(x == 2)
        sys.resolve()

        check x.assignment == 2
        check b1.assignment == 0
        check b2.assignment == 1
        check b3.assignment == 0

    test "Sum of indicator variables":
        var sys = initConstraintSystem[int]()

        var indicators = sys.newConstrainedSequence(5)
        indicators.setDomain(@[0, 1])

        sys.addConstraint(indicators.sum() == 2)
        sys.resolve()

        let assignment = indicators.assignment
        var count = 0
        for v in assignment:
            if v == 1:
                count += 1
        check count == 2

    test "Implication constraint (evening -> not morning)":
        var sys = initConstraintSystem[int]()

        var day1 = sys.newConstrainedVariable()
        var day2 = sys.newConstrainedVariable()
        day1.setDomain(@[Morning, Midday, Evening, Off])
        day2.setDomain(@[Morning, Midday, Evening, Off])

        sys.addConstraint((day1 == Evening) -> (day2 != Morning))
        sys.addConstraint(day1 == Evening)
        sys.resolve()

        check day1.assignment == Evening
        check day2.assignment != Morning
