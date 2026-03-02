## Employee Scheduling Problem
## ===========================
##
## From Siddharth Chitnis, Madhu Yennamani, Gopal Gupta:
## "ExSched: Solving Constraint Satisfaction Problems with the Spreadsheet Paradigm"
##
## Problem: Schedule five managers (Bill, Mary, John, Gary, Linda) for a week.
##
## Constraints:
## 1. Three shifts: morning, midday, evening, plus days off
## 2. At least one manager must be present at any shift each day
## 3. Each manager should get two days off
## 4. Evening shift worker cannot work morning next day
## 5. Schedule should be fair (minimize sum of abs point differences)
##
## Points: Morning=1, Midday=2, Evening=3, Off=0
## Optimal solution: all managers have 10 points, Z=0

import std/[strformat, strutils]
import ../src/crusher

const
    NumPeople = 5
    NumDays = 7

    # Off=0 so that sum(X[p]) = total shift points directly
    Off = 0
    Morning = 1
    Midday = 2
    Evening = 3

    ShiftNames = ["off", "morning", "midday", "evening"]
    PeopleNames = ["bill", "mary", "john", "gary", "linda"]
    DayNames = ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]

proc employeeScheduling*(): int =
    echo "Employee Scheduling Problem"
    echo "==========================="
    echo ""
    echo fmt"Scheduling {NumPeople} managers for {NumDays} days"
    echo "Shifts: Morning (1pt), Midday (2pt), Evening (3pt), Off (0pt)"
    echo ""

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

    echo "Solving with optimization (minimize Z)..."
    echo ""

    sys.minimize(zObjective, verbose=false, tabuThreshold=10000)

    # Display solution
    echo "Schedule:"
    echo "            " & DayNames.mapIt(it.alignLeft(10)).join(" ")

    for p in 0..<NumPeople:
        let assignment = X[p].assignment
        var row = PeopleNames[p].alignLeft(10) & ": "
        for d in 0..<NumDays:
            row &= ShiftNames[assignment[d]].alignLeft(10) & " "
        echo row

    # Calculate points
    var pointsVals: array[NumPeople, int]
    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            pointsVals[p] += X[p].assignment[d]

    echo ""
    echo "Points: ", @pointsVals

    # Calculate actual Z
    var z = 0
    for p1 in 0..<NumPeople:
        for p2 in (p1+1)..<NumPeople:
            z += abs(pointsVals[p1] - pointsVals[p2])

    echo fmt"Z (sum of abs differences): {z}"
    echo ""

    # Verification
    echo "Constraint verification:"
    var allValid = true

    for d in 0..<NumDays:
        for s in [Morning, Midday, Evening]:
            var count = 0
            for p in 0..<NumPeople:
                if X[p].assignment[d] == s:
                    count += 1
            if count < 1:
                echo fmt"  x No one assigned to {ShiftNames[s]} on {DayNames[d]}"
                allValid = false

    for p in 0..<NumPeople:
        var offCount = 0
        for d in 0..<NumDays:
            if X[p].assignment[d] == Off:
                offCount += 1
        if offCount != 2:
            echo fmt"  x {PeopleNames[p]} has {offCount} days off (should be 2)"
            allValid = false

    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            let nextDay = (d + 1) mod NumDays
            if X[p].assignment[d] == Evening and X[p].assignment[nextDay] == Morning:
                echo fmt"  x {PeopleNames[p]} works evening {DayNames[d]} then morning {DayNames[nextDay]}"
                allValid = false

    if allValid:
        echo "  All constraints satisfied"

    return z

when isMainModule:
    let z = employeeScheduling()
    echo ""
    if z == 0:
        echo "OPTIMAL: Z=0 (perfectly fair distribution)"
    else:
        echo fmt"Solution found with Z={z} (optimal is 0)"
