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

import std/[sequtils, strformat, strutils]
import ../src/crusher

const
    NumPeople = 5
    NumDays = 7

    # Shift values (matching Picat: 1..4)
    Morning = 1
    Midday = 2
    Evening = 3
    Off = 4

    ShiftNames = ["", "morning", "midday", "evening", "off"]
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

    # X[p][d] = shift for person p on day d (domain 1..4)
    var X: array[NumPeople, ConstrainedSequence[int]]
    for p in 0..<NumPeople:
        X[p] = sys.newConstrainedSequence(NumDays)
        X[p].setDomain(@[Morning, Midday, Evening, Off])

    # Reified indicators: B[p][d][s] = 1 iff X[p][d] == (s+1)
    # Using 0..3 to index shifts 1..4
    var B: array[NumPeople, array[NumDays, array[4, ConstrainedVariable[int]]]]
    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            for s in 0..<4:
                B[p][d][s] = sys.newConstrainedVariable()
                B[p][d][s].setDomain(@[0, 1])

    # Channeling: B[p][d][s] = 1 <-> X[p][d] == (s+1)
    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            for s in 0..<4:
                let shiftVal = s + 1
                sys.addConstraint((B[p][d][s] == 1) <-> (X[p][d] == shiftVal))

    # Points[p] = sum over d,s of s * B[p][d][s-1]
    # where s in {Morning=1, Midday=2, Evening=3}
    var points = sys.newConstrainedSequence(NumPeople)
    points.setDomain(toSeq(0..21))

    for p in 0..<NumPeople:
        var pointTerms: seq[AlgebraicExpression[int]] = @[]
        for d in 0..<NumDays:
            # Morning=1 contributes 1 point
            pointTerms.add(1 * B[p][d][0])
            # Midday=2 contributes 2 points
            pointTerms.add(2 * B[p][d][1])
            # Evening=3 contributes 3 points
            pointTerms.add(3 * B[p][d][2])
            # Off contributes 0 points
        sys.addConstraint(sum(pointTerms) == points[p])

    # Constraint: At least one manager per shift per day
    # sum([B[p][d][s] : p in 0..<NumPeople]) >= 1 for each d, s in {0,1,2}
    for d in 0..<NumDays:
        for s in 0..<3:  # Morning, Midday, Evening
            var shiftCount: seq[AlgebraicExpression[int]] = @[]
            for p in 0..<NumPeople:
                shiftCount.add(B[p][d][s])
            sys.addConstraint(sum(shiftCount) >= 1)

    # Constraint: Each manager gets exactly two days off
    # sum([B[p][d][3] : d in 0..<NumDays]) == 2 for each p
    for p in 0..<NumPeople:
        var offCount: seq[AlgebraicExpression[int]] = @[]
        for d in 0..<NumDays:
            offCount.add(B[p][d][3])  # Off is index 3
        sys.addConstraint(sum(offCount) == 2)

    # Constraint: Evening => not morning next day
    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            let nextDay = (d + 1) mod NumDays
            sys.addConstraint((X[p][d] == Evening) -> (X[p][nextDay] != Morning))

    # Objective: minimize Z = sum of |Points[p1] - Points[p2]| for p1 < p2
    # Model using diff variables with diff >= |a - b|
    let numPairs = (NumPeople * (NumPeople - 1)) div 2
    var diffs = sys.newConstrainedSequence(numPairs)
    diffs.setDomain(toSeq(0..21))

    var pairIdx = 0
    for p1 in 0..<NumPeople:
        for p2 in (p1+1)..<NumPeople:
            sys.addConstraint(diffs[pairIdx] >= points[p1] - points[p2])
            sys.addConstraint(diffs[pairIdx] >= points[p2] - points[p1])
            pairIdx += 1

    let zObjective = diffs.sum()

    echo "Solving with optimization (minimize Z)..."
    echo ""

    sys.minimize(zObjective, verbose=false, tabuThreshold=100000, multiplier=10)

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
        let assignment = X[p].assignment
        pointsVals[p] = 0
        for d in 0..<NumDays:
            if assignment[d] != Off:
                pointsVals[p] += assignment[d]

    echo ""
    echo "Points (calculated): ", @pointsVals
    echo "Points (vars): ", points.assignment

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
                echo fmt"  ✗ No one assigned to {ShiftNames[s]} on {DayNames[d]}"
                allValid = false

    for p in 0..<NumPeople:
        var offCount = 0
        for d in 0..<NumDays:
            if X[p].assignment[d] == Off:
                offCount += 1
        if offCount != 2:
            echo fmt"  ✗ {PeopleNames[p]} has {offCount} days off (should be 2)"
            allValid = false

    for p in 0..<NumPeople:
        for d in 0..<NumDays:
            let nextDay = (d + 1) mod NumDays
            if X[p].assignment[d] == Evening and X[p].assignment[nextDay] == Morning:
                echo fmt"  ✗ {PeopleNames[p]} works evening {DayNames[d]} then morning {DayNames[nextDay]}"
                allValid = false

    if allValid:
        echo "  ✓ All constraints satisfied"

    return z

when isMainModule:
    let z = employeeScheduling()
    echo ""
    if z == 0:
        echo "OPTIMAL: Z=0 (perfectly fair distribution)"
    else:
        echo fmt"Solution found with Z={z} (optimal is 0)"
