## Newspaper Scheduling Test
##
## From B-Prolog / Picat: https://www.hakank.org/picat/newspaper.pi
##
## Four roommates subscribing to four newspapers. Each person reads
## each newspaper for a different amount of time. Nobody can read
## more than one newspaper at a time, and each newspaper can be read
## by only one person at a time.
##
## Wake-up times: Akiko 7:00, Bobby 7:15, Cho 7:15, Dola 8:00
## Optimal makespan: 650 minutes (10:50 AM)

import std/[sequtils, unittest]
import crusher

const
    AkikoWakes = 7 * 60        # 420
    BobbyWakes = 7 * 60 + 15   # 435
    ChoWakes = 7 * 60 + 15     # 435
    DolaWakes = 8 * 60         # 480
    MinTime = 7 * 60           # 420 (earliest wake-up)
    MaxTime = 11 * 60          # 660 (just above optimal 650)

    # Reading times [Asahi, Nishi, Orient, Sankei]
    AkikoTimes = [60, 30, 2, 5]
    BobbyTimes = [75, 3, 15, 10]
    ChoTimes = [5, 15, 10, 13]
    DolaTimes = [90, 1, 1, 1]

    OptimalMakespan = 650
    NumVars = 16

    WakeTimes = [AkikoWakes, BobbyWakes, ChoWakes, DolaWakes]
    ReadTimes = [AkikoTimes, BobbyTimes, ChoTimes, DolaTimes]

proc solveNewspaper(): tuple[solution: seq[int], makespan: int] =
    var sys = initConstraintSystem[int]()

    var startTimes = sys.newConstrainedSequence(NumVars)
    startTimes.setDomain(toSeq(MinTime..MaxTime))

    # Wake-up time constraints
    for p in 0..3:
        for n in 0..3:
            sys.addConstraint(startTimes[p * 4 + n] >= WakeTimes[p])

    # Each person can read only one newspaper at a time (cumulative capacity 1)
    for p in 0..3:
        var personStarts: seq[AlgebraicExpression[int]] = @[]
        for n in 0..3:
            personStarts.add(startTimes[p * 4 + n])
        sys.addConstraint(cumulative[int](personStarts, @(ReadTimes[p]), @[1, 1, 1, 1], 1))

    # Each newspaper can be read by only one person at a time (cumulative capacity 1)
    for n in 0..3:
        var paperStarts: seq[AlgebraicExpression[int]] = @[]
        var paperDurations: seq[int] = @[]
        for p in 0..3:
            paperStarts.add(startTimes[p * 4 + n])
            paperDurations.add(ReadTimes[p][n])
        sys.addConstraint(cumulative[int](paperStarts, paperDurations, @[1, 1, 1, 1], 1))

    # End time expressions for all activities
    var endExpressions: seq[AlgebraicExpression[int]] = @[]
    for p in 0..3:
        for n in 0..3:
            endExpressions.add(startTimes[p * 4 + n] + ReadTimes[p][n])

    let makespan = max(endExpressions)

    sys.minimize(makespan, parallel=true, verbose=true,
                 tabuThreshold=100)

    let solution = startTimes.assignment

    var actualMakespan = 0
    for p in 0..3:
        for n in 0..3:
            actualMakespan = max(actualMakespan, solution[p * 4 + n] + ReadTimes[p][n])

    return (solution, actualMakespan)

proc verifyNewspaper(solution: seq[int]): bool =
    # Verify wake-up constraints
    for p in 0..3:
        for n in 0..3:
            if solution[p * 4 + n] < WakeTimes[p]:
                return false

    # Verify no person reads two papers at once
    for p in 0..3:
        for n1 in 0..3:
            for n2 in (n1+1)..3:
                let s1 = solution[p * 4 + n1]
                let e1 = s1 + ReadTimes[p][n1]
                let s2 = solution[p * 4 + n2]
                let e2 = s2 + ReadTimes[p][n2]
                if not (e1 <= s2 or e2 <= s1):
                    return false

    # Verify no paper is read by two people at once
    for n in 0..3:
        for p1 in 0..3:
            for p2 in (p1+1)..3:
                let s1 = solution[p1 * 4 + n]
                let e1 = s1 + ReadTimes[p1][n]
                let s2 = solution[p2 * 4 + n]
                let e2 = s2 + ReadTimes[p2][n]
                if not (e1 <= s2 or e2 <= s1):
                    return false

    return true

suite "Newspaper Scheduling Tests":

    test "Find optimal newspaper schedule (makespan=650)":
        let (solution, makespan) = solveNewspaper()

        echo "Makespan: ", makespan, " minutes"

        check verifyNewspaper(solution)
        check makespan == OptimalMakespan

