## Newspaper Scheduling Problem
##
## From B-Prolog / Picat: https://www.hakank.org/picat/newspaper.pi
##
## Four roommates subscribing to four newspapers:
##
##   Person/Newspaper/Minutes
##   =============================================
##   Person || Asahi  | Nishi | Orient | Sankei
##   Akiko  ||    60  |   30  |      2 |  5
##   Bobby  ||    75  |    3  |     15 | 10
##   Cho    ||     5  |   15  |     10 | 13
##   Dola   ||    90  |    1  |      1 |  1
##
## Wake-up times: Akiko 7:00, Bobby 7:15, Cho 7:15, Dola 8:00
##
## Constraints:
##   - Nobody can read more than one newspaper at a time
##   - Each newspaper can be read by only one person at a time
##
## Objective: Minimize the time when everyone finishes
## Optimal: 650 minutes (10:50 AM)

import std/[sequtils, strformat]
import ../src/crusher

const
    # Time in minutes from midnight
    AkikoWakes = 7 * 60        # 420
    BobbyWakes = 7 * 60 + 15   # 435
    ChoWakes = 7 * 60 + 15     # 435
    DolaWakes = 8 * 60         # 480
    MaxTime = 12 * 60          # 720

    # Reading times [Asahi, Nishi, Orient, Sankei]
    AkikoTimes = [60, 30, 2, 5]
    BobbyTimes = [75, 3, 15, 10]
    ChoTimes = [5, 15, 10, 13]
    DolaTimes = [90, 1, 1, 1]

    OptimalMakespan = 650  # 10:50 AM

    # Variable indices
    NumVars = 16
    # Akiko: 0-3, Bobby: 4-7, Cho: 8-11, Dola: 12-15
    # Each group: [Asahi, Nishi, Orient, Sankei]

proc solveNewspaper() =
    echo "Newspaper Scheduling Problem"
    echo "============================"
    echo ""
    echo "Reading times (minutes):"
    echo "  Akiko: Asahi=60, Nishi=30, Orient=2, Sankei=5"
    echo "  Bobby: Asahi=75, Nishi=3, Orient=15, Sankei=10"
    echo "  Cho:   Asahi=5, Nishi=15, Orient=10, Sankei=13"
    echo "  Dola:  Asahi=90, Nishi=1, Orient=1, Sankei=1"
    echo ""
    echo "Wake-up times: Akiko 7:00, Bobby 7:15, Cho 7:15, Dola 8:00"
    echo ""

    var sys = initConstraintSystem[int]()

    # Start times for each person-newspaper combination
    var startTimes = sys.newConstrainedSequence(NumVars)
    startTimes.setDomain(toSeq(0..MaxTime))

    # Wake-up time constraints
    # Akiko (indices 0-3) >= 420
    for i in 0..3:
        sys.addConstraint(startTimes[i] >= AkikoWakes)
    # Bobby (indices 4-7) >= 435
    for i in 4..7:
        sys.addConstraint(startTimes[i] >= BobbyWakes)
    # Cho (indices 8-11) >= 435
    for i in 8..11:
        sys.addConstraint(startTimes[i] >= ChoWakes)
    # Dola (indices 12-15) >= 480
    for i in 12..15:
        sys.addConstraint(startTimes[i] >= DolaWakes)

    # Each person can read only one newspaper at a time (cumulative with capacity 1)
    # Akiko
    var akikoStarts: seq[AlgebraicExpression[int]] = @[]
    for i in 0..3: akikoStarts.add(startTimes[i])
    sys.addConstraint(cumulative[int](akikoStarts, @AkikoTimes, @[1, 1, 1, 1], 1))

    # Bobby
    var bobbyStarts: seq[AlgebraicExpression[int]] = @[]
    for i in 4..7: bobbyStarts.add(startTimes[i])
    sys.addConstraint(cumulative[int](bobbyStarts, @BobbyTimes, @[1, 1, 1, 1], 1))

    # Cho
    var choStarts: seq[AlgebraicExpression[int]] = @[]
    for i in 8..11: choStarts.add(startTimes[i])
    sys.addConstraint(cumulative[int](choStarts, @ChoTimes, @[1, 1, 1, 1], 1))

    # Dola
    var dolaStarts: seq[AlgebraicExpression[int]] = @[]
    for i in 12..15: dolaStarts.add(startTimes[i])
    sys.addConstraint(cumulative[int](dolaStarts, @DolaTimes, @[1, 1, 1, 1], 1))

    # Each newspaper can be read by only one person at a time (cumulative with capacity 1)
    # Asahi (indices 0, 4, 8, 12)
    var asahiStarts: seq[AlgebraicExpression[int]] = @[]
    asahiStarts.add(startTimes[0])
    asahiStarts.add(startTimes[4])
    asahiStarts.add(startTimes[8])
    asahiStarts.add(startTimes[12])
    sys.addConstraint(cumulative[int](asahiStarts, @[AkikoTimes[0], BobbyTimes[0], ChoTimes[0], DolaTimes[0]], @[1, 1, 1, 1], 1))

    # Nishi (indices 1, 5, 9, 13)
    var nishiStarts: seq[AlgebraicExpression[int]] = @[]
    nishiStarts.add(startTimes[1])
    nishiStarts.add(startTimes[5])
    nishiStarts.add(startTimes[9])
    nishiStarts.add(startTimes[13])
    sys.addConstraint(cumulative[int](nishiStarts, @[AkikoTimes[1], BobbyTimes[1], ChoTimes[1], DolaTimes[1]], @[1, 1, 1, 1], 1))

    # Orient (indices 2, 6, 10, 14)
    var orientStarts: seq[AlgebraicExpression[int]] = @[]
    orientStarts.add(startTimes[2])
    orientStarts.add(startTimes[6])
    orientStarts.add(startTimes[10])
    orientStarts.add(startTimes[14])
    sys.addConstraint(cumulative[int](orientStarts, @[AkikoTimes[2], BobbyTimes[2], ChoTimes[2], DolaTimes[2]], @[1, 1, 1, 1], 1))

    # Sankei (indices 3, 7, 11, 15)
    var sankeiStarts: seq[AlgebraicExpression[int]] = @[]
    sankeiStarts.add(startTimes[3])
    sankeiStarts.add(startTimes[7])
    sankeiStarts.add(startTimes[11])
    sankeiStarts.add(startTimes[15])
    sys.addConstraint(cumulative[int](sankeiStarts, @[AkikoTimes[3], BobbyTimes[3], ChoTimes[3], DolaTimes[3]], @[1, 1, 1, 1], 1))

    # End time expressions for each activity
    var endExpressions: seq[AlgebraicExpression[int]] = @[]
    # Akiko
    for i in 0..3:
        endExpressions.add(startTimes[i] + AkikoTimes[i])
    # Bobby
    for i in 0..3:
        endExpressions.add(startTimes[4 + i] + BobbyTimes[i])
    # Cho
    for i in 0..3:
        endExpressions.add(startTimes[8 + i] + ChoTimes[i])
    # Dola
    for i in 0..3:
        endExpressions.add(startTimes[12 + i] + DolaTimes[i])

    # Objective: minimize makespan
    let makespan = max(endExpressions)

    echo "Starting optimization..."
    echo ""

    sys.minimize(makespan, parallel=true, verbose=false)

    let solution = startTimes.assignment

    # Calculate actual makespan
    var actualMakespan = 0
    for i in 0..3:
        actualMakespan = max(actualMakespan, solution[i] + AkikoTimes[i])
        actualMakespan = max(actualMakespan, solution[4 + i] + BobbyTimes[i])
        actualMakespan = max(actualMakespan, solution[8 + i] + ChoTimes[i])
        actualMakespan = max(actualMakespan, solution[12 + i] + DolaTimes[i])

    let hours = actualMakespan div 60
    let mins = actualMakespan mod 60

    echo "Solution"
    echo "========"
    echo ""
    echo "Schedule (start times in minutes from midnight):"
    echo fmt"  Akiko: Asahi={solution[0]}, Nishi={solution[1]}, Orient={solution[2]}, Sankei={solution[3]}"
    echo fmt"  Bobby: Asahi={solution[4]}, Nishi={solution[5]}, Orient={solution[6]}, Sankei={solution[7]}"
    echo fmt"  Cho:   Asahi={solution[8]}, Nishi={solution[9]}, Orient={solution[10]}, Sankei={solution[11]}"
    echo fmt"  Dola:  Asahi={solution[12]}, Nishi={solution[13]}, Orient={solution[14]}, Sankei={solution[15]}"
    echo ""
    echo fmt"Makespan: {actualMakespan} minutes ({hours}:{mins:02})"
    echo ""

    if actualMakespan == OptimalMakespan:
        echo "SUCCESS: Found optimal solution!"
    elif actualMakespan < OptimalMakespan:
        echo "UNEXPECTED: Found better than known optimal?!"
    else:
        echo fmt"Found solution with makespan {actualMakespan} (optimal: {OptimalMakespan})"

when isMainModule:
    solveNewspaper()
