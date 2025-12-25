## Schedule1 - Cumulative Scheduling Example
##
## Ported from Picat model by Hakan Kjellerstrand
## Original source: https://www.hakank.org/picat/schedule1.pi
##
## Example from SICStus Prolog:
## http://www.sics.se/sicstus/docs/latest/html/sicstus/Cumulative-Scheduling.html
##
## """
## Cumulative Scheduling
##
## This example is a very small scheduling problem. We consider seven
## tasks where each task has a fixed duration and a fixed amount of used
## resource:
##
## Task Duration Resource
##  t1    16       2
##  t2     6       9
##  t3    13       3
##  t4     7       7
##  t5     5      10
##  t6    18       1
##  t7     4      11
##
## The goal is to find a schedule that minimizes the completion time for
## the schedule while not exceeding the capacity 13 of the resource. The
## resource constraint is succinctly captured by a cumulative/4
## constraint. Branch-and-bound search is used to find the minimal
## completion time.
##
## This example was adapted from [Beldiceanu & Contejean 94].
## """
##
## Optimal solution (from Picat):
##   Start times: [1, 17, 10, 10, 5, 5, 1]
##   End time: 23

import std/[sequtils, strformat, tables]
import ../src/crusher

const
    NumTasks = 7
    Capacity = 13

    # Task data
    Durations = [16, 6, 13, 7, 5, 18, 4]
    Resources = [2, 9, 3, 7, 10, 1, 11]

    # Known optimal from Picat
    OptimalMakespan = 23

proc verifyResourceProfile(starts: openArray[int]): tuple[valid: bool, maxUsage: int, makespan: int] =
    ## Verifies that the resource profile never exceeds capacity
    var resourceProfile = initTable[int, int]()
    var makespan = 0

    for i in 0..<NumTasks:
        let startTime = starts[i]
        let endTime = startTime + Durations[i]
        makespan = max(makespan, endTime)

        for t in startTime..<endTime:
            resourceProfile[t] = resourceProfile.getOrDefault(t, 0) + Resources[i]

    var maxUsage = 0
    var valid = true

    if resourceProfile.len > 0:
        let times = toSeq(resourceProfile.keys)
        for t in times.min..times.max:
            let usage = resourceProfile.getOrDefault(t, 0)
            maxUsage = max(maxUsage, usage)
            if usage > Capacity:
                valid = false

    return (valid, maxUsage, makespan)

proc solveSchedule1() =
    echo "Schedule1 - Cumulative Scheduling Optimization"
    echo "==============================================="
    echo ""
    echo "Problem: 7 tasks with resource capacity 13"
    echo "Known optimal makespan: ", OptimalMakespan
    echo ""
    echo "Task data:"
    for i in 0..<NumTasks:
        echo fmt"  t{i+1}: duration={Durations[i]:2}, resource={Resources[i]:2}"
    echo ""

    # Create constraint system
    var sys = initConstraintSystem[int]()

    # Decision variables: start times for each task (domain 1..30 as in Picat)
    var startTimes = sys.newConstrainedSequence(NumTasks)
    startTimes.setDomain(toSeq(1..30))

    # Create algebraic expressions for start times (for cumulative)
    var startExpressions: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<NumTasks:
        startExpressions.add(startTimes[i])

    # Cumulative constraint: resource usage at each time <= Capacity
    sys.addConstraint(cumulative[int](startExpressions, @Durations, @Resources, Capacity))

    # Create end time expressions for each task: start[i] + duration[i]
    var endExpressions: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<NumTasks:
        endExpressions.add(startTimes[i] + Durations[i])

    # Objective: minimize makespan (max of all end times)
    let makespan = max(endExpressions)

    echo "Starting optimization from scratch..."
    echo ""

    # Minimize the makespan
    sys.minimize(makespan, parallel=true, verbose=true)

    # Get the solution
    let solution = startTimes.assignment
    let (valid, maxUsage, finalMakespan) = verifyResourceProfile(solution)

    echo ""
    echo "Final Solution"
    echo "=============="
    echo ""
    echo "Schedule:"
    for i in 0..<NumTasks:
        let startTime = solution[i]
        let endTime = startTime + Durations[i]
        echo fmt"  t{i+1}: start={startTime:2}, end={endTime:2}"

    echo ""
    echo fmt"Makespan: {finalMakespan}"
    echo fmt"Max resource usage: {maxUsage}/{Capacity}"
    echo fmt"Resource constraint satisfied: {valid}"
    echo ""

    if finalMakespan == OptimalMakespan:
        echo "SUCCESS: Found optimal solution!"
    elif finalMakespan < OptimalMakespan:
        echo "UNEXPECTED: Found better than known optimal?!"
    else:
        echo fmt"Found solution with makespan {finalMakespan} (optimal is {OptimalMakespan})"

when isMainModule:
    solveSchedule1()
