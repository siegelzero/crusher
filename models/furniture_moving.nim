## Furniture Moving Scheduling Problem
## ==================================
##
## This model implements the furniture moving scheduling problem from
## "Advanced Constraint Modeling" (Chapter 3, Section 3.6).
##
## Problem: Schedule moving furniture with 4 people. Each piece of furniture
## has a duration and requires a certain number of people to move.
##
## The cumulative constraint ensures that at any point in time, the total
## number of people working doesn't exceed 4.
##
## Precedence constraints:
##   - shelf1 must be moved before bed
##   - shelf2 must be moved before table
##   - bed must be moved before piano
##   - tv must be moved before table
##
## Objective: Minimize the total time (makespan)

import std/[sequtils, strformat, tables]
import ../src/crusher

# Task indices
const
    Piano = 0
    Chair1 = 1
    Chair2 = 2
    Chair3 = 3
    Chair4 = 4
    Bed = 5
    Table = 6
    Shelf1 = 7
    Shelf2 = 8
    Tv = 9

# Task data: (name, people needed, duration in minutes)
const TaskData = [
    ("piano", 3, 30),
    ("chair1", 1, 10),
    ("chair2", 1, 10),
    ("chair3", 1, 10),
    ("chair4", 1, 10),
    ("bed", 3, 20),
    ("table", 2, 15),
    ("shelf1", 2, 15),
    ("shelf2", 2, 15),
    ("tv", 2, 15)
]

const MaxPeople = 4

proc furnitureMoving() =
    echo "Furniture Moving Scheduling Problem"
    echo "===================================="
    echo ""

    let numTasks = TaskData.len

    # Extract durations and people needed (heights)
    let durations = TaskData.mapIt(it[2])
    let heights = TaskData.mapIt(it[1])

    # Calculate max possible time (if all tasks sequential)
    let maxTime = durations.foldl(a + b)

    echo "Tasks:"
    for i, task in TaskData:
        echo fmt"  {i}: {task[0]:8} - {task[1]} people, {task[2]} minutes"
    echo ""
    echo fmt"Max people available: {MaxPeople}"
    echo fmt"Max possible time: {maxTime} minutes"
    echo ""

    # Create constraint system
    var sys = initConstraintSystem[int]()

    # Decision variables: start times for each task
    var startTimes = sys.newConstrainedSequence(numTasks)
    startTimes.setDomain(toSeq(0..maxTime))

    # End times (computed as start + duration)
    # For constraints, we use expressions: endTime[i] = startTimes[i] + duration[i]
    var endExprs: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<numTasks:
        endExprs.add(startTimes[i] + durations[i])

    # Add cumulative constraint - use position-based version directly for efficiency
    var originPositions: seq[int] = @[]
    for i in 0..<numTasks:
        originPositions.add(i)
    sys.addConstraint(cumulative[int](originPositions, durations, heights, MaxPeople))

    # Precedence constraints (using STRICT inequality to match Picat model):
    # shelf1 must be moved before bed: end[shelf1] < start[bed]
    sys.addConstraint(endExprs[Shelf1] < startTimes[Bed])

    # shelf2 must be moved before table: end[shelf2] < start[table]
    sys.addConstraint(endExprs[Shelf2] < startTimes[Table])

    # bed must be moved before piano: end[bed] < start[piano]
    sys.addConstraint(endExprs[Bed] < startTimes[Piano])

    # tv must be moved before table: end[tv] < start[table]
    sys.addConstraint(endExprs[Tv] < startTimes[Table])

    # Create a max expression over all end times for optimization
    let makespanExpr = max(endExprs)

    echo "Solving with optimization (minimize makespan)..."
    echo ""

    # Minimize the max of all end times
    sys.minimize(makespanExpr, verbose=false)

    # Get results
    let solution = startTimes.assignment

    echo ""
    echo "Solution:"
    echo "---------"

    # Calculate and display end times
    var maxEndTime = 0
    for i in 0..<numTasks:
        let startTime = solution[i]
        let endTime = startTime + durations[i]
        maxEndTime = max(maxEndTime, endTime)
        echo fmt"  {TaskData[i][0]:8}: start={startTime:3}, end={endTime:3}, people={heights[i]}"

    echo ""
    echo fmt"Total time (makespan): {maxEndTime} minutes"
    echo ""

    # Verify cumulative constraint
    echo "Resource usage over time:"
    var resourceProfile = initTable[int, int]()
    for i in 0..<numTasks:
        let startTime = solution[i]
        let duration = durations[i]
        let height = heights[i]
        for t in startTime..<(startTime + duration):
            resourceProfile[t] = resourceProfile.getOrDefault(t, 0) + height

    # Find time range and show profile
    let times = toSeq(resourceProfile.keys)
    let minT = times.min
    let maxT = times.max

    echo fmt"  Time range: {minT} to {maxT}"

    # Check for violations
    var maxUsage = 0
    var violations = false
    for t in minT..maxT:
        let usage = resourceProfile.getOrDefault(t, 0)
        maxUsage = max(maxUsage, usage)
        if usage > MaxPeople:
            echo fmt"  VIOLATION at time {t}: {usage} > {MaxPeople}"
            violations = true

    if not violations:
        echo fmt"  All time points satisfy resource limit (max usage: {maxUsage}/{MaxPeople})"

    # Verify precedence constraints
    echo ""
    echo "Precedence constraint verification:"

    proc checkPrecedence(name: string, task1, task2: int) =
        let end1 = solution[task1] + durations[task1]
        let start2 = solution[task2]
        let satisfied = end1 <= start2
        let symbol = if satisfied: "✓" else: "✗"
        echo fmt"  {symbol} {TaskData[task1][0]} ends at {end1} <= {TaskData[task2][0]} starts at {start2}"

    checkPrecedence("shelf1 -> bed", Shelf1, Bed)
    checkPrecedence("shelf2 -> table", Shelf2, Table)
    checkPrecedence("bed -> piano", Bed, Piano)
    checkPrecedence("tv -> table", Tv, Table)

when isMainModule:
    furnitureMoving()
