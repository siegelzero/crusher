## Test that verifies the Picat optimal solution has cost 0 in Crusher
## and tests if Crusher can recover from a perturbation

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

# Picat optimal solution: start = [52,30,40,50,60,31,16,15,0,0]
const OptimalStarts = [52, 30, 40, 50, 60, 31, 16, 15, 0, 0]

proc testOptimalSolution() =
    echo "Testing Picat optimal solution in Crusher"
    echo "=========================================="
    echo ""

    let numTasks = TaskData.len
    let durations = TaskData.mapIt(it[2])
    let heights = TaskData.mapIt(it[1])
    let maxTime = durations.foldl(a + b)

    # Create constraint system
    var sys = initConstraintSystem[int]()

    # Decision variables: start times for each task
    var startTimes = sys.newConstrainedSequence(numTasks)
    startTimes.setDomain(toSeq(0..maxTime))

    # End times
    var endExprs: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<numTasks:
        endExprs.add(startTimes[i] + durations[i])

    # Cumulative constraint
    var startExpressions: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<numTasks:
        startExpressions.add(startTimes[i])
    sys.addConstraint(cumulative[int](startExpressions, durations, heights, MaxPeople))

    # Precedence constraints (STRICT inequality to match Picat model)
    sys.addConstraint(endExprs[Shelf1] < startTimes[Bed])
    sys.addConstraint(endExprs[Shelf2] < startTimes[Table])
    sys.addConstraint(endExprs[Bed] < startTimes[Piano])
    sys.addConstraint(endExprs[Tv] < startTimes[Table])

    # Initialize with optimal solution
    var assignment = newSeq[int](numTasks)
    for i in 0..<numTasks:
        assignment[i] = OptimalStarts[i]

    sys.initialize(assignment)

    # Check total cost
    var totalCost = 0
    for constraint in sys.baseArray.constraints:
        let p = constraint.penalty()
        totalCost += p
        echo fmt"  Constraint penalty: {p}"

    echo ""
    echo fmt"Total cost with optimal solution: {totalCost}"

    # Verify resource profile
    echo ""
    echo "Resource profile verification:"
    var resourceProfile = initTable[int, int]()
    for i in 0..<numTasks:
        let startTime = OptimalStarts[i]
        let duration = durations[i]
        let height = heights[i]
        for t in startTime..<(startTime + duration):
            resourceProfile[t] = resourceProfile.getOrDefault(t, 0) + height

    var maxUsage = 0
    var violations = 0
    let times = toSeq(resourceProfile.keys)
    for t in times.min..times.max:
        let usage = resourceProfile.getOrDefault(t, 0)
        maxUsage = max(maxUsage, usage)
        if usage > MaxPeople:
            echo fmt"  VIOLATION at time {t}: {usage} > {MaxPeople}"
            violations += 1

    if violations == 0:
        echo fmt"  No violations (max usage: {maxUsage}/{MaxPeople})"
    else:
        echo fmt"  {violations} violation(s) found!"

    # Calculate makespan
    var maxEnd = 0
    for i in 0..<numTasks:
        maxEnd = max(maxEnd, OptimalStarts[i] + durations[i])
    echo fmt"  Makespan: {maxEnd}"

    echo ""
    if totalCost == 0:
        echo "SUCCESS: Optimal solution has cost 0"
    else:
        echo "FAILURE: Optimal solution has non-zero cost!"

    echo ""
    echo "Now testing perturbation recovery..."
    echo ""

    # Perturb the solution: move one task
    var perturbedAssignment = assignment
    perturbedAssignment[Chair1] = 0  # Move chair1 from 30 to 0

    sys.initialize(perturbedAssignment)

    totalCost = 0
    for constraint in sys.baseArray.constraints:
        totalCost += constraint.penalty()

    echo fmt"Perturbed solution cost: {totalCost}"

    # Try to resolve with tabu search
    echo "Running tabu search to recover..."
    try:
        sys.resolve(parallel=false, tabuThreshold=2000, verbose=true)

        # Check final solution
        let solution = startTimes.assignment
        var finalCost = 0
        for constraint in sys.baseArray.constraints:
            finalCost += constraint.penalty()

        maxEnd = 0
        for i in 0..<numTasks:
            maxEnd = max(maxEnd, solution[i] + durations[i])

        echo ""
        echo fmt"Recovered solution cost: {finalCost}"
        echo fmt"Recovered makespan: {maxEnd}"
        echo ""

        echo "Final schedule:"
        for i in 0..<numTasks:
            let startTime = solution[i]
            let endTime = startTime + durations[i]
            echo fmt"  {TaskData[i][0]:8}: start={startTime:3}, end={endTime:3}"

    except NoSolutionFoundError:
        echo "Failed to recover from perturbation"

when isMainModule:
    testOptimalSolution()
