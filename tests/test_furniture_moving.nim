## Furniture Moving Scheduling Test
## =================================
##
## Port of hakank's furniture moving scheduling problem from Picat.
## From "Advanced Constraint Modeling" (Chapter 3, Section 3.6).
##
## Schedule moving furniture with 4 people. Each piece of furniture
## has a duration and requires a certain number of people to move.
## The cumulative constraint limits total workers to 4 at any time.
##
## Precedence constraints:
##   shelf1 -> bed -> piano
##   shelf2 -> table
##   tv -> table
##
## Objective: Minimize makespan

import std/[sequtils, tables, unittest]
import crusher

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

    TaskData = [
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

    MaxPeople = 4

proc solveFurnitureMoving(): tuple[solution: seq[int], makespan: int] =
    let numTasks = TaskData.len
    let durations = TaskData.mapIt(it[2])
    let heights = TaskData.mapIt(it[1])
    let maxTime = durations.foldl(a + b)

    var sys = initConstraintSystem[int]()

    var startTimes = sys.newConstrainedSequence(numTasks)
    startTimes.setDomain(toSeq(0..maxTime))

    var endExprs: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<numTasks:
        endExprs.add(startTimes[i] + durations[i])

    # Cumulative: total workers <= 4 at any time
    var originPositions: seq[int] = @[]
    for i in 0..<numTasks:
        originPositions.add(i)
    sys.addConstraint(cumulative[int](originPositions, durations, heights, MaxPeople))

    # Precedence constraints (strict)
    sys.addConstraint(endExprs[Shelf1] < startTimes[Bed])
    sys.addConstraint(endExprs[Shelf2] < startTimes[Table])
    sys.addConstraint(endExprs[Bed] < startTimes[Piano])
    sys.addConstraint(endExprs[Tv] < startTimes[Table])

    let makespanExpr = max(endExprs)

    sys.minimize(makespanExpr, verbose=true, parallel=true,
                 tabuThreshold=100)

    let solution = startTimes.assignment
    var makespan = 0
    for i in 0..<numTasks:
        makespan = max(makespan, solution[i] + durations[i])

    return (solution, makespan)

proc verifyFurniture(solution: seq[int]): tuple[resourceOk: bool, precedenceOk: bool, maxUsage: int] =
    let durations = TaskData.mapIt(it[2])
    let heights = TaskData.mapIt(it[1])

    # Verify cumulative constraint
    var resourceProfile = initTable[int, int]()
    for i in 0..<TaskData.len:
        for t in solution[i]..<(solution[i] + durations[i]):
            resourceProfile[t] = resourceProfile.getOrDefault(t, 0) + heights[i]

    var maxUsage = 0
    var resourceOk = true
    if resourceProfile.len > 0:
        let times = toSeq(resourceProfile.keys)
        for t in times.min..times.max:
            let usage = resourceProfile.getOrDefault(t, 0)
            maxUsage = max(maxUsage, usage)
            if usage > MaxPeople:
                resourceOk = false

    # Verify precedence constraints (strict: end < start)
    var precedenceOk = true
    let endTime = proc(i: int): int = solution[i] + durations[i]

    if endTime(Shelf1) >= solution[Bed]: precedenceOk = false
    if endTime(Shelf2) >= solution[Table]: precedenceOk = false
    if endTime(Bed) >= solution[Piano]: precedenceOk = false
    if endTime(Tv) >= solution[Table]: precedenceOk = false

    return (resourceOk, precedenceOk, maxUsage)

suite "Furniture Moving Scheduling Tests":

    test "Optimize furniture moving schedule":
        let (solution, makespan) = solveFurnitureMoving()
        let (resourceOk, precedenceOk, maxUsage) = verifyFurniture(solution)

        echo "Makespan: ", makespan
        echo "Max resource usage: ", maxUsage, "/", MaxPeople

        check resourceOk
        check precedenceOk
        # Critical path shelf1(15)->gap->bed(20)->gap->piano(30) = at least 67
        check makespan >= 67
        check makespan <= 100

