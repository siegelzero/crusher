import std/[sequtils, unittest]
import crusher
import constraints/circuitTimeProp

## Small TSPTW instance: 5 locations, depot at 0 (0-based)
## Tour: 0 → 1 → 2 → 3 → 4 → 0
## Distance matrix [to][from]:
const N = 5
let dist = @[
    @[0, 10, 20, 30, 15],   # to 0 from [0,1,2,3,4]
    @[10, 0, 12, 25, 20],   # to 1
    @[20, 12, 0, 10, 18],   # to 2
    @[30, 25, 10, 0, 14],   # to 3
    @[15, 20, 18, 14, 0],   # to 4
]
let early = @[0, 5, 15, 25, 35]
let late  = @[100, 50, 60, 70, 80]

suite "CircuitTimeProp Constraint":
    test "Valid circuit has cost 0":
        # pred[l] = predecessor of l. Tour: 0→1→2→3→4→0
        # So pred = [4, 0, 1, 2, 3] (pred of 0 is 4, pred of 1 is 0, etc.)
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0  # 0-based
        )
        # Assignment: pred[0]=4, pred[1]=0, pred[2]=1, pred[3]=2, pred[4]=3
        let assignment = @[4, 0, 1, 2, 3]
        c.initialize(assignment)

        # Tour traversal: depot(0) → succ[0]=1 → succ[1]=2 → succ[2]=3 → succ[3]=4 → back to 0
        # arrival[1] = dep[0] + dist[1][0] = 0 + 10 = 10, dep[1] = max(10, 5) = 10
        # arrival[2] = dep[1] + dist[2][1] = 10 + 12 = 22, dep[2] = max(22, 15) = 22
        # arrival[3] = dep[2] + dist[3][2] = 22 + 10 = 32, dep[3] = max(32, 25) = 32
        # arrival[4] = dep[3] + dist[4][3] = 32 + 14 = 46, dep[4] = max(46, 35) = 46
        # arrival[0] = dep[4] + dist[0][4] = 46 + 15 = 61
        # All departures within late windows: 10≤50, 22≤60, 32≤70, 46≤80, 61≤100 ✓
        check c.cost == 0
        check c.arrivalTime[0] == 61  # arrival back at depot
        check c.arrivalTime[1] == 10
        check c.arrivalTime[2] == 22
        check c.arrivalTime[3] == 32
        check c.arrivalTime[4] == 46

    test "Two-cycle configuration has circuit penalty":
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        )
        # Two cycles: 0→1→0 and 2→3→4→2
        # pred = [1, 0, 4, 2, 3]
        let assignment = @[1, 0, 4, 2, 3]
        c.initialize(assignment)

        # Depot reachability: 0→succ[0]=1→succ[1]=0 (back to depot after 2 nodes)
        # Nodes 2,3,4 are unreachable. circuitPenalty = 3
        check c.circuitPenalty == 3
        check c.cost > 0

    test "moveDelta consistency":
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        )
        # Start with two cycles
        let assignment = @[1, 0, 4, 2, 3]
        c.initialize(assignment)
        let initialCost = c.cost

        # Try all single-variable moves and verify moveDelta matches actual cost change
        for pos in 0..<N:
            for newVal in 0..<N:
                let oldVal = assignment[pos]
                if newVal == oldVal: continue
                let delta = c.moveDelta(pos, oldVal, newVal)

                # Apply the move, check actual cost
                c.updatePosition(pos, newVal)
                let actualNewCost = c.cost
                check actualNewCost == initialCost + delta

                # Restore
                c.updatePosition(pos, oldVal)
                check c.cost == initialCost

    test "Time window violation penalty":
        # Use tight late times so the valid tour violates some
        let tightLate = @[100, 50, 60, 30, 80]  # late[3]=30, but arrival[3]=32
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = tightLate,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        )
        # Valid circuit: pred = [4, 0, 1, 2, 3]
        let assignment = @[4, 0, 1, 2, 3]
        c.initialize(assignment)

        # Circuit is valid → circuitPenalty = 0
        check c.circuitPenalty == 0
        # But departure[3] = 32 > late[3] = 30 → timeWindowPenalty = 2
        check c.timeWindowPenalty == 2
        check c.cost == 2  # circuitWeight * 0 + 2

    test "Objective bound penalty":
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        )
        let assignment = @[4, 0, 1, 2, 3]
        c.initialize(assignment)
        check c.cost == 0

        # Set objective bound: arrival at depot must be ≤ 50
        # Actual arrival = 61, so penalty = 61 - 50 = 11
        c.setObjectiveBound(50)
        check c.cost == 11

        # moveDelta should account for objective bound
        let delta = c.moveDelta(0, 4, 3)  # change pred[0] from 4 to 3
        c.updatePosition(0, 3)
        let newCost = c.cost
        # Restore to verify delta
        c.updatePosition(0, 4)
        check newCost == c.cost + delta

        # Clear bound
        c.clearObjectiveBound()
        check c.cost == 0

    test "deepCopy preserves objective bound":
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        )
        let assignment = @[4, 0, 1, 2, 3]
        c.initialize(assignment)
        c.setObjectiveBound(50)
        let origCost = c.cost

        let c2 = c.deepCopy()
        check c2.cost == origCost
        check c2.objectiveBoundActive == true
        check c2.objectiveUpperBound == 50

        # Modifying original shouldn't affect copy
        c.clearObjectiveBound()
        check c.cost == 0
        check c2.cost == origCost

    test "Solve small TSPTW":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(N)
        x.setDomain(toSeq(0..<N))  # 0-based

        let predPositions = toSeq(x.offset..<(x.offset + N))
        sys.addConstraint(circuitTimeProp[int](
            predPositions, dist, early, late,
            depotIndex = 0, depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        ))

        sys.resolve(parallel=false, tabuThreshold=50000, verbose=true)

        if not sys.hasFeasibleSolution:
            echo "Solver did not find feasible. Best assignment: ", x.assignment()
            # Re-initialize constraint with the solver's assignment and check
            let c2 = newCircuitTimePropConstraint[int](
                predPositions = @[0,1,2,3,4], distanceMatrix = dist,
                earlyTimes = early, lateTimes = late,
                depotIndex = 0, depotDeparture = 0,
                arrivalPositions = @[-1,-1,-1,-1,-1],
                departurePositions = @[-1,-1,-1,-1,-1], valueOffset = 0)
            c2.initialize(sys.assignment)
            echo "Re-initialized cost: ", c2.cost,
                 " circPen=", c2.circuitPenalty, " twPen=", c2.timeWindowPenalty
        check sys.hasFeasibleSolution

    test "1-based indexing":
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 1  # 1-based values
        )
        # Same tour as before but 1-based: pred = [5, 1, 2, 3, 4]
        let assignment = @[5, 1, 2, 3, 4]
        c.initialize(assignment)
        check c.cost == 0
        check c.arrivalTime[0] == 61

    test "Duplicate values create unreachable nodes":
        var c = newCircuitTimePropConstraint[int](
            predPositions = @[0,1,2,3,4],
            distanceMatrix = dist,
            earlyTimes = early,
            lateTimes = late,
            depotIndex = 0,
            depotDeparture = 0,
            arrivalPositions = @[-1,-1,-1,-1,-1],
            departurePositions = @[-1,-1,-1,-1,-1],
            valueOffset = 0
        )
        # pred = [1, 1, 1, 2, 3] — value 1 appears 3 times, values 0 and 4 missing
        # succ[1] = one of {0,1,2} (last wins), others become orphans
        let assignment = @[1, 1, 1, 2, 3]
        c.initialize(assignment)
        # Some nodes will be unreachable from depot
        check c.circuitPenalty > 0
