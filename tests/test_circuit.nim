import std/[sequtils, tables, unittest]
import crusher
import constraints/circuit

proc validateCircuit(assignment: seq[int], n: int): bool =
    ## Validate that an assignment forms a single Hamiltonian circuit.
    ## Assignment uses 1-based values: value j at position i means node i -> node j.
    var visited = newSeq[bool](n)
    var current = 0  # start at node 0 (1-based node 1)
    for step in 0..<n:
        if visited[current]:
            return false  # visited a node twice before completing
        visited[current] = true
        let next = assignment[current] - 1  # convert 1-based to 0-based
        if next < 0 or next >= n:
            return false
        current = next
    # After n steps, should be back at start
    return current == 0 and visited.allIt(it)

suite "Circuit Constraint":
    test "Penalty: valid single circuit [2,3,4,5,6,1]":
        # Single cycle: 1->2->3->4->5->6->1, penalty = 0
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(circuit(x))

        let assignment = @[2, 3, 4, 5, 6, 1]
        sys.initialize(assignment)

        let cost = sys.baseArray.constraints[0].penalty()
        check cost == 0

    test "Penalty: three 2-cycles [2,1,4,3,6,5]":
        # Three cycles: (1,2)(3,4)(5,6), penalty = 2
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(circuit(x))

        let assignment = @[2, 1, 4, 3, 6, 5]
        sys.initialize(assignment)

        let cost = sys.baseArray.constraints[0].penalty()
        check cost == 2

    test "Penalty: all self-loops [1,2,3,4,5,6]":
        # Six self-loops, penalty = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(circuit(x))

        let assignment = @[1, 2, 3, 4, 5, 6]
        sys.initialize(assignment)

        let cost = sys.baseArray.constraints[0].penalty()
        check cost == 5

    test "moveDelta consistency":
        # Start from a known state, compute moveDelta, apply move, verify cost matches
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(circuit(x))

        # Start with three 2-cycles: [2,1,4,3,6,5]
        let assignment = @[2, 1, 4, 3, 6, 5]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]
        let initialCost = constraint.penalty()
        check initialCost == 2

        # Try changing position 1 (node 2) from value 1 to value 3
        # This would make: [2,3,4,3,6,5] -- node 2 now goes to 3 instead of 1
        let delta = constraint.moveDelta(1, 1, 3)
        constraint.updatePosition(1, 3)
        let newCost = constraint.penalty()
        check newCost == initialCost + delta

    test "Simple 6-node circuit (solver)":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(allDifferent(x))
        sys.addConstraint(circuit(x))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let sol = x.assignment()
        check validateCircuit(sol, 6)

    test "Knight's tour 6x6":
        const N = 6
        const numCells = N * N

        # Knight move offsets
        const knightDx = @[-2, -2, -1, -1, 1, 1, 2, 2]
        const knightDy = @[-1, 1, -2, 2, -2, 2, -1, 1]

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(numCells)

        # Set per-cell domains: each cell can only go to cells reachable by a knight move
        for row in 0..<N:
            for col in 0..<N:
                let cell = row * N + col
                var moves: seq[int] = @[]
                for k in 0..<8:
                    let nr = row + knightDx[k]
                    let nc = col + knightDy[k]
                    if nr >= 0 and nr < N and nc >= 0 and nc < N:
                        moves.add(nr * N + nc + 1)  # 1-based
                x.setDomain(cell, moves)

        sys.addConstraint(allDifferent(x))
        sys.addConstraint(circuit(x))

        sys.resolve(parallel=true, tabuThreshold=50000)

        let sol = x.assignment()

        # Validate it's a valid circuit
        check validateCircuit(sol, numCells)

        # Validate all moves are valid knight moves
        for cell in 0..<numCells:
            let fromRow = cell div N
            let fromCol = cell mod N
            let toCell = sol[cell] - 1  # convert 1-based to 0-based
            let toRow = toCell div N
            let toCol = toCell mod N
            let dr = abs(fromRow - toRow)
            let dc = abs(fromCol - toCol)
            check (dr == 1 and dc == 2) or (dr == 2 and dc == 1)

    test "Multi-step moveDelta + updatePosition consistency":
        # Simulate solver behavior: repeatedly pick a move, check delta, apply, verify
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(circuit(x))

        let initial = @[2, 1, 4, 3, 6, 5]
        sys.initialize(initial)

        let constraint = sys.baseArray.constraints[0]
        let circuitRef = constraint.circuitState
        var current = initial

        # Sequence of moves: (position, newValue)
        let moves = @[
            (1, 3), (0, 4), (3, 1), (5, 2), (2, 6), (4, 3),
            (0, 1), (1, 2), (3, 5), (2, 3), (5, 6), (4, 1),
            (0, 3), (1, 5), (2, 1), (3, 6), (4, 4), (5, 2),
        ]

        for (pos, newVal) in moves:
            let oldVal = current[pos]
            # Check moveDelta
            let delta = constraint.moveDelta(pos, oldVal, newVal)
            let costBefore = constraint.penalty()
            # Apply
            constraint.updatePosition(pos, newVal)
            current[pos] = newVal
            let actualCost = constraint.penalty()
            # Verify via full recomputation
            let expectedCost = circuitRef.computePenalty()
            check actualCost == expectedCost
            # Verify delta was correct
            check actualCost == costBefore + delta
            # Also verify moveDelta for all possible next moves from this state
            for testPos in 0..<6:
                for testVal in 1..6:
                    if testVal == current[testPos]:
                        continue
                    let testDelta = constraint.moveDelta(testPos, current[testPos], testVal)
                    let oldSucc2 = circuitRef.successorArray[testPos]
                    circuitRef.successorArray[testPos] = testVal - 1
                    let expectedCost2 = circuitRef.computePenalty()
                    circuitRef.successorArray[testPos] = oldSucc2
                    check testDelta == expectedCost2 - actualCost

    test "Exhaustive moveDelta consistency (6-node, all moves)":
        # Try every possible (position, newValue) on several starting configurations
        # and verify that moveDelta matches full recomputation via computePenalty.
        let configs = @[
            @[2, 3, 4, 5, 6, 1],  # single circuit
            @[2, 1, 4, 3, 6, 5],  # three 2-cycles
            @[1, 2, 3, 4, 5, 6],  # all self-loops
            @[3, 1, 2, 6, 4, 5],  # two 3-cycles
            @[2, 3, 1, 5, 6, 4],  # two 3-cycles (different)
            @[4, 5, 6, 1, 2, 3],  # two 3-cycles (shifted)
        ]

        for config in configs:
            var sys = initConstraintSystem[int]()
            var x = sys.newConstrainedSequence(6)
            x.setDomain(toSeq(1..6))
            sys.addConstraint(circuit(x))

            sys.initialize(config)

            let constraint = sys.baseArray.constraints[0]
            let circuitRef = constraint.circuitState

            for pos in 0..<6:
                let oldVal = config[pos]
                for newVal in 1..6:
                    if newVal == oldVal:
                        continue
                    let delta = constraint.moveDelta(pos, oldVal, newVal)
                    # Compute expected via full recomputation
                    let oldSucc = circuitRef.successorArray[pos]
                    circuitRef.successorArray[pos] = newVal - 1
                    let expectedNewCost = circuitRef.computePenalty()
                    circuitRef.successorArray[pos] = oldSucc
                    let expectedDelta = expectedNewCost - constraint.penalty()
                    check delta == expectedDelta
