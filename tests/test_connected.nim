import std/[sequtils, tables, unittest]
import crusher
import constraints/connected

suite "Connected Constraint":
    test "All nodes active, fully connected graph → penalty 0":
        # Triangle: 0-1, 1-2, 0-2 — all active
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(3)  # node vars at positions 0,1,2
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(3)  # edge vars at positions 3,4,5
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2]
        let edgePos = @[3, 4, 5]
        let edgeFrom = @[0, 1, 0]
        let edgeTo = @[1, 2, 2]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        # All nodes and edges active
        let assignment = @[1, 1, 1, 1, 1, 1]
        sys.initialize(assignment)

        let cost = sys.baseArray.constraints[0].penalty()
        check cost == 0

    test "Two disconnected components → penalty 1":
        # 4 nodes, 2 edges: 0-1, 2-3 — all active but two components
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(4)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(2)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2, 3]
        let edgePos = @[4, 5]
        let edgeFrom = @[0, 2]
        let edgeTo = @[1, 3]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[1, 1, 1, 1, 1, 1]
        sys.initialize(assignment)

        check sys.baseArray.constraints[0].penalty() == 1

    test "Three components → penalty 2":
        # 6 nodes, 3 edges: 0-1, 2-3, 4-5 — three components
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(6)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(3)
        es.setDomain(@[0, 1])

        let nodePos = toSeq(0..5)
        let edgePos = @[6, 7, 8]
        let edgeFrom = @[0, 2, 4]
        let edgeTo = @[1, 3, 5]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[1, 1, 1, 1, 1, 1, 1, 1, 1]
        sys.initialize(assignment)

        check sys.baseArray.constraints[0].penalty() == 2

    test "Single active node → penalty 0":
        # 3 nodes, 2 edges, only node 1 active
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(3)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(2)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2]
        let edgePos = @[3, 4]
        let edgeFrom = @[0, 1]
        let edgeTo = @[1, 2]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[0, 1, 0, 0, 0]
        sys.initialize(assignment)

        check sys.baseArray.constraints[0].penalty() == 0

    test "No nodes active → penalty 0":
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(3)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(2)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2]
        let edgePos = @[3, 4]
        let edgeFrom = @[0, 1]
        let edgeTo = @[1, 2]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[0, 0, 0, 0, 0]
        sys.initialize(assignment)

        check sys.baseArray.constraints[0].penalty() == 0

    test "moveDelta consistency: toggle node on/off":
        # Path graph: 0-1-2-3
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(4)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(3)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2, 3]
        let edgePos = @[4, 5, 6]
        let edgeFrom = @[0, 1, 2]
        let edgeTo = @[1, 2, 3]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        # All active, connected
        let assignment = @[1, 1, 1, 1, 1, 1, 1]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]
        check constraint.penalty() == 0

        # Deactivate middle node (1) → splits into {0} and {2,3}
        let delta1 = constraint.moveDelta(1, 1, 0)
        constraint.updatePosition(1, 0)
        check constraint.penalty() == 0 + delta1
        check constraint.penalty() == 1  # two components

        # Reactivate node 1 → connected again
        let delta2 = constraint.moveDelta(1, 0, 1)
        constraint.updatePosition(1, 1)
        check constraint.penalty() == 1 + delta2
        check constraint.penalty() == 0

    test "moveDelta consistency: multi-step on grid graph":
        # 2x2 grid: nodes 0,1,2,3
        # Edges: 0-1, 0-2, 1-3, 2-3
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(4)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(4)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2, 3]
        let edgePos = @[4, 5, 6, 7]
        let edgeFrom = @[0, 0, 1, 2]
        let edgeTo = @[1, 2, 3, 3]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[1, 1, 1, 1, 1, 1, 1, 1]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]
        let connRef = constraint.connectedState
        var current = assignment

        # Sequence of toggles
        let moves = @[
            (0, 0),  # deactivate node 0
            (3, 0),  # deactivate node 3
            (1, 0),  # deactivate node 1
            (2, 0),  # deactivate node 2
            (0, 1),  # reactivate node 0
            (1, 1),  # reactivate node 1
            (2, 1),  # reactivate node 2
            (3, 1),  # reactivate node 3
        ]

        for (pos, newVal) in moves:
            let oldVal = current[pos]
            let delta = constraint.moveDelta(pos, oldVal, newVal)
            let costBefore = constraint.penalty()
            constraint.updatePosition(pos, newVal)
            current[pos] = newVal
            let actualCost = constraint.penalty()
            # Verify via full recomputation
            let expectedCost = max(0, connRef.computeComponents() - 1)
            check actualCost == expectedCost
            check actualCost == costBefore + delta

    test "Edge position changes are ignored by moveDelta":
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(3)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(2)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2]
        let edgePos = @[3, 4]
        let edgeFrom = @[0, 1]
        let edgeTo = @[1, 2]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[1, 1, 1, 1, 1]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]

        # Changing an edge variable should have zero delta
        let delta = constraint.moveDelta(3, 1, 0)
        check delta == 0

    test "deepCopy independence":
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(4)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(3)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2, 3]
        let edgePos = @[4, 5, 6]
        let edgeFrom = @[0, 1, 2]
        let edgeTo = @[1, 2, 3]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        let assignment = @[1, 1, 1, 1, 1, 1, 1]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]
        let original = constraint.connectedState
        let copy = original.deepCopy()

        check copy.cost == original.cost
        check copy.numComponents == original.numComponents

        # Modify original
        original.updatePosition(1, 0)
        check original.cost != copy.cost  # copy should be unaffected

    test "3x3 grid Hitori-like scenario":
        # 3x3 grid, 9 nodes, 12 edges
        # Nodes indexed row-major: 0..8
        # Edges: horizontal (0-1,1-2,3-4,4-5,6-7,7-8) + vertical (0-3,1-4,2-5,3-6,4-7,5-8)
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(9)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(12)
        es.setDomain(@[0, 1])

        let nodePos = toSeq(0..8)
        let edgePos = toSeq(9..20)
        let edgeFrom = @[0, 1, 3, 4, 6, 7, 0, 1, 2, 3, 4, 5]
        let edgeTo   = @[1, 2, 4, 5, 7, 8, 3, 4, 5, 6, 7, 8]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        # All active → connected
        var assignment = newSeq[int](21)
        for i in 0..<21:
            assignment[i] = 1
        sys.initialize(assignment)
        check sys.baseArray.constraints[0].penalty() == 0

        let constraint = sys.baseArray.constraints[0]

        # Deactivate center node (4) — remaining nodes still connected via edges
        let delta = constraint.moveDelta(4, 1, 0)
        constraint.updatePosition(4, 0)
        # 8 remaining nodes on the border of a 3x3 grid form a cycle → connected
        check constraint.penalty() == 0

        # Deactivate node 1 (top middle) — now 0 is only connected to 3
        # Remaining: 0,2,3,5,6,7,8
        let delta2 = constraint.moveDelta(1, 1, 0)
        constraint.updatePosition(1, 0)
        # Still connected: 0-3-6-7-8-5-2 is a path
        check constraint.penalty() == 0

        # Deactivate node 3 — now node 0 is isolated
        let delta3 = constraint.moveDelta(3, 1, 0)
        constraint.updatePosition(3, 0)
        # Remaining: 0 (isolated) + {2,5,6,7,8} — 2 components
        check constraint.penalty() == 1

    test "end-to-end resolve: path graph":
        # 4 nodes in a path: 0-1-2-3
        # Solver must find an assignment where active nodes are connected.
        var sys = initConstraintSystem[int]()
        var ns = sys.newConstrainedSequence(4)
        ns.setDomain(@[0, 1])
        var es = sys.newConstrainedSequence(3)
        es.setDomain(@[0, 1])

        let nodePos = @[0, 1, 2, 3]
        let edgePos = @[4, 5, 6]
        let edgeFrom = @[0, 1, 2]
        let edgeTo = @[1, 2, 3]

        sys.addConstraint(connected[int](nodePos, edgePos, edgeFrom, edgeTo))

        # Force at least 2 nodes active via a simple sum constraint
        let sumExpr = ns[0] + ns[1] + ns[2] + ns[3]
        sys.addConstraint(sumExpr >= 2)

        sys.resolve()

        # Verify all constraints satisfied (zero penalty)
        let assignment = sys.assignment
        sys.initialize(assignment)
        for c in sys.baseArray.constraints:
            check c.penalty() == 0
