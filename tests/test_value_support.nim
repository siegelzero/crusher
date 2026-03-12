import std/[unittest, sequtils, packedsets]
import crusher

suite "ValueSupport constraint":
    test "basic penalty computation - satisfied":
        # Cell value 1: no predecessors needed → cost 0
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])
        sys.addConstraint(valueSupport[int](cell.offset, @[n1.offset, n2.offset], 5))
        sys.resolve(parallel=false, tabuThreshold=1000)
        let cv = cell.assignment()
        let nv1 = n1.assignment()
        let nv2 = n2.assignment()
        # The constraint should be satisfied: for cell value N,
        # all 1..N-1 must appear among neighbours
        if cv == 1:
            check true  # Always satisfied
        elif cv == 2:
            check (nv1 == 1 or nv2 == 1)
        elif cv == 3:
            check ({nv1, nv2} == {1, 2})

    test "penalty for missing predecessors":
        # Direct constraint test: cell=3, neighbours=[2,2]
        # Missing: value 1 → cost = 1
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])

        let c = valueSupport[int](cell.offset, @[n1.offset, n2.offset], 5)
        # Manually initialize with a specific assignment
        var assignment = newSeq[int](3)
        assignment[cell.offset] = 3
        assignment[n1.offset] = 2
        assignment[n2.offset] = 2
        c.valueSupportState.initialize(assignment)
        check c.valueSupportState.cost == 1  # missing value 1

    test "penalty - all predecessors present":
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])

        let c = valueSupport[int](cell.offset, @[n1.offset, n2.offset], 5)
        var assignment = newSeq[int](3)
        assignment[cell.offset] = 3
        assignment[n1.offset] = 1
        assignment[n2.offset] = 2
        c.valueSupportState.initialize(assignment)
        check c.valueSupportState.cost == 0

    test "moveDelta - cell value change":
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])

        let c = valueSupport[int](cell.offset, @[n1.offset, n2.offset], 5)
        var assignment = newSeq[int](3)
        assignment[cell.offset] = 3
        assignment[n1.offset] = 1
        assignment[n2.offset] = 2
        c.valueSupportState.initialize(assignment)
        check c.valueSupportState.cost == 0

        # Change cell from 3 to 1: no predecessors needed → cost becomes 0, delta = 0
        let d1 = c.valueSupportState.moveDelta(cell.offset, 3, 1)
        check d1 == 0

        # Change cell from 3 to 5: need 1,2,3,4 - have 1,2 → missing 3,4 → cost=2, delta=2
        let d2 = c.valueSupportState.moveDelta(cell.offset, 3, 5)
        check d2 == 2

    test "moveDelta - neighbour value change":
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])

        let c = valueSupport[int](cell.offset, @[n1.offset, n2.offset], 5)
        var assignment = newSeq[int](3)
        assignment[cell.offset] = 3  # need 1,2
        assignment[n1.offset] = 1
        assignment[n2.offset] = 2
        c.valueSupportState.initialize(assignment)
        check c.valueSupportState.cost == 0

        # Change n1 from 1 to 5: lose sole provider of 1 → delta = +1
        let d1 = c.valueSupportState.moveDelta(n1.offset, 1, 5)
        check d1 == 1

        # Change n2 from 2 to 1: lose sole provider of 2 → delta = +1 (value 1 now has 2 providers but 2 lost)
        let d2 = c.valueSupportState.moveDelta(n2.offset, 2, 1)
        check d2 == 1

    test "moveDelta matches recompute":
        # Verify moveDelta matches full recomputation for all positions/values
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        var n3 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])
        n3.setDomain(@[1, 2, 3, 4, 5])

        let positions = @[n1.offset, n2.offset, n3.offset]
        let c = valueSupport[int](cell.offset, positions, 5)

        # Test with assignment: cell=4, n1=1, n2=3, n3=2
        var assignment = newSeq[int](4)
        assignment[cell.offset] = 4
        assignment[n1.offset] = 1
        assignment[n2.offset] = 3
        assignment[n3.offset] = 2
        c.valueSupportState.initialize(assignment)
        let baseCost = c.valueSupportState.cost
        check baseCost == 0  # has 1,2,3 → need 1,2,3 for cell=4

        # Test moveDelta for every position and every value
        for pos in @[cell.offset, n1.offset, n2.offset, n3.offset]:
            for v in 1..5:
                let oldV = assignment[pos]
                let delta = c.valueSupportState.moveDelta(pos, oldV, v)
                # Recompute from scratch
                var newAssign = assignment
                newAssign[pos] = v
                var c2 = valueSupport[int](cell.offset, positions, 5)
                c2.valueSupportState.initialize(newAssign)
                let expectedDelta = c2.valueSupportState.cost - baseCost
                check delta == expectedDelta

    test "batchMovePenalty matches moveDelta":
        var sys = initConstraintSystem[int]()
        var cell = sys.newConstrainedVariable()
        var n1 = sys.newConstrainedVariable()
        var n2 = sys.newConstrainedVariable()
        cell.setDomain(@[1, 2, 3, 4, 5])
        n1.setDomain(@[1, 2, 3, 4, 5])
        n2.setDomain(@[1, 2, 3, 4, 5])

        let c = valueSupport[int](cell.offset, @[n1.offset, n2.offset], 5)
        var assignment = newSeq[int](3)
        assignment[cell.offset] = 4
        assignment[n1.offset] = 1
        assignment[n2.offset] = 3
        c.valueSupportState.initialize(assignment)

        let domain = @[1, 2, 3, 4, 5]
        for pos in @[cell.offset, n1.offset, n2.offset]:
            let batch = c.valueSupportState.batchMovePenalty(pos, assignment[pos], domain)
            for i in 0..<domain.len:
                let expected = c.valueSupportState.moveDelta(pos, assignment[pos], domain[i])
                check batch[i] == expected

    test "solve small grid with value-support":
        # 2x2 grid: each cell has 2 neighbours (edges)
        # Cell layout: 0 1
        #              2 3
        # Neighbours: 0→{1,2}, 1→{0,3}, 2→{0,3}, 3→{1,2}
        var sys = initConstraintSystem[int]()
        var cells = newSeq[ConstrainedVariable[int]](4)
        for i in 0..3:
            cells[i] = sys.newConstrainedVariable()
            cells[i].setDomain(@[1, 2, 3])

        let neighbours = @[
            @[cells[1].offset, cells[2].offset],  # cell 0
            @[cells[0].offset, cells[3].offset],  # cell 1
            @[cells[0].offset, cells[3].offset],  # cell 2
            @[cells[1].offset, cells[2].offset],  # cell 3
        ]

        for i in 0..3:
            sys.addConstraint(valueSupport[int](cells[i].offset, neighbours[i], 3))

        sys.resolve(parallel=false, tabuThreshold=5000)

        # Verify solution: for each cell with value N, neighbours have all 1..N-1
        for i in 0..3:
            let cv = cells[i].assignment()
            if cv > 1:
                for v in 1..<cv:
                    var found = false
                    for ni in neighbours[i]:
                        # Find which cell this position corresponds to
                        for j in 0..3:
                            if cells[j].offset == ni and cells[j].assignment() == v:
                                found = true
                    check found
