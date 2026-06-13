import std/[unittest, random, tables]
import ../src/constraints/adjacencyEqual

# Brute-force reference: a pair (a, b) is violated iff
# coord(a) == coord(b) + 1 and the label equation does not hold.
proc refCost(items: seq[AdjItemForm[int]], pairs: seq[AdjPairSpec[int]],
             assignment: seq[int]): int =
    var coords = newSeq[int](items.len)
    for i in 0..<items.len:
        var c = items[i].constant
        for k in 0..<items[i].positions.len:
            c += items[i].coeffs[k] * assignment[items[i].positions[k]]
        coords[i] = c
    for p in pairs:
        if coords[p.a] != coords[p.b] + 1: continue
        var s = 0
        var exempt = false
        if p.labelPositions.len > 0:
            for k in 0..<p.labelPositions.len:
                s += p.labelCoeffs[k] * assignment[p.labelPositions[k]]
            exempt = s == p.labelRhs
        if not exempt:
            inc result

proc randomInstance(rng: var Rand, nPositions, nItems, nPairs: int):
        (seq[AdjItemForm[int]], seq[AdjPairSpec[int]]) =
    var items: seq[AdjItemForm[int]]
    for i in 0..<nItems:
        var form = AdjItemForm[int](constant: rng.rand(-3..3))
        let nv = rng.rand(0..2)
        for k in 0..<nv:
            form.positions.add(rng.rand(0..<nPositions))
            form.coeffs.add(rng.sample(@[1, 2, 7]))
        items.add(form)
    var pairs: seq[AdjPairSpec[int]]
    for pi in 0..<nPairs:
        var p = AdjPairSpec[int](
            a: int32(rng.rand(0..<nItems)), b: int32(rng.rand(0..<nItems)))
        if rng.rand(1.0) < 0.8:
            # label equation over 1-2 positions
            let nl = rng.rand(1..2)
            for k in 0..<nl:
                p.labelPositions.add(rng.rand(0..<nPositions))
                p.labelCoeffs.add(rng.sample(@[1, -1]))
            p.labelRhs = rng.rand(-2..2)
        pairs.add(p)
    (items, pairs)

suite "AdjacencyEqual constraint":
    test "cost matches brute force under random updatePosition sequences":
        var rng = initRand(20260611)
        for trial in 0..<50:
            let nPositions = 8
            let (items, pairs) = randomInstance(rng, nPositions, 10, 25)
            let c = newAdjacencyEqualConstraint[int](items, pairs)
            var assignment = newSeq[int](nPositions)
            for p in 0..<nPositions: assignment[p] = rng.rand(0..6)
            c.initialize(assignment)
            check c.cost == refCost(items, pairs, assignment)
            for step in 0..<200:
                let pos = rng.rand(0..<nPositions)
                let newVal = rng.rand(0..6)
                let predicted = c.cost + c.moveDelta(pos, assignment[pos], newVal)
                assignment[pos] = newVal
                c.updatePosition(pos, newVal)
                let expected = refCost(items, pairs, assignment)
                check c.cost == expected
                check predicted == expected

    test "batchMovePenalty matches moveDelta":
        var rng = initRand(424242)
        for trial in 0..<20:
            let nPositions = 6
            let (items, pairs) = randomInstance(rng, nPositions, 8, 16)
            let c = newAdjacencyEqualConstraint[int](items, pairs)
            var assignment = newSeq[int](nPositions)
            for p in 0..<nPositions: assignment[p] = rng.rand(0..5)
            c.initialize(assignment)
            var domain: seq[int]
            for v in 0..5: domain.add(v)
            for pos in 0..<nPositions:
                let batch = c.batchMovePenalty(pos, assignment[pos], domain)
                for i, v in domain:
                    check batch[i] == c.moveDelta(pos, assignment[pos], v)

    test "deepCopy is independent":
        var rng = initRand(7)
        let (items, pairs) = randomInstance(rng, 5, 6, 12)
        let c = newAdjacencyEqualConstraint[int](items, pairs)
        var assignment = @[1, 2, 3, 4, 5]
        c.initialize(assignment)
        let cc = c.deepCopy()
        check cc.cost == c.cost
        c.updatePosition(0, 4)
        cc.updatePosition(0, 0)
        var a1 = assignment; a1[0] = 4
        var a2 = assignment; a2[0] = 0
        check c.cost == refCost(items, pairs, a1)
        check cc.cost == refCost(items, pairs, a2)
