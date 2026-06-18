import std/[sequtils, unittest, random]
import crusher
import constraints/involution
import constraints/unionCycle

suite "Involution Constraint":
    test "valid fixed-point-free involution has penalty 0":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))
        sys.addConstraint(involution(x))
        sys.initialize(@[2, 1, 4, 3, 6, 5])     # (1 2)(3 4)(5 6)
        check sys.baseArray.constraints[0].penalty() == 0

    test "fixed points are penalized":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..4))
        sys.addConstraint(involution(x))
        sys.initialize(@[1, 2, 3, 4])            # every node a fixed point
        check sys.baseArray.constraints[0].penalty() == 4

    test "non-involution permutation is penalized":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(1..3))
        sys.addConstraint(involution(x))
        sys.initialize(@[2, 3, 1])               # 3-cycle: x[x[i]] != i everywhere
        check sys.baseArray.constraints[0].penalty() == 3

    test "moveDelta matches recomputed penalty":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..4))
        sys.addConstraint(involution(x))
        sys.initialize(@[2, 1, 4, 3])
        let c = sys.baseArray.constraints[0]
        let before = c.penalty()
        let delta = c.moveDelta(0, 2, 3)         # node 0: 2 -> 3
        c.updatePosition(0, 3)
        check c.penalty() == before + delta

suite "Union-Cycle Constraint":
    test "two matchings whose union is one cycle: penalty 0":
        var sys = initConstraintSystem[int]()
        var a = sys.newConstrainedSequence(6)
        a.setDomain(toSeq(1..6))
        var b = sys.newConstrainedSequence(6)
        b.setDomain(toSeq(1..6))
        sys.addConstraint(unionCycle(a, b))
        # a = (1 2)(3 4)(5 6); b = (1 6)(2 3)(4 5). Union edges:
        #   0-1, 2-3, 4-5  ∪  0-5, 1-2, 3-4  =  single 6-cycle.
        sys.initialize(@[2, 1, 4, 3, 6, 5,   6, 3, 2, 5, 4, 1])
        check sys.baseArray.constraints[0].penalty() == 0

    test "union with two components is penalized":
        var sys = initConstraintSystem[int]()
        var a = sys.newConstrainedSequence(6)
        a.setDomain(toSeq(1..6))
        var b = sys.newConstrainedSequence(6)
        b.setDomain(toSeq(1..6))
        sys.addConstraint(unionCycle(a, b))
        # a = b = (1 2)(3 4)(5 6): union is three 2-cycles -> 3 components -> 2.
        sys.initialize(@[2, 1, 4, 3, 6, 5,   2, 1, 4, 3, 6, 5])
        check sys.baseArray.constraints[0].penalty() == 2

    test "moveDelta matches recomputed penalty":
        var sys = initConstraintSystem[int]()
        var a = sys.newConstrainedSequence(4)
        a.setDomain(toSeq(1..4))
        var b = sys.newConstrainedSequence(4)
        b.setDomain(toSeq(1..4))
        sys.addConstraint(unionCycle(a, b))
        sys.initialize(@[2, 1, 4, 3,   2, 1, 4, 3])   # two 2-cycles each -> 2 comps
        let c = sys.baseArray.constraints[0]
        let before = c.penalty()
        let delta = c.moveDelta(0, 2, 3)              # node 0's a-edge: 2 -> 3
        c.updatePosition(0, 3)
        check c.penalty() == before + delta

    test "incremental moveDelta matches full recompute over random states":
        # Exercises both the O(1) fast path (matching locally valid) and the O(n)
        # fallback (matching broken) across many random assignments and moves.
        var rng = initRand(98765)
        let n = 6
        for trial in 0..<400:
            var sys = initConstraintSystem[int]()
            var a = sys.newConstrainedSequence(n)
            a.setDomain(toSeq(1..n))
            var b = sys.newConstrainedSequence(n)
            b.setDomain(toSeq(1..n))
            sys.addConstraint(unionCycle(a, b))
            var asg = newSeq[int](2 * n)
            for k in 0..<(2 * n): asg[k] = rng.rand(1..n)
            sys.initialize(asg)
            let c = sys.baseArray.constraints[0]
            let pos = rng.rand(0..<(2 * n))
            let oldV = asg[pos]
            let newV = rng.rand(1..n)
            let predicted = c.moveDelta(pos, oldV, newV)
            let before = c.penalty()
            c.updatePosition(pos, newV)
            let actual = c.penalty() - before
            check predicted == actual

    test "solver finds a perfect 1-factorization of K_6":
        # Matching-level p1f model: involution rows, all-different columns, every
        # pair of rows unions to a single cycle.
        let n = 6
        let m = n - 1
        var sys = initConstraintSystem[int]()
        var rows: seq[seq[int]] = @[]
        var rowSeqs: seq[ConstrainedSequence[int]] = @[]
        for r in 0..<m:
            var row = sys.newConstrainedSequence(n)
            for i in 0..<n:
                row.setDomain(i, toSeq(1..n).filterIt(it != i + 1))
            rowSeqs.add(row)
            let posns = toSeq(row.offset..<(row.offset + row.size))
            rows.add(posns)
            sys.baseArray.addInverseGroup(posns, -1)
            sys.addConstraint(involution(row))
        for col in 0..<n:
            sys.addConstraint(allDifferent[int](rows.mapIt(it[col])))
        for a in 0..<m:
            for b in (a + 1)..<m:
                sys.addConstraint(unionCycle(rowSeqs[a], rowSeqs[b]))

        sys.resolve(parallel = true, tabuThreshold = 5000)

        # Validate the returned assignment is a genuine perfect 1-factorization.
        var asg: seq[seq[int]] = @[]
        for r in 0..<m: asg.add(rowSeqs[r].assignment)
        for r in 0..<m:
            for i in 0..<n:
                check asg[r][i] != i + 1                 # no fixed point
                check asg[r][asg[r][i] - 1] == i + 1     # involution
        for a in 0..<m:
            for b in (a + 1)..<m:
                var parent = toSeq(0..<n)
                proc find(p: var seq[int], x: int): int =
                    var r = x
                    while p[r] != r: r = p[r]
                    r
                for i in 0..<n:
                    let ta = asg[a][i] - 1
                    if find(parent, i) != find(parent, ta): parent[find(parent, i)] = find(parent, ta)
                    let tb = asg[b][i] - 1
                    if find(parent, i) != find(parent, tb): parent[find(parent, i)] = find(parent, tb)
                var comps = 0
                for i in 0..<n:
                    if find(parent, i) == i: comps += 1
                check comps == 1                         # union is a single cycle
