import std/[sequtils, unittest, sets, random]
import crusher
import ../src/constraints/groupValueDisjoint
import ../src/constraints/guardedCount

suite "GroupValueDisjoint Constraint Tests":

    test "incompatible groups use disjoint facility sets":
        # 4 groups of 3 tokens each over values 1..4; pairs (0,1), (1,2), (2,3), (0,3)
        # incompatible. A 4-cycle is 2-colourable, so two values suffice, but the
        # solver may use more; only disjointness is required.
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(12)
        x.setDomain(toSeq(1..4))
        var groups: seq[seq[int]]
        for g in 0..<4:
            groups.add(@[3*g, 3*g + 1, 3*g + 2])
        let pairs = @[(0, 1), (1, 2), (2, 3), (0, 3)]
        sys.addConstraint(groupValueDisjoint[int](groups, @[newSeq[int](), @[], @[], @[]], pairs, 1, 4))
        sys.resolve()
        check sys.hasFeasibleSolution
        let a = x.assignment
        for (g, h) in pairs:
            let vg = groups[g].mapIt(a[it]).toHashSet
            let vh = groups[h].mapIt(a[it]).toHashSet
            check (vg * vh).len == 0

    test "constant members count as used values":
        # Group 0 = {x0, x1}, group 1 has only the constant member 2: x0, x1 != 2.
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(2)
        x.setDomain(toSeq(1..3))
        sys.addConstraint(groupValueDisjoint[int](@[@[0, 1], newSeq[int]()], @[newSeq[int](), @[2]], @[(0, 1)], 1, 3))
        sys.resolve()
        check sys.hasFeasibleSolution
        for v in x.assignment:
            check v != 2

    test "incremental state matches recomputation under random moves":
        randomize(7)
        let n = 30
        var groups: seq[seq[int]]
        for g in 0..<6:
            groups.add(toSeq(5*g ..< 5*g + 5))
        let pairs = @[(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5), (1, 2)]
        let c = newGroupValueDisjointConstraint[int](groups, newSeqWith(6, newSeq[int]()), pairs, 1, 5)
        var a = newSeq[int](n)
        for i in 0..<n: a[i] = rand(1..5)
        c.initialize(a)
        proc brute(a: seq[int]): int =
            for (g, h) in pairs:
                let vg = groups[g].mapIt(a[it]).toHashSet
                let vh = groups[h].mapIt(a[it]).toHashSet
                result += (vg * vh).len
        check c.cost == brute(a)
        for step in 0..<500:
            let p = rand(n - 1)
            let v = rand(1..5)
            let predicted = c.moveDelta(p, a[p], v)
            let before = c.cost
            a[p] = v
            c.updatePosition(p, v)
            check c.cost == brute(a)
            check c.cost - before == predicted

suite "GuardedCount Constraint Tests":

    test "closed facilities receive no tokens":
        # 6 tokens over facilities 1..3; guards g1..g3 (positions 6..8) with
        # active value 0 meaning "closed": closed facility -> count <= 0.
        # Facility 2 is forced closed, so no token may take value 2.
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(9)
        for i in 0..<6: x.setDomain(i, toSeq(1..3))
        x.setDomain(6, @[0, 1])
        x.setDomain(7, @[0])
        x.setDomain(8, @[0, 1])
        sys.addConstraint(guardedCount[int](toSeq(0..<6), @[1, 2, 3], @[6, 7, 8], @[0, 0, 0], @[0, 0, 0]))
        sys.resolve()
        check sys.hasFeasibleSolution
        let a = x.assignment
        for i in 0..<6:
            check a[i] != 2
            check a[6 + a[i] - 1] == 1

    test "incremental state matches recomputation under random moves":
        randomize(11)
        let nIn = 20
        let inputs = toSeq(0..<nIn)
        let values = @[1, 2, 3, 4]
        let guards = @[20, 21, 22, 23]
        let active = @[0, 0, 1, 0]
        let ubs = @[0, 2, 3, 1]
        let c = newGuardedCountConstraint[int](inputs, values, guards, active, ubs)
        var a = newSeq[int](24)
        for i in 0..<nIn: a[i] = rand(1..4)
        for g in guards: a[g] = rand(0..1)
        c.initialize(a)
        proc brute(a: seq[int]): int =
            for s, v in values:
                if a[guards[s]] == active[s]:
                    var cnt = 0
                    for i in 0..<nIn:
                        if a[i] == v: inc cnt
                    result += max(0, cnt - ubs[s])
        check c.cost == brute(a)
        for step in 0..<600:
            var p, v: int
            if rand(3) == 0:
                p = guards[rand(3)]; v = rand(0..1)
            else:
                p = rand(nIn - 1); v = rand(1..4)
            let predicted = c.moveDelta(p, a[p], v)
            let before = c.cost
            a[p] = v
            c.updatePosition(p, v)
            check c.cost == brute(a)
            check c.cost - before == predicted
