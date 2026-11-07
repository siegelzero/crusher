## Cumulative sweep mode (event-based, no time-indexed profile) must agree
## exactly with the profile mode: cost, moveDelta, batchMovePenalty and
## incremental updates, including tasks clipped at the horizon ends.

import std/[unittest, random, sequtils]
import crusher
import constraints/cumulative

proc pair(n: int, durs, heights: seq[int], limit: int,
          useExpr: bool, offsets: seq[int]): (CumulativeConstraint[int], CumulativeConstraint[int]) =
    if useExpr:
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..100))
        var e1, e2: seq[AlgebraicExpression[int]]
        for i in 0..<n:
            e1.add(x[i] + offsets[i])
            e2.add(x[i] + offsets[i])
        result = (newCumulativeConstraint[int](e1, durs, heights, limit),
                  newCumulativeConstraint[int](e2, durs, heights, limit))
    else:
        let pos = toSeq(0..<n)
        result = (newCumulativeConstraint[int](pos, durs, heights, limit),
                  newCumulativeConstraint[int](pos, durs, heights, limit))
    result[0].sweepOverride = 1
    result[1].sweepOverride = -1

suite "Cumulative sweep mode":
    test "sweep and profile modes agree on random instances":
        randomize(12345)
        var checked = 0
        for trial in 0..<60:
            let n = rand(1..9)
            let useExpr = trial mod 2 == 1
            var durs, heights, offsets: seq[int]
            for i in 0..<n:
                durs.add(rand(0..40))
                heights.add(rand(0..4))
                offsets.add(rand(-5..5))
            let limit = rand(0..5)
            let horizon = 150
            var (sw, pr) = pair(n, durs, heights, limit, useExpr, offsets)
            var a = newSeq[int](n)
            for i in 0..<n: a[i] = rand(0..horizon)
            sw.initialize(a)
            pr.initialize(a)
            check sw.sweepMode
            check not pr.sweepMode
            check sw.cost == pr.cost
            for step in 0..<40:
                let p = rand(0..<n)
                # values may push tasks before 0 or past maxTime (clipping)
                let dom = toSeq(-10..horizon + 60)
                let bs = sw.batchMovePenalty(p, a[p], dom)
                let bp = pr.batchMovePenalty(p, a[p], dom)
                check bs == bp
                for k in 0..<5:
                    let v = dom[rand(0..<dom.len)]
                    check sw.moveDelta(p, a[p], v) == pr.moveDelta(p, a[p], v)
                    inc checked
                let v = rand(0..horizon)
                let before = sw.cost
                let md = sw.moveDelta(p, a[p], v)
                sw.updatePosition(p, v)
                pr.updatePosition(p, v)
                a[p] = v
                check sw.cost == pr.cost
                check sw.cost - before == md
        check checked > 0

    test "auto mode picks sweep for long durations, profile for short":
        let pos = @[0, 1, 2]
        var long = newCumulativeConstraint[int](pos, @[50000, 60000, 70000], @[1, 1, 1], 1)
        long.initialize(@[0, 10000, 300000])
        check long.sweepMode
        check long.resourceProfile.len == 0
        check long.cost == 40000 + 0     # [10000, 50000) overlaps
        var short = newCumulativeConstraint[int](pos, @[3, 4, 5], @[1, 1, 1], 1)
        short.initialize(@[0, 1, 20])
        check not short.sweepMode
        check short.cost == 2            # [1, 3)

    test "sweep-mode disjunctive solved end to end":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(0..20).mapIt(it * 10000))
        let durs = @[60000, 50000, 40000, 30000]
        sys.addConstraint(cumulative[int]([0, 1, 2, 3], durs, @[1, 1, 1, 1], 1))
        sys.resolve(parallel = false, tabuThreshold = 5000)
        check sys.hasFeasibleSolution
        let a = s.assignment
        for i in 0..<4:
            for j in i + 1..<4:
                check a[i] + durs[i] <= a[j] or a[j] + durs[j] <= a[i]

    test "constant durations passed as -1 position arrays still use sweep":
        # The FZN disjunctive translation passes dur/height position arrays of -1.
        let pos = @[0, 1]
        var c = newCumulativeConstraint[int](pos, @[50000, 60000], @[1, 1], 1)
        c.durationPositions = @[-1, -1]
        c.heightPositions = @[-1, -1]
        c.initialize(@[0, 20000])
        check c.sweepMode
        check c.cost == 30000
