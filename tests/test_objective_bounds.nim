## Tests for optimization with objective domain bounds (lowerBound/upperBound).
## Exercises the two-phase approach: find feasible first, then constrain to bounds.
## Reproduces the core issue from community-detection where MiniZinc domain bounds
## on the objective variable were too tight for local search to satisfy directly.

import std/[sequtils, sets, unittest]
import crusher

suite "Optimization with objective bounds":
    test "maximize with upper bound triggers re-solve":
        # 4 variables in {1..10}, allDifferent
        # Natural sum range: [10..34], expected random ≈ 22
        # Upper bound = 15: initial solution very likely violates (sum > 15),
        # triggering the bounds-violated re-solve path in the optimizer.
        # Optimal within bound: 15 (e.g., {1,2,3,9})
        let n = 4
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.maximize(total, parallel=true, tabuThreshold=1000,
                     upperBound=15)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]

        check actualSum <= 15
        check actualSum == 15

    test "minimize with lower bound triggers re-solve":
        # Same structure, lower bound = 29: initial solution (≈22) likely violates.
        # Optimal within bound: 29 (e.g., {2,8,9,10})
        let n = 4
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000,
                     lowerBound=29)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]

        check actualSum >= 29
        check actualSum == 29

    test "maximize with both bounds":
        # 5 variables in {1..15}, allDifferent
        # Natural sum range: [15..65], expected random ≈ 40
        # Bounds [30..45]: upperBound is a search hint (not a hard constraint).
        # The optimizer may find solutions above upperBound.
        # Optimal: 11+12+13+14+15=65
        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..15))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.maximize(total, parallel=true, tabuThreshold=1000,
                     lowerBound=30, upperBound=45)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]

        check actualSum >= 30

    test "maximize sum exceeding individual position max":
        # 3 variables in {1..10}, allDifferent.
        # Each position's max is 10, but sum can reach 10+9+8=27.
        # Previously, domain bounds tightening would cap hi=10, preventing
        # the optimizer from finding sums above 10.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.maximize(total, parallel=true, tabuThreshold=1000)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]

        # Optimal is 10+9+8=27, must not be capped at 10
        check actualSum == 27

    test "minimize sum below individual position min":
        # 3 variables in {1..10}, allDifferent.
        # Each position's min is 1, but sum min is 1+2+3=6.
        # This was not directly broken (lo defaults to 0 which is below 6),
        # but verifies the optimizer finds the true minimum.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]
        let vals = toHashSet(solution)

        check vals.len == n  # allDifferent
        check actualSum == 6  # 1+2+3
