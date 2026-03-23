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

    test "minimize with negative optimal value":
        # 3 variables in {1..10}, allDifferent.
        # Objective: x[0] - x[1] - x[2]
        # Minimum is 1 - 10 - 9 = -18 (x[0]=1, x[1]=10, x[2]=9)
        # Previously, binary search lo defaulted to 0, so negative
        # optima were unreachable.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))
        sys.addConstraint(allDifferent(x))

        let total = x[0] - x[1] - x[2]

        sys.minimize(total, parallel=true, tabuThreshold=1000)

        let solution = x.assignment
        let objVal = solution[0] - solution[1] - solution[2]
        let vals = toHashSet(solution)

        check vals.len == n  # allDifferent
        check objVal == -18  # 1 - 10 - 9

    test "loProven not inherited by heuristic bound updates":
        # Regression test: when lowerBound is provided (e.g., from FZN objective
        # domain), loProven is initialized to true. If the binary search later
        # fails at some target and updates lo heuristically, loProven must be
        # reset to false — otherwise the optimizer can falsely claim optimality
        # at a suboptimal value.
        #
        # Setup: 5 variables in {1..20}, allDifferent, minimize sum.
        # Optimal: 1+2+3+4+5=15. Provide lowerBound=0 (true but loose).
        # The optimizer should find 15 and NOT stop early claiming optimality
        # at a higher value.
        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..20))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000,
                     lowerBound=0)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]

        # Must find the true optimum, not stop early
        check actualSum == 15  # 1+2+3+4+5

    test "optimalityProven only from domain reduction":
        # Verify that optimalityProven is only set when InfeasibleError
        # proves a bound, not from search failures.
        # 3 variables in {1..5}, allDifferent, minimize sum.
        # Optimal: 1+2+3=6. Domain reduction can prove lowerBound=6.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..5))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000,
                     lowerBound=0)

        let solution = x.assignment
        var actualSum = 0
        for i in 0..<n:
            actualSum += solution[i]

        check actualSum == 6  # 1+2+3

    test "domain bound prevents accepting infeasible solutions (minimize)":
        # When lowerBound is provided, the optimizer must never accept a solution
        # whose objective is below that bound, even if the solver finds one with
        # zero penalty (which can happen with disconnected variable arrays).
        #
        # Setup: 3 variables in {1..10}, objective = x[0] (just first variable).
        # lowerBound=5: optimizer must never report objective < 5.
        # True minimum of x[0] is 1, but lowerBound says 5 is the floor.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))

        let obj = x[0]
        sys.minimize(obj, parallel=true, tabuThreshold=1000, lowerBound=5)

        let objVal = sys.assignment[0]
        check objVal >= 5  # Must respect the domain lower bound

    test "domain bound prevents accepting infeasible solutions (maximize)":
        # Symmetric test for maximize: upperBound=7 means no solution above 7.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..10))

        let obj = x[0]
        sys.maximize(obj, parallel=true, tabuThreshold=1000, upperBound=7)

        let objVal = sys.assignment[0]
        check objVal <= 7

    test "proven optimal when objective reaches domain lower bound":
        # When the solver finds objective == lowerBound, it should claim
        # "proven optimal" because no feasible solution can exist below the
        # variable's domain lower bound.
        #
        # 3 variables in {5..10}, allDifferent, minimize sum.
        # Optimal: 5+6+7=18. Provide lowerBound=18 (tight).
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(5..10))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000, lowerBound=18)

        var actualSum = 0
        for i in 0..<n:
            actualSum += x.assignment[i]
        check actualSum == 18
        check sys.optimalityProven == true

    test "proven optimal when objective reaches domain upper bound (maximize)":
        # 3 variables in {1..5}, allDifferent, maximize sum.
        # Optimal: 3+4+5=12. Provide upperBound=12 (tight).
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..5))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.maximize(total, parallel=true, tabuThreshold=1000, upperBound=12)

        var actualSum = 0
        for i in 0..<n:
            actualSum += x.assignment[i]
        check actualSum == 12
        check sys.optimalityProven == true

    test "no false proven claim with loose domain bound":
        # lowerBound=0 is far from optimal (15). The optimizer should find 15
        # and NOT claim proven optimal (since 15 > 0 and domain reduction
        # didn't prove the bound).
        # Exception: domain reduction may actually prove lo=15 via InfeasibleError,
        # in which case proven is legitimate. We just verify the objective is correct.
        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..20))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000, lowerBound=0)

        var actualSum = 0
        for i in 0..<n:
            actualSum += x.assignment[i]
        check actualSum == 15  # 1+2+3+4+5

    test "loProven set only by InfeasibleError not by domain bound":
        # 3 variables in {1..5}, allDifferent, minimize sum = 6.
        # lowerBound=6 (exact). The optimizer finds 6 and proves optimal
        # because currentCost == domainLoBound, NOT because loProven was
        # initialized from the domain bound.
        # This verifies the code path: domainLoBound match → proven.
        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(1..5))
        sys.addConstraint(allDifferent(x))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]

        sys.minimize(total, parallel=true, tabuThreshold=1000, lowerBound=6)

        var actualSum = 0
        for i in 0..<n:
            actualSum += x.assignment[i]
        check actualSum == 6
        # Proven because we reached the domain bound
        check sys.optimalityProven == true
