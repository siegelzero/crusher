import std/[sequtils, tables, unittest]
import crusher
import expressions/weightedSameValue

suite "WeightedSameValueExpression Tests":

    test "Basic evaluate":
        # 3 pairs: (0,1,10), (0,2,20), (1,2,30), constant=5
        let pairs = @[
            (posA: 0, posB: 1, coeff: 10),
            (posA: 0, posB: 2, coeff: 20),
            (posA: 1, posB: 2, coeff: 30),
        ]
        let expr = newWeightedSameValueExpression[int](pairs, constant=5)

        # All same: 5 + 10 + 20 + 30 = 65
        let a1 = @[1, 1, 1]
        check expr.evaluate(a1) == 65

        # None match: 5
        let a2 = @[1, 2, 3]
        check expr.evaluate(a2) == 5

        # Only (0,1) match: 5 + 10 = 15
        let a3 = @[1, 1, 3]
        check expr.evaluate(a3) == 15

    test "Initialize and getValue":
        let pairs = @[
            (posA: 0, posB: 1, coeff: 10),
            (posA: 2, posB: 3, coeff: 20),
        ]
        let expr = newWeightedSameValueExpression[int](pairs, constant=0)

        # pos 0=1, pos 1=1 (match), pos 2=3, pos 3=4 (no match) => 10
        expr.initialize(@[1, 1, 3, 4])
        check expr.value == 10

    test "updatePosition creates match":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newWeightedSameValueExpression[int](pairs, constant=0)

        expr.initialize(@[1, 2])
        check expr.value == 0

        # Change pos 1 from 2 to 1 -> now matches
        expr.updatePosition(1, 1)
        check expr.value == 10

    test "updatePosition breaks match":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newWeightedSameValueExpression[int](pairs, constant=0)

        expr.initialize(@[1, 1])
        check expr.value == 10

        # Change pos 0 from 1 to 2 -> no longer matches
        expr.updatePosition(0, 2)
        check expr.value == 0

    test "updatePosition no effect":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newWeightedSameValueExpression[int](pairs, constant=0)

        expr.initialize(@[1, 2])
        check expr.value == 0

        # Change pos 0 from 1 to 3 -> still no match
        expr.updatePosition(0, 3)
        check expr.value == 0

    test "moveDelta matches full recomputation":
        let pairs = @[
            (posA: 0, posB: 1, coeff: 10),
            (posA: 0, posB: 2, coeff: 20),
            (posA: 1, posB: 2, coeff: 30),
        ]
        let expr = newWeightedSameValueExpression[int](pairs, constant=5)

        expr.initialize(@[1, 2, 1])
        # (0,2) match: value = 5 + 20 = 25
        check expr.value == 25

        # moveDelta: change pos 1 from 2 to 1
        let delta = expr.moveDelta(1, 2, 1)
        # After: all same -> value = 65, delta = 65 - 25 = 40
        check delta == 40

        # moveDelta: change pos 0 from 1 to 3
        let delta2 = expr.moveDelta(0, 1, 3)
        # After: pos0=3, pos1=2, pos2=1 -> no matches -> value = 5, delta = 5 - 25 = -20
        check delta2 == -20

    test "Self-pairs folded into constant":
        let pairs = @[
            (posA: 0, posB: 0, coeff: 100),  # self-pair, always matches
            (posA: 0, posB: 1, coeff: 10),
        ]
        let expr = newWeightedSameValueExpression[int](pairs, constant=5)

        # Self-pair should be folded: constant = 5 + 100 = 105
        # Only 1 real pair remains
        check expr.pairs.len == 1
        check expr.constant == 105

        expr.initialize(@[1, 2])
        check expr.value == 105  # no match on real pair

        expr.initialize(@[1, 1])
        check expr.value == 115  # match on real pair: 105 + 10

    test "deepCopy independence":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newWeightedSameValueExpression[int](pairs, constant=5)

        expr.initialize(@[1, 1])
        check expr.value == 15

        let copy = expr.deepCopy()
        check copy.value == 15

        # Modify original
        expr.updatePosition(0, 2)
        check expr.value == 5

        # Copy should be unaffected
        check copy.value == 15

    test "Integration: minimize weighted same-value objective":
        # 4 variables with domain {1,2,3}
        # Objective: sum of coeff * delta(x_i == x_j) for all pairs
        # Minimizing => want all different
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(@[1, 2, 3, 4])

        let pairs = @[
            (posA: 0, posB: 1, coeff: 1),
            (posA: 0, posB: 2, coeff: 1),
            (posA: 0, posB: 3, coeff: 1),
            (posA: 1, posB: 2, coeff: 1),
            (posA: 1, posB: 3, coeff: 1),
            (posA: 2, posB: 3, coeff: 1),
        ]
        let obj = newWeightedSameValueExpression[int](pairs, constant=0)

        minimize(sys, obj, parallel=true, tabuThreshold=1000)

        obj.initialize(sys.assignment)
        # Minimum is 0 (all different)
        check obj.value == 0
        echo "Minimize result: ", x.assignment, " objective=", obj.value

    test "Integration: maximize weighted same-value objective":
        # 3 variables with domain {1,2}
        # Maximize same-value pairs => want all same
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(@[1, 2])

        let pairs = @[
            (posA: 0, posB: 1, coeff: 1),
            (posA: 0, posB: 2, coeff: 1),
            (posA: 1, posB: 2, coeff: 1),
        ]
        let obj = newWeightedSameValueExpression[int](pairs, constant=0)

        maximize(sys, obj, parallel=true, tabuThreshold=1000)

        obj.initialize(sys.assignment)
        # Maximum is 3 (all same)
        check obj.value == 3
        echo "Maximize result: ", x.assignment, " objective=", obj.value

    test "moveDelta on position not in any pair":
        let pairs = @[(posA: 0, posB: 1, coeff: 10)]
        let expr = newWeightedSameValueExpression[int](pairs, constant=0)

        expr.initialize(@[1, 1, 5])
        # Position 2 is not in any pair
        check expr.moveDelta(2, 5, 9) == 0
