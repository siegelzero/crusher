import std/[sequtils, unittest]
import crusher

suite "CountEq Constraint Tests":

    test "Basic count_eq - constant target position":
        # count(array, 3) == x[target] where target has domain {2}
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(5)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..5))
        target.setDomain(@[2])  # exactly 2 occurrences of value 3

        sys.addConstraint(countEq[int](toSeq(0..4), 3, 5))
        sys.resolve()

        let assignment = arr.assignment
        var count = 0
        for v in assignment:
            if v == 3:
                count += 1
        check count == 2
        echo "Basic count_eq: ", assignment, " target=", target.assignment, " count=", count

    test "CountEq - self-referential (magic sequence style)":
        # x[i] = count(x, i) for a small n
        # Magic sequence for n=5: [2, 1, 2, 0, 0]
        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..<n))

        for i in 0..<n:
            sys.addConstraint(countEq[int](toSeq(0..<n), i, i))

        # Also add the well-known sum constraint: sum(x) == n
        sys.addConstraint(x.sum() == n)

        sys.resolve(parallel=true, tabuThreshold=10000)

        let assignment = x.assignment
        echo "Magic sequence n=", n, ": ", assignment

        # Verify: for each i, count of i in assignment == assignment[i]
        for i in 0..<n:
            var count = 0
            for v in assignment:
                if v == i:
                    count += 1
            check count == assignment[i]

    test "CountEq - self-referential n=7":
        # Magic sequence for n=7: [3, 2, 1, 1, 0, 0, 0]
        let n = 7
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..<n))

        for i in 0..<n:
            sys.addConstraint(countEq[int](toSeq(0..<n), i, i))

        sys.addConstraint(x.sum() == n)

        sys.resolve(parallel=true, tabuThreshold=10000)

        let assignment = x.assignment
        echo "Magic sequence n=", n, ": ", assignment

        for i in 0..<n:
            var count = 0
            for v in assignment:
                if v == i:
                    count += 1
            check count == assignment[i]

    test "CountEq penalty and moveDelta":
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(4)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(0..3))
        target.setDomain(toSeq(0..4))

        let constraint = countEq[int](toSeq(0..3), 1, 4)
        sys.addConstraint(constraint)

        # Test: array = [1, 1, 0, 0], target = 2 → count(1) = 2, required = 2, cost = 0
        let assignment1 = @[1, 1, 0, 0, 2]
        constraint.initialize(assignment1)
        check constraint.penalty() == 0

        # Test: array = [1, 1, 0, 0], target = 3 → count(1) = 2, required = 3, cost = 1
        let assignment2 = @[1, 1, 0, 0, 3]
        constraint.initialize(assignment2)
        check constraint.penalty() == 1

        # Test moveDelta: change pos 2 from 0 to 1 → count becomes 3, required still 3 → cost 0
        let delta = constraint.countEqState.moveDelta(2, 0, 1)
        check delta == -1  # cost goes from 1 to 0

        # Test moveDelta on target position: change target from 3 to 1 → required becomes 1, count still 2
        let delta2 = constraint.countEqState.moveDelta(4, 3, 1)
        check delta2 == 0  # cost goes from 1 to |2-1|=1, delta=0

    test "CountEq with value 0":
        # Count of 0s should equal target
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(6)
        var target = sys.newConstrainedVariable()
        arr.setDomain(@[0, 1])
        target.setDomain(toSeq(0..6))

        sys.addConstraint(countEq[int](toSeq(0..5), 0, 6))
        # Also constrain target to be 4
        let targetExpr = sys.baseArray[6]
        sys.addConstraint(targetExpr == 4)

        sys.resolve()

        let assignment = arr.assignment
        var count = 0
        for v in assignment:
            if v == 0:
                count += 1
        check count == 4
        check target.assignment == 4
        echo "Count of 0s: ", assignment, " target=", target.assignment
