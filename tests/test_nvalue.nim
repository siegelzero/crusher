import std/[sequtils, unittest]
import crusher

suite "NValue Constraint Tests":

    test "Basic nvalue - all different":
        # 5 positions, all must be distinct => nvalue = 5
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(5)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..5))
        target.setDomain(@[5])  # exactly 5 distinct values

        sys.addConstraint(nvalue[int](toSeq(0..4), 5))
        sys.addConstraint(allDifferent[int](arr))
        sys.resolve()

        let assignment = arr.assignment
        var distinct_vals: seq[int]
        for v in assignment:
            if v notin distinct_vals:
                distinct_vals.add(v)
        check distinct_vals.len == 5
        echo "All different nvalue: ", assignment, " distinct=", distinct_vals.len

    test "NValue - all same":
        # 5 positions, all must be the same => nvalue = 1
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(5)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..5))
        target.setDomain(@[1])

        sys.addConstraint(nvalue[int](toSeq(0..4), 5))
        sys.resolve()

        let assignment = arr.assignment
        var distinct_vals: seq[int]
        for v in assignment:
            if v notin distinct_vals:
                distinct_vals.add(v)
        check distinct_vals.len == 1
        echo "All same nvalue: ", assignment, " distinct=", distinct_vals.len

    test "NValue - exactly 3 distinct values":
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(6)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..5))
        target.setDomain(@[3])

        sys.addConstraint(nvalue[int](toSeq(0..5), 6))
        sys.resolve()

        let assignment = arr.assignment
        var distinct_vals: seq[int]
        for v in assignment:
            if v notin distinct_vals:
                distinct_vals.add(v)
        check distinct_vals.len == 3
        echo "Exactly 3 nvalue: ", assignment, " distinct=", distinct_vals.len

    test "NValue - variable target":
        # nvalue constraint where target is a search variable
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(4)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..4))
        target.setDomain(toSeq(1..4))

        # Add nvalue constraint + force all different
        sys.addConstraint(nvalue[int](toSeq(0..3), 4))
        sys.addConstraint(allDifferent[int](arr))
        sys.resolve()

        let assignment = arr.assignment
        let targetVal = target.assignment
        var distinct_vals: seq[int]
        for v in assignment:
            if v notin distinct_vals:
                distinct_vals.add(v)
        check distinct_vals.len == targetVal
        echo "Variable target nvalue: ", assignment, " target=", targetVal, " distinct=", distinct_vals.len

    test "NValue penalty and moveDelta":
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(4)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..4))
        target.setDomain(@[2])  # require exactly 2 distinct values

        let c = nvalue[int](toSeq(0..3), 4)
        sys.addConstraint(c)

        # Initialize with assignment [1, 1, 2, 2] -> 2 distinct, target=2 -> cost=0
        var assignment = @[1, 1, 2, 2, 2]
        c.initialize(assignment)
        check c.penalty() == 0

        # moveDelta: change pos 0 from 1 to 3 -> [3, 1, 2, 2] -> 3 distinct, cost=|3-2|=1
        let delta1 = c.moveDelta(0, 1, 3)
        check delta1 == 1

        # moveDelta: change pos 1 from 1 to 2 -> [1, 2, 2, 2] -> still 2 distinct, cost=0
        let delta2 = c.moveDelta(1, 1, 2)
        check delta2 == 0

        # moveDelta: change pos 2 from 2 to 1 -> [1, 1, 1, 2] -> still 2 distinct, cost=0
        let delta3 = c.moveDelta(2, 2, 1)
        check delta3 == 0

        # moveDelta: change target (pos 4) from 2 to 1 -> 2 distinct but target=1 -> cost=|2-1|=1
        let delta4 = c.moveDelta(4, 2, 1)
        check delta4 == 1

        # Apply move: pos 0 from 1 to 3
        c.updatePosition(0, 3)
        check c.penalty() == 1  # 3 distinct, target=2

        # Apply move: pos 1 from 1 to 3
        c.updatePosition(1, 3)
        check c.penalty() == 0  # 2 distinct (2,3), target=2

        echo "NValue penalty/moveDelta tests passed"

    test "NValue - moveDelta removing last occurrence":
        var sys = initConstraintSystem[int]()
        var arr = sys.newConstrainedSequence(3)
        var target = sys.newConstrainedVariable()
        arr.setDomain(toSeq(1..5))
        target.setDomain(@[2])

        let c = nvalue[int](toSeq(0..2), 3)
        sys.addConstraint(c)

        # Assignment [1, 2, 3] -> 3 distinct, target=2, cost=|3-2|=1
        var assignment = @[1, 2, 3, 2]
        c.initialize(assignment)
        check c.penalty() == 1

        # Change pos 2 from 3 to 1 -> [1, 2, 1] -> 2 distinct, cost=|2-2|=0
        let delta = c.moveDelta(2, 3, 1)
        check delta == -1

        # Change pos 0 from 1 to 2 -> [2, 2, 3] -> 2 distinct, cost=|2-2|=0
        let delta2 = c.moveDelta(0, 1, 2)
        check delta2 == -1

        echo "NValue remove-last-occurrence tests passed"
