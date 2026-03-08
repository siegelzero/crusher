import std/[sequtils, unittest]
import crusher

suite "Constraint re-initialization":

    test "allDifferent penalty resets on re-initialize":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..4))
        sys.addConstraint(allDifferent(x))

        # First init with a violating assignment: [1,1,1,1] -> 3 duplicates
        let violating = @[1, 1, 1, 1]
        sys.initialize(violating)
        let penalty1 = sys.baseArray.constraints[0].penalty()
        check penalty1 == 3

        # Re-init with a valid assignment: [1,2,3,4] -> 0 violations
        let valid = @[1, 2, 3, 4]
        sys.initialize(valid)
        let penalty2 = sys.baseArray.constraints[0].penalty()
        check penalty2 == 0

        # Re-init with violating again to confirm it's exactly 3, not accumulated
        sys.initialize(violating)
        let penalty3 = sys.baseArray.constraints[0].penalty()
        check penalty3 == 3

    test "allDifferentExcept0 penalty resets on re-initialize":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(0..3))
        sys.addConstraint(allDifferentExcept0(x))

        # [1,1,2,3] -> 1 duplicate (value 1 appears twice)
        let violating = @[1, 1, 2, 3]
        sys.initialize(violating)
        let penalty1 = sys.baseArray.constraints[0].penalty()
        check penalty1 == 1

        # [0,0,1,2] -> 0 violations (zeros exempt)
        let valid = @[0, 0, 1, 2]
        sys.initialize(valid)
        let penalty2 = sys.baseArray.constraints[0].penalty()
        check penalty2 == 0

        # Re-init with violating again
        sys.initialize(violating)
        let penalty3 = sys.baseArray.constraints[0].penalty()
        check penalty3 == 1

    test "globalCardinality penalty resets on re-initialize":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(1..2))

        # value 1 should appear 2 times, value 2 should appear 2 times
        let constraint = globalCardinality[int]([0, 1, 2, 3], [1, 2], [2, 2])
        sys.addConstraint(constraint)

        # [1,1,1,1] -> value 1 has 4 (excess 2), value 2 has 0 (deficit 2) = penalty 4
        let violating = @[1, 1, 1, 1]
        sys.initialize(violating)
        let penalty1 = sys.baseArray.constraints[0].penalty()
        check penalty1 > 0

        # [1,1,2,2] -> exact counts, 0 violations
        let valid = @[1, 1, 2, 2]
        sys.initialize(valid)
        let penalty2 = sys.baseArray.constraints[0].penalty()
        check penalty2 == 0

        # Re-init with violating to confirm no accumulation
        sys.initialize(violating)
        let penalty3 = sys.baseArray.constraints[0].penalty()
        check penalty3 == penalty1
