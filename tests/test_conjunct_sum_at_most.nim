import std/[algorithm, unittest]
import crusher

suite "ConjunctSumAtMost Constraint":

    test "moveDelta and updatePosition track group truth":
        # 4 positions, each binary; two pair-groups; budget 1.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(4)
        seqq.setDomain([0, 1])
        # groups: (pos0 AND pos1), (pos2 AND pos3); count up to 1 of these all-1
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3]], 1, 1)
        sys.addConstraint(cons)
        sys.resolve()
        let asgn = seqq.assignment
        # Sanity: at most one pair has both members = 1
        var both = 0
        if asgn[0] == 1 and asgn[1] == 1: inc both
        if asgn[2] == 1 and asgn[3] == 1: inc both
        check both <= 1

    test "Phase 5e: trigger reduction with one fixed-target factor":
        # Group 1 = (pos0 AND pos1), Group 2 = (pos2 AND pos3), budget = 1.
        # Pin pos0 = 1 and pos2 = 1 via singleton domains.
        # Then forcing pos1 = 1 OR pos3 = 1 forces a group; either alone is fine
        # (forcedCount = 0, triggerCount[pos1] = triggerCount[pos3] = 1, both
        # within budget). So no reduction expected.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(4)
        seqq.setDomain([0, 1])
        seqq.setDomain(0, [1])  # pin pos0 = 1
        seqq.setDomain(2, [1])  # pin pos2 = 1
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3]], 1, 1)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        # Domains for pos1 and pos3 should still allow both 0 and 1.
        check reduced[1].sorted == @[0, 1]
        check reduced[3].sorted == @[0, 1]

    test "Phase 5e: trigger reduction when forced count is full":
        # Three pair-groups, budget 1. Pin Group 1 fully to (1,1) so it is
        # already a forced group (forcedCount = 1). Pin pos2 = 1 in Group 2
        # so Group 2's only unfixed factor is pos3 — setting pos3 = 1 would
        # force a second group, exceeding the budget. Phase 5e must exclude
        # 1 from pos3's domain.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(6)
        seqq.setDomain([0, 1])
        seqq.setDomain(0, [1])  # pos0 = 1 (Group 1 first factor)
        seqq.setDomain(1, [1])  # pos1 = 1 (Group 1 second factor) → Group 1 forced
        seqq.setDomain(2, [1])  # pos2 = 1 (Group 2 first factor)
        # pos3 unfixed (Group 2 second factor) — should be reduced to {0}
        # pos4, pos5 unfixed (Group 3) — both unfixed, no reduction
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3], @[4, 5]], 1, 1)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        check reduced[3].sorted == @[0]
        # pos4 and pos5 are still unfixed because Group 3 has 2 unfixed factors
        check reduced[4].sorted == @[0, 1]
        check reduced[5].sorted == @[0, 1]

    test "Phase 5e: high-fanout trigger position":
        # Build N pair-groups, all sharing pos0 as first factor with pos0 fixed
        # to 1. Each group's "other" position is pos1..posN. Budget = 2.
        # forcedCount = 0; each pos_i has triggerCount = 1.
        # 0 + 1 = 1 ≤ 2 → no reduction. (Sanity check that it does NOT misfire.)
        var sys = initConstraintSystem[int]()
        let n = 5
        var seqq = sys.newConstrainedSequence(n + 1)
        seqq.setDomain([0, 1])
        seqq.setDomain(0, [1])
        var groups: seq[seq[int]]
        for i in 1 .. n:
            groups.add(@[0, i])
        let cons = conjunctSumAtMost[int](groups, 1, 2)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        for i in 1 .. n:
            check reduced[i].sorted == @[0, 1]

    test "Phase 5e: dead group ignored":
        # Group 1 = (pos0 AND pos1), pos1 fixed to 0 → Group 1 is dead.
        # Group 2 = (pos2 AND pos3), pos2 fixed to 1, pos3 unfixed.
        # Budget 0 → no group may be true. Group 1 is dead (good), Group 2's
        # trigger position pos3 must be excluded from 1.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(4)
        seqq.setDomain([0, 1])
        seqq.setDomain(1, [0])
        seqq.setDomain(2, [1])
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3]], 1, 0)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        check reduced[3].sorted == @[0]
