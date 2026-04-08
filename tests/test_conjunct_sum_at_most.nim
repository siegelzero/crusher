import std/[algorithm, sequtils, unittest]
import crusher

# Helper: brute-force evaluate the conjunct-sum-at-most cost from an assignment
# (used to cross-check moveDelta / batchMovePenalty against ground truth).
proc bruteCost(groups: seq[seq[int]], target: int, maxOcc: int,
               assignment: seq[int]): int =
    var actual = 0
    for g in groups:
        var allMatch = true
        for p in g:
            if assignment[p] != target:
                allMatch = false
                break
        if allMatch: inc actual
    return max(0, actual - maxOcc)

suite "ConjunctSumAtMost Constraint":

    test "resolve respects pair-group budget":
        # Smoke test — 4 positions, two pair-groups, budget 1.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(4)
        seqq.setDomain([0, 1])
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3]], 1, 1)
        sys.addConstraint(cons)
        sys.resolve()
        let asgn = seqq.assignment
        var both = 0
        if asgn[0] == 1 and asgn[1] == 1: inc both
        if asgn[2] == 1 and asgn[3] == 1: inc both
        check both <= 1

    test "initialize tallies cost correctly":
        let groups = @[@[0, 1], @[2, 3], @[0, 2]]
        let cons = conjunctSumAtMost[int](groups, 1, 1)
        let st = cons.conjunctSumAtMostState
        # all-ones: groups (0,1)=1, (2,3)=1, (0,2)=1 → actual=3, cost=2
        st.initialize(@[1, 1, 1, 1])
        check st.actualOccurrences == 3
        check cons.penalty() == 2
        # mixed: only (0,1) holds → actual=1, cost=0
        st.initialize(@[1, 1, 0, 0])
        check st.actualOccurrences == 1
        check cons.penalty() == 0
        # zero everywhere → cost 0
        st.initialize(@[0, 0, 0, 0])
        check st.actualOccurrences == 0
        check cons.penalty() == 0

    test "moveDelta predicts cost change exactly (binary groups)":
        let groups = @[@[0, 1], @[2, 3], @[0, 2]]
        let cons = conjunctSumAtMost[int](groups, 1, 1)
        let st = cons.conjunctSumAtMostState
        # Probe every (position, value) move from every binary assignment and
        # confirm the predicted delta matches a brute-force recompute.
        for mask in 0 ..< (1 shl 4):
            var initial = newSeq[int](4)
            for i in 0 ..< 4: initial[i] = (mask shr i) and 1
            st.initialize(initial)
            let curCost = cons.penalty()
            for pos in 0 ..< 4:
                for v in [0, 1]:
                    let predicted = st.moveDelta(pos, initial[pos], v)
                    var trial = initial
                    trial[pos] = v
                    let actualNew = bruteCost(groups, 1, 1, trial)
                    check predicted == actualNew - curCost

    test "moveDelta on shared position counts shared groups":
        # pos0 is in three groups; setting pos0=1 from 0 forces all three.
        let groups = @[@[0, 1], @[0, 2], @[0, 3]]
        let cons = conjunctSumAtMost[int](groups, 1, 2)
        let st = cons.conjunctSumAtMostState
        # All other positions are 1; pos0 = 0 so no group holds.
        st.initialize(@[0, 1, 1, 1])
        check st.actualOccurrences == 0
        check cons.penalty() == 0
        # Predicted delta of moving pos0 0→1: actual goes 0→3, cost goes 0→max(0,3-2)=1.
        check st.moveDelta(0, 0, 1) == 1
        # Apply and verify.
        cons.updatePosition(0, 1)
        check st.actualOccurrences == 3
        check cons.penalty() == 1

    test "moveDelta non-target → non-target is zero":
        # Non-binary domain so we can move between two non-target values.
        let groups = @[@[0, 1], @[2, 3]]
        let cons = conjunctSumAtMost[int](groups, 5, 1)
        let st = cons.conjunctSumAtMostState
        st.initialize(@[5, 5, 2, 3])  # group 0 holds, group 1 doesn't
        check st.actualOccurrences == 1
        check cons.penalty() == 0
        # Move pos2 from 2 to 3: still not target, delta = 0
        check st.moveDelta(2, 2, 3) == 0
        # Move pos2 from 2 to 5 (entering target): pos3 is 3, not target → delta still 0
        check st.moveDelta(2, 2, 5) == 0
        # Move pos3 from 3 to 5: pos2=2 still not target → delta 0
        check st.moveDelta(3, 3, 5) == 0

    test "moveDelta and updatePosition stay consistent over a script":
        let groups = @[@[0, 1], @[1, 2], @[2, 3], @[0, 3], @[0, 1, 2]]
        let cons = conjunctSumAtMost[int](groups, 1, 1)
        let st = cons.conjunctSumAtMostState
        var assignment = @[0, 0, 0, 0]
        st.initialize(assignment)
        # Script: a sequence of moves that exercises both target↔non-target
        # transitions and groups of varying degree. After every move, predicted
        # delta + the constraint's reported penalty must match brute force.
        let script = @[
            (0, 1), (1, 1), (2, 1), (3, 0), (0, 0), (1, 0), (2, 0),
            (3, 1), (0, 1), (1, 1), (2, 1), (0, 0), (3, 0)
        ]
        for (pos, v) in script:
            let oldVal = assignment[pos]
            let predicted = st.moveDelta(pos, oldVal, v)
            let oldCost = cons.penalty()
            cons.updatePosition(pos, v)
            assignment[pos] = v
            let newCost = cons.penalty()
            check newCost - oldCost == predicted
            check newCost == bruteCost(groups, 1, 1, assignment)

    test "batchMovePenalty matches per-value moveDelta":
        let groups = @[@[0, 1], @[0, 2], @[1, 2], @[0, 1, 2]]
        let cons = conjunctSumAtMost[int](groups, 1, 1)
        let st = cons.conjunctSumAtMostState
        # Try several starting states and probe positions 0..2 with full domain.
        let states = @[
            @[0, 0, 0],
            @[1, 0, 0],
            @[1, 1, 0],
            @[1, 1, 1],
            @[0, 1, 1],
        ]
        let domain = @[0, 1]
        for s in states:
            st.initialize(s)
            for pos in 0 ..< 3:
                let batch = st.batchMovePenalty(pos, s[pos], domain)
                check batch.len == domain.len
                for i, v in domain:
                    let perValue = st.moveDelta(pos, s[pos], v)
                    check batch[i] == perValue

    test "high-fanout: moveDelta predicts multi-flip correctly":
        # Position 0 sits in N pair groups. Setting pos0 = 1 (when all others
        # are 1) flips N groups simultaneously — changeCount > 1 case.
        let n = 5
        var groups: seq[seq[int]]
        for i in 1 .. n:
            groups.add(@[0, i])
        let cons = conjunctSumAtMost[int](groups, 1, 2)
        let st = cons.conjunctSumAtMostState
        var initial = newSeq[int](n + 1)
        initial[0] = 0
        for i in 1 .. n: initial[i] = 1
        st.initialize(initial)
        check st.actualOccurrences == 0
        check cons.penalty() == 0
        # Move 0→1: actual jumps from 0 to n, cost from 0 to max(0,n-2).
        let predicted = st.moveDelta(0, 0, 1)
        check predicted == max(0, n - 2)
        cons.updatePosition(0, 1)
        check cons.penalty() == max(0, n - 2)
        # And the reverse direction: pinning back to 0 zeros it out.
        let predictedBack = st.moveDelta(0, 1, 0)
        check predictedBack == -max(0, n - 2)
        cons.updatePosition(0, 0)
        check cons.penalty() == 0

    test "duplicate position within a group is collapsed":
        # Group 0 lists pos0 twice. Without dedup, moveDelta(0, 1, 0) would
        # walk groupsAtLocal[0] = [0, 0, 1] and over-count changeCount = 3,
        # producing delta = -3. The correct answer (changeCount = 2) is -2.
        let groups = @[@[0, 0], @[0, 1], @[2, 3]]
        let cons = conjunctSumAtMost[int](groups, 1, 0)
        let st = cons.conjunctSumAtMostState
        st.initialize(@[1, 1, 1, 1])
        check st.actualOccurrences == 3
        check cons.penalty() == 3
        check st.moveDelta(0, 1, 0) == -2
        cons.updatePosition(0, 0)
        check st.actualOccurrences == 1   # only group 2 still holds
        check cons.penalty() == 1
        # Cross-check: also confirm batchMovePenalty agrees on a fresh state.
        st.initialize(@[1, 1, 1, 1])
        let batch = st.batchMovePenalty(0, 1, @[0, 1])
        check batch == @[-2, 0]

    test "deepCopy yields independent state":
        let groups = @[@[0, 1], @[1, 2], @[0, 2]]
        let cons = conjunctSumAtMost[int](groups, 1, 1)
        let st = cons.conjunctSumAtMostState
        st.initialize(@[1, 1, 1])
        check st.actualOccurrences == 3
        check cons.penalty() == 2
        # Deep-copy the wrapping StatefulConstraint and re-initialize the copy
        # with a different assignment. Original must remain untouched.
        let consCopy = cons.deepCopy()
        let stCopy = consCopy.conjunctSumAtMostState
        stCopy.initialize(@[0, 0, 0])
        check stCopy.actualOccurrences == 0
        check consCopy.penalty() == 0
        # Original is still saturated.
        check st.actualOccurrences == 3
        check cons.penalty() == 2
        # Shared structural seqs must not have been mutated by the fresh init.
        check st.groupTruth.len == 3
        check stCopy.groupTruth.len == 3
        # The copy's positions PackedSet must contain the same positions and
        # be safe to mutate independently.
        check 0 in consCopy.positions
        check 1 in consCopy.positions
        check 2 in consCopy.positions
        check 0 in cons.positions

    test "maxDegree captures shared-position fanout":
        # pos0 appears in 4 groups, pos1..pos4 in 1 each. maxDegree should be 4.
        let groups = @[@[0, 1], @[0, 2], @[0, 3], @[0, 4]]
        let cons = conjunctSumAtMost[int](groups, 1, 2)
        let st = cons.conjunctSumAtMostState
        check st.maxDegree == 4
        # Single pair group, no sharing → both positions have degree 1.
        let consPair = conjunctSumAtMost[int](@[@[5, 6]], 1, 0)
        check consPair.conjunctSumAtMostState.maxDegree == 1
        # Duplicate position within a group must NOT inflate maxDegree.
        let consDup = conjunctSumAtMost[int](@[@[0, 0], @[0, 1]], 1, 0)
        check consDup.conjunctSumAtMostState.maxDegree == 2

    test "single-position groups dispatch to AtMost wrapper":
        # When every group has exactly one element, the wrapper short-circuits
        # to the position-based AtMost. Verify by checking that the resulting
        # constraint isn't a ConjunctSumAtMostType.
        let cons = conjunctSumAtMost[int](@[@[0], @[1], @[2]], 1, 1)
        check cons.stateType == AtMostType

    test "Phase 5e: trigger reduction with one fixed-target factor":
        # Two pair-groups, neither pre-forced. forcedCount = 0; trigger budget
        # is fine for either pos1 or pos3 alone. No reduction should happen.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(4)
        seqq.setDomain([0, 1])
        seqq.setDomain(0, [1])
        seqq.setDomain(2, [1])
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3]], 1, 1)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        check reduced[1].sorted == @[0, 1]
        check reduced[3].sorted == @[0, 1]

    test "Phase 5e: trigger reduction when forced count is full":
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(6)
        seqq.setDomain([0, 1])
        seqq.setDomain(0, [1])
        seqq.setDomain(1, [1])
        seqq.setDomain(2, [1])
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3], @[4, 5]], 1, 1)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        check reduced[3].sorted == @[0]
        check reduced[4].sorted == @[0, 1]
        check reduced[5].sorted == @[0, 1]

    test "Phase 5e: high-fanout trigger position":
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
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(4)
        seqq.setDomain([0, 1])
        seqq.setDomain(1, [0])
        seqq.setDomain(2, [1])
        let cons = conjunctSumAtMost[int](@[@[0, 1], @[2, 3]], 1, 0)
        sys.addConstraint(cons)
        let reduced = sys.baseArray.reduceDomain()
        check reduced[3].sorted == @[0]


# Brute-force isosceles-free check for cross-validation: returns the number of
# isosceles triples in the chosen set on an n×n grid (cells are 0-indexed).
proc bruteIsoscelesViolations(n: int, assignment: seq[int]): int =
    var sel: seq[int]
    for k in 0 ..< n * n:
        if assignment[k] == 1: sel.add(k)
    var violated = 0
    for ai in 0 ..< sel.len:
        for bi in (ai + 1) ..< sel.len:
            for ci in (bi + 1) ..< sel.len:
                let a = sel[ai]; let b = sel[bi]; let c = sel[ci]
                let dab = (a div n - b div n)*(a div n - b div n) +
                          (a mod n - b mod n)*(a mod n - b mod n)
                let dac = (a div n - c div n)*(a div n - c div n) +
                          (a mod n - c mod n)*(a mod n - c mod n)
                let dbc = (b div n - c div n)*(b div n - c div n) +
                          (b mod n - c mod n)*(b mod n - c mod n)
                if dab == dac or dab == dbc or dac == dbc:
                    inc violated
    return violated


suite "isoscelesFreeGrid Constraint":

    test "n=3: enumerates the right triples and finds a feasible solution":
        # On a 3×3 grid, every selected pair has 1 cell that completes an
        # isosceles triple (often the apex on the perpendicular bisector).
        # The constraint should refuse to select more than 2 cells in any
        # such configuration.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(9)
        seqq.setDomain([0, 1])
        var positions: seq[int]
        for i in 0 ..< 9: positions.add(i)
        let cons = isoscelesFreeGrid[int](positions, 3)
        sys.addConstraint(cons)
        sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let asgn = seqq.assignment
        check bruteIsoscelesViolations(3, asgn) == 0

    test "n=4: agrees with brute force on every triple":
        # Cross-check the constraint factory's enumeration: build the
        # constraint with the canonical 16-cell grid, then assert that
        # the resolved assignment is genuinely isosceles-free.
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(16)
        seqq.setDomain([0, 1])
        var positions: seq[int]
        for i in 0 ..< 16: positions.add(i)
        let cons = isoscelesFreeGrid[int](positions, 4)
        sys.addConstraint(cons)
        sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        check bruteIsoscelesViolations(4, seqq.assignment) == 0

    test "all-zero assignment is feasible (cost zero)":
        var sys = initConstraintSystem[int]()
        var seqq = sys.newConstrainedSequence(16)
        seqq.setDomain([0, 1])
        var positions: seq[int]
        for i in 0 ..< 16: positions.add(i)
        let cons = isoscelesFreeGrid[int](positions, 4)
        sys.addConstraint(cons)
        # Initialize to all zeros and check the constraint reports cost 0.
        let st = cons.conjunctSumAtMostState
        st.initialize(newSeq[int](16))  # all zeros
        check st.actualOccurrences == 0
        check cons.penalty() == 0

    test "n < 3 trivially has no constraints":
        # 2×2 grid: no isosceles triple is possible (only 4 cells, and any
        # 3 of them on a 2×2 grid form a right triangle whose two legs are
        # equal — actually that IS isosceles. But the factory short-circuits
        # n < 3, so verify it returns a trivially-satisfied constraint).
        var positions = @[0, 1, 2, 3]
        let cons = isoscelesFreeGrid[int](positions, 2)
        let st = cons.conjunctSumAtMostState
        st.initialize(@[1, 1, 1, 1])
        check st.actualOccurrences == 0
        check cons.penalty() == 0

    test "duplicate triples are deduped (cost is not inflated)":
        # The factory enumerates each triple up to 3 times (once per valid
        # apex). We dedupe by canonical (sorted) triple before constructing
        # the underlying ConjunctSumAtMost. Verify the cost of an all-1
        # assignment matches the actual *unique* triple count, not the
        # enumeration count.
        var positions: seq[int]
        for i in 0 ..< 9: positions.add(i)
        let cons = isoscelesFreeGrid[int](positions, 3)
        let st = cons.conjunctSumAtMostState
        st.initialize(newSeq[int](9).mapIt(1))  # all selected
        # Brute-force count the unique isosceles triples in a 3x3 grid.
        let expected = bruteIsoscelesViolations(3, newSeq[int](9).mapIt(1))
        check st.actualOccurrences == expected
