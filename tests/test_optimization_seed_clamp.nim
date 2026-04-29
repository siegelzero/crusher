## Tests that newTabuState clamps seed values that fall outside the (possibly
## tightened) sharedDomain. This regression covers a crash on the radiation
## benchmark: during binary-search optimization, tightenReducedDomain shrinks a
## position's reducedDomain in light of a tighter objective bound, and the
## seedAssignment from the previous iteration can hold values that are no
## longer in-domain. Without clamping, the binary fast path in
## updateNeighborPenalties indexes constraintPenalties[pos][localIdx][2] and
## the assertion "index 2 not in 0 .. 1" fires.

import std/[sequtils, unittest]
import ../src/crusher
import ../src/search/tabu

suite "Optimization seed clamping":
    test "newTabuState clamps out-of-domain seed values":
        # Build a 4-variable constraint system over {0..5}. We drive the seed
        # crash directly by tightening one position's reducedDomain to {0,1}
        # and seeding with value 2 there.
        var system = initConstraintSystem[int]()
        let xs = system.newConstrainedSequence(4)
        xs.setDomain(toSeq(0..5))
        system.addConstraint(sum(xs) <= 10)

        # Force domain reduction to materialize reducedDomain.
        system.baseArray.reducedDomain = newSeq[seq[int]](4)
        for i in 0..<4:
            system.baseArray.reducedDomain[i] = toSeq(0..5)
        # Tighten position 1 to a binary domain (mirrors what
        # tightenReducedDomain does after a fresh objective bound).
        system.baseArray.reducedDomain[1] = @[0, 1]
        system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain

        # Seed has value 2 at position 1, which is no longer in-domain.
        let staleSeed = @[3, 2, 0, 1]

        # Without the clamp, init writes 2 into state.assignment[1]; subsequent
        # binary fast-path penalty updates would crash with IndexDefect. With
        # the clamp, init replaces it with a domain value.
        let state = newTabuState[int](system.baseArray, staleSeed)

        check state.assignment[1] in @[0, 1]
        # Other positions whose seed values are still in-domain are preserved.
        check state.assignment[0] == 3
        check state.assignment[2] == 0
        check state.assignment[3] == 1

    test "minimize binary search survives domain tightening between iterations":
        # End-to-end check that the optimizer's binary search no longer crashes
        # when tightenReducedDomain shrinks a position's domain after the seed
        # was recorded. We use a small problem where:
        #   - x[i] in {0..5}, sum(x[i]) <= bound, maximize sum.
        #   - Initial bound is loose, so x[i] can take values ≥ 2.
        #   - As the optimizer ratchets the bound down, bounds propagation
        #     tightens individual x[i] domains, invalidating prior seeds.
        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..5))

        var total: AlgebraicExpression[int] = x[0]
        for i in 1..<n:
            total = total + x[i]
        sys.addConstraint(total <= 10)

        # Maximizing total against the same bound forces binary search to
        # exercise multiple objective-bound constraints, each of which calls
        # tightenReducedDomain and re-seeds with the previous best assignment.
        sys.maximize(total, parallel=true, tabuThreshold=500,
                     upperBound=10)

        var actual = 0
        for i in 0..<n:
            actual += x.assignment[i]
        check actual == 10
