## Tests for SetIntersectCardConstraint.
## Covers: initialize, moveDelta (cross-checked against ground-truth recompute),
## updatePosition, the minCard > 0 lower-bound arm, and deepCopy independence.

import std/unittest
import constraints/setIntersectCard

proc groundTruthCost(
    left, right: openArray[int],
    vals: openArray[int],
    posBase, maxCard, minCard: int): int =
  ## Recompute dotProduct and cost from scratch, independent of incremental state.
  var dot = 0
  for i in 0..<left.len:
    let a = vals[left[i] - posBase]
    let b = vals[right[i] - posBase]
    dot += min(a, b)
  result = max(0, dot - maxCard) + max(0, minCard - dot)

suite "SetIntersectCard Constraint":

  test "initialize: dotProduct and cost match ground truth":
    # Two 4-element "set" bools. Universe positions 0..7.
    # A.bools = positions 0..3, B.bools = positions 4..7 (parallel: (0,4),(1,5),(2,6),(3,7)).
    # maxCard = 1 means at most 1 index where both A[i] = B[i] = 1.
    let left = @[0, 1, 2, 3]
    let right = @[4, 5, 6, 7]
    let c = newSetIntersectCardConstraint[int](left, right, maxCard = 1, minCard = 0)

    # Assignment: A = {0,1,_,_}, B = {_,1,1,_}. Overlap at index 1 only. dot = 1 → cost 0.
    var assignment = @[1, 1, 0, 0,   0, 1, 1, 0]
    c.initialize(assignment)
    check c.dotProduct == 1
    check c.cost == 0

    # Assignment that overshoots: A = {1,1,1,0}, B = {1,1,1,0}. dot = 3, cost = 3 - 1 = 2.
    var overshoot = @[1, 1, 1, 0,   1, 1, 1, 0]
    c.initialize(overshoot)
    check c.dotProduct == 3
    check c.cost == 2

  test "moveDelta matches ground-truth recompute for every (position, value) pair":
    # Deliberately interleaved positions so posMap has side-0 and side-1 entries at
    # different offsets, and one position (5) belongs to both sides (shared universe element).
    let left  = @[0, 2, 5, 7]
    let right = @[1, 3, 5, 8]  # position 5 appears in both A and B (index 2)
    let c = newSetIntersectCardConstraint[int](left, right, maxCard = 2, minCard = 0)

    # Start with all zeros, then walk through every position flipping 0↔1 and
    # cross-check the incremental delta against a from-scratch recompute.
    var assignment = newSeq[int](9)  # positions 0..8
    c.initialize(assignment)

    let allPositions = @[0, 1, 2, 3, 5, 7, 8]  # every position in the constraint
    for p in allPositions:
      for newVal in [0, 1]:
        let oldVal = c.vals[p - c.posBase]
        let delta = c.moveDelta(p, oldVal, newVal)

        # Ground truth: flip the value in a copy, recompute cost, compare to c.cost + delta.
        var trialVals = c.vals
        trialVals[p - c.posBase] = newVal
        let expectedCost = groundTruthCost(
          left, right, trialVals, c.posBase, c.maxCard, c.minCard)
        check c.cost + delta == expectedCost

  test "moveDelta is zero for same-value moves and for out-of-range positions":
    let c = newSetIntersectCardConstraint[int](@[0, 1], @[2, 3], maxCard = 1, minCard = 0)
    var assignment = @[1, 0, 1, 0]
    c.initialize(assignment)
    # Same value → delta = 0
    check c.moveDelta(0, 1, 1) == 0
    # Position outside constraint's range → delta = 0
    check c.moveDelta(99, 0, 1) == 0
    # Position inside range but not in posMap (impossible here since n=2 covers all)
    # is not testable without crafting a specific layout.

  test "updatePosition applies moves incrementally and keeps cost consistent":
    let c = newSetIntersectCardConstraint[int](@[0, 1, 2], @[3, 4, 5], maxCard = 1, minCard = 0)
    var assignment = @[1, 1, 0, 1, 1, 0]  # dot = min(1,1)+min(1,1)+min(0,0) = 2, cost = 1
    c.initialize(assignment)
    check c.dotProduct == 2
    check c.cost == 1

    # Flip position 1 (A's second bool) to 0 → dot becomes 1, cost 0.
    c.updatePosition(1, 0)
    check c.dotProduct == 1
    check c.cost == 0

    # Flip position 4 (B's second bool) to 0 → dot stays 1 (min(0,0)=0 contributes nothing extra).
    # Wait: previously A[1]=0 B[1]=1 → min=0. Flipping B[1] to 0 doesn't change dot.
    c.updatePosition(4, 0)
    check c.dotProduct == 1
    check c.cost == 0

  test "minCard > 0: lower-bound arm produces positive cost when dot is too low":
    # Require at least 2 intersection elements.
    let c = newSetIntersectCardConstraint[int](@[0, 1, 2], @[3, 4, 5], maxCard = 3, minCard = 2)

    # Zero overlap → cost = minCard - dot = 2.
    var assignment = @[1, 0, 1, 0, 1, 0]  # mins: 0, 0, 0 → dot = 0
    c.initialize(assignment)
    check c.dotProduct == 0
    check c.cost == 2

    # Bring one overlap online: set position 3 (B[0]) to 1. Now A[0]=1 B[0]=1 → dot=1, cost=1.
    let delta1 = c.moveDelta(3, 0, 1)
    check delta1 == -1
    c.updatePosition(3, 1)
    check c.dotProduct == 1
    check c.cost == 1

    # Bring second overlap online: set position 2 (A[2]) to... wait, A[2] is already 1.
    # Set position 5 (B[2]) to 1 instead. Now min(A[2]=1, B[2]=1)=1 → dot=2, cost=0.
    let delta2 = c.moveDelta(5, 0, 1)
    check delta2 == -1
    c.updatePosition(5, 1)
    check c.dotProduct == 2
    check c.cost == 0

    # Overshoot: bring third overlap online. A[1]=0, set both A[1] and B[1] to 1.
    c.updatePosition(1, 1)  # A[1] = 1 now, but B[1]=1, so dot = 3
    check c.dotProduct == 3
    check c.cost == 0  # 3 is within [minCard=2, maxCard=3]

  test "degenerate: empty positions are trivially satisfied":
    let c = newSetIntersectCardConstraint[int](newSeq[int](), newSeq[int](), maxCard = 0, minCard = 0)
    var assignment = newSeq[int](0)
    c.initialize(assignment)
    check c.dotProduct == 0
    check c.cost == 0
    # moveDelta on any position should return 0 since n = 0 (no entries anywhere).
    check c.moveDelta(0, 0, 1) == 0

  test "deepCopy produces independent constraint state":
    let c = newSetIntersectCardConstraint[int](@[0, 1], @[2, 3], maxCard = 0, minCard = 0)
    var assignment = @[1, 1, 1, 1]
    c.initialize(assignment)
    check c.cost == 2  # dot = 2, maxCard = 0 → cost 2

    let c2 = c.deepCopy()
    var zeroAssignment = @[0, 0, 0, 0]
    c2.initialize(zeroAssignment)
    check c2.cost == 0

    # Original untouched by c2's reinitialization.
    check c.cost == 2
    check c.dotProduct == 2
