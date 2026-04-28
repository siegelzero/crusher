## Unit tests for MultiMachineNoOverlapConstraint with sequence-dependent
## setup-time matrix.
##
## Penalty for a machine =
##   Σ over consecutive (i, j) on the machine in start-time order of
##     max(0, end[i] + setup[i][j] - start[j])
##
## When the setup matrix is empty, the constraint reverts to plain no-overlap.

import unittest
import constraints/multiMachineNoOverlap

suite "MultiMachineNoOverlap with setup matrix":

  test "no setup matrix preserves plain no-overlap semantics":
    # 3 tasks all on machine 0, durations [3, 2, 4], starts [0, 5, 7].
    # Intervals: [0,3), [5,7), [7,11) — no overlap → cost = 0.
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1, 2],
      machinePositions = @[-1, -1, -1],
      fixedMachines = @[0, 0, 0],
      durations = @[3, 2, 4],
      numMachineValues = 1,
      maxTime = 20)
    c.initialize(@[0, 5, 7])
    check c.cost == 0

    # Move task 1 to start at 2 → overlap with task 0 ([0,3) vs [2,4)).
    c.updatePosition(1, 2)
    check c.cost > 0

  test "setup matrix introduces violations for tight starts":
    # 2 tasks on machine 0, durations [3, 2].
    # Setup[0][1] = 5, setup[1][0] = 0. Starts [0, 4].
    # End(0) = 3, required start(1) >= 3 + 5 = 8. start(1) = 4 → violation 4.
    let setup = @[@[0, 5], @[0, 0]]
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1],
      machinePositions = @[-1, -1],
      fixedMachines = @[0, 0],
      durations = @[3, 2],
      numMachineValues = 1,
      maxTime = 30,
      setupMatrix = setup)
    c.initialize(@[0, 4])
    check c.cost == 4

    # Push task 1 to start=8 → exactly the required time, cost = 0.
    c.updatePosition(1, 8)
    check c.cost == 0

  test "setup penalty for ordering reversal":
    # Same tasks, but now task 1 starts BEFORE task 0.
    # Order becomes [1, 0]. End(1) = start(1)+2 = 2. Setup[1][0] = 0.
    # Required start(0) >= 2 → start(0) = 5 satisfies. Cost = 0.
    let setup = @[@[0, 5], @[0, 0]]
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1],
      machinePositions = @[-1, -1],
      fixedMachines = @[0, 0],
      durations = @[3, 2],
      numMachineValues = 1,
      maxTime = 30,
      setupMatrix = setup)
    c.initialize(@[5, 0])
    check c.cost == 0

  test "moveDelta agrees with full recomputation under setup":
    # Asymmetric setup. Verify moveDelta == difference of recomputed costs.
    let setup = @[
      @[0, 4, 7],
      @[3, 0, 2],
      @[6, 1, 0]]
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1, 2],
      machinePositions = @[-1, -1, -1],
      fixedMachines = @[0, 0, 0],
      durations = @[2, 3, 1],
      numMachineValues = 1,
      maxTime = 50,
      setupMatrix = setup)
    c.initialize(@[0, 5, 12])
    let baseCost = c.cost

    # Try shifting task 1's start to a few values; predicted delta must match
    # the actual delta seen after updatePosition (which recomputes).
    let testValues = @[3, 6, 9, 11, 15]
    for v in testValues:
      let predicted = c.moveDelta(1, c.currentStarts[1], v)
      let oldStart = c.currentStarts[1]
      c.updatePosition(1, v)
      let actualDelta = c.cost - baseCost
      check predicted == actualDelta
      # Restore for next iteration
      c.updatePosition(1, oldStart)
      check c.cost == baseCost

  test "machine reassignment with setup":
    # 4 tasks; machines variable. Reassigning a task between machines must
    # update both old and new machine penalties correctly.
    let setup = @[
      @[0, 3, 5, 2],
      @[3, 0, 4, 1],
      @[5, 4, 0, 6],
      @[2, 1, 6, 0]]
    # Tasks 0,1 start on machine 0, task 2 on machine 1, task 3 on machine 1.
    # Initial layout: m0 = [0, 1], m1 = [2, 3].
    # startPositions = 0..3 (each task's start var)
    # machinePositions = 4..7 (each task's machine var)
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1, 2, 3],
      machinePositions = @[4, 5, 6, 7],
      fixedMachines = @[-1, -1, -1, -1],
      durations = @[2, 2, 2, 2],
      numMachineValues = 2,
      maxTime = 50,
      setupMatrix = setup)
    # Position layout: 0..3 = task starts, 4..7 = task machine assignments.
    var asg = newSeq[int](8)
    asg[0] = 0; asg[1] = 6   # starts for tasks 0, 1
    asg[2] = 0; asg[3] = 6   # starts for tasks 2, 3
    asg[4] = 0; asg[5] = 0   # task 0, 1 → machine 0
    asg[6] = 1; asg[7] = 1   # task 2, 3 → machine 1
    c.initialize(asg)
    let initialCost = c.cost
    # m0: tasks 0 and 1, start [0, 6], dur 2 each. End(0)=2, setup[0][1]=3,
    #     required start(1) >= 5. start(1)=6 → ok, cost 0.
    # m1: tasks 2 and 3, start [0, 6], dur 2 each. End(2)=2, setup[2][3]=6,
    #     required start(3) >= 8. start(3)=6 → violation 2.
    check initialCost == 2

    # Reassign task 3 to machine 0.
    let predicted = c.moveDelta(7, 1, 0)
    c.updatePosition(7, 0)
    check c.cost - initialCost == predicted
    # m0 now has [0,1,3]: starts 0,6,6, dur 2 each. Sorted by start (tie-break
    # by index): order is 0, 1, 3.
    # End(0)=2, setup[0][1]=3, req start(1)>=5; start(1)=6 → ok.
    # End(1)=8, setup[1][3]=1, req start(3)>=9; start(3)=6 → violation 3.
    # m1 now has [2]: cost 0.
    # New total: 3.
    check c.cost == 3

  test "deepCopy carries setup matrix and isolates state":
    # Parallel-worker safety: deepCopy must propagate the setupMatrix into the
    # clone, and mutations to the clone must not affect the original.
    let setup = @[@[0, 7], @[3, 0]]
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1],
      machinePositions = @[-1, -1],
      fixedMachines = @[0, 0],
      durations = @[2, 1],
      numMachineValues = 1,
      maxTime = 30,
      setupMatrix = setup)
    c.initialize(@[0, 5])
    # End(0)=2, setup[0][1]=7, req start(1) >= 9. start(1)=5 → violation 4.
    check c.cost == 4

    let clone = c.deepCopy()
    # Setup matrix carried across.
    check clone.setupMatrix.len == 2
    check clone.setupMatrix[0] == @[0, 7]
    check clone.setupMatrix[1] == @[3, 0]
    # The clone needs initialize() to populate per-task state.
    clone.initialize(@[0, 9])  # different starts: end(0)=2, setup=7, req=9. ok.
    check clone.cost == 0
    # Original is unaffected by clone mutation.
    check c.cost == 4

  test "batchMovePenalty under setup falls back consistently":
    # batchMovePenalty currently falls back to per-value moveDelta when setup
    # is enabled. Verify the result matches per-value moveDelta exactly.
    let setup = @[@[0, 4, 6], @[2, 0, 3], @[5, 1, 0]]
    let c = newMultiMachineNoOverlapConstraint[int](
      startPositions = @[0, 1, 2],
      machinePositions = @[-1, -1, -1],
      fixedMachines = @[0, 0, 0],
      durations = @[2, 2, 2],
      numMachineValues = 1,
      maxTime = 40,
      setupMatrix = setup)
    c.initialize(@[0, 5, 12])
    let domain = @[0, 3, 7, 10, 14, 20]
    let batched = c.batchMovePenalty(1, c.currentStarts[1], domain)
    check batched.len == domain.len
    for i, v in domain:
      let direct = c.moveDelta(1, c.currentStarts[1], v)
      check batched[i] == direct
