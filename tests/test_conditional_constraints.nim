import std/[unittest]
import constraints/[conditionalCumulative, conditionalNoOverlap, conditionalDayCapacity]

suite "ConditionalCumulative":
  test "penalty and moveDelta consistency":
    # Two tasks: task 0 at position 0 (start), condition at position 2 (room==1)
    #            task 1 at position 1 (start), condition at position 3 (room==1)
    # Duration=2, height=1, limit=1, maxTime=5
    let tasks = @[
      ConditionalTask(startPosition: 0, fixedStart: -1, duration: 2, height: 1,
                      conditions: @[TaskCondition(position: 2, value: 1)]),
      ConditionalTask(startPosition: 1, fixedStart: -1, duration: 2, height: 1,
                      conditions: @[TaskCondition(position: 3, value: 1)])
    ]
    let c = newConditionalCumulativeConstraint[int](@[], tasks, 1, 5)

    # Assignment: starts=[0, 0], conditions=[1, 1] → both active, overlap at t=0,1
    let assignment = @[0, 0, 1, 1]
    c.initialize(assignment)
    check c.cost == 2  # excess of 1 at t=0 and t=1

    # moveDelta for shifting task 0 start from 0 to 2 → no overlap
    let delta = c.moveDelta(0, 0, 2)
    c.updatePosition(0, 2)
    check c.cost == 0
    check delta == c.cost - 2  # was 2, now 0

  test "moveDelta for condition change":
    let tasks = @[
      ConditionalTask(startPosition: 0, fixedStart: -1, duration: 3, height: 2,
                      conditions: @[TaskCondition(position: 1, value: 1)])
    ]
    let c = newConditionalCumulativeConstraint[int](@[], tasks, 1, 5)

    # Active: start=0, cond=1, height=2, limit=1 → excess 1 at t=0,1,2 → cost=3
    c.initialize(@[0, 1])
    check c.cost == 3

    # Deactivate: cond 1→0
    let delta = c.moveDelta(1, 1, 0)
    c.updatePosition(1, 0)
    check c.cost == 0
    check delta == -3

  test "fixed tasks contribute to profile":
    let fixed = @[FixedTask(start: 0, duration: 2, height: 1)]
    let tasks = @[
      ConditionalTask(startPosition: 0, fixedStart: -1, duration: 2, height: 1,
                      conditions: @[TaskCondition(position: 1, value: 1)])
    ]
    let c = newConditionalCumulativeConstraint[int](fixed, tasks, 1, 5)

    # Fixed task at t=0,1 + conditional task at t=0,1 → excess 1 at t=0,1
    c.initialize(@[0, 1])
    check c.cost == 2

    # Shift conditional task to t=3 → no overlap with fixed
    let delta = c.moveDelta(0, 0, 3)
    c.updatePosition(0, 3)
    check c.cost == 0
    check delta == -2

  test "moveDelta matches full recompute for all domain values":
    let tasks = @[
      ConditionalTask(startPosition: 0, fixedStart: -1, duration: 2, height: 1,
                      conditions: @[TaskCondition(position: 2, value: 1)]),
      ConditionalTask(startPosition: 1, fixedStart: -1, duration: 2, height: 1,
                      conditions: @[TaskCondition(position: 3, value: 1)])
    ]
    let c = newConditionalCumulativeConstraint[int](@[], tasks, 1, 5)
    let cVerify = newConditionalCumulativeConstraint[int](@[], tasks, 1, 5)

    let assignment = @[1, 2, 1, 1]
    c.initialize(assignment)

    # Test moveDelta for every possible start value for task 0
    for newVal in 0..4:
      let delta = c.moveDelta(0, assignment[0], newVal)
      var newAssignment = assignment
      newAssignment[0] = newVal
      cVerify.initialize(newAssignment)
      check delta == cVerify.cost - c.cost


suite "ConditionalNoOverlapPair":
  test "basic overlap detection":
    # Two patients: startA=pos0, startB=pos1, durA=3, durB=2
    # resourceA=pos2, resourceB=pos3, condA=pos4, condB=pos5
    let c = newConditionalNoOverlapPairConstraint[int](
      startAPos=0, startBPos=1, durationA=3, durationB=2,
      resourceAPos=2, resourceBPos=3, resourceAFixed= -1, resourceBFixed= -1,
      condAPos=4, condBPos=5)

    # Both active, same room, overlapping: start 0..3 and 1..3
    c.initialize(@[0, 1, 5, 5, 1, 1])
    check c.cost == 1

    # Different rooms → no violation
    c.initialize(@[0, 1, 5, 6, 1, 1])
    check c.cost == 0

    # Same room, non-overlapping: [0,3) and [3,5)
    c.initialize(@[0, 3, 5, 5, 1, 1])
    check c.cost == 0

  test "condition deactivation":
    let c = newConditionalNoOverlapPairConstraint[int](
      startAPos=0, startBPos=1, durationA=3, durationB=2,
      resourceAPos=2, resourceBPos=3, resourceAFixed= -1, resourceBFixed= -1,
      condAPos=4, condBPos=5)

    # Overlapping but condA=0 → no violation
    c.initialize(@[0, 1, 5, 5, 0, 1])
    check c.cost == 0

  test "moveDelta matches full recompute":
    let c = newConditionalNoOverlapPairConstraint[int](
      startAPos=0, startBPos=1, durationA=3, durationB=2,
      resourceAPos=2, resourceBPos=3, resourceAFixed= -1, resourceBFixed= -1,
      condAPos=4, condBPos=5)
    let cVerify = newConditionalNoOverlapPairConstraint[int](
      startAPos=0, startBPos=1, durationA=3, durationB=2,
      resourceAPos=2, resourceBPos=3, resourceAFixed= -1, resourceBFixed= -1,
      condAPos=4, condBPos=5)

    let assignment = @[0, 1, 5, 5, 1, 1]
    c.initialize(assignment)

    # Test moveDelta for start position changes
    for newVal in 0..5:
      let delta = c.moveDelta(0, assignment[0], newVal)
      var newAssignment = assignment
      newAssignment[0] = newVal
      cVerify.initialize(newAssignment)
      check delta == cVerify.cost - c.cost

    # Test moveDelta for condition changes
    for newVal in 0..1:
      let delta = c.moveDelta(4, assignment[4], newVal)
      var newAssignment = assignment
      newAssignment[4] = newVal
      cVerify.initialize(newAssignment)
      check delta == cVerify.cost - c.cost

    # Test moveDelta for resource changes
    for newVal in 4..6:
      let delta = c.moveDelta(2, assignment[2], newVal)
      var newAssignment = assignment
      newAssignment[2] = newVal
      cVerify.initialize(newAssignment)
      check delta == cVerify.cost - c.cost

  test "fixed resource":
    let c = newConditionalNoOverlapPairConstraint[int](
      startAPos=0, startBPos=1, durationA=3, durationB=2,
      resourceAPos=2, resourceBPos= -1, resourceAFixed= -1, resourceBFixed=5,
      condAPos= -1, condBPos= -1)

    # resourceA=5 (variable), resourceBFixed=5 → same room, overlapping
    c.initialize(@[0, 1, 5])
    check c.cost == 1

    # resourceA=6 → different
    c.initialize(@[0, 1, 6])
    check c.cost == 0


suite "ConditionalDayCapacity":
  test "basic capacity":
    # 2 tasks, capacities [10, 10] for days 0,1
    let tasks = @[
      DayCapacityTask(weight: 7, admissionPos: 0, selectionPos: 2, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0),
      DayCapacityTask(weight: 5, admissionPos: 1, selectionPos: 3, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0)
    ]
    let c = newConditionalDayCapacityConstraint[int](tasks, @[10, 10], 1)

    # Both on day 0, both active: load=12 > 10, excess=2
    c.initialize(@[0, 0, 1, 1])
    check c.cost == 2

    # Move task 1 to day 1: load[0]=7, load[1]=5, no excess
    let delta = c.moveDelta(1, 0, 1)
    c.updatePosition(1, 1)
    check c.cost == 0
    check delta == -2

  test "selection deactivation":
    let tasks = @[
      DayCapacityTask(weight: 7, admissionPos: 0, selectionPos: 1, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0)
    ]
    let c = newConditionalDayCapacityConstraint[int](tasks, @[5], 0)

    # Active: load=7 > 5, excess=2
    c.initialize(@[0, 1])
    check c.cost == 2

    # Deactivate: sel 1→0
    let delta = c.moveDelta(1, 1, 0)
    c.updatePosition(1, 0)
    check c.cost == 0
    check delta == -2

  test "moveDelta matches full recompute":
    let tasks = @[
      DayCapacityTask(weight: 5, admissionPos: 0, selectionPos: 2, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0),
      DayCapacityTask(weight: 3, admissionPos: 1, selectionPos: 3, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0)
    ]
    let c = newConditionalDayCapacityConstraint[int](tasks, @[6, 6, 6], 2)
    let cVerify = newConditionalDayCapacityConstraint[int](tasks, @[6, 6, 6], 2)

    let assignment = @[0, 1, 1, 1]
    c.initialize(assignment)

    # Test admission position changes
    for pos in 0..1:
      for newVal in 0..2:
        let delta = c.moveDelta(pos, assignment[pos], newVal)
        var newAssignment = assignment
        newAssignment[pos] = newVal
        cVerify.initialize(newAssignment)
        check delta == cVerify.cost - c.cost

    # Test selection changes
    for pos in 2..3:
      for newVal in 0..1:
        let delta = c.moveDelta(pos, assignment[pos], newVal)
        var newAssignment = assignment
        newAssignment[pos] = newVal
        cVerify.initialize(newAssignment)
        check delta == cVerify.cost - c.cost

  test "batchMovePenalty matches individual moveDelta":
    let tasks = @[
      DayCapacityTask(weight: 5, admissionPos: 0, selectionPos: 2, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0),
      DayCapacityTask(weight: 3, admissionPos: 1, selectionPos: 3, selectionVal: 1,
                      extraCondPos: -1, extraCondVal: 0)
    ]
    let c = newConditionalDayCapacityConstraint[int](tasks, @[6, 6, 6], 2)

    let assignment = @[0, 0, 1, 1]
    c.initialize(assignment)

    let domain = @[0, 1, 2]

    # Test batch for admission position
    let batch0 = c.batchMovePenalty(0, 0, domain)
    for i, v in domain:
      check batch0[i] == c.moveDelta(0, 0, v)

    # Test batch for selection position
    let selDomain = @[0, 1]
    let batch2 = c.batchMovePenalty(2, 1, selDomain)
    for i, v in selDomain:
      check batch2[i] == c.moveDelta(2, 1, v)

  test "extra condition":
    let tasks = @[
      DayCapacityTask(weight: 10, admissionPos: 0, selectionPos: 1, selectionVal: 1,
                      extraCondPos: 2, extraCondVal: 3)
    ]
    let c = newConditionalDayCapacityConstraint[int](tasks, @[5], 0)

    # All conditions met: load=10 > 5
    c.initialize(@[0, 1, 3])
    check c.cost == 5

    # Extra condition not met: inactive
    c.initialize(@[0, 1, 2])
    check c.cost == 0
