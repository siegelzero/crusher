import std/[sequtils, unittest]
import crusher

suite "Regular":

    test "regular - global contiguity (Fig 3.11)":
        # DFA: ensures all 2s (on) appear contiguously
        # States: 1=before-on, 2=in-on, 3=after-on
        # Input: 1=off, 2=on
        # Transition: state x input -> next state (0=fail)
        #   State 1: input 1->1, input 2->2
        #   State 2: input 1->3, input 2->2
        #   State 3: input 1->3, input 2->0 (fail)
        let transition = @[
            @[1, 2],  # state 1
            @[3, 2],  # state 2
            @[3, 0],  # state 3
        ]

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(@[1, 2])

        sys.addConstraint(regular[int](toSeq(0..5), 3, 1, 2, transition, 1, @[1, 2, 3]))
        # Require at least one "on" (value 2)
        sys.addConstraint(atLeast[int](toSeq(0..5), 2, 1))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()

        # Verify contiguity: all 2s appear as a single contiguous block
        var firstOn = -1
        var lastOn = -1
        for i in 0..<6:
            if a[i] == 2:
                if firstOn == -1:
                    firstOn = i
                lastOn = i

        check firstOn >= 0  # at least one on
        # All positions between firstOn and lastOn should be 2
        for i in firstOn..lastOn:
            check a[i] == 2

    test "regular - global contiguity allows all-off":
        # The global_contiguity DFA accepts sequences with zero 1s (all off).
        # Pattern "0*1*0*" includes the empty-1s case "0*" = all zeros.
        let transition = @[
            @[1, 2],  # state 1
            @[3, 2],  # state 2
            @[3, 0],  # state 3
        ]

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(@[1, 2])

        sys.addConstraint(regular[int](toSeq(0..5), 3, 1, 2, transition, 1, @[1, 2, 3]))
        # Force all values to be "off" (value 1)
        sys.addConstraint(atMost[int](toSeq(0..5), 2, 0))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        for i in 0..<6:
            check a[i] == 1

    test "regular - global contiguity longer sequence":
        # Same DFA on a 12-element sequence, requiring exactly 4 "on" values.
        # The DFA guarantees they form a contiguous block.
        let transition = @[
            @[1, 2],  # state 1
            @[3, 2],  # state 2
            @[3, 0],  # state 3
        ]

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(12)
        x.setDomain(@[1, 2])

        let positions = toSeq(0..11)
        sys.addConstraint(regular[int](positions, 3, 1, 2, transition, 1, @[1, 2, 3]))
        # Exactly 4 "on" values
        sys.addConstraint(atLeast[int](positions, 2, 4))
        sys.addConstraint(atMost[int](positions, 2, 4))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()

        var firstOn = -1
        var lastOn = -1
        var onCount = 0
        for i in 0..<12:
            if a[i] == 2:
                if firstOn == -1:
                    firstOn = i
                lastOn = i
                onCount += 1

        check onCount == 4
        check (lastOn - firstOn + 1) == 4  # contiguous block of exactly 4
        for i in firstOn..lastOn:
            check a[i] == 2

    test "regular - nurse schedule DFA single nurse (Fig 3.12)":
        # DFA from Section 3.9.2 enforces:
        #   - at most 3 consecutive working days (day off every 4 days)
        #   - at most 2 consecutive night shifts
        # Inputs: 1=day, 2=night, 3=off
        # 6 states, all accepting
        let transition = @[
            @[2, 3, 1],  # state 1: fresh (just had off or start)
            @[4, 4, 1],  # state 2: 1 shift worked, last was day
            @[4, 5, 1],  # state 3: 1 shift worked, last was night
            @[6, 6, 1],  # state 4: 2 shifts worked, <=1 consecutive night
            @[6, 0, 1],  # state 5: 2 consecutive nights (3rd night fails)
            @[0, 0, 1],  # state 6: 3 shifts worked (4th work day fails)
        ]

        var sys = initConstraintSystem[int]()
        var schedule = sys.newConstrainedSequence(14)
        schedule.setDomain(@[1, 2, 3])

        let positions = toSeq(0..13)
        sys.addConstraint(regular[int](positions, 6, 1, 3, transition, 1, toSeq(1..6)))
        # Require a mix: at least 3 day shifts, 2 night shifts, 2 off days
        sys.addConstraint(atLeast[int](positions, 1, 3))
        sys.addConstraint(atLeast[int](positions, 2, 2))
        sys.addConstraint(atLeast[int](positions, 3, 2))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = schedule.assignment()

        # Verify: no 4 consecutive working days
        for start in 0..10:
            var allWork = true
            for j in start..start+3:
                if a[j] == 3:
                    allWork = false
                    break
            check not allWork

        # Verify: no 3 consecutive night shifts
        for start in 0..11:
            check not (a[start] == 2 and a[start+1] == 2 and a[start+2] == 2)

        # Verify required minimums
        var dayCount, nightCount, offCount: int
        for v in a:
            if v == 1: dayCount += 1
            elif v == 2: nightCount += 1
            else: offCount += 1
        check dayCount >= 3
        check nightCount >= 2
        check offCount >= 2

    test "regular - nurse rostering multi-nurse (Fig 3.13)":
        # Full nurse rostering from Section 3.9.2 (smaller instance).
        # Each nurse's 7-day schedule must be accepted by the DFA.
        # Per-day staffing minimums are enforced with atLeast.
        const numNurses = 5
        const numDays = 7
        const minDayShift = 2
        const minNightShift = 1
        const dayShift = 1
        const nightShift = 2
        const offShift = 3

        let transition = @[
            @[2, 3, 1],  # state 1
            @[4, 4, 1],  # state 2
            @[4, 5, 1],  # state 3
            @[6, 6, 1],  # state 4
            @[6, 0, 1],  # state 5
            @[0, 0, 1],  # state 6
        ]

        var sys = initConstraintSystem[int]()
        var nurses: array[numNurses, ConstrainedSequence[int]]
        for i in 0..<numNurses:
            nurses[i] = sys.newConstrainedSequence(numDays)
            nurses[i].setDomain(@[dayShift, nightShift, offShift])

        # DFA constraint per nurse (using expression-based overload)
        for i in 0..<numNurses:
            var nurseExprs: seq[AlgebraicExpression[int]]
            for d in 0..<numDays:
                nurseExprs.add(nurses[i][d])
            sys.addConstraint(regular[int](nurseExprs, 6, 1, 3, transition, 1, toSeq(1..6)))

        # Per-day minimum staffing (collect expressions across nurses)
        for d in 0..<numDays:
            var dayExprs: seq[AlgebraicExpression[int]]
            for i in 0..<numNurses:
                dayExprs.add(nurses[i][d])
            sys.addConstraint(atLeast[int](dayExprs, dayShift, minDayShift))
            sys.addConstraint(atLeast[int](dayExprs, nightShift, minNightShift))

        sys.resolve(parallel=true, tabuThreshold=20000)

        # Verify each nurse's schedule
        for i in 0..<numNurses:
            let a = nurses[i].assignment()

            # No 4 consecutive working days
            for start in 0..(numDays - 4):
                var allWork = true
                for j in start..start+3:
                    if a[j] == offShift:
                        allWork = false
                        break
                check not allWork

            # No 3 consecutive night shifts
            for start in 0..(numDays - 3):
                check not (a[start] == nightShift and
                           a[start+1] == nightShift and
                           a[start+2] == nightShift)

        # Verify minimum staffing per day
        for d in 0..<numDays:
            var dayCount, nightCount: int
            for i in 0..<numNurses:
                let a = nurses[i].assignment()
                if a[d] == dayShift: dayCount += 1
                if a[d] == nightShift: nightCount += 1
            check dayCount >= minDayShift
            check nightCount >= minNightShift

    test "regular - nurse DFA moveDelta consistency":
        # Test incremental evaluation of the 6-state nurse DFA.
        let transition = @[
            @[2, 3, 1],
            @[4, 4, 1],
            @[4, 5, 1],
            @[6, 6, 1],
            @[6, 0, 1],
            @[0, 0, 1],
        ]

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(7)
        x.setDomain(@[1, 2, 3])
        sys.addConstraint(regular[int](toSeq(0..6), 6, 1, 3, transition, 1, toSeq(1..6)))

        # Valid schedule: day, day, night, off, day, night, off
        # Trace: S1-d->S2-d->S4-n->S6-o->S1-d->S2-n->S4-o->S1
        let assignment = @[1, 1, 2, 3, 1, 2, 3]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]
        let costBefore = constraint.penalty()
        check costBefore == 0  # valid schedule

        # Change position 3 from off(3) to night(2): [1,1,2,2,1,2,3]
        # Trace: S1-d->S2-d->S4-n->S6-n->0 (FAIL at position 3)
        let delta = constraint.moveDelta(3, 3, 2)
        constraint.updatePosition(3, 2)
        let costAfter = constraint.penalty()
        check costAfter > 0  # now invalid (4th consecutive work day)
        check costAfter == costBefore + delta

    test "regular - moveDelta consistency":
        let transition = @[
            @[1, 2],
            @[3, 2],
            @[3, 0],
        ]

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(6)
        x.setDomain(@[1, 2])
        sys.addConstraint(regular[int](toSeq(0..5), 3, 1, 2, transition, 1, @[1, 2, 3]))

        let assignment = @[1, 2, 2, 1, 1, 1]
        sys.initialize(assignment)

        let constraint = sys.baseArray.constraints[0]
        let costBefore = constraint.penalty()
        check costBefore == 0  # valid contiguous pattern

        # Try a move that breaks contiguity
        let delta = constraint.moveDelta(2, 2, 1)
        constraint.updatePosition(2, 1)
        let costAfter = constraint.penalty()
        check costAfter == costBefore + delta
