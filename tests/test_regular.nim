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
