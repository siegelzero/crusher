## Tests for inverse group (involution) compound moves.
##
## An inverse group enforces the involution invariant: if position[i] = j,
## then position[j] = i (self-inverse permutation). When the solver assigns
## a new value at one position, computeInverseForcedChanges produces forced
## changes to maintain this invariant.
##
## These tests verify:
## 1. The involution invariant holds in solutions
## 2. The specific scenario where inverse groups interact with channel variables
##    (the context for a bug where computeChannelDepDelta produced duplicate
##    forced positions, corrupting assignment restore)

import std/[packedsets, sequtils, sets, unittest]
import crusher

proc isValidInvolution(assignment: seq[int], positions: seq[int], offset: int): bool =
    ## Check that the assignment at the given positions forms a valid involution.
    for i in 0..<positions.len:
        let v = assignment[positions[i]]
        let j = v + offset  # local index of partner
        if j < 0 or j >= positions.len:
            return false
        let partnerVal = assignment[positions[j]]
        let expected = i - offset
        if partnerVal != expected:
            return false
    return true

suite "Inverse Group Tests":
    test "Small involution with allDifferent":
        var sys = initConstraintSystem[int]()
        let offset0 = sys.baseArray.len
        var x = sys.newConstrainedSequence(4)
        x.setDomain(toSeq(0..3))

        sys.addConstraint(allDifferent(x))
        sys.baseArray.addInverseGroup(toSeq(offset0..<offset0+4), 0)

        sys.resolve(tabuThreshold = 5000)

        check isValidInvolution(sys.assignment, toSeq(offset0..<offset0+4), 0)

    test "6-element involution with no fixed points":
        var sys = initConstraintSystem[int]()
        let offset0 = sys.baseArray.len
        var x = sys.newConstrainedSequence(6)
        x.setDomain(toSeq(1..6))

        sys.addConstraint(allDifferent(x))
        for i in 0..<6:
            sys.addConstraint(x[i] != i + 1)

        sys.baseArray.addInverseGroup(toSeq(offset0..<offset0+6), -1)

        sys.resolve(tabuThreshold = 5000)

        check isValidInvolution(sys.assignment, toSeq(offset0..<offset0+6), -1)
        let sol = x.assignment
        check sol.toHashSet.len == 6
        for i, v in sol:
            check v != i + 1

    test "8-element involution no fixed points":
        ## Mimics a single TTPV round with 8 teams.
        var sys = initConstraintSystem[int]()
        let offset0 = sys.baseArray.len
        var x = sys.newConstrainedSequence(8)
        x.setDomain(toSeq(1..8))

        sys.addConstraint(allDifferent(x))
        for i in 0..<8:
            sys.addConstraint(x[i] != i + 1)

        sys.baseArray.addInverseGroup(toSeq(offset0..<offset0+8), -1)

        sys.resolve(tabuThreshold = 10000)

        check isValidInvolution(sys.assignment, toSeq(offset0..<offset0+8), -1)
        let sol = x.assignment
        for i, v in sol:
            check v != i + 1

    test "Multiple involution groups":
        ## Two rounds, each an involution, no repeated opponents.
        var sys = initConstraintSystem[int]()
        let offset1 = sys.baseArray.len
        var round1 = sys.newConstrainedSequence(4)
        round1.setDomain(toSeq(1..4))
        let offset2 = sys.baseArray.len
        var round2 = sys.newConstrainedSequence(4)
        round2.setDomain(toSeq(1..4))

        sys.addConstraint(allDifferent(round1))
        sys.addConstraint(allDifferent(round2))
        for i in 0..<4:
            sys.addConstraint(round1[i] != i + 1)
            sys.addConstraint(round2[i] != i + 1)
            sys.addConstraint(round1[i] != round2[i])

        sys.baseArray.addInverseGroup(toSeq(offset1..<offset1+4), -1)
        sys.baseArray.addInverseGroup(toSeq(offset2..<offset2+4), -1)

        sys.resolve(tabuThreshold = 10000)

        check isValidInvolution(sys.assignment, toSeq(offset1..<offset1+4), -1)
        check isValidInvolution(sys.assignment, toSeq(offset2..<offset2+4), -1)
        let sol1 = round1.assignment
        let sol2 = round2.assignment
        for i in 0..<4:
            check sol1[i] != sol2[i]

    test "Involution with channel variables":
        ## Tests the interaction between inverse groups and channel variables.
        ## This was the context for the original bug: computeChannelDepDelta
        ## temporarily modifies assignment for simulation, and duplicate forced
        ## changes from computeInverseForcedChanges caused restore corruption.
        ##
        ## Setup: 4 opponent positions forming an involution, plus channel
        ## variables derived from opponent values (simulating venue lookups),
        ## plus constraints on channels to create channel-dep constraints.
        var sys = initConstraintSystem[int]()
        let oppOffset = sys.baseArray.len
        var opponents = sys.newConstrainedSequence(4)
        opponents.setDomain(toSeq(1..4))

        sys.addConstraint(allDifferent(opponents))
        for i in 0..<4:
            sys.addConstraint(opponents[i] != i + 1)

        # Channel variables: venue[i] = lookup[opponents[i] - 1]
        # This creates channel bindings so venue values are computed, not searched.
        let lookup = @[10, 20, 30, 40]
        var venueOffsets: seq[int]
        for i in 0..<4:
            let venueOffset = sys.baseArray.len
            venueOffsets.add(venueOffset)
            var venue = sys.newConstrainedVariable()
            venue.setDomain(@[10, 20, 30, 40])
            let indexExpr = opponents[i] - 1
            var arrayElems: seq[ArrayElement[int]]
            for v in lookup:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))
            sys.baseArray.addChannelBinding(venueOffset, indexExpr, arrayElems)

        # Add a constraint on channel variables to create channel-dep constraints
        # (constraints where all positions are channels — invisible to normal penalty maps).
        # This forces computeChannelDepDelta to simulate moves + channel propagation,
        # which is where the duplicate forced-change bug manifested.
        sys.addConstraint(allDifferent(@[
            sys.baseArray[venueOffsets[0]],
            sys.baseArray[venueOffsets[1]],
            sys.baseArray[venueOffsets[2]],
            sys.baseArray[venueOffsets[3]],
        ]))

        sys.baseArray.addInverseGroup(toSeq(oppOffset..<oppOffset+4), -1)

        # Run multiple trials to exercise various move sequences and increase
        # chance of hitting the scenario where newJ is a fixed point.
        for trial in 0..<10:
            sys.resolve(tabuThreshold = 5000)

            check isValidInvolution(sys.assignment, toSeq(oppOffset..<oppOffset+4), -1)
            let sol = opponents.assignment
            for i, v in sol:
                check v != i + 1
