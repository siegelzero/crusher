## Tests for argmax channel bindings.
##
## An argmax channel tracks the index of the first maximum among a set of
## input expressions: channelPos = valueOffset + argmax(inputExprs).
## These tests verify initialization, search propagation, interaction with
## other channel types, and edge cases.

import std/[sequtils, unittest]
import crusher

suite "Argmax Channel Bindings":
    test "Basic argmax: channel reflects index of maximum signal":
        ## Three signals with known values; argmax channel must equal
        ## the 1-based index of the largest signal.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            # Search vars: s0, s1, s2 (signals)
            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])
            let posS2 = sys.baseArray.len
            var s2 = sys.newConstrainedVariable()
            s2.setDomain(@[1, 2, 3, 4, 5])

            # Argmax channel: tower = 1 + argmax(s0, s1, s2)
            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[1, 2, 3])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1], sys.baseArray[posS2]],
                valueOffset = 1)

            # Force s0=2, s1=5, s2=3 → argmax is index 1 → tower = 2
            sys.addConstraint(sys.baseArray[posS0] == 2)
            sys.addConstraint(sys.baseArray[posS1] == 5)
            sys.addConstraint(sys.baseArray[posS2] == 3)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posS0] == 2
            check sys.assignment[posS1] == 5
            check sys.assignment[posS2] == 3
            check sys.assignment[posTower] == 2  # 1-based index of max

    test "Argmax with 0-based offset":
        ## Verify valueOffset=0 produces 0-based index.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posA = sys.baseArray.len
            var a = sys.newConstrainedVariable()
            a.setDomain(@[1, 2, 3])
            let posB = sys.baseArray.len
            var b = sys.newConstrainedVariable()
            b.setDomain(@[1, 2, 3])

            let posArgmax = sys.baseArray.len
            var argmaxVar = sys.newConstrainedVariable()
            argmaxVar.setDomain(@[0, 1])
            sys.baseArray.addArgmaxChannelBinding(posArgmax,
                @[sys.baseArray[posA], sys.baseArray[posB]],
                valueOffset = 0)

            # a=1, b=3 → argmax index 1 → channel = 0 + 1 = 1
            sys.addConstraint(sys.baseArray[posA] == 1)
            sys.addConstraint(sys.baseArray[posB] == 3)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posArgmax] == 1

    test "Argmax first-max-wins tie-breaking":
        ## When multiple signals tie for the maximum, the channel should
        ## report the first (lowest index) one.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])
            let posS2 = sys.baseArray.len
            var s2 = sys.newConstrainedVariable()
            s2.setDomain(@[1, 2, 3, 4, 5])

            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[1, 2, 3])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1], sys.baseArray[posS2]],
                valueOffset = 1)

            # All signals = 4 → tie → first max at index 0 → tower = 1
            sys.addConstraint(sys.baseArray[posS0] == 4)
            sys.addConstraint(sys.baseArray[posS1] == 4)
            sys.addConstraint(sys.baseArray[posS2] == 4)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posTower] == 1  # first-max-wins

    test "Argmax with different max positions":
        ## Verify that argmax correctly reports the max index for each
        ## distinct configuration (max at index 0, 1, 2).
        for maxIdx in 0..2:
            var sys = initConstraintSystem[int]()

            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])
            let posS2 = sys.baseArray.len
            var s2 = sys.newConstrainedVariable()
            s2.setDomain(@[1, 2, 3, 4, 5])

            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[1, 2, 3])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1], sys.baseArray[posS2]],
                valueOffset = 1)

            # Set the signal at maxIdx to 5, others to 1
            let positions = [posS0, posS1, posS2]
            for i in 0..2:
                if i == maxIdx:
                    sys.addConstraint(sys.baseArray[positions[i]] == 5)
                else:
                    sys.addConstraint(sys.baseArray[positions[i]] == 1)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posTower] == maxIdx + 1

    test "Argmax with expression inputs (linear combinations)":
        ## Input expressions are linear combinations, not bare variables.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posA = sys.baseArray.len
            var a = sys.newConstrainedVariable()
            a.setDomain(@[1, 2, 3])
            let posB = sys.baseArray.len
            var b = sys.newConstrainedVariable()
            b.setDomain(@[1, 2, 3])

            # signals: 2*a, 3*b → if a=2→4, b=3→9 → argmax=1
            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[0, 1])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posA] * 2, sys.baseArray[posB] * 3],
                valueOffset = 0)

            # a=2, b=3 → 2*2=4, 3*3=9 → argmax=1 → tower=1
            sys.addConstraint(sys.baseArray[posA] == 2)
            sys.addConstraint(sys.baseArray[posB] == 3)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posTower] == 1

    test "Argmax chain: argmax feeds into element channel":
        ## Argmax output used as index for an element channel.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            # Signals
            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])

            # Argmax channel: tower = argmax(s0, s1) (0-based)
            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[0, 1])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1]],
                valueOffset = 0)

            # Element channel: selected = elem(tower, [s0, s1])
            # i.e., the value of the strongest signal
            let posSelected = sys.baseArray.len
            var selected = sys.newConstrainedVariable()
            selected.setDomain(@[1, 2, 3, 4, 5])
            sys.baseArray.addChannelBinding(posSelected, sys.baseArray[posTower],
                @[ArrayElement[int](isConstant: false, variablePosition: posS0),
                  ArrayElement[int](isConstant: false, variablePosition: posS1)])

            # Force s0=2, s1=4 → tower=1, selected=s1=4
            sys.addConstraint(sys.baseArray[posS0] == 2)
            sys.addConstraint(sys.baseArray[posS1] == 4)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posTower] == 1
            check sys.assignment[posSelected] == 4

    test "Argmax propagation with allDifferent signals":
        ## Signals are constrained by allDifferent; the solver must find
        ## a valid assignment and the argmax channel must reflect the result.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])
            let posS2 = sys.baseArray.len
            var s2 = sys.newConstrainedVariable()
            s2.setDomain(@[1, 2, 3, 4, 5])

            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[1, 2, 3])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1], sys.baseArray[posS2]],
                valueOffset = 1)

            # allDifferent + force s1=5 → s1 is strictly max → tower=2
            sys.addConstraint(allDifferent(@[sys.baseArray[posS0], sys.baseArray[posS1], sys.baseArray[posS2]]))
            sys.addConstraint(sys.baseArray[posS1] == 5)

            sys.resolve(tabuThreshold = 5000)

            let sol = sys.assignment
            check sol[posS1] == 5
            check sol[posS0] != sol[posS1]
            check sol[posS0] != sol[posS2]
            check sol[posS1] != sol[posS2]
            check sol[posTower] == 2  # s1 is strictly the max

    test "Argmax with minmax chain: both channels agree":
        ## Argmax and minmax channels over the same signals.
        ## Force signals and verify both channels compute correctly.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])

            # Argmax channel: tower = 1 + argmax(s0, s1)
            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[1, 2])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1]],
                valueOffset = 1)

            # MinMax channel: maxVal = max(s0, s1)
            let posMaxVal = sys.baseArray.len
            var maxVal = sys.newConstrainedVariable()
            maxVal.setDomain(@[1, 2, 3, 4, 5])
            sys.baseArray.addMinMaxChannelBinding(posMaxVal, isMin = false,
                @[sys.baseArray[posS0], sys.baseArray[posS1]])

            # s0=4, s1=2 → tower=1 (s0 is max), maxVal=4
            sys.addConstraint(sys.baseArray[posS0] == 4)
            sys.addConstraint(sys.baseArray[posS1] == 2)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posTower] == 1
            check sys.assignment[posMaxVal] == 4

    test "Argmax single input":
        ## Edge case: only one signal → argmax is always index 0.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posS = sys.baseArray.len
            var s = sys.newConstrainedVariable()
            s.setDomain(@[1, 2, 3, 4, 5])

            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[0, 1, 2])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS]],
                valueOffset = 0)

            # Force s=3, tower should always be 0 (only input → index 0)
            sys.addConstraint(sys.baseArray[posS] == 3)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posS] == 3
            check sys.assignment[posTower] == 0  # always index 0

    test "Argmax with optimization: minimize signal sum subject to tower constraint":
        ## Use argmax channel in an optimization context.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            let posS0 = sys.baseArray.len
            var s0 = sys.newConstrainedVariable()
            s0.setDomain(@[1, 2, 3, 4, 5])
            let posS1 = sys.baseArray.len
            var s1 = sys.newConstrainedVariable()
            s1.setDomain(@[1, 2, 3, 4, 5])
            let posS2 = sys.baseArray.len
            var s2 = sys.newConstrainedVariable()
            s2.setDomain(@[1, 2, 3, 4, 5])

            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(@[1, 2, 3])
            sys.baseArray.addArgmaxChannelBinding(posTower,
                @[sys.baseArray[posS0], sys.baseArray[posS1], sys.baseArray[posS2]],
                valueOffset = 1)

            # Require tower == 2 (s1 is strictly the max)
            sys.addConstraint(sys.baseArray[posTower] == 2)

            # Minimize s0 + s1 + s2 subject to tower == 2
            # Optimal: s0=1, s2=1, s1=2 → sum=4
            sys.minimize(sys.baseArray[posS0] + sys.baseArray[posS1] + sys.baseArray[posS2],
                         lowerBound = 3)

            check sys.hasFeasibleSolution
            let sol = sys.assignment
            check sol[posTower] == 2
            check sol[posS1] > sol[posS0]
            check sol[posS1] > sol[posS2]
            # Optimal sum is 4 (s1=2, s0=1, s2=1)
            check sol[posS0] + sol[posS1] + sol[posS2] == 4

    test "Argmax many inputs":
        ## Five signals — verify argmax picks the correct one.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            var positions: seq[int]
            var exprs: seq[AlgebraicExpression[int]]
            for i in 0..<5:
                let p = sys.baseArray.len
                positions.add(p)
                var v = sys.newConstrainedVariable()
                v.setDomain(@[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
                exprs.add(sys.baseArray[p])

            let posTower = sys.baseArray.len
            var tower = sys.newConstrainedVariable()
            tower.setDomain(toSeq(1..5))
            sys.baseArray.addArgmaxChannelBinding(posTower, exprs, valueOffset = 1)

            # Force signal 3 (index 3) to be the unique max
            sys.addConstraint(sys.baseArray[positions[3]] == 10)
            for i in 0..<5:
                if i != 3:
                    sys.addConstraint(sys.baseArray[positions[i]] == 1)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[posTower] == 4  # 1-based index of signal 3
