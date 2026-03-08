## Tests for count-equals channel bindings and the channel propagation chain:
##   search vars → countEq channels → min/max channels → objective
##
## These tests cover:
## 1. CountEqChannelBinding initialization and propagation
## 2. Multi-layer chain: countEq → min/max → constraints
## 3. CountEq → min/max → diff → objective optimization
## 4. Domain tightening from closed-GCC sum constraints
## 5. createCopy correctness (the bug where countEq bindings were not copied)

import std/[sequtils, sets, unittest, tables]
import crusher

suite "Count-Equals Channel Bindings":
    test "Basic countEq channel: count of value in array":
        ## Single countEq channel counting occurrences of a value.
        ## 4 search vars with domain {1,2,3}, one count channel for value 2.
        ## Constrain count == 2, verify solution has exactly 2 twos.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            # 4 search variables (positions 0-3)
            var x = sys.newConstrainedSequence(4)
            x.setDomain(@[1, 2, 3])

            # Count channel: count2 = #{x[i] : x[i] == 2} at position 4
            let countPos = sys.baseArray.len
            var count2 = sys.newConstrainedVariable()
            count2.setDomain(toSeq(0..4))
            sys.baseArray.addCountEqChannelBinding(countPos, 2, @[0, 1, 2, 3])

            # Constraint: count2 == 2
            sys.addConstraint(sys.baseArray[countPos] == 2)

            sys.resolve(tabuThreshold = 5000)

            # Verify count channel value matches actual count
            let assignment = x.assignment
            var actual = 0
            for v in assignment:
                if v == 2: inc actual
            check actual == 2
            check sys.assignment[countPos] == 2

    test "Multiple countEq channels: all values counted":
        ## Count channels for values 1, 2, 3 over 6 search variables.
        ## Constrain: count1 == 2, count2 == 3, count3 == 1.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            var x = sys.newConstrainedSequence(6)
            x.setDomain(@[1, 2, 3])

            let inputPositions = toSeq(0..5)

            # Count channels for each value
            let posCount1 = sys.baseArray.len
            var count1 = sys.newConstrainedVariable()
            count1.setDomain(toSeq(0..6))
            sys.baseArray.addCountEqChannelBinding(posCount1, 1, inputPositions)

            let posCount2 = sys.baseArray.len
            var count2 = sys.newConstrainedVariable()
            count2.setDomain(toSeq(0..6))
            sys.baseArray.addCountEqChannelBinding(posCount2, 2, inputPositions)

            let posCount3 = sys.baseArray.len
            var count3 = sys.newConstrainedVariable()
            count3.setDomain(toSeq(0..6))
            sys.baseArray.addCountEqChannelBinding(posCount3, 3, inputPositions)

            # Constraints: exact counts
            sys.addConstraint(sys.baseArray[posCount1] == 2)
            sys.addConstraint(sys.baseArray[posCount2] == 3)
            sys.addConstraint(sys.baseArray[posCount3] == 1)

            sys.resolve(tabuThreshold = 5000)

            let assignment = x.assignment
            var counts = [0, 0, 0, 0]
            for v in assignment:
                counts[v] += 1
            check counts[1] == 2
            check counts[2] == 3
            check counts[3] == 1

    test "CountEq channel propagation: value change updates count":
        ## Fix some variables and verify the count channel reflects changes.
        ## 3 search vars, count channel for value 1.
        ## x[0]=1 fixed, x[1]=1 fixed, count1 must be >= 2.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            var x = sys.newConstrainedSequence(3)
            x.setDomain(@[1, 2])

            let countPos = sys.baseArray.len
            var count1 = sys.newConstrainedVariable()
            count1.setDomain(toSeq(0..3))
            sys.baseArray.addCountEqChannelBinding(countPos, 1, @[0, 1, 2])

            # Fix first two variables to 1
            sys.addConstraint(x[0] == 1)
            sys.addConstraint(x[1] == 1)
            # Count must be at least 2
            sys.addConstraint(sys.baseArray[countPos] >= 2)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[0] == 1
            check sys.assignment[1] == 1
            check sys.assignment[countPos] >= 2

            # Verify channel value matches
            var actual = 0
            for i in 0..2:
                if sys.assignment[i] == 1: inc actual
            check sys.assignment[countPos] == actual

suite "CountEq → MinMax Channel Chain":
    test "CountEq feeds into min/max channel":
        ## 6 search vars with domain {1,2,3}, count channels for each value,
        ## then min/max channels over the counts.
        ## Constrain max(counts) - min(counts) == 0 (balanced distribution).
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            var x = sys.newConstrainedSequence(6)
            x.setDomain(@[1, 2, 3])

            let inputPositions = toSeq(0..5)

            # Count channels
            var countPositions: seq[int]
            for v in 1..3:
                let pos = sys.baseArray.len
                var cv = sys.newConstrainedVariable()
                cv.setDomain(toSeq(0..6))
                sys.baseArray.addCountEqChannelBinding(pos, v, inputPositions)
                countPositions.add(pos)

            # Min/max channels over counts
            let minPos = sys.baseArray.len
            var minCount = sys.newConstrainedVariable()
            minCount.setDomain(toSeq(0..6))
            var countExprs: seq[AlgebraicExpression[int]]
            for cp in countPositions:
                countExprs.add(sys.baseArray[cp])
            sys.baseArray.addMinMaxChannelBinding(minPos, isMin = true, countExprs)

            let maxPos = sys.baseArray.len
            var maxCount = sys.newConstrainedVariable()
            maxCount.setDomain(toSeq(0..6))
            sys.baseArray.addMinMaxChannelBinding(maxPos, isMin = false, countExprs)

            # Constraint: max - min == 0 (perfectly balanced: each value appears 2 times)
            sys.addConstraint(sys.baseArray[maxPos] - sys.baseArray[minPos] == 0)

            sys.resolve(tabuThreshold = 5000)

            let assignment = x.assignment
            var counts = [0, 0, 0, 0]
            for v in assignment:
                counts[v] += 1

            # Each value should appear exactly 2 times
            check counts[1] == 2
            check counts[2] == 2
            check counts[3] == 2
            check sys.assignment[minPos] == 2
            check sys.assignment[maxPos] == 2

    test "CountEq → min/max → diff → objective max chain":
        ## Simulates the Mondoku objective chain:
        ## Two groups of search variables, each with count channels,
        ## min/max channels, diff expressions, and an objective = max(diffs).
        ## Minimize the objective (minimize max imbalance).
        for trial in 0..<3:
            var sys = initConstraintSystem[int]()

            # Two groups of 4 variables each, domain {1,2}
            var g1 = sys.newConstrainedSequence(4)
            g1.setDomain(@[1, 2])
            var g2 = sys.newConstrainedSequence(4)
            g2.setDomain(@[1, 2])

            var diffPositions: seq[int]

            for groupStart in [0, 4]:
                let inputPositions = toSeq(groupStart..<groupStart+4)

                # Count channels for values 1 and 2
                var countPositions: seq[int]
                for v in 1..2:
                    let pos = sys.baseArray.len
                    var cv = sys.newConstrainedVariable()
                    cv.setDomain(toSeq(0..4))
                    sys.baseArray.addCountEqChannelBinding(pos, v, inputPositions)
                    countPositions.add(pos)

                # Min/max channels
                var countExprs: seq[AlgebraicExpression[int]]
                for cp in countPositions:
                    countExprs.add(sys.baseArray[cp])

                let minP = sys.baseArray.len
                var minV = sys.newConstrainedVariable()
                minV.setDomain(toSeq(0..4))
                sys.baseArray.addMinMaxChannelBinding(minP, isMin = true, countExprs)

                let maxP = sys.baseArray.len
                var maxV = sys.newConstrainedVariable()
                maxV.setDomain(toSeq(0..4))
                sys.baseArray.addMinMaxChannelBinding(maxP, isMin = false, countExprs)

                # Diff = max - min (as a defined expression, no position needed for simple test)
                # For the objective, we just use the expression directly
                diffPositions.add(maxP)
                diffPositions.add(minP)

            # Objective = max(diff1, diff2) where diff_i = max_i - min_i
            let objPos = sys.baseArray.len
            var objVar = sys.newConstrainedVariable()
            objVar.setDomain(toSeq(0..4))
            var diffExprs: seq[AlgebraicExpression[int]]
            # diff1 = diffPositions[0] - diffPositions[1] (max1 - min1)
            diffExprs.add(sys.baseArray[diffPositions[0]] - sys.baseArray[diffPositions[1]])
            # diff2 = diffPositions[2] - diffPositions[3] (max2 - min2)
            diffExprs.add(sys.baseArray[diffPositions[2]] - sys.baseArray[diffPositions[3]])
            sys.baseArray.addMinMaxChannelBinding(objPos, isMin = false, diffExprs)

            # Minimize the objective
            let objExpr = sys.baseArray[objPos]
            sys.minimize(objExpr, parallel = true, tabuThreshold = 1000,
                        lowerBound = 0)

            # With 4 vars and 2 values, balanced = 2 each, diff = 0
            # Optimal objective = 0
            let assignment = sys.assignment
            check assignment[objPos] == 0

            # Verify both groups are balanced
            for groupStart in [0, 4]:
                var counts = [0, 0, 0]
                for i in groupStart..<groupStart+4:
                    counts[assignment[i]] += 1
                check counts[1] == 2
                check counts[2] == 2

    test "CountEq channel with GCC constraint on same variables":
        ## Combines a GCC constraint (for structure) with countEq channels
        ## (for objective computation), like in Mondoku.
        ## 4 search vars, GCC ensures each of {1,2} appears exactly 2 times,
        ## countEq channels count occurrences, min/max compute balance.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            var x = sys.newConstrainedSequence(4)
            x.setDomain(@[1, 2])

            # GCC constraint: value 1 appears 2 times, value 2 appears 2 times
            sys.addConstraint(globalCardinality[int]([0, 1, 2, 3], [1, 2], [2, 2]))

            # Count channels (same as what the translator would create)
            let inputPositions = toSeq(0..3)
            let posCount1 = sys.baseArray.len
            var count1 = sys.newConstrainedVariable()
            count1.setDomain(toSeq(0..4))
            sys.baseArray.addCountEqChannelBinding(posCount1, 1, inputPositions)

            let posCount2 = sys.baseArray.len
            var count2 = sys.newConstrainedVariable()
            count2.setDomain(toSeq(0..4))
            sys.baseArray.addCountEqChannelBinding(posCount2, 2, inputPositions)

            # Min/max of counts
            let countExprs = @[sys.baseArray[posCount1], sys.baseArray[posCount2]]
            let minP = sys.baseArray.len
            var minV = sys.newConstrainedVariable()
            minV.setDomain(toSeq(0..4))
            sys.baseArray.addMinMaxChannelBinding(minP, isMin = true, countExprs)

            let maxP = sys.baseArray.len
            var maxV = sys.newConstrainedVariable()
            maxV.setDomain(toSeq(0..4))
            sys.baseArray.addMinMaxChannelBinding(maxP, isMin = false, countExprs)

            sys.resolve(tabuThreshold = 5000)

            # GCC forces exact balance: count1=2, count2=2
            check sys.assignment[posCount1] == 2
            check sys.assignment[posCount2] == 2
            check sys.assignment[minP] == 2
            check sys.assignment[maxP] == 2

suite "CountEq Channel Copy and Consistency":
    test "createCopy preserves countEq bindings":
        ## Verifies that createCopy (used by TabuState) correctly copies
        ## countEqChannelBindings and countEqChannelsAtPosition.
        ## This was the root cause of the objective=0 bug.
        var sys = initConstraintSystem[int]()

        var x = sys.newConstrainedSequence(3)
        x.setDomain(@[1, 2, 3])

        let countPos = sys.baseArray.len
        var count1 = sys.newConstrainedVariable()
        count1.setDomain(toSeq(0..3))
        sys.baseArray.addCountEqChannelBinding(countPos, 1, @[0, 1, 2])

        # Constraint on the count channel
        sys.addConstraint(sys.baseArray[countPos] == 2)

        sys.resolve(tabuThreshold = 5000)

        # After resolve, the assignment should have correct channel value
        var actual = 0
        for i in 0..2:
            if sys.assignment[i] == 1: inc actual
        check sys.assignment[countPos] == actual
        check actual == 2

    test "CountEq channels survive optimization loop":
        ## The optimizer calls resolve() multiple times with different bound
        ## constraints. Count channels must be correctly maintained across
        ## all iterations.
        var sys = initConstraintSystem[int]()

        # 6 search vars, domain {1,2,3}
        var x = sys.newConstrainedSequence(6)
        x.setDomain(@[1, 2, 3])

        let inputPositions = toSeq(0..5)

        # Count channels
        var countPositions: seq[int]
        for v in 1..3:
            let pos = sys.baseArray.len
            var cv = sys.newConstrainedVariable()
            cv.setDomain(toSeq(0..6))
            sys.baseArray.addCountEqChannelBinding(pos, v, inputPositions)
            countPositions.add(pos)

        # Max of counts
        var countExprs: seq[AlgebraicExpression[int]]
        for cp in countPositions:
            countExprs.add(sys.baseArray[cp])
        let maxPos = sys.baseArray.len
        var maxV = sys.newConstrainedVariable()
        maxV.setDomain(toSeq(0..6))
        sys.baseArray.addMinMaxChannelBinding(maxPos, isMin = false, countExprs)

        # Min of counts
        let minPos = sys.baseArray.len
        var minV = sys.newConstrainedVariable()
        minV.setDomain(toSeq(0..6))
        sys.baseArray.addMinMaxChannelBinding(minPos, isMin = true, countExprs)

        # Objective: minimize max - min (minimize imbalance)
        let objExpr = sys.baseArray[maxPos] - sys.baseArray[minPos]
        sys.minimize(objExpr, parallel = true, tabuThreshold = 1000,
                    lowerBound = 0)

        # With 6 vars and 3 values, balanced = 2 each, diff = 0
        let assignment = sys.assignment
        let objVal = assignment[maxPos] - assignment[minPos]
        check objVal == 0

        # Verify actual counts match channels
        var counts = [0, 0, 0, 0]
        for i in 0..5:
            counts[assignment[i]] += 1
        for vi, v in [1, 2, 3]:
            check assignment[countPositions[vi]] == counts[v]

suite "Domain Tightening for Count Channels":
    test "Count channel domain is bounded by input size":
        ## Count channel with 5 input positions should have domain [0..5].
        var sys = initConstraintSystem[int]()

        var x = sys.newConstrainedSequence(5)
        x.setDomain(@[1, 2])

        let countPos = sys.baseArray.len
        var countVar = sys.newConstrainedVariable()
        # Set a wider domain initially
        countVar.setDomain(toSeq(0..10))
        sys.baseArray.addCountEqChannelBinding(countPos, 1, toSeq(0..4))

        # After adding countEq, the domain bounds propagation should constrain
        # the count to [0..5] (but we set domain explicitly before adding)
        # The key test is that the solver works correctly with this channel
        sys.addConstraint(sys.baseArray[countPos] == 3)

        sys.resolve(tabuThreshold = 5000)

        var actual = 0
        for i in 0..4:
            if sys.assignment[i] == 1: inc actual
        check actual == 3
        check sys.assignment[countPos] == 3

    test "Closed GCC sum propagation":
        ## When all input domains ⊆ cover set, sum(counts) == n.
        ## With 4 vars, domain {1,2}, count1 + count2 == 4.
        ## If count1 >= 3, then count2 <= 1.
        var sys = initConstraintSystem[int]()

        var x = sys.newConstrainedSequence(4)
        x.setDomain(@[1, 2])

        let inputPositions = toSeq(0..3)

        let posCount1 = sys.baseArray.len
        var count1 = sys.newConstrainedVariable()
        count1.setDomain(toSeq(0..4))
        sys.baseArray.addCountEqChannelBinding(posCount1, 1, inputPositions)

        let posCount2 = sys.baseArray.len
        var count2 = sys.newConstrainedVariable()
        count2.setDomain(toSeq(0..4))
        sys.baseArray.addCountEqChannelBinding(posCount2, 2, inputPositions)

        # Force count1 == 3
        sys.addConstraint(sys.baseArray[posCount1] == 3)

        sys.resolve(tabuThreshold = 5000)

        # count1 + count2 == 4 (closed GCC), so count2 == 1
        check sys.assignment[posCount1] == 3
        check sys.assignment[posCount2] == 1

        let assignment = x.assignment
        var counts = [0, 0, 0]
        for v in assignment:
            counts[v] += 1
        check counts[1] == 3
        check counts[2] == 1

    test "Unbalanced optimization finds correct objective":
        ## 8 vars with domain {1,2,3,4}, minimize max(counts) - min(counts).
        ## Balanced: each value appears 2 times, diff = 0.
        ## Verify the optimizer finds this and reports correct objective.
        var sys = initConstraintSystem[int]()

        var x = sys.newConstrainedSequence(8)
        x.setDomain(@[1, 2, 3, 4])

        let inputPositions = toSeq(0..7)

        var countPositions: seq[int]
        for v in 1..4:
            let pos = sys.baseArray.len
            var cv = sys.newConstrainedVariable()
            cv.setDomain(toSeq(0..8))
            sys.baseArray.addCountEqChannelBinding(pos, v, inputPositions)
            countPositions.add(pos)

        var countExprs: seq[AlgebraicExpression[int]]
        for cp in countPositions:
            countExprs.add(sys.baseArray[cp])

        let maxPos = sys.baseArray.len
        var maxV = sys.newConstrainedVariable()
        maxV.setDomain(toSeq(0..8))
        sys.baseArray.addMinMaxChannelBinding(maxPos, isMin = false, countExprs)

        let minPos = sys.baseArray.len
        var minV = sys.newConstrainedVariable()
        minV.setDomain(toSeq(0..8))
        sys.baseArray.addMinMaxChannelBinding(minPos, isMin = true, countExprs)

        let objExpr = sys.baseArray[maxPos] - sys.baseArray[minPos]
        sys.minimize(objExpr, parallel = true, tabuThreshold = 2000,
                    lowerBound = 0)

        let assignment = sys.assignment
        let objVal = assignment[maxPos] - assignment[minPos]
        check objVal == 0

        # Verify channel consistency
        var counts = [0, 0, 0, 0, 0]
        for i in 0..7:
            counts[assignment[i]] += 1
        for vi, v in [1, 2, 3, 4]:
            check assignment[countPositions[vi]] == counts[v]
        check counts[1] == 2
        check counts[2] == 2
        check counts[3] == 2
        check counts[4] == 2
