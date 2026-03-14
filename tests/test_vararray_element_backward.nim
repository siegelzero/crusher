## Tests for Phase 6b-elem: Variable-array element backward propagation.
##
## Phase 6b-elem restricts the domain of positions that appear as variable
## array elements in element constraints to the union of reachable value-position
## domains.

import std/[packedsets, sequtils, unittest]
import crusher

suite "Variable-Array Element Backward Propagation":

    test "variable array element domain restricted by value domain":
        ## element(idx, [a, b, c], val) with val domain = {10, 20}
        ## a,b,c all have domain {10, 20, 30, 40}
        ## After backward propagation, a,b,c should lose 30 and 40
        ## because val can only be 10 or 20.
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1, 2])

        let aPos = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[10, 20, 30, 40])

        let bPos = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[10, 20, 30, 40])

        let cPos = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[10, 20, 30, 40])

        let valPos = sys.baseArray.len
        var val = sys.newConstrainedVariable()
        val.setDomain(@[10, 20])

        sys.addConstraint(element(idx, @[a + 0, b + 0, c + 0], val))

        let reduced = reduceDomain(sys.baseArray)

        # Each array element should be pruned to {10, 20}
        check 30 notin reduced[aPos]
        check 40 notin reduced[aPos]
        check 10 in reduced[aPos]
        check 20 in reduced[aPos]

        check 30 notin reduced[bPos]
        check 40 notin reduced[bPos]

        check 30 notin reduced[cPos]
        check 40 notin reduced[cPos]

    test "unreachable array element not pruned":
        ## element(idx, [a, b, c], val) with idx domain = {0, 1} (c is unreachable)
        ## val domain = {10, 20}
        ## a and b should be pruned to {10, 20}, c should keep full domain
        ## because no index can reach position 2.
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1])  # can't reach index 2

        let aPos = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[10, 20, 30, 40])

        let bPos = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[10, 20, 30, 40])

        let cPos = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[10, 20, 30, 40])

        let valPos = sys.baseArray.len
        var val = sys.newConstrainedVariable()
        val.setDomain(@[10, 20])

        sys.addConstraint(element(idx, @[a + 0, b + 0, c + 0], val))

        let reduced = reduceDomain(sys.baseArray)

        # a and b reachable: pruned to {10, 20}
        check 30 notin reduced[aPos]
        check 40 notin reduced[aPos]

        check 30 notin reduced[bPos]
        check 40 notin reduced[bPos]

        # c is unreachable from idx domain — but 6b-elem builds allowedValues
        # only from constraints where pos IS reachable. c participates in the
        # constraint but no index maps to it, so allowedValues stays empty for c,
        # meaning no pruning occurs. c keeps full domain.
        check 30 in reduced[cPos]
        check 40 in reduced[cPos]

    test "variable array element backward propagation solves correctly":
        ## End-to-end: element with variable array + tight value constraint
        var sys = initConstraintSystem[int]()

        var idx = sys.newConstrainedVariable()
        idx.setDomain(toSeq(0..2))

        var arr = sys.newConstrainedSequence(3)
        arr.setDomain(toSeq(0..20))

        var val = sys.newConstrainedVariable()
        val.setDomain(toSeq(0..20))

        # arr[idx] == val
        var arrExprs: seq[AlgebraicExpression[int]] = @[]
        for i in 0..<3:
            arrExprs.add(arr[i])
        sys.addConstraint(element(idx, arrExprs, val))

        # Fix array values
        sys.addConstraint(arr[0] == 5)
        sys.addConstraint(arr[1] == 10)
        sys.addConstraint(arr[2] == 15)

        # val must be 10
        sys.addConstraint(val == 10)

        sys.resolve(parallel=true, tabuThreshold=1000)

        check idx.assignment == 1
        check val.assignment == 10

    test "duplicate variable position in array does not cause issues":
        ## element(idx, [a, b, a], val) — position a appears at indices 0 and 2
        ## Tests issue #7 fix: deduplicated constraint indices in elemArrayParticipation
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1, 2])

        let aPos = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[10, 20, 30, 40])

        let bPos = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[10, 20, 30, 40])

        let valPos = sys.baseArray.len
        var val = sys.newConstrainedVariable()
        val.setDomain(@[10, 20])

        # a appears at index 0 and 2
        let mixedArray = @[
            ArrayElement[int](isConstant: false, variablePosition: aPos),
            ArrayElement[int](isConstant: false, variablePosition: bPos),
            ArrayElement[int](isConstant: false, variablePosition: aPos),
        ]
        sys.addConstraint(element(idx, mixedArray, val))

        let reduced = reduceDomain(sys.baseArray)

        # a should be pruned to {10, 20} (reachable via idx=0 or idx=2)
        check 30 notin reduced[aPos]
        check 40 notin reduced[aPos]
        check 10 in reduced[aPos]
        check 20 in reduced[aPos]

        # b should also be pruned
        check 30 notin reduced[bPos]
        check 40 notin reduced[bPos]
