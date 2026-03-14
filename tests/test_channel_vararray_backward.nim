## Tests for Phase CB-var: Variable-array channel binding backward propagation.
##
## Phase CB-var restricts the domain of positions that appear as variable array
## elements in channel bindings to the union of reachable channel-position domains.

import std/[packedsets, sequtils, tables, unittest]
import crusher

suite "Channel Variable-Array Backward Propagation":

    test "channel binding prunes variable array element domain":
        ## Set up a channel binding: ch = arr[idx]
        ## where arr contains variable positions with domain {0..9}
        ## and ch has domain {3, 4}.
        ## The variable array elements reachable from idx should be pruned to {3, 4}.
        var sys = initConstraintSystem[int]()

        # idx: the index variable
        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1, 2])

        # Array element variables
        let aPos = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(toSeq(0..9))

        let bPos = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(toSeq(0..9))

        let cPos = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(toSeq(0..9))

        # Channel variable
        let chPos = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[3, 4])

        # Create the channel binding: ch = [a, b, c][idx]
        let idxExpr = sys.baseArray[idxPos] + 0  # identity expression
        let arrayElems = @[
            ArrayElement[int](isConstant: false, variablePosition: aPos),
            ArrayElement[int](isConstant: false, variablePosition: bPos),
            ArrayElement[int](isConstant: false, variablePosition: cPos),
        ]
        sys.baseArray.addChannelBinding(chPos, idxExpr, arrayElems)

        let reduced = reduceDomain(sys.baseArray)

        # All array elements reachable from idx: should be pruned to {3, 4}
        for pos in [aPos, bPos, cPos]:
            check 3 in reduced[pos]
            check 4 in reduced[pos]
            for v in 0..9:
                if v != 3 and v != 4:
                    check v notin reduced[pos]

    test "unreachable array element not pruned by channel binding":
        ## ch = [a, b, c][idx] with idx domain = {0, 1}
        ## c is unreachable — should keep full domain.
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1])  # can't reach index 2

        let aPos = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(toSeq(0..5))

        let bPos = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(toSeq(0..5))

        let cPos = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(toSeq(0..5))

        let chPos = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[2, 3])

        let idxExpr = sys.baseArray[idxPos] + 0
        let arrayElems = @[
            ArrayElement[int](isConstant: false, variablePosition: aPos),
            ArrayElement[int](isConstant: false, variablePosition: bPos),
            ArrayElement[int](isConstant: false, variablePosition: cPos),
        ]
        sys.baseArray.addChannelBinding(chPos, idxExpr, arrayElems)

        let reduced = reduceDomain(sys.baseArray)

        # a and b reachable: pruned to {2, 3}
        for pos in [aPos, bPos]:
            check 2 in reduced[pos]
            check 3 in reduced[pos]
            check 0 notin reduced[pos]
            check 5 notin reduced[pos]

        # c unreachable: keeps full domain
        check 0 in reduced[cPos]
        check 5 in reduced[cPos]

    test "channel binding with offset index expression":
        ## ch = [a, b, c][idx - 1] (1-based indexing)
        ## idx domain = {1, 2, 3}, ch domain = {7, 8}
        ## All elements reachable, all should be pruned to {7, 8}
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[1, 2, 3])

        let aPos = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(toSeq(5..10))

        let bPos = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(toSeq(5..10))

        let cPos = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(toSeq(5..10))

        let chPos = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[7, 8])

        # idx - 1 offset expression
        let idxExpr = sys.baseArray[idxPos] - 1
        let arrayElems = @[
            ArrayElement[int](isConstant: false, variablePosition: aPos),
            ArrayElement[int](isConstant: false, variablePosition: bPos),
            ArrayElement[int](isConstant: false, variablePosition: cPos),
        ]
        sys.baseArray.addChannelBinding(chPos, idxExpr, arrayElems)

        let reduced = reduceDomain(sys.baseArray)

        for pos in [aPos, bPos, cPos]:
            check 7 in reduced[pos]
            check 8 in reduced[pos]
            check 5 notin reduced[pos]
            check 10 notin reduced[pos]
