## Tests for element constraint backward propagation in domain reduction (Phase 1b).
##
## Phase 1b propagates bidirectionally through constant-array element constraints:
##   Forward:  result domain ∩= { array[idx] : idx ∈ index domain }
##   Backward: index domain  ∩= { idx : array[idx] ∈ result domain }
## Handles both PositionBased and ExpressionBased (single-position) elements.

import std/[packedsets, sequtils, unittest]
import crusher

suite "Element Backward Propagation":

    test "PositionBased constant array — backward prunes index":
        ## array = [10, 20, 30, 40, 50]
        ## index domain = {0..4}, result domain = {20, 40}
        ## Backward: index should be pruned to {1, 3}
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1, 2, 3, 4])

        let resPos = sys.baseArray.len
        var res = sys.newConstrainedVariable()
        res.setDomain(@[20, 40])

        sys.addConstraint(element(idx, @[10, 20, 30, 40, 50], res))

        let reduced = reduceDomain(sys.baseArray)

        check reduced[idxPos] == @[1, 3]
        check reduced[resPos] == @[20, 40]

    test "PositionBased constant array — forward prunes result":
        ## array = [10, 20, 30, 40, 50]
        ## index domain = {0, 2}, result domain = {10..50}
        ## Forward: result should be pruned to {10, 30}
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 2])

        let resPos = sys.baseArray.len
        var res = sys.newConstrainedVariable()
        res.setDomain(@[10, 20, 30, 40, 50])

        sys.addConstraint(element(idx, @[10, 20, 30, 40, 50], res))

        let reduced = reduceDomain(sys.baseArray)

        check reduced[idxPos] == @[0, 2]
        check reduced[resPos] == @[10, 30]

    test "PositionBased constant array — bidirectional fixed-point":
        ## array = [5, 10, 5, 20, 5]
        ## index domain = {0..4}, result domain = {5, 10, 15}
        ## Forward: result pruned to {5, 10} (no index maps to 15)
        ## Then: index domain stays {0, 1, 2, 4} (all map to 5 or 10)
        ## Index 3 maps to 20 which is not in result domain → pruned
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1, 2, 3, 4])

        let resPos = sys.baseArray.len
        var res = sys.newConstrainedVariable()
        res.setDomain(@[5, 10, 15])

        sys.addConstraint(element(idx, @[5, 10, 5, 20, 5], res))

        let reduced = reduceDomain(sys.baseArray)

        check 15 notin reduced[resPos]
        check 20 notin reduced[resPos]
        check 3 notin reduced[idxPos]  # maps to 20, not in result domain
        check 0 in reduced[idxPos]     # maps to 5
        check 1 in reduced[idxPos]     # maps to 10
        check 2 in reduced[idxPos]     # maps to 5

    test "ExpressionBased constant array — backward prunes index":
        ## Simulates FlatZinc pattern: array_int_element(idx, [10,20,30], result)
        ## Translated as elementExpr(idx - 1, [10,20,30], result) for 1-based indexing
        ## idx domain = {1,2,3}, result domain = {30}
        ## Backward: idx should be pruned to {3} (only idx=3 → array[2]=30)
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[1, 2, 3])

        let resPos = sys.baseArray.len
        var res = sys.newConstrainedVariable()
        res.setDomain(@[30])

        # elementExpr with idx-1 offset (FlatZinc 1-based to 0-based)
        let idxExpr = sys.baseArray[idxPos] - 1
        let resExpr = sys.baseArray[resPos] + 0  # identity expression
        sys.addConstraint(elementExpr(idxExpr, @[10, 20, 30], resExpr))

        let reduced = reduceDomain(sys.baseArray)

        check reduced[idxPos] == @[3]
        check reduced[resPos] == @[30]

    test "ExpressionBased constant array — forward prunes result":
        ## elementExpr(idx - 1, [100, 200, 300, 400], result)
        ## idx domain = {1, 3}, result domain = {100..400}
        ## Forward: result should be pruned to {100, 300}
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[1, 3])

        let resPos = sys.baseArray.len
        var res = sys.newConstrainedVariable()
        res.setDomain(@[100, 200, 300, 400])

        let idxExpr = sys.baseArray[idxPos] - 1
        let resExpr = sys.baseArray[resPos] + 0
        sys.addConstraint(elementExpr(idxExpr, @[100, 200, 300, 400], resExpr))

        let reduced = reduceDomain(sys.baseArray)

        check reduced[idxPos] == @[1, 3]
        check reduced[resPos] == @[100, 300]

    test "ExpressionBased constant array — out-of-bounds index pruned":
        ## elementExpr(idx - 1, [10, 20, 30], result)
        ## idx domain = {0, 1, 2, 3, 4}
        ## idx=0 → array[-1] out of bounds → pruned
        ## idx=4 → array[3] out of bounds → pruned
        var sys = initConstraintSystem[int]()

        let idxPos = sys.baseArray.len
        var idx = sys.newConstrainedVariable()
        idx.setDomain(@[0, 1, 2, 3, 4])

        let resPos = sys.baseArray.len
        var res = sys.newConstrainedVariable()
        res.setDomain(@[10, 20, 30])

        let idxExpr = sys.baseArray[idxPos] - 1
        let resExpr = sys.baseArray[resPos] + 0
        sys.addConstraint(elementExpr(idxExpr, @[10, 20, 30], resExpr))

        let reduced = reduceDomain(sys.baseArray)

        check 0 notin reduced[idxPos]  # out of bounds
        check 4 notin reduced[idxPos]  # out of bounds
        check 1 in reduced[idxPos]
        check 2 in reduced[idxPos]
        check 3 in reduced[idxPos]

    test "element backward propagation solves constrained lookup":
        ## Practical test: index selects from lookup table, result must equal target.
        ## lookup = [7, 3, 9, 1, 5], target = 9
        ## Without backward propagation: index searches over {0..4}
        ## With backward propagation: index restricted to {2} (only lookup[2]=9)
        var sys = initConstraintSystem[int]()

        var idx = sys.newConstrainedVariable()
        idx.setDomain(toSeq(0..4))

        var res = sys.newConstrainedVariable()
        res.setDomain(toSeq(0..10))

        sys.addConstraint(element(idx, @[7, 3, 9, 1, 5], res))
        sys.addConstraint(res == 9)

        sys.resolve(parallel = true, tabuThreshold = 1000, verbose = false)

        check idx.assignment == 2
        check res.assignment == 9
