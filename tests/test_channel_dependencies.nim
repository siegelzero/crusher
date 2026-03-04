## Tests for multi-layer channel dependency propagation.
##
## These tests verify that channel bindings correctly propagate through
## multiple layers: minmax channels feeding into element channels, and
## element channels feeding back into minmax channels.
##
## The bugs these tests cover:
## 1. Init ordering: element channels evaluated before min/max fixed-point
##    converges, reading placeholder values that are never refreshed.
## 2. Registration: addChannelBinding only registered dependencies at index
##    expression positions, not array element positions — so min/max channel
##    changes didn't trigger element re-evaluation during search.

import std/[packedsets, sequtils, unittest]
import crusher

suite "Multi-Layer Channel Dependencies":
    test "Init fixed-point: element channel reads min/max channel output":
        ## Minimal reproduction of the init ordering bug.
        ## Without the fix, mm has placeholder=0 when sel is computed,
        ## so sel=0 and the constraint is violated.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            # Search vars: a (pos 0), b (pos 1), idx (pos 2)
            let pos0 = sys.baseArray.len
            var a = sys.newConstrainedVariable()
            a.setDomain(@[0, 1])
            let pos1 = sys.baseArray.len
            var b = sys.newConstrainedVariable()
            b.setDomain(@[0, 1])
            let pos2 = sys.baseArray.len
            var idx = sys.newConstrainedVariable()
            idx.setDomain(@[0, 1])

            # Min/max channel: mm = max(a, b) at pos 3
            let pos3 = sys.baseArray.len
            var mm = sys.newConstrainedVariable()
            mm.setDomain(@[0, 1])
            sys.baseArray.addMinMaxChannelBinding(pos3, isMin = false,
                @[sys.baseArray[pos0], sys.baseArray[pos1]])

            # Element channel: sel = elem(idx, [mm, 0]) at pos 4
            # When idx=0, sel=mm; when idx=1, sel=0
            let pos4 = sys.baseArray.len
            var sel = sys.newConstrainedVariable()
            sel.setDomain(@[0, 1])
            sys.baseArray.addChannelBinding(pos4, sys.baseArray[pos2],
                @[ArrayElement[int](isConstant: false, variablePosition: pos3),
                  ArrayElement[int](isConstant: true, constantValue: 0)])

            # Constraints: a == 1, idx == 0, sel == 1
            sys.addConstraint(sys.baseArray[pos0] == 1)
            sys.addConstraint(sys.baseArray[pos2] == 0)
            sys.addConstraint(sys.baseArray[pos4] == 1)

            sys.resolve(tabuThreshold = 5000)

            # a must be 1, so mm = max(1, b) = 1
            # idx = 0, so sel = elem(0, [mm, 0]) = mm = 1
            check sys.assignment[pos0] == 1
            check sys.assignment[pos2] == 0
            check sys.assignment[pos3] == 1  # mm = max(a, b) >= 1
            check sys.assignment[pos4] == 1  # sel = mm = 1

    test "Search propagation: min/max change triggers element re-evaluation":
        ## Tests the registration fix: element channel must be registered
        ## at array element positions (not just index expression positions)
        ## so that changing x updates mm, which triggers sel re-evaluation.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            # Search vars: x (pos 0), idx (pos 1, fixed to 0)
            let pos0 = sys.baseArray.len
            var x = sys.newConstrainedVariable()
            x.setDomain(@[0, 1])
            let pos1 = sys.baseArray.len
            var idx = sys.newConstrainedVariable()
            idx.setDomain(@[0])

            # Min/max channel: mm = max(x) at pos 2
            let pos2 = sys.baseArray.len
            var mm = sys.newConstrainedVariable()
            mm.setDomain(@[0, 1])
            sys.baseArray.addMinMaxChannelBinding(pos2, isMin = false,
                @[sys.baseArray[pos0]])

            # Element channel: sel = elem(idx, [mm]) at pos 3
            # Since idx is always 0, sel = mm
            let pos3 = sys.baseArray.len
            var sel = sys.newConstrainedVariable()
            sel.setDomain(@[0, 1])
            sys.baseArray.addChannelBinding(pos3, sys.baseArray[pos1],
                @[ArrayElement[int](isConstant: false, variablePosition: pos2)])

            # Constraint: sel == 1
            # Solver must find x=1 → mm=1 → sel=1
            sys.addConstraint(sys.baseArray[pos3] == 1)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[pos0] == 1  # x must be 1
            check sys.assignment[pos2] == 1  # mm = max(x) = 1
            check sys.assignment[pos3] == 1  # sel = mm = 1

    test "Three-layer chain: minmax → element → minmax":
        ## Full multi-layer chain simulating the gt-sort pattern.
        ## Exercises both bugs simultaneously: init ordering AND search
        ## propagation through the minmax→element→minmax chain.
        for trial in 0..<10:
            var sys = initConstraintSystem[int]()

            # Search vars: a0, a1, b0, b1 (domain {0,1}), idx (domain {0,1})
            let posA0 = sys.baseArray.len
            var a0 = sys.newConstrainedVariable()
            a0.setDomain(@[0, 1])
            let posA1 = sys.baseArray.len
            var a1 = sys.newConstrainedVariable()
            a1.setDomain(@[0, 1])
            let posB0 = sys.baseArray.len
            var b0 = sys.newConstrainedVariable()
            b0.setDomain(@[0, 1])
            let posB1 = sys.baseArray.len
            var b1 = sys.newConstrainedVariable()
            b1.setDomain(@[0, 1])
            let posIdx = sys.baseArray.len
            var idx = sys.newConstrainedVariable()
            idx.setDomain(@[0, 1])

            # Layer 1 (min/max channels): product membership booleans
            # set1_v0 = max(a0*b0)  — product membership for sum=0
            let posSet1V0 = sys.baseArray.len
            var set1V0 = sys.newConstrainedVariable()
            set1V0.setDomain(@[0, 1])
            sys.baseArray.addMinMaxChannelBinding(posSet1V0, isMin = false,
                @[sys.baseArray[posA0] * sys.baseArray[posB0]])

            # set1_v1 = max(a0*b1, a1*b0)  — product membership for sum=1
            let posSet1V1 = sys.baseArray.len
            var set1V1 = sys.newConstrainedVariable()
            set1V1.setDomain(@[0, 1])
            sys.baseArray.addMinMaxChannelBinding(posSet1V1, isMin = false,
                @[sys.baseArray[posA0] * sys.baseArray[posB1],
                  sys.baseArray[posA1] * sys.baseArray[posB0]])

            # set2_v0 = max(a0*b0)  — duplicate set for element selection
            let posSet2V0 = sys.baseArray.len
            var set2V0 = sys.newConstrainedVariable()
            set2V0.setDomain(@[0, 1])
            sys.baseArray.addMinMaxChannelBinding(posSet2V0, isMin = false,
                @[sys.baseArray[posA0] * sys.baseArray[posB0]])

            # Layer 2 (element channels):
            # sel0 = elem(idx, [set1_v0, set2_v0])
            let posSel0 = sys.baseArray.len
            var sel0 = sys.newConstrainedVariable()
            sel0.setDomain(@[0, 1])
            sys.baseArray.addChannelBinding(posSel0, sys.baseArray[posIdx],
                @[ArrayElement[int](isConstant: false, variablePosition: posSet1V0),
                  ArrayElement[int](isConstant: false, variablePosition: posSet2V0)])

            # sel1 = elem(idx, [set1_v1, 0])
            let posSel1 = sys.baseArray.len
            var sel1 = sys.newConstrainedVariable()
            sel1.setDomain(@[0, 1])
            sys.baseArray.addChannelBinding(posSel1, sys.baseArray[posIdx],
                @[ArrayElement[int](isConstant: false, variablePosition: posSet1V1),
                  ArrayElement[int](isConstant: true, constantValue: 0)])

            # Layer 3 (min/max channel — second comprehension):
            # final = max(sel0, sel1)  — union of selected booleans
            let posFinal = sys.baseArray.len
            var final_var = sys.newConstrainedVariable()
            final_var.setDomain(@[0, 1])
            sys.baseArray.addMinMaxChannelBinding(posFinal, isMin = false,
                @[sys.baseArray[posSel0], sys.baseArray[posSel1]])

            # Constraints: a0==1, a1==1, b0==1, idx==0, final==1
            sys.addConstraint(sys.baseArray[posA0] == 1)
            sys.addConstraint(sys.baseArray[posA1] == 1)
            sys.addConstraint(sys.baseArray[posB0] == 1)
            sys.addConstraint(sys.baseArray[posIdx] == 0)
            sys.addConstraint(sys.baseArray[posFinal] == 1)

            sys.resolve(tabuThreshold = 5000)

            # With a0=1, a1=1, b0=1:
            #   set1_v0 = max(1*1) = 1
            #   set1_v1 = max(1*b1, 1*1) = 1
            #   set2_v0 = max(1*1) = 1
            # With idx=0:
            #   sel0 = elem(0, [set1_v0, set2_v0]) = set1_v0 = 1
            #   sel1 = elem(0, [set1_v1, 0]) = set1_v1 = 1
            # final = max(sel0, sel1) = max(1, 1) = 1
            check sys.assignment[posA0] == 1
            check sys.assignment[posA1] == 1
            check sys.assignment[posB0] == 1
            check sys.assignment[posIdx] == 0
            check sys.assignment[posFinal] == 1
