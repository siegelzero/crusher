## Tests for multi-position (3+) Channel Binding arc consistency in domain reduction.
##
## The Channel AC phase in reduceDomain() propagates domain restrictions
## bidirectionally between key positions and channel positions for channel
## bindings with constant arrays. This tests the N-position (3-6) index
## expression case.

import std/[packedsets, sequtils, unittest]
import crusher

suite "Multi-Position Channel AC Domain Reduction":
    test "3-position forward: channel domain restricted to reachable values":
        ## Channel ch = lookup[a*4 + b*2 + c] with a,b,c ∈ {0,1}
        ## lookup = [10, 20, 30, 40, 50, 60, 70, 80]
        ## ch starts with domain {10,20,...,80,90,100}
        ## After forward propagation, ch should be restricted to {10..80}
        var sys = initConstraintSystem[int]()

        let posA = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[0, 1])

        let posB = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[0, 1])

        let posC = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[0, 1])

        # Channel position
        let posCh = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[10, 20, 30, 40, 50, 60, 70, 80, 90, 100])

        # Index expression: a*4 + b*2 + c
        let idxExpr = sys.baseArray[posA] * 4 + sys.baseArray[posB] * 2 + sys.baseArray[posC]

        # Constant lookup: [10, 20, 30, 40, 50, 60, 70, 80]
        var arrayElems: seq[ArrayElement[int]]
        for v in [10, 20, 30, 40, 50, 60, 70, 80]:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

        sys.baseArray.addChannelBinding(posCh, idxExpr, arrayElems)

        # Need at least one constraint to make it a valid system
        sys.addConstraint(sys.baseArray[posA] >= 0)

        let reduced = reduceDomain(sys.baseArray)

        # Forward: ch should only contain values reachable from lookup
        check 90 notin reduced[posCh]
        check 100 notin reduced[posCh]
        check 10 in reduced[posCh]
        check 80 in reduced[posCh]
        check reduced[posCh].len == 8

    test "3-position backward: key position pruned when no support":
        ## Channel ch = lookup[a*6 + b*3 + c] where:
        ## a ∈ {0,1}, b ∈ {0,1,2}, c ∈ {0,1,2}
        ## lookup has 18 entries, but ch domain restricted to {99}
        ## Only index 10 maps to 99 → a=1, b=1, c=1 (1*6+1*3+1=10)
        ## Index 10 is NOT reachable with a=0 (max a=0 index: 0+2*3+2=8)
        var sys = initConstraintSystem[int]()

        let posA = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[0, 1])

        let posB = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[0, 1, 2])

        let posC = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[0, 1, 2])

        let posCh = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[99])

        # Index: a*6 + b*3 + c
        let idxExpr = sys.baseArray[posA] * 6 + sys.baseArray[posB] * 3 + sys.baseArray[posC]

        # Lookup: only index 10 (a=1,b=1,c=1) maps to 99; rest map to 0
        var arrayElems: seq[ArrayElement[int]]
        for i in 0..<18:
            if i == 10:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 99))
            else:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))

        sys.baseArray.addChannelBinding(posCh, idxExpr, arrayElems)

        sys.addConstraint(sys.baseArray[posA] >= 0)

        let reduced = reduceDomain(sys.baseArray)

        # Backward: a=1 (only way to reach index 10)
        check reduced[posA] == @[1]
        # b=1, c=1 (1*6 + 1*3 + 1 = 10)
        check reduced[posB] == @[1]
        check reduced[posC] == @[1]

    test "3-position bidirectional propagation with constraint":
        ## Combine channel AC with a constraint on search vars.
        ## a ∈ {0,1,2}, b ∈ {0,1,2}, c ∈ {0,1,2}
        ## ch = lookup[a*9 + b*3 + c] where lookup maps to {1..27}
        ## Constraint: ch == 14
        ## Index 13 (0-based) has value 14, meaning a=1, b=1, c=1
        var sys = initConstraintSystem[int]()

        let posA = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[0, 1, 2])

        let posB = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[0, 1, 2])

        let posC = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[0, 1, 2])

        let posCh = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(toSeq(1..27))

        # Index: a*9 + b*3 + c  (0-based)
        let idxExpr = sys.baseArray[posA] * 9 + sys.baseArray[posB] * 3 + sys.baseArray[posC]

        # Lookup: entry i has unique value i+1
        var arrayElems: seq[ArrayElement[int]]
        for i in 0..<27:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: i + 1))

        sys.baseArray.addChannelBinding(posCh, idxExpr, arrayElems)

        # Constraint: ch must equal 14 → index 13 → a=1, b=1, c=1
        sys.addConstraint(sys.baseArray[posCh] == 14)

        let reduced = reduceDomain(sys.baseArray)

        # Single-var constraint reduction fixes ch = {14}
        # Backward propagation forces a=1, b=1, c=1
        check reduced[posCh] == @[14]
        check reduced[posA] == @[1]
        check reduced[posB] == @[1]
        check reduced[posC] == @[1]

    test "4-position forward and backward":
        ## 4 binary positions: idx = a*8 + b*4 + c*2 + d
        ## 16 entries, ch restricted to {42}
        ## Only index 5 (a=0, b=1, c=0, d=1) maps to 42
        var sys = initConstraintSystem[int]()

        var positions: array[4, int]
        var vars: array[4, ConstrainedVariable[int]]
        for i in 0..<4:
            positions[i] = sys.baseArray.len
            vars[i] = sys.newConstrainedVariable()
            vars[i].setDomain(@[0, 1])

        let posCh = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[42])

        let idxExpr = sys.baseArray[positions[0]] * 8 +
                      sys.baseArray[positions[1]] * 4 +
                      sys.baseArray[positions[2]] * 2 +
                      sys.baseArray[positions[3]]

        var arrayElems: seq[ArrayElement[int]]
        for i in 0..<16:
            if i == 5:  # 0*8 + 1*4 + 0*2 + 1 = 5
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 42))
            else:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))

        sys.baseArray.addChannelBinding(posCh, idxExpr, arrayElems)
        sys.addConstraint(sys.baseArray[positions[0]] >= 0)

        let reduced = reduceDomain(sys.baseArray)

        check reduced[positions[0]] == @[0]  # a=0
        check reduced[positions[1]] == @[1]  # b=1
        check reduced[positions[2]] == @[0]  # c=0
        check reduced[positions[3]] == @[1]  # d=1

    test "3-position no pruning when table is dense":
        ## When all lookup values are in ch's domain, nothing should be pruned.
        ## This mirrors the portal problem behavior.
        var sys = initConstraintSystem[int]()

        let posA = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[0, 1])

        let posB = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[0, 1])

        let posC = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[0, 1])

        let posCh = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(toSeq(0..7))

        let idxExpr = sys.baseArray[posA] * 4 + sys.baseArray[posB] * 2 + sys.baseArray[posC]

        # Dense: lookup[i] = i, so all values 0..7 are reachable
        var arrayElems: seq[ArrayElement[int]]
        for i in 0..<8:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: i))

        sys.baseArray.addChannelBinding(posCh, idxExpr, arrayElems)
        sys.addConstraint(sys.baseArray[posA] >= 0)

        let reduced = reduceDomain(sys.baseArray)

        # No pruning — all values have support
        check reduced[posA].len == 2
        check reduced[posB].len == 2
        check reduced[posC].len == 2
        check reduced[posCh].len == 8

    test "3-position partial backward: some key values pruned":
        ## a ∈ {0,1,2}, b ∈ {0,1}, c ∈ {0,1}
        ## lookup has 12 entries, ch restricted to {5, 10}
        ## Only certain combos map to those values
        var sys = initConstraintSystem[int]()

        let posA = sys.baseArray.len
        var a = sys.newConstrainedVariable()
        a.setDomain(@[0, 1, 2])

        let posB = sys.baseArray.len
        var b = sys.newConstrainedVariable()
        b.setDomain(@[0, 1])

        let posC = sys.baseArray.len
        var c = sys.newConstrainedVariable()
        c.setDomain(@[0, 1])

        let posCh = sys.baseArray.len
        var ch = sys.newConstrainedVariable()
        ch.setDomain(@[5, 10])

        # Index: a*4 + b*2 + c
        let idxExpr = sys.baseArray[posA] * 4 + sys.baseArray[posB] * 2 + sys.baseArray[posC]

        # Lookup: index 3 (a=0,b=1,c=1) → 5, index 9 (a=2,b=0,c=1) → 10
        # All others → 0
        var arrayElems: seq[ArrayElement[int]]
        for i in 0..<12:
            case i
            of 3: arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 5))
            of 9: arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 10))
            else: arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))

        sys.baseArray.addChannelBinding(posCh, idxExpr, arrayElems)
        sys.addConstraint(sys.baseArray[posA] >= 0)

        let reduced = reduceDomain(sys.baseArray)

        # a=1 has no support (indices 4..7 all map to 0) → pruned
        check 0 in reduced[posA]
        check 1 notin reduced[posA]
        check 2 in reduced[posA]
        # b: both 0 and 1 have support (index 3 needs b=1, index 9 needs b=0)
        check reduced[posB].len == 2
        # c: must be 1 (both index 3 and 9 have c=1)
        check reduced[posC] == @[1]
