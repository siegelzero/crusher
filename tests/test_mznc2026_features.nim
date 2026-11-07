## Tests for features added while working on the MiniZinc Challenge 2026 set:
##   - regular: Hamming-distance penalty (exact DP) + moveDelta/updatePosition consistency
##   - regular line-rewrite moves (small nonogram solved end-to-end)
##   - fzn_nvalue with a constant count / literal array entries
##   - constant (presolved) objective: solved as satisfaction
##   - expression channels in channel-dep cascades: an objective defined through
##     int_times channels over weighted-count loads must steer the search

import std/[unittest, sequtils, sets, random, packedsets, times, tables]
import crusher
import constraints/regular
import flatzinc/[parser, translator]
import search/tabu

# Nonogram line DFA over {1 = blank, 2 = filled} for the given block lengths.
proc lineDfa(blocks: seq[int]): (seq[seq[int]], int, seq[int]) =
    # States: 1 = leading blanks; then for each block, one state per filled cell,
    # followed by a "gap" state (>=1 blank) except after the last block.
    var trans: seq[seq[int]] = @[@[1, 0]]   # state 1: blank->1, filled->set below
    var s = 1
    for bi, b in blocks:
        for k in 0..<b:
            trans.add(@[0, 0])
            let ns = trans.len            # 1-based id of the new state
            if k == 0:
                trans[s - 1][1] = ns       # enter block on filled
            else:
                trans[s - 1][1] = ns
            s = ns
        if bi < blocks.len - 1:
            trans.add(@[0, 0])
            let gap = trans.len
            trans[s - 1][0] = gap          # mandatory blank after the block
            trans[gap - 1][0] = gap        # extra blanks
            s = gap
    trans.add(@[0, 0])
    let tail = trans.len
    trans[s - 1][0] = tail
    trans[tail - 1][0] = tail
    (trans, 1, @[s, tail])

proc accepts(trans: seq[seq[int]], init: int, finals: seq[int], word: seq[int]): bool =
    var s = init
    for v in word:
        if s <= 0: return false
        s = trans[s - 1][v - 1]
    s > 0 and s in finals

proc bruteHamming(trans: seq[seq[int]], init: int, finals: seq[int], word: seq[int]): int =
    result = word.len + 1
    let n = word.len
    for mask in 0..<(1 shl n):
        var w = newSeq[int](n)
        for i in 0..<n: w[i] = (if (mask shr i and 1) == 1: 2 else: 1)
        if accepts(trans, init, finals, w):
            var d = 0
            for i in 0..<n:
                if w[i] != word[i]: inc d
            result = min(result, d)

suite "MZNC 2026 features":

    test "regular Hamming penalty equals brute-force distance; deltas consistent":
        randomize(4242)
        for blocks in [@[2, 1], @[3], @[1, 1, 1], @[2, 2]]:
            let (trans, init, finals) = lineDfa(blocks)
            let n = 8
            let positions = toSeq(0..<n)
            let rc = newRegularConstraint[int](positions, trans.len, 1, 2, trans, init, finals)
            check rc.useHamming
            for trial in 0..<30:
                var word = newSeq[int](n)
                for i in 0..<n: word[i] = 1 + rand(1)
                rc.initialize(word)
                check rc.cost == bruteHamming(trans, init, finals, word)
                # moveDelta matches recompute; updatePosition keeps cost exact
                for i in 0..<n:
                    let nv = 3 - word[i]
                    var w2 = word
                    w2[i] = nv
                    let expected = bruteHamming(trans, init, finals, w2) - rc.cost
                    check rc.moveDelta(i, word[i], nv) == expected
                let i = rand(n - 1)
                word[i] = 3 - word[i]
                rc.updatePosition(i, word[i])
                check rc.cost == bruteHamming(trans, init, finals, word)

    test "nonogram 5x5 solved with Hamming regular + line moves":
        # Picture (rows):  .X.X.  XXXXX  .XXX.  ..X..  .X.X.
        let rows = @[@[1, 1], @[5], @[3], @[1], @[1, 1]]
        let cols = @[@[1], @[3, 1], @[3], @[3, 1], @[1]]
        var sys = initConstraintSystem[int]()
        var grid = sys.newConstrainedSequence(25)
        grid.setDomain(@[1, 2])
        for r in 0..<5:
            let (t, i0, f) = lineDfa(rows[r])
            sys.addConstraint(regular[int](toSeq(r*5 ..< r*5 + 5), t.len, 1, 2, t, i0, f))
        for c in 0..<5:
            let (t, i0, f) = lineDfa(cols[c])
            sys.addConstraint(regular[int](@[c, 5 + c, 10 + c, 15 + c, 20 + c], t.len, 1, 2, t, i0, f))
        sys.resolve(parallel = true, tabuThreshold = 10000)
        let a = grid.assignment()
        for r in 0..<5:
            let (t, i0, f) = lineDfa(rows[r])
            check accepts(t, i0, f, a[r*5 ..< r*5 + 5])
        for c in 0..<5:
            let (t, i0, f) = lineDfa(cols[c])
            check accepts(t, i0, f, @[a[c], a[5 + c], a[10 + c], a[15 + c], a[20 + c]])

    test "fzn_nvalue with constant count and literal entries":
        let src = """
var 1..4: x1;
var 1..4: x2;
var 1..4: x3;
array [1..3] of var int: x:: output_array([1..3]) = [x1,x2,x3];
constraint fzn_nvalue(2, [x1, x2, x3, 4]);
constraint int_ne(x1, x2);
solve satisfy;
"""
        var tr = translate(parseFzn(src))
        tr.sys.resolve(parallel = true, tabuThreshold = 5000)
        var vals = @[4]
        for pos in tr.arrayPositions["x"]: vals.add(tr.sys.assignment[pos])
        check vals.toHashSet.len == 2

    test "constant (presolved) objective is recognised":
        let src = """
int: X_INTRODUCED_9_ = 726404;
var 0..1: a;
var 0..1: b;
constraint int_ne(a, b);
solve minimize X_INTRODUCED_9_;
"""
        let tr = translate(parseFzn(src))
        check tr.objectivePos == ObjPosConstant

    test "move scoring sees constraints through int_times expression channels":
        # Loads are weighted-count channels (bin_packing_load), squares are
        # int_times expression channels, and the only violated constraint is a
        # bound on the sum of squares. Every move's predicted delta (penalty map
        # via cascades, and costDelta via the per-value fallback) must equal the
        # actual cost change; before expression channels joined the cascades /
        # fallback worklist, these predictions ignored the squares entirely.
        let src = """
var 1..2: b1;
var 1..2: b2;
var 1..2: b3;
var 1..2: b4;
var 1..2: b5;
var 1..2: b6;
var 0..12: l1;
var 0..12: l2;
var 0..144: s1 ::var_is_introduced :: is_defined_var;
var 0..144: s2 ::var_is_introduced :: is_defined_var;
array [1..6] of var int: bins:: output_array([1..6]) = [b1,b2,b3,b4,b5,b6];
constraint fzn_bin_packing_load([l1,l2],[b1,b2,b3,b4,b5,b6],[3,3,2,2,1,1]);
constraint int_times(l1,l1,s1):: defines_var(s1);
constraint int_times(l2,l2,s2):: defines_var(s2);
constraint int_lin_le([1,1],[s1,s2],72);
solve satisfy;
"""
        var tr = translate(parseFzn(src))
        tr.sys.baseArray.reducedDomain = reduceDomain(tr.sys.baseArray)
        tr.sys.baseArray.sharedDomainPtr = addr tr.sys.baseArray.reducedDomain
        let st = newTabuState[int](tr.sys.baseArray, @[1, 1, 1, 1, 1, 1] &
            newSeq[int](tr.sys.baseArray.len - 6))
        var checked = 0
        for round in 0..<3:
            for pos in tr.arrayPositions["bins"]:
                let cur = st.assignment[pos]
                let v = 3 - cur
                let predictedMap = st.penaltyAt(pos, v)
                let predictedCd = st.costDelta(pos, v)
                let before = st.cost
                st.assignValue(pos, v)
                let actual = st.cost - before
                check predictedMap == actual
                check predictedCd == actual
                inc checked
        check checked == 18
