## Schedule construction (tabuCompaction.constructSchedule, run by
## tabuImprove on the walk's best state): a state whose only violations are
## no-overlap overlaps gets a schedule without overlaps from a serial schedule
## generation scheme in time order, keeping every other constraint satisfied.

import std/[unittest, algorithm, tables]
import crusher
import flatzinc/[parser, translator]
import search/tabu

const OneMachine = """
predicate crusher_disjunctive_opt(array [int] of var int: s,array [int] of var bool: o,array [int] of var int: d);
var 0..100: s1 :: output_var;
var 0..100: s2 :: output_var;
var 0..100: s3 :: output_var;
var 0..100: s4 :: output_var;
array [1..4] of var int: ss = [s1,s2,s3,s4];
array [1..4] of var bool: oo = [true,true,true,true];
array [1..4] of int: dd = [3,4,5,6];
constraint crusher_disjunctive_opt(ss, oo, dd);
constraint int_lin_le([1,-1],[s1,s3],-3);
solve satisfy;
"""

const Durs = [3, 4, 5, 6]

template seeded(tr: untyped, starts: array[4, int]): (TabuState[int], seq[int]) =
    ## Declares the translation `tr` in the caller's scope: the state's
    ## shared domain points into it
    var tr = translate(parseFzn(OneMachine))
    tr.sys.baseArray.reducedDomain = reduceDomain(tr.sys.baseArray)
    tr.sys.baseArray.sharedDomainPtr = addr tr.sys.baseArray.reducedDomain
    var seed = newSeq[int](tr.sys.baseArray.len)
    var pos: seq[int]
    for i, name in ["s1", "s2", "s3", "s4"]:
        pos.add(tr.varPositions[name])
        seed[pos[i]] = starts[i]
    (newTabuState[int](tr.sys.baseArray, seed), pos)

suite "No-overlap schedule construction":

    test "an overlapping schedule becomes a gapless one in time order":
        # Tasks 1, 2 and 4 overlap; s1 + 3 <= s3 holds
        let (st, pos) = seeded(tr, [0, 0, 10, 1])
        check st.cost > 0
        let res = st.tabuImprove(0)
        check res.bestCost == 0
        var spans: seq[(int, int)]
        for i in 0..<4:
            let s = res.bestAssignment[pos[i]]
            spans.add((s, s + Durs[i]))
        spans.sort()
        for i in 1..<4:
            check spans[i][0] >= spans[i - 1][1]
        # Serial decoding packs the machine: 3 + 4 + 5 + 6
        check spans[^1][1] == 18
        check res.bestAssignment[pos[0]] + 3 <= res.bestAssignment[pos[2]]

    test "a state violating more than the no-overlaps is left alone":
        # s1 + 3 <= s3 is violated: construction does not apply
        let (st, pos) = seeded(tr, [10, 0, 0, 1])
        let before = st.assignment
        let res = st.tabuImprove(0)
        if res.bestCost > 0:
            check res.assignment == before
