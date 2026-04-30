## Tests for ranking-pattern translation:
##   - detectFixedAllDifferent (Phase 1.1)
##   - detectPairLinLeTable + emitPairLinLeTable (Phase 1.2)
##   - detectRankingFromCounters + emitRankingChain (Phase 2)
##   - propagateRankingChainBounds (Phase 3)
##   - consumeRankingDecomposition + tryComputeRankingOutput (Phase 2B)
##   - emitRankingPairConstraints (Phase 4)

import unittest
import std/[tables, sets, strutils, osproc]
import crusher
import flatzinc/[parser, translator, output]
import constraints/types

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

proc resolveValue(tr: FznTranslator, varName: string): int =
    ## Resolve a variable's current value: real position, defining expression,
    ## or singleton parameter. Mirrors output.lookupVarValue (private).
    if varName in tr.varPositions:
        return tr.sys.assignment[tr.varPositions[varName]]
    if varName in tr.definedVarExprs:
        return tr.definedVarExprs[varName].evaluate(tr.sys.assignment)
    if varName in tr.paramValues:
        return tr.paramValues[varName]
    raise newException(KeyError, "Cannot resolve var '" & varName & "'")

# ---------------------------------------------------------------------------
# Phase 1.1: detectFixedAllDifferent
# ---------------------------------------------------------------------------

suite "detectFixedAllDifferent":

    test "all-literal alldifferent over distinct constants is dropped":
        let src = """
array [1..3] of int: c = [3, 1, 2];
var 1..10: x :: output_var;
constraint int_eq(x, 5);
constraint fzn_all_different_int([3, 1, 2]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # The all-literal alldifferent should have been consumed.
        var nAlldiffInSystem = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType == AllDifferentType: inc nAlldiffInSystem
        check nAlldiffInSystem == 0

    test "all-literal alldifferent with duplicates is left in place (UNSAT signal)":
        let src = """
var 1..10: x :: output_var;
constraint int_eq(x, 5);
constraint fzn_all_different_int([1, 2, 1]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # The duplicate-literal alldifferent must NOT be silently dropped —
        # the existing translation creates an allDifferent constraint that
        # carries a permanent positive cost. (Crusher reports UNKNOWN for
        # such infeasibility; we just check the constraint stays alive.)
        var nAlldiffInSystem = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType == AllDifferentType: inc nAlldiffInSystem
        check nAlldiffInSystem == 1

    test "mixed literal/var alldifferent is NOT dropped":
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
constraint fzn_all_different_int([x1, x2, 1]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        var nAlldiffInSystem = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType == AllDifferentType: inc nAlldiffInSystem
        check nAlldiffInSystem == 1

    test "alldifferent over a fully-fixed inline-initialized var array is dropped":
        ## An array decl with all-literal initializer survives in the FZN as
        ## `array of var ...` but every element is a literal. The detector
        ## walks model.variables for these and treats them like a constant
        ## array.
        let src = """
array [1..3] of var int: arr = [4, 7, 9];
var 1..10: x :: output_var;
constraint int_eq(x, 5);
constraint fzn_all_different_int(arr);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        var nAlldiffInSystem = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType == AllDifferentType: inc nAlldiffInSystem
        check nAlldiffInSystem == 0


# ---------------------------------------------------------------------------
# Phase 1.2: detectPairLinLeTable
# ---------------------------------------------------------------------------

suite "detectPairLinLeTable":

    test "complementary pair over {0,1,3} vars collapses to tableIn":
        ## Two int_lin_le's: a + b <= 3 AND -(a+b) <= -2 ⇒ 2 ≤ a+b ≤ 3.
        ## With dom(a) = dom(b) = {0,1,3}, allowed tuples are {(0,3),(3,0),(1,1)}.
        let src = """
var {0,1,3}: a :: output_var;
var {0,1,3}: b :: output_var;
constraint int_lin_le([1,1], [a,b], 3);
constraint int_lin_le([-1,-1], [a,b], -2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.pairLinLeTableDefs.len == 1
        check tr.pairLinLeTableDefs[0].tuples.len == 3
        var asSet: HashSet[seq[int]]
        for t in tr.pairLinLeTableDefs[0].tuples: asSet.incl(t)
        check @[0, 3] in asSet
        check @[3, 0] in asSet
        check @[1, 1] in asSet
        # Solve and verify the assignment is one of the allowed tuples.
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
        let av = tr.sys.assignment[tr.varPositions["a"]]
        let bv = tr.sys.assignment[tr.varPositions["b"]]
        check (av + bv) >= 2 and (av + bv) <= 3
        check av in {0, 1, 3}
        check bv in {0, 1, 3}

    test "non-complementary pair NOT collapsed":
        ## Two int_lin_le's whose coefficient vectors are NOT negations of
        ## each other should not match the detector.
        let src = """
var 0..5: a :: output_var;
var 0..5: b :: output_var;
constraint int_lin_le([1,1], [a,b], 5);
constraint int_lin_le([1,2], [a,b], 8);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.pairLinLeTableDefs.len == 0

    test "complementary pair over too-large domain product not collapsed":
        ## Cartesian product (10 × 10 = 100) > maxDomainProduct (256/X) — but
        ## actually 100 < 256 so this is borderline. Use a 4-var pair test
        ## where 4-vars × 16-domain blow past the limit.
        let src = """
var 0..30: a :: output_var;
var 0..30: b :: output_var;
constraint int_lin_le([1,1], [a,b], 60);
constraint int_lin_le([-1,-1], [a,b], 0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # Domain product 31*31 = 961 > 256 → skipped.
        check tr.pairLinLeTableDefs.len == 0

    test "same vars in different order across the pair still recognised":
        ## int_lin_le([1,2], [a,b], 5) and int_lin_le([-2,-1], [b,a], -3)
        ## have variables in different orders. The detector aligns them.
        let src = """
var 0..3: a :: output_var;
var 0..3: b :: output_var;
constraint int_lin_le([1,2], [a,b], 5);
constraint int_lin_le([-2,-1], [b,a], -3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check tr.pairLinLeTableDefs.len == 1


# ---------------------------------------------------------------------------
# Phase 2 / 2B / 3 / 4: ranking-from-counters end-to-end
# ---------------------------------------------------------------------------
#
# Constructing a faithful ECP-style FZN inline is verbose, so we exercise the
# pipeline against the real benchmark instances available in the repo. The
# tests check downstream invariants (chain emitted, decomposition consumed,
# output rules built) rather than exact constraint counts.

const BenchModelMzn = "minizinc_challenge/2020/soccer-computational/ecp.mzn"

proc compileEcp(dzn: string): string =
    ## Compiles an ECP instance to FZN via minizinc and returns the FZN text.
    let outPath = "/tmp/test_fzn_ranking_" & dzn.split('/')[^1].replace(".dzn", ".fzn")
    let cmd = "minizinc -c --solver minizinc/crusher.msc " &
              BenchModelMzn & " " & dzn & " -o " & outPath & " 2>/dev/null"
    let exitCode = execCmd(cmd)
    doAssert exitCode == 0, "minizinc compile failed for " & dzn
    return readFile(outPath)

proc parseEcp(dzn: string): FznModel =
    parseFzn(compileEcp("minizinc_challenge/2020/soccer-computational/" & dzn))

suite "Ranking-from-counters: full chain (xIGData_22_12_22_5)":
    ## All 22 teams pinned by op=1 positionConstraints.
    test "detect, propagate, consume — full chain":
        let model = parseEcp("xIGData_22_12_22_5.dzn")
        var tr = translate(model)

        # Phase 2: chain emission.
        check tr.rankingChainDefs.len == 1
        check tr.rankingChainDefs[0].orderedVarNames.len == 22

        # Phase 2B: consume → output rules for both worstPosition and bestPosition.
        check tr.rankingOutputRules.len == 2
        var arrayNames: HashSet[string]
        for r in tr.rankingOutputRules: arrayNames.incl(r.arrayName)
        check "worstPosition" in arrayNames
        check "bestPosition" in arrayNames
        # Both rule arrays should reference all 22 fp slots; one slot per
        # array may correspond to a MiniZinc-fixed literal (worstPos[i]=N or
        # bestPos[i]=1) and have an empty fp-name entry.
        for r in tr.rankingOutputRules:
            check r.indexFpVarNames.len == 22
            var nWithFp = 0
            for nm in r.indexFpVarNames:
                if nm != "": inc nWithFp
            check nWithFp >= 21
            check r.sourceFpVarNames.len == 22

        # No pair-link constraints needed for a full chain (chain alone enforces
        # the linkage; the pinned-pinned filter rejects all unordered pairs).
        check tr.rankingPairConstraintDefs.len == 0

    test "instance solves to a valid solution":
        let model = parseEcp("xIGData_22_12_22_5.dzn")
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 10000,
                       verbose = false)
        # Recover fPoints values for all 22 teams.
        var fpVals = newSeq[int](22)
        for i, vn in tr.arrayElementNames["fPoints"]:
            fpVals[i] = tr.resolveValue(vn)
        # Inverse permutation of finalPosition should sort fp descending
        # (ties allowed).
        let inversePerm = [14, 20, 1, 15, 18, 17, 9, 12, 7, 22, 21, 11, 13,
                           16, 4, 19, 3, 6, 10, 8, 5, 2]
        for k in 0 ..< 21:
            let prev = fpVals[inversePerm[k] - 1]
            let next = fpVals[inversePerm[k + 1] - 1]
            check prev >= next

    test "formatSolution output matches rule-computed worstPos/bestPos":
        ## After consuming the rank decomposition, worstPosition[] and
        ## bestPosition[] no longer have defining expressions; the FZN output
        ## writer falls through to tryComputeRankingOutput and reconstructs
        ## values directly from fp. This test drives a real solve, then
        ## independently recomputes worstPosition[i] = #{j : fp_j ≥ fp_i} and
        ## bestPosition[i] = 1 + #{j ≠ i : fp_j > fp_i} from the assignment
        ## and verifies the formatted output line carries those values.
        let model = parseEcp("xIGData_22_12_22_5.dzn")
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 10000,
                       verbose = false)
        # Recover fp values.
        var fpVals = newSeq[int](22)
        for i, vn in tr.arrayElementNames["fPoints"]:
            fpVals[i] = tr.resolveValue(vn)
        # Independent recompute.
        var expectedWorst = newSeq[int](22)
        var expectedBest = newSeq[int](22)
        for i in 0 ..< 22:
            for j in 0 ..< 22:
                if fpVals[j] >= fpVals[i]: inc expectedWorst[i]
            expectedBest[i] = 1
            for j in 0 ..< 22:
                if j != i and fpVals[j] > fpVals[i]: inc expectedBest[i]
        # Format and parse out the worstPosition / bestPosition arrays.
        let solStr = tr.formatSolution()
        proc parseArrayLine(text, name: string): seq[int] =
            for line in text.splitLines():
                if not line.startsWith(name & " ="): continue
                let lo = line.find('[')
                let hi = line.rfind(']')
                if lo < 0 or hi < 0: return @[]
                let body = line[lo + 1 ..< hi]
                for tok in body.split(','):
                    result.add(parseInt(tok.strip()))
                return
            return @[]
        let outWorst = parseArrayLine(solStr, "worstPosition")
        let outBest = parseArrayLine(solStr, "bestPosition")
        check outWorst.len == 22
        check outBest.len == 22
        for i in 0 ..< 22:
            check outWorst[i] == expectedWorst[i]
            check outBest[i] == expectedBest[i]


suite "Ranking-from-counters: partial chain (xIGData_24_24_16_1)":
    ## Only 16 of 24 teams pinned by op=1 positionConstraints. The remaining 8
    ## are linked to fPoints through pair-link disjunctive clauses.
    test "detect partial; pair-link constraints queued":
        let model = parseEcp("xIGData_24_24_16_1.dzn")
        var tr = translate(model)

        check tr.rankingChainDefs.len == 1
        # Pinned subset only — chain length matches the count of op=1 entries.
        check tr.rankingChainDefs[0].orderedVarNames.len == 16

        # Output rules still built for both arrays despite partial pinning.
        check tr.rankingOutputRules.len == 2

        # Pair-link defs queued: one per unordered pair that isn't both-pinned.
        # 24 teams: C(24, 2) = 276 unordered pairs. Both-pinned pairs:
        # C(16, 2) = 120 → skipped. Remaining: 276 - 120 = 156. Each def will
        # be emitted as a single 2-disjunct conjunction-clause covering both
        # ordering directions.
        check tr.rankingPairConstraintDefs.len == 156

    test "instance solves to a valid solution":
        let model = parseEcp("xIGData_24_24_16_1.dzn")
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 10000,
                       verbose = false)
        # Verify the rank-by-fp invariant: better finalPosition ⇔ at-least-as-many fp.
        var fpVals = newSeq[int](24)
        for i, vn in tr.arrayElementNames["fPoints"]:
            fpVals[i] = tr.resolveValue(vn)
        var finalPosVals = newSeq[int](24)
        for i, pos in tr.arrayPositions["finalPosition"]:
            if pos >= 0:
                finalPosVals[i] = tr.sys.assignment[pos]
            else:
                finalPosVals[i] = tr.resolveValue(
                    tr.arrayElementNames["finalPosition"][i])
        for i in 0 ..< 24:
            for j in (i + 1) ..< 24:
                if finalPosVals[i] < finalPosVals[j]:
                    check fpVals[i] >= fpVals[j]
                elif finalPosVals[i] > finalPosVals[j]:
                    check fpVals[i] <= fpVals[j]


# ---------------------------------------------------------------------------
# Phase 3: chain bound propagation
# ---------------------------------------------------------------------------

suite "propagateRankingChainBounds":
    ## A monotone chain over an array of vars must climb lower bounds upward
    ## and descend upper bounds downward. We exercise this against the full
    ## ECP instance (which Phase 2 detects as a 22-element decreasing chain)
    ## and check that at least some bounds were tightened.

    test "lb climbs upward / ub descends downward through the chain":
        let model = parseEcp("xIGData_22_12_22_5.dzn")
        var tr = translate(model)
        # Inverse permutation rank → team name (1-based ranks).
        let chain = tr.rankingChainDefs[0].orderedVarNames
        check chain.len == 22
        # After propagation, presolveDomains should contain entries for at
        # least one chain participant whose lb > the team's iPoints.
        # iPoints = [12,12,12,12,18,12,12,12,26,22,12,22,12,23,16,21,18,22,12,28,12,25]
        # The top-ranked team is team 14 (iPoints=23). Chain forces
        # fp[14] >= fp[20] = lb at least iPoints[20] = 28, so fp[14].lb >= 28.
        let team14Var = tr.arrayElementNames["fPoints"][13]   # 0-based
        check team14Var in tr.presolveDomains
        let team14Dom = tr.presolveDomains[team14Var]
        check team14Dom.len > 0
        check team14Dom[0] >= 28   # iPoints[20]
