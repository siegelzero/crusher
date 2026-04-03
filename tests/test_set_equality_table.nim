## Tests for the set-equality-to-table pattern detection.
## Covers detectSetEqualityTablePattern in translatorPatterns.nim:
##   - Pattern detection: non-defines_var set_union + array_set_element
##   - Chain tracing through defines_var set_union intermediates
##   - Source variable tracing through int_mod channels
##   - Constant source handling (fixed mod results)
##   - Domain reduction for index and source variables
##   - Correct solving with the consumed constraints

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]
import crusher
import flatzinc/[parser, translator, output]

suite "Set-Equality-to-Table Pattern Detection":

  test "2-voice pattern: set_union(sing1, sing2, target) without defines_var":
    ## Simplest case: 2 singleton sets directly unioned into the target set.
    ## No chain intermediates needed.
    ##
    ## Pattern:
    ##   int_mod(v1, 3, pc1), int_mod(v2, 3, pc2)
    ##   set_in(pc1, sing1), set_card(sing1, 1)
    ##   set_in(pc2, sing2), set_card(sing2, 1)
    ##   set_union(sing1, sing2, target)  -- NO defines_var = equality
    ##   array_set_element(idx, [{0,1},{1,2},{0,2}], target) :: defines_var(target)
    let src = """
var 0..8: v1 :: output_var;
var 0..8: v2 :: output_var;
var 1..3: idx :: output_var;
var 0..2: pc1 :: var_is_introduced;
var 0..2: pc2 :: var_is_introduced;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: target :: var_is_introduced :: is_defined_var;
constraint int_mod(v1, 3, pc1);
constraint int_mod(v2, 3, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint array_set_element(idx, [{0,1},{1,2},{0,2}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Pattern should be detected
    check tr.setEqualityTableDefs.len == 1
    check tr.setEqualityTableDefs[0].idxVarName == "idx"
    check tr.setEqualityTableDefs[0].sourceVarNames.len == 2
    check tr.setEqualityTableDefs[0].modulus == 3

    # Singleton set variables should be skipped
    check "sing1" in tr.skipSetVarNames
    check "sing2" in tr.skipSetVarNames

    # Solve and verify correctness
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let v1Val = tr.sys.assignment[tr.varPositions["v1"]]
    let v2Val = tr.sys.assignment[tr.varPositions["v2"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]

    let pc1Val = v1Val mod 3
    let pc2Val = v2Val mod 3
    let chordSets = [@[0, 1], @[1, 2], @[0, 2]]
    let targetSet = toHashSet(chordSets[idxVal - 1])

    # Membership: each pitch class must be in the chord set
    check pc1Val in targetSet
    check pc2Val in targetSet
    # Coverage: the chord set must be covered
    check toHashSet([pc1Val, pc2Val]) == targetSet

  test "3-voice pattern: chain + equality union":
    ## 3 voices require one chain intermediate:
    ##   set_union(sing1, sing2, intermediate) :: defines_var(intermediate)
    ##   set_union(intermediate, sing3, target)  -- equality
    ##   array_set_element(idx, sets, target) :: defines_var(target)
    let src = """
var 0..11: v1 :: output_var;
var 0..11: v2 :: output_var;
var 0..11: v3 :: output_var;
var 1..3: idx :: output_var;
var 0..3: pc1 :: var_is_introduced;
var 0..3: pc2 :: var_is_introduced;
var 0..3: pc3 :: var_is_introduced;
var set of 0..3: sing1 :: var_is_introduced;
var set of 0..3: sing2 :: var_is_introduced;
var set of 0..3: sing3 :: var_is_introduced;
var set of 0..3: intermediate :: var_is_introduced :: is_defined_var;
var set of 0..3: target :: var_is_introduced :: is_defined_var;
constraint int_mod(v1, 4, pc1);
constraint int_mod(v2, 4, pc2);
constraint int_mod(v3, 4, pc3);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_in(pc3, sing3);
constraint set_card(sing3, 1);
constraint set_union(sing1, sing2, intermediate) :: defines_var(intermediate);
constraint set_union(intermediate, sing3, target);
constraint array_set_element(idx, [{0,1,2},{1,2,3},{0,2,3}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Pattern should be detected with chain tracing
    check tr.setEqualityTableDefs.len == 1
    check tr.setEqualityTableDefs[0].sourceVarNames.len == 3
    check tr.setEqualityTableDefs[0].modulus == 4

    # Chain intermediate should be skipped
    check "intermediate" in tr.skipSetVarNames
    check "sing1" in tr.skipSetVarNames
    check "sing2" in tr.skipSetVarNames
    check "sing3" in tr.skipSetVarNames

    # Solve and verify
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let v1Val = tr.sys.assignment[tr.varPositions["v1"]]
    let v2Val = tr.sys.assignment[tr.varPositions["v2"]]
    let v3Val = tr.sys.assignment[tr.varPositions["v3"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]

    let chordSets = [@[0, 1, 2], @[1, 2, 3], @[0, 2, 3]]
    let targetSet = toHashSet(chordSets[idxVal - 1])
    let coveredSet = toHashSet([v1Val mod 4, v2Val mod 4, v3Val mod 4])

    # Membership
    check (v1Val mod 4) in targetSet
    check (v2Val mod 4) in targetSet
    check (v3Val mod 4) in targetSet
    # Coverage
    check targetSet <= coveredSet

  test "pattern with constant source (fixed voice)":
    ## One voice is fixed (constant mod result), like soprano in Harmony.
    ## int_mod(5, 3, pc1) → pc1 = 2 (constant).
    ## The pattern should still detect and handle this.
    let src = """
var 0..8: v2 :: output_var;
var 1..3: idx :: output_var;
var 0..2: pc1 :: var_is_introduced;
var 0..2: pc2 :: var_is_introduced;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: target :: var_is_introduced :: is_defined_var;
constraint int_mod(5, 3, pc1);
constraint int_mod(v2, 3, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint array_set_element(idx, [{0,2},{1,2},{0,1}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Pattern should be detected even with constant source
    check tr.setEqualityTableDefs.len == 1
    check tr.setEqualityTableDefs[0].modulus == 3

    # Solve and verify
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let v2Val = tr.sys.assignment[tr.varPositions["v2"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]

    # pc1 is fixed at 5 mod 3 = 2
    let pc1Val = 2
    let pc2Val = v2Val mod 3
    let chordSets = [@[0, 2], @[1, 2], @[0, 1]]
    let targetSet = toHashSet(chordSets[idxVal - 1])

    check pc1Val in targetSet
    check pc2Val in targetSet
    check toHashSet([pc1Val, pc2Val]) == targetSet

  test "no detection when defines_var is on the equality union":
    ## If the set_union HAS defines_var, it's a channel, not an equality.
    ## The pattern should NOT be detected.
    let src = """
var 0..8: v1 :: output_var;
var 0..8: v2 :: output_var;
var 1..2: idx :: output_var;
var 0..2: pc1 :: var_is_introduced;
var 0..2: pc2 :: var_is_introduced;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: result :: var_is_introduced :: is_defined_var;
var set of 0..2: target :: var_is_introduced :: is_defined_var;
constraint int_mod(v1, 3, pc1);
constraint int_mod(v2, 3, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, result) :: defines_var(result);
constraint array_set_element(idx, [{0,1},{1,2}], target) :: defines_var(target);
constraint set_eq(result, target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # No set-equality-to-table pattern — the union has defines_var
    check tr.setEqualityTableDefs.len == 0

  test "no detection when target is not from array_set_element":
    ## set_union(sing1, sing2, target) without defines_var, but target
    ## is NOT defined by array_set_element. Pattern should not match.
    let src = """
var 0..8: v1 :: output_var;
var 0..8: v2 :: output_var;
var 0..2: pc1 :: var_is_introduced;
var 0..2: pc2 :: var_is_introduced;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: target :: var_is_introduced;
constraint int_mod(v1, 3, pc1);
constraint int_mod(v2, 3, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint set_eq(target, {0, 1});
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.setEqualityTableDefs.len == 0

  test "domain reduction from pattern: idx restricted by fixed source":
    ## If a source has a fixed pitch class, the idx domain should be restricted
    ## to chords that contain that pitch class.
    ## pc1 is fixed at 0 (v1=6, mod 3). Only chords {0,1} and {0,2} contain 0.
    let src = """
var 0..8: v2 :: output_var;
var 1..3: idx :: output_var;
var 0..2: pc1 :: var_is_introduced;
var 0..2: pc2 :: var_is_introduced;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: target :: var_is_introduced :: is_defined_var;
constraint int_mod(6, 3, pc1);
constraint int_mod(v2, 3, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint array_set_element(idx, [{0,1},{1,2},{0,2}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.setEqualityTableDefs.len == 1

    # idx domain should be restricted: chord {1,2} does NOT contain pitch class 0
    # So idx=2 should be excluded. Valid: idx=1 ({0,1}) and idx=3 ({0,2}).
    if "idx" in tr.presolveDomains:
      let idxDom = tr.presolveDomains["idx"]
      check 1 in idxDom
      check 2 notin idxDom  # {1,2} doesn't contain 0
      check 3 in idxDom

  test "multiple patterns: separate timesteps detected independently":
    ## Two independent patterns (like two timesteps) should both be detected.
    let src = """
var 0..5: v1a :: output_var;
var 0..5: v2a :: output_var;
var 1..2: idxA :: output_var;
var 0..5: v1b :: output_var;
var 0..5: v2b :: output_var;
var 1..2: idxB :: output_var;
var 0..2: pc1a :: var_is_introduced;
var 0..2: pc2a :: var_is_introduced;
var 0..2: pc1b :: var_is_introduced;
var 0..2: pc2b :: var_is_introduced;
var set of 0..2: sA1 :: var_is_introduced;
var set of 0..2: sA2 :: var_is_introduced;
var set of 0..2: sB1 :: var_is_introduced;
var set of 0..2: sB2 :: var_is_introduced;
var set of 0..2: tA :: var_is_introduced :: is_defined_var;
var set of 0..2: tB :: var_is_introduced :: is_defined_var;
constraint int_mod(v1a, 3, pc1a);
constraint int_mod(v2a, 3, pc2a);
constraint set_in(pc1a, sA1);
constraint set_card(sA1, 1);
constraint set_in(pc2a, sA2);
constraint set_card(sA2, 1);
constraint set_union(sA1, sA2, tA);
constraint array_set_element(idxA, [{0,1},{1,2}], tA) :: defines_var(tA);
constraint int_mod(v1b, 3, pc1b);
constraint int_mod(v2b, 3, pc2b);
constraint set_in(pc1b, sB1);
constraint set_card(sB1, 1);
constraint set_in(pc2b, sB2);
constraint set_card(sB2, 1);
constraint set_union(sB1, sB2, tB);
constraint array_set_element(idxB, [{0,1},{1,2}], tB) :: defines_var(tB);
constraint int_lin_ne([1,-1],[idxA,idxB],0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Two separate patterns detected
    check tr.setEqualityTableDefs.len == 2

    # Both should have 2 source vars, modulus 3
    for def in tr.setEqualityTableDefs:
      check def.sourceVarNames.len == 2
      check def.modulus == 3

    # Solve and verify
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let idxAVal = tr.sys.assignment[tr.varPositions["idxA"]]
    let idxBVal = tr.sys.assignment[tr.varPositions["idxB"]]
    check idxAVal != idxBVal

  test "constraint reduction: fewer constraints after detection":
    ## Verify that detected constraints are consumed (skipped), reducing
    ## the total constraint count.
    let src = """
var 0..8: v1 :: output_var;
var 0..8: v2 :: output_var;
var 1..2: idx :: output_var;
var 0..2: pc1 :: var_is_introduced;
var 0..2: pc2 :: var_is_introduced;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: target :: var_is_introduced :: is_defined_var;
constraint int_mod(v1, 3, pc1);
constraint int_mod(v2, 3, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint array_set_element(idx, [{0,1},{1,2}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.setEqualityTableDefs.len == 1

    # 4 constraints consumed: set_in(pc1), set_card(sing1), set_in(pc2), set_card(sing2)
    # + 1 equality union
    # = 5 consumed constraints
    let def = tr.setEqualityTableDefs[0]
    check def.consumedCIs.len >= 5  # set_in×2 + set_card×2 + equality union

  test "no mod: direct variables in singleton sets":
    ## Source variables are used directly (no int_mod). This tests the
    ## fallback path where x_i is used as-is.
    let src = """
var 0..2: v1 :: output_var;
var 0..2: v2 :: output_var;
var 1..2: idx :: output_var;
var set of 0..2: sing1 :: var_is_introduced;
var set of 0..2: sing2 :: var_is_introduced;
var set of 0..2: target :: var_is_introduced :: is_defined_var;
constraint set_in(v1, sing1);
constraint set_card(sing1, 1);
constraint set_in(v2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint array_set_element(idx, [{0,1},{1,2}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.setEqualityTableDefs.len == 1
    check tr.setEqualityTableDefs[0].modulus == 0  # no mod
    check tr.setEqualityTableDefs[0].sourceVarNames.len == 2

    # Solve and verify
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let v1Val = tr.sys.assignment[tr.varPositions["v1"]]
    let v2Val = tr.sys.assignment[tr.varPositions["v2"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]

    let chordSets = [@[0, 1], @[1, 2]]
    let targetSet = toHashSet(chordSets[idxVal - 1])
    check v1Val in targetSet
    check v2Val in targetSet
    check toHashSet([v1Val, v2Val]) == targetSet

  test "4-voice pattern with deep chain":
    ## 4 voices = 2 chain unions + 1 equality union, like the actual Harmony.
    let src = """
var 0..11: v1 :: output_var;
var 0..11: v2 :: output_var;
var 0..11: v3 :: output_var;
var 0..11: v4 :: output_var;
var 1..3: idx :: output_var;
var 0..3: pc1 :: var_is_introduced;
var 0..3: pc2 :: var_is_introduced;
var 0..3: pc3 :: var_is_introduced;
var 0..3: pc4 :: var_is_introduced;
var set of 0..3: sing1 :: var_is_introduced;
var set of 0..3: sing2 :: var_is_introduced;
var set of 0..3: sing3 :: var_is_introduced;
var set of 0..3: sing4 :: var_is_introduced;
var set of 0..3: int1 :: var_is_introduced :: is_defined_var;
var set of 0..3: int2 :: var_is_introduced :: is_defined_var;
var set of 0..3: target :: var_is_introduced :: is_defined_var;
constraint int_mod(v1, 4, pc1);
constraint int_mod(v2, 4, pc2);
constraint int_mod(v3, 4, pc3);
constraint int_mod(v4, 4, pc4);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_in(pc3, sing3);
constraint set_card(sing3, 1);
constraint set_in(pc4, sing4);
constraint set_card(sing4, 1);
constraint set_union(sing1, sing2, int1) :: defines_var(int1);
constraint set_union(int1, sing3, int2) :: defines_var(int2);
constraint set_union(int2, sing4, target);
constraint array_set_element(idx, [{0,1,2},{1,2,3},{0,1,3}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.setEqualityTableDefs.len == 1
    check tr.setEqualityTableDefs[0].sourceVarNames.len == 4
    check tr.setEqualityTableDefs[0].modulus == 4

    # All intermediates and singletons should be skipped
    check "int1" in tr.skipSetVarNames
    check "int2" in tr.skipSetVarNames
    check "sing1" in tr.skipSetVarNames
    check "sing2" in tr.skipSetVarNames
    check "sing3" in tr.skipSetVarNames
    check "sing4" in tr.skipSetVarNames

    # Solve and verify
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]
    let chordSets = [@[0, 1, 2], @[1, 2, 3], @[0, 1, 3]]
    let targetSet = toHashSet(chordSets[idxVal - 1])

    var coveredSet: HashSet[int]
    for name in ["v1", "v2", "v3", "v4"]:
      let val = tr.sys.assignment[tr.varPositions[name]]
      let pc = val mod 4
      check pc in targetSet
      coveredSet.incl(pc)

    check targetSet <= coveredSet

  test "offset from int_lin_eq defined var (Harmony-like pattern)":
    ## Models the actual Harmony FlatZinc pattern where pitch class computation
    ## goes through a defined intermediate: y = v - 1, pc = y mod 4.
    ## The table must use f(v) = (v - 1) mod 4 when generating tuples.
    let src = """
var 1..8: v1 :: output_var;
var 1..8: v2 :: output_var;
var 1..3: idx :: output_var;
var 0..127: y1 :: var_is_introduced :: is_defined_var;
var 0..127: y2 :: var_is_introduced :: is_defined_var;
var 0..3: pc1 :: var_is_introduced;
var 0..3: pc2 :: var_is_introduced;
var set of 0..3: sing1 :: var_is_introduced;
var set of 0..3: sing2 :: var_is_introduced;
var set of 0..3: target :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([1,-1],[v1,y1],1) :: defines_var(y1);
constraint int_lin_eq([1,-1],[v2,y2],1) :: defines_var(y2);
constraint int_mod(y1, 4, pc1);
constraint int_mod(y2, 4, pc2);
constraint set_in(pc1, sing1);
constraint set_card(sing1, 1);
constraint set_in(pc2, sing2);
constraint set_card(sing2, 1);
constraint set_union(sing1, sing2, target);
constraint array_set_element(idx, [{0,1},{1,2},{0,2}], target) :: defines_var(target);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Pattern should be detected with offset
    check tr.setEqualityTableDefs.len == 1
    check tr.setEqualityTableDefs[0].modulus == 4
    # Source offsets should be 1 (from int_lin_eq)
    for off in tr.setEqualityTableDefs[0].sourceOffsets:
      check off == 1

    # Solve and verify
    tr.sys.resolve(parallel = true, tabuThreshold = 10000, verbose = false)

    let v1Val = tr.sys.assignment[tr.varPositions["v1"]]
    let v2Val = tr.sys.assignment[tr.varPositions["v2"]]
    let idxVal = tr.sys.assignment[tr.varPositions["idx"]]

    # Pitch class = (v - 1) mod 4
    let pc1Val = (v1Val - 1) mod 4
    let pc2Val = (v2Val - 1) mod 4
    let chordSets = [@[0, 1], @[1, 2], @[0, 2]]
    let targetSet = toHashSet(chordSets[idxVal - 1])

    check pc1Val in targetSet
    check pc2Val in targetSet
    check toHashSet([pc1Val, pc2Val]) == targetSet
