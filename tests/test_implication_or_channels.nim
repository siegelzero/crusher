## Tests for implication-OR channel detection:
## detectImplicationOrChannels recognizes the pattern
##   int_eq_reif(V, 1, B)        :: defines_var(B)
##   int_ne_reif(W_i, 1, N_i)    :: defines_var(N_i)
##   bool_clause([N_i, B], [])                       -- W_i = 1 → V = 1
## When V is held high by ≥ 2 such implications, channelize V = OR(W_i).
##
## Originally motivated by sdn-chain (MZN Challenge 2020), where this pattern
## traps single-flip tabu local search at a delta = 0 plateau because each V's
## flip breaks multiple implications. Channelizing removes V from the search
## space and lets flips on the W_i positions propagate to V automatically.

import unittest
import std/[sequtils, sets, tables]
import crusher
import flatzinc/[parser, translator]

suite "Implication-OR Channel Detection":

  test "basic V = OR(W1, W2): two implications channelized":
    ## Two implications W_i = 1 → V = 1. V is binary, has no other channelization.
    ## Detector should turn V into a channel V = OR(W1, W2).
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "V" in tr.channelVarNames
    check tr.implicationOrChannelDefs.anyIt(it.targetVar == "V")
    let def = tr.implicationOrChannelDefs.filterIt(it.targetVar == "V")[0]
    check def.sourceVars.toHashSet() == ["W1", "W2"].toHashSet()

  test "single implication is not channelized":
    ## Only one forcer — pattern is too weak (could just leave as a constraint).
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint bool_clause([N1, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check not tr.implicationOrChannelDefs.anyIt(it.targetVar == "V")

  test "channel propagates V = OR(W1, W2, W3) at runtime":
    ## End-to-end: search forces W1=1, expect V=1 via channel.
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var 0..1: W3 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
var bool: N3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint int_ne_reif(W3, 1, N3) :: defines_var(N3);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
constraint bool_clause([N3, B], []);
constraint int_eq(W1, 1);
constraint int_eq(W2, 0);
constraint int_eq(W3, 0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "V" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let vVal = tr.sys.assignment[tr.varPositions["V"]]
    let w1Val = tr.sys.assignment[tr.varPositions["W1"]]
    check w1Val == 1
    check vVal == 1  # V = OR(1, 0, 0) = 1

  test "channel propagates V = 0 when all W_i = 0":
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
constraint int_eq(W1, 0);
constraint int_eq(W2, 0);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check "V" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let vVal = tr.sys.assignment[tr.varPositions["V"]]
    check vVal == 0  # V = OR(0, 0) = 0

  test "consumed bool_clauses are in definingConstraints":
    ## After channelization the 2-literal bool_clauses should be skipped during
    ## constraint translation (they're now structurally implied by the channel).
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "V" in tr.channelVarNames
    # Both bool_clause constraints should be in definingConstraints.
    var clauseCis: seq[int]
    for ci, con in model.constraints:
      if con.name == "bool_clause":
        clauseCis.add(ci)
    check clauseCis.len == 2
    for ci in clauseCis:
      check ci in tr.definingConstraints

  test "non-binary V is not channelized":
    ## V's domain isn't {0, 1}, so the OR encoding doesn't apply.
    let src = """
var 0..5: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # Detection records the candidate name-based, but the build phase rejects it
    # because V's domain isn't {0, 1}. We ensure no spurious channel binding shows up.
    let nBindingsAfter = tr.sys.baseArray.channelBindings.len
    # No build of an OR channel for V (V lacks a binary domain).
    # Look for a channelBinding whose channelPosition matches V's position.
    let vPos = tr.varPositions["V"]
    var orBindingForV = false
    for binding in tr.sys.baseArray.channelBindings:
      if binding.channelPosition == vPos:
        # Check if its array is the "OR encoding": [0, 1, 1, ..., 1].
        if binding.arrayElements.len >= 2 and
           binding.arrayElements[0].isConstant and binding.arrayElements[0].constantValue == 0 and
           binding.arrayElements[^1].isConstant and binding.arrayElements[^1].constantValue == 1:
          orBindingForV = true
    check not orBindingForV

  test "non-binary W is not channelized":
    ## W must be binary for the index-sum encoding to map correctly to OR.
    let src = """
var 0..1: V :: output_var;
var 0..5: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let vPos = tr.varPositions["V"]
    var orBindingForV = false
    for binding in tr.sys.baseArray.channelBindings:
      if binding.channelPosition == vPos:
        if binding.arrayElements.len >= 2 and
           binding.arrayElements[0].isConstant and binding.arrayElements[0].constantValue == 0 and
           binding.arrayElements[^1].isConstant and binding.arrayElements[^1].constantValue == 1:
          orBindingForV = true
    check not orBindingForV

  test "wrong reified value (V == 2 not V == 1) is not channelized":
    ## The implication W=1 → V=1 is encoded as int_eq_reif(V, 1, B). If the
    ## eq_reif checks V == 2 instead, the bool_clause means W=1 → V=2, which
    ## is a different (still valid) implication but doesn't fit the OR encoding
    ## V = OR(W_i). The detector must not false-positive on it.
    let src = """
var 0..3: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 2, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.implicationOrChannelDefs.anyIt(it.targetVar == "V")
    check "V" notin tr.channelVarNames

  test "wrong ne_reif value (W != 0 not W != 1) is not channelized":
    ## Mirror case for the source side: W != 0 → V = 1 doesn't fit the OR pattern
    ## (the encoding assumes the source forcer fires when W = 1).
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 0, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 0, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check not tr.implicationOrChannelDefs.anyIt(it.targetVar == "V")

  test "self-implication W = V is rejected at build time":
    ## Pathological case: an implication points back to V itself (V = 1 → V = 1).
    ## The detector groups it but the build phase must reject (wPos == vPos).
    ## We emit two implications so the dedup at detect time keeps both V→V and
    ## another forcer; the build then sees self-loop and skips the whole channel.
    let src = """
var 0..1: V :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: NV :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(V, 1, NV) :: defines_var(NV);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([NV, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    # Self-loop check happens in build phase; verify no OR-style channel
    # binding was actually built for V.
    if "V" in tr.varPositions:
      let vPos = tr.varPositions["V"]
      var orBindingForV = false
      for binding in tr.sys.baseArray.channelBindings:
        if binding.channelPosition == vPos:
          if binding.arrayElements.len >= 2 and
             binding.arrayElements[0].isConstant and binding.arrayElements[0].constantValue == 0 and
             binding.arrayElements[^1].isConstant and binding.arrayElements[^1].constantValue == 1:
            orBindingForV = true
      check not orBindingForV

  test "mixed: V1 channelized, V2 not (only 1 forcer)":
    ## Two targets in the same model; only V1 has 2+ forcers and gets channelized.
    let src = """
var 0..1: V1 :: output_var;
var 0..1: V2 :: output_var;
var 0..1: W1a :: output_var;
var 0..1: W1b :: output_var;
var 0..1: W2 :: output_var;
var bool: B1 :: var_is_introduced :: is_defined_var;
var bool: B2 :: var_is_introduced :: is_defined_var;
var bool: N1a :: var_is_introduced :: is_defined_var;
var bool: N1b :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V1, 1, B1) :: defines_var(B1);
constraint int_eq_reif(V2, 1, B2) :: defines_var(B2);
constraint int_ne_reif(W1a, 1, N1a) :: defines_var(N1a);
constraint int_ne_reif(W1b, 1, N1b) :: defines_var(N1b);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1a, B1], []);
constraint bool_clause([N1b, B1], []);
constraint bool_clause([N2, B2], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "V1" in tr.channelVarNames
    check tr.implicationOrChannelDefs.anyIt(it.targetVar == "V1")
    # V2 must NOT be claimed by the OR detector. (Other detectors like
    # case-analysis may still channelize V2 on a different path; that's fine.)
    check not tr.implicationOrChannelDefs.anyIt(it.targetVar == "V2")

  test "duplicate forcers are deduplicated":
    ## The same W appears in multiple bool_clauses (degenerate but valid).
    ## The detector should dedup so the OR has unique source positions.
    let src = """
var 0..1: V :: output_var;
var 0..1: W1 :: output_var;
var 0..1: W2 :: output_var;
var bool: B :: var_is_introduced :: is_defined_var;
var bool: N1 :: var_is_introduced :: is_defined_var;
var bool: N2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V, 1, B) :: defines_var(B);
constraint int_ne_reif(W1, 1, N1) :: defines_var(N1);
constraint int_ne_reif(W2, 1, N2) :: defines_var(N2);
constraint bool_clause([N1, B], []);
constraint bool_clause([N1, B], []);
constraint bool_clause([N2, B], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    let defs = tr.implicationOrChannelDefs.filterIt(it.targetVar == "V")
    check defs.len == 1
    # Sources should be {W1, W2}, not {W1, W1, W2}
    check defs[0].sourceVars.toHashSet() == ["W1", "W2"].toHashSet()
    check defs[0].sourceVars.len == 2

  test "SFC-style channel: count constraint reaches feasibility":
    ## Mini SFC: V1, V2 are forced by W's, count(V1+V2) = 1. With single-flip
    ## moves and graduated penalty, this is the failure mode that traps tabu in
    ## the real sdn-chain instance. Channelizing V1, V2 lets the count be
    ## satisfied by flipping W's directly.
    let src = """
var 0..1: V1 :: output_var;
var 0..1: V2 :: output_var;
var 0..1: W1a :: output_var;
var 0..1: W1b :: output_var;
var 0..1: W2a :: output_var;
var 0..1: W2b :: output_var;
var bool: B1 :: var_is_introduced :: is_defined_var;
var bool: B2 :: var_is_introduced :: is_defined_var;
var bool: N1a :: var_is_introduced :: is_defined_var;
var bool: N1b :: var_is_introduced :: is_defined_var;
var bool: N2a :: var_is_introduced :: is_defined_var;
var bool: N2b :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(V1, 1, B1) :: defines_var(B1);
constraint int_eq_reif(V2, 1, B2) :: defines_var(B2);
constraint int_ne_reif(W1a, 1, N1a) :: defines_var(N1a);
constraint int_ne_reif(W1b, 1, N1b) :: defines_var(N1b);
constraint int_ne_reif(W2a, 1, N2a) :: defines_var(N2a);
constraint int_ne_reif(W2b, 1, N2b) :: defines_var(N2b);
constraint bool_clause([N1a, B1], []);
constraint bool_clause([N1b, B1], []);
constraint bool_clause([N2a, B2], []);
constraint bool_clause([N2b, B2], []);
constraint int_lin_eq([1, 1], [V1, V2], 1);
constraint int_lin_eq([1, 1, 1, 1], [W1a, W1b, W2a, W2b], 1);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "V1" in tr.channelVarNames
    check "V2" in tr.channelVarNames
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

    let v1 = tr.sys.assignment[tr.varPositions["V1"]]
    let v2 = tr.sys.assignment[tr.varPositions["V2"]]
    let w1a = tr.sys.assignment[tr.varPositions["W1a"]]
    let w1b = tr.sys.assignment[tr.varPositions["W1b"]]
    let w2a = tr.sys.assignment[tr.varPositions["W2a"]]
    let w2b = tr.sys.assignment[tr.varPositions["W2b"]]
    check v1 + v2 == 1
    check w1a + w1b + w2a + w2b == 1
    # Channel consistency: V_i = OR(its W_i's)
    check v1 == max(w1a, w1b)
    check v2 == max(w2a, w2b)
