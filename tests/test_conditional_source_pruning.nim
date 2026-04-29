## Tests for the conditional-source channel + clause-pruning extensions
## (translatorCaseAnalysis.nim, translatorChannels.nim).
##
## Three behaviours are covered:
##   1. derive2LitClauseCondVals — picks up the "else" branch from a
##      no-neg 2-literal disjunction clause [cond_reif, eq_reif]. Without
##      this the detector saw only the implication clauses and built
##      tautological "T = T" defaults for non-cond values.
##   2. Synthetic source-var lists (ConditionalSourceDef.sourceVars) —
##      lets the detector handle ITE patterns whose branches read from
##      different declared FZN arrays. The legacy path needed a single
##      common array.
##   3. pruneClausesImpliedByConditionalSource — strips bool_clauses and
##      tr.disjunctiveClauses entries that are tautologically satisfied
##      once the channel is built. Catches the lot-sizing case where
##      14+14 phantom clauses produced 65% of the initial cost.

import unittest
import std/[sequtils, sets, strutils, tables]
import crusher
import flatzinc/[parser, translator]


suite "Conditional-source: derive condVals from no-neg disjunction":

  test "2-cond: implication + disjunction → both branches mapped":
    ## ITE pattern: T = if cond==0 then a else b.
    ## Encoded as:
    ##   b_then = (T == a)        -- target-eq for "then" branch
    ##   b_else = (T == b)        -- target-eq for "else" branch
    ##   b_cond = (cond == 0)     -- cond reif
    ##   bool_clause([b_then], [b_cond])      -- (cond==0)  → (T == a)
    ##   bool_clause([b_cond, b_else], [])    -- (cond==0) ∨ (T == b)
    ##
    ## The detector must read the second clause as "¬(cond==0) → (T == b)"
    ## so it learns b_else's condVals = condDom \ {0} = {1}. Otherwise it
    ## sees only one source mapping and builds a tautological default.
    let src = """
var 0..1: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: t :: output_var;
array [1..2] of var int: src_arr ::var_is_introduced = [a, b];
var bool: b_cond ::var_is_introduced ::is_defined_var;
var bool: b_then ::var_is_introduced ::is_defined_var;
var bool: b_else ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond) :: defines_var(b_cond);
constraint int_eq_reif(t, a, b_then) :: defines_var(b_then);
constraint int_eq_reif(t, b, b_else) :: defines_var(b_else);
constraint bool_clause([b_then], [b_cond]);
constraint bool_clause([b_cond, b_else], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # T should be detected as a conditional-source channel.
    check "t" in tr.channelVarNames
    check tr.conditionalSourceDefs.len == 1

    let def = tr.conditionalSourceDefs[0]
    check def.targetVarName == "t"
    check def.condVarName == "cond"
    # Both cond values must be covered: cond=0 → slot 1 (a), cond=1 → slot 2 (b).
    # Either legacy form (sourceMap into src_arr) or synthetic (sourceVars).
    if def.sourceVars.len > 0:
      # Synthetic shape — direct per-condDom var names.
      check def.sourceVars == @["a", "b"]
    else:
      check def.sourceArrayName == "src_arr"
      check def.sourceMap == @[1, 2]


suite "Conditional-source: synthetic sourceVars across arrays":

  test "branches in different declared arrays produce sourceVars":
    ## "Then" reads from arr_then[1] = a; "else" reads from arr_else[1] = b.
    ## a and b live in different declared arrays, so the legacy "common
    ## declared array" path can't fire. The synthetic-sourceVars fallback
    ## should still build a def listing [a, b].
    let src = """
var 0..1: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: t :: output_var;
array [1..1] of var int: arr_then ::var_is_introduced = [a];
array [1..1] of var int: arr_else ::var_is_introduced = [b];
var bool: b_cond ::var_is_introduced ::is_defined_var;
var bool: b_then ::var_is_introduced ::is_defined_var;
var bool: b_else ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond) :: defines_var(b_cond);
constraint int_eq_reif(t, a, b_then) :: defines_var(b_then);
constraint int_eq_reif(t, b, b_else) :: defines_var(b_else);
constraint bool_clause([b_then], [b_cond]);
constraint bool_clause([b_cond, b_else], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check "t" in tr.channelVarNames
    check tr.conditionalSourceDefs.len == 1
    let def = tr.conditionalSourceDefs[0]
    # No single declared array contains both a and b → synthetic path.
    check def.sourceVars == @["a", "b"]
    check def.sourceArrayName == ""


suite "Conditional-source: clause pruning":

  test "implication and disjunction clauses are both pruned":
    ## Same pattern as the first test. After detection + prune, neither
    ## the implication clause nor the disjunction clause should remain
    ## as a residual constraint:
    ##   - implication ends up in tr.definingConstraints (consumed)
    ##   - disjunction is removed from tr.disjunctiveClauses
    let src = """
var 0..1: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: t :: output_var;
array [1..2] of var int: src_arr ::var_is_introduced = [a, b];
var bool: b_cond ::var_is_introduced ::is_defined_var;
var bool: b_then ::var_is_introduced ::is_defined_var;
var bool: b_else ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond) :: defines_var(b_cond);
constraint int_eq_reif(t, a, b_then) :: defines_var(b_then);
constraint int_eq_reif(t, b, b_else) :: defines_var(b_else);
constraint bool_clause([b_then], [b_cond]);
constraint bool_clause([b_cond, b_else], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    check tr.conditionalSourceDefs.len == 1
    # Both clauses should be either consumed (defining) or absent from
    # the disjunctive-clauses pool. Locate their constraint indices.
    var implCi = -1
    var disjCi = -1
    for ci, con in tr.model.constraints:
      if con.name != "bool_clause": continue
      if con.args.len < 2: continue
      let pos = con.args[0]
      let neg = con.args[1]
      if pos.kind != FznArrayLit or neg.kind != FznArrayLit: continue
      if neg.elems.len == 1: implCi = ci
      elif neg.elems.len == 0 and pos.elems.len == 2: disjCi = ci
    check implCi >= 0
    check disjCi >= 0
    # Implication clause should be marked defining (consumed by prune).
    check implCi in tr.definingConstraints
    # Disjunction clause should NOT survive in tr.disjunctiveClauses
    # (detectDisjunctivePairs emits it; the prune pass removes it).
    for clause in tr.disjunctiveClauses:
      # If the disjunction clause survived, its sourceBools would name
      # the eq_reifs from this test.
      check clause.sourceBools != @["b_cond", "b_else"]

  test "unrelated bool_clause is NOT pruned":
    ## A bool_clause whose literals reference variables outside the def's
    ## target/cond/source set must remain untouched. Guards against an
    ## over-aggressive prune.
    let src = """
var 0..1: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: t :: output_var;
var 0..9: x :: output_var;
var 0..9: y :: output_var;
array [1..2] of var int: src_arr ::var_is_introduced = [a, b];
var bool: b_cond ::var_is_introduced ::is_defined_var;
var bool: b_then ::var_is_introduced ::is_defined_var;
var bool: b_else ::var_is_introduced ::is_defined_var;
var bool: b_xy ::var_is_introduced ::is_defined_var;
var bool: b_xa ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond) :: defines_var(b_cond);
constraint int_eq_reif(t, a, b_then) :: defines_var(b_then);
constraint int_eq_reif(t, b, b_else) :: defines_var(b_else);
constraint int_eq_reif(x, y, b_xy) :: defines_var(b_xy);
constraint int_eq_reif(x, a, b_xa) :: defines_var(b_xa);
constraint bool_clause([b_then], [b_cond]);
constraint bool_clause([b_cond, b_else], []);
constraint bool_clause([b_xy, b_xa], []);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)

    # The unrelated clause [b_xy, b_xa] does not match any
    # ConditionalSourceDef and must survive somewhere.
    var unrelatedSurvived = false
    for clause in tr.disjunctiveClauses:
      let sb = clause.sourceBools
      if (sb == @["b_xy", "b_xa"]) or (sb == @["b_xa", "b_xy"]):
        unrelatedSurvived = true
        break
    if not unrelatedSurvived:
      # Could also have stayed unconsumed in tr.model.constraints if it
      # didn't pass detectDisjunctivePairs's filter — also acceptable.
      var unrelatedConstraintCi = -1
      for ci, con in tr.model.constraints:
        if con.name != "bool_clause": continue
        if con.args.len < 2: continue
        let pos = con.args[0]
        let neg = con.args[1]
        if pos.kind != FznArrayLit or neg.kind != FznArrayLit: continue
        if neg.elems.len != 0 or pos.elems.len != 2: continue
        var idents: seq[string]
        for e in pos.elems:
          if e.kind == FznIdent: idents.add(e.ident)
        if "b_xy" in idents and "b_xa" in idents:
          unrelatedConstraintCi = ci
      check unrelatedConstraintCi >= 0
      # And it must NOT have been marked defining by the prune.
      check unrelatedConstraintCi notin tr.definingConstraints


suite "Conditional-source: solving with synthetic sourceVars":

  test "channel binding is wired correctly for cross-array sources":
    ## End-to-end: detect, build, and solve a model that exercises the
    ## synthetic-sourceVars binding path. With cond fixed and a/b fixed,
    ## t must take the value of the source picked by cond.
    let src = """
var 0..1: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: t :: output_var;
array [1..1] of var int: arr_then ::var_is_introduced = [a];
array [1..1] of var int: arr_else ::var_is_introduced = [b];
var bool: b_cond ::var_is_introduced ::is_defined_var;
var bool: b_then ::var_is_introduced ::is_defined_var;
var bool: b_else ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond) :: defines_var(b_cond);
constraint int_eq_reif(t, a, b_then) :: defines_var(b_then);
constraint int_eq_reif(t, b, b_else) :: defines_var(b_else);
constraint bool_clause([b_then], [b_cond]);
constraint bool_clause([b_cond, b_else], []);
constraint int_eq(cond, 1);
constraint int_eq(a, 3);
constraint int_eq(b, 7);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    check tr.conditionalSourceDefs.len == 1
    check tr.conditionalSourceDefs[0].sourceVars == @["a", "b"]
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    # cond=1 → t = b = 7 (synthetic source position 1).
    check tr.sys.assignment[tr.varPositions["t"]] == 7

  test "cond=0 picks the 'then' branch":
    let src = """
var 0..1: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: t :: output_var;
array [1..1] of var int: arr_then ::var_is_introduced = [a];
array [1..1] of var int: arr_else ::var_is_introduced = [b];
var bool: b_cond ::var_is_introduced ::is_defined_var;
var bool: b_then ::var_is_introduced ::is_defined_var;
var bool: b_else ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond) :: defines_var(b_cond);
constraint int_eq_reif(t, a, b_then) :: defines_var(b_then);
constraint int_eq_reif(t, b, b_else) :: defines_var(b_else);
constraint bool_clause([b_then], [b_cond]);
constraint bool_clause([b_cond, b_else], []);
constraint int_eq(cond, 0);
constraint int_eq(a, 4);
constraint int_eq(b, 9);
solve satisfy;
"""
    let model = parseFzn(src)
    var tr = translate(model)
    tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)
    # cond=0 → t = a = 4.
    check tr.sys.assignment[tr.varPositions["t"]] == 4
