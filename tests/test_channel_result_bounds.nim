## Tests for channel-result bound enforcement.
##
## When an element constraint with a constant array has `defines_var(R)` and the
## array contains values outside R's FZN-declared domain (e.g., -1 sentinel for
## infeasible cells in MZN models that gate via `var 0..max: R`), the translator
## must emit explicit `R >= lo` / `R <= hi` constraints. Otherwise the channel
## binding silently writes the sentinel into the channel value with no penalty.

import unittest
import std/[tables, sequtils, packedsets]
import crusher
import flatzinc/[parser, translator]
import constraints/[types, constraintNode]

suite "Channel-Result Bound Enforcement":

    test "sentinel-array element emits lower bound on channel result":
        ## Array = [-1, 5, -1, 7] with result var declared 0..100.
        ## Channel binding will produce -1 for some idx values; we must add
        ## `R >= 0` so search has a penalty signal away from sentinel cells.
        ## R is used as the objective so the dead-channel elimination keeps it.
        let src = """
var 1..4: idx :: output_var;
var 0..100: R :: var_is_introduced :: is_defined_var :: output_var;
array [1..4] of int: arr = [-1, 5, -1, 7];
constraint array_int_element(idx, arr, R) :: defines_var(R);
solve minimize R;
"""
        let model = parseFzn(src)
        let tr = translate(model)

        # The channel binding for R should exist
        check tr.sys.baseArray.channelBindings.len >= 1
        let rPos = tr.varPositions["R"]
        var rChannelExists = false
        for b in tr.sys.baseArray.channelBindings:
            if b.channelPosition == rPos:
                rChannelExists = true
                break
        check rChannelExists

        # A relational constraint enforcing R >= 0 should have been added.
        # Look for a GreaterThanEq constraint involving R's position.
        var foundLowerBound = false
        for c in tr.sys.baseArray.constraints:
            if c.stateType != RelationalType: continue
            let rs = c.relationalState
            if rs.relation != GreaterThanEq: continue
            if rPos in rs.positions:
                foundLowerBound = true
                break
        check foundLowerBound

    test "search avoids sentinel cells with the bound constraint":
        ## Same setup as above; resolve and verify R is non-negative (i.e.
        ## search picked idx ∈ {2, 4} where arr[idx] >= 0, not idx ∈ {1, 3}).
        let src = """
var 1..4: idx :: output_var;
var 0..100: R :: var_is_introduced :: is_defined_var :: output_var;
array [1..4] of int: arr = [-1, 5, -1, 7];
constraint array_int_element(idx, arr, R) :: defines_var(R);
solve minimize R;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        let rPos = tr.varPositions["R"]
        let rVal = tr.sys.assignment[rPos]
        check rVal >= 0
        check rVal in @[5, 7]

    test "upper bound emitted when array exceeds declared hi":
        ## Array values include 99, but R declared 0..50 → emit R <= 50.
        let src = """
var 1..3: idx :: output_var;
var 0..50: R :: var_is_introduced :: is_defined_var :: output_var;
array [1..3] of int: arr = [10, 99, 30];
constraint array_int_element(idx, arr, R) :: defines_var(R);
solve minimize R;
"""
        let model = parseFzn(src)
        let tr = translate(model)

        let rPos = tr.varPositions["R"]
        var foundUpperBound = false
        for c in tr.sys.baseArray.constraints:
            if c.stateType != RelationalType: continue
            let rs = c.relationalState
            if rs.relation != LessThanEq: continue
            if rPos in rs.positions:
                foundUpperBound = true
                break
        check foundUpperBound

    test "no bound emitted when array is fully within declared domain":
        ## Array = [10, 20, 30], R declared 0..100. No sentinels → no extra
        ## bound constraints (avoid spurious overhead on dense lookup tables).
        let src = """
var 1..3: idx :: output_var;
var 0..100: R :: var_is_introduced :: is_defined_var :: output_var;
array [1..3] of int: arr = [10, 20, 30];
constraint array_int_element(idx, arr, R) :: defines_var(R);
solve minimize R;
"""
        let model = parseFzn(src)
        let tr = translate(model)

        let rPos = tr.varPositions["R"]
        var nBoundsOnR = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType != RelationalType: continue
            let rs = c.relationalState
            if rs.relation in {GreaterThanEq, LessThanEq}:
                if rPos in rs.positions:
                    inc nBoundsOnR
        check nBoundsOnR == 0

    test "no bound on bool channel when presolve narrows post-FZN domain":
        ## Bool channel `b` with declared domain bool (0..1). After int_eq(x, 2)
        ## fixes x, presolve may narrow b's domain to a singleton {1}, but the
        ## reification array is [0, 1, 0] and the channel correctly produces 1.
        ## Using FZN-declared bounds (not post-presolve), we must NOT emit
        ## `b >= 1` or `b <= 1` — that would conflict with case-analysis
        ## lookup tables whose unreachable cells carry placeholder values.
        let src = """
var 1..3: x :: output_var;
var bool: b :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x, 2, b) :: defines_var(b);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        let tr = translate(model)

        check "b" in tr.varPositions
        if "b" in tr.varPositions:
            let bPos = tr.varPositions["b"]
            var nBoundsOnB = 0
            for c in tr.sys.baseArray.constraints:
                if c.stateType != RelationalType: continue
                let rs = c.relationalState
                if rs.relation in {GreaterThanEq, LessThanEq}:
                    if bPos in rs.positions:
                        inc nBoundsOnB
            check nBoundsOnB == 0
