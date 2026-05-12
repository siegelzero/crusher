## Tests for channel-result bound enforcement.
##
## When an element constraint with a constant array has `defines_var(R)` and the
## array contains values outside R's FZN-declared domain (e.g., -1 sentinel for
## infeasible cells in MZN models that gate via `var 0..max: R`), the translator
## must emit explicit `R >= lo` / `R <= hi` constraints. Otherwise the channel
## binding silently writes the sentinel into the channel value with no penalty.

import unittest
import std/[tables, packedsets]
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

    test "bool channel result with reification array stays unbounded (naturally in domain)":
        ## Bool channel `b` declared `var bool` → FZN-declared bounds [0, 1].
        ## The reification array `int_eq_reif(x, 2, b)` for x ∈ 1..3 is [0, 1, 0],
        ## entirely within [0, 1]. The pass should hit the "naturally in domain"
        ## branch and emit nothing — bool channels with proper {0, 1} arrays
        ## carry no sentinels.
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

    test "case-analysis lookup table with post-presolve singleton emits no spurious bound":
        ## Exercises the FZN-declared-vs-post-presolve guard. R is declared
        ## `var 0..100`, but `int_eq(R, 7)` lets presolve narrow R's domain
        ## to {7}. The lookup table `[5, 7, 10]` has values inside the FZN
        ## domain (0..100) but two of them (5, 10) outside the post-presolve
        ## singleton. The pass MUST use FZN-declared bounds and emit nothing:
        ## the array is naturally in [0..100], even though it strays outside
        ## {7}. Emitting against the post-presolve singleton would falsely
        ## penalise reachable cells in models where presolve only tightens
        ## one branch of a case analysis.
        let src = """
var 1..3: idx :: output_var;
var 0..100: R :: var_is_introduced :: is_defined_var :: output_var;
array [1..3] of int: arr = [5, 7, 10];
constraint array_int_element(idx, arr, R) :: defines_var(R);
constraint int_eq(R, 7);
solve satisfy;
"""
        let model = parseFzn(src)
        let tr = translate(model)

        check "R" in tr.varPositions
        let rPos = tr.varPositions["R"]
        var nBoundsOnR = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType != RelationalType: continue
            let rs = c.relationalState
            if rs.relation in {GreaterThanEq, LessThanEq}:
                if rPos in rs.positions:
                    inc nBoundsOnR
        check nBoundsOnR == 0

    test "FznIntSet declared variable picks up min/max bounds":
        ## Variable declared with enumerated set `var {0, 5, 10}` → bounds
        ## [0, 10]. Array `[-1, 5, -1]` has -1 outside [0, 10], so a lower
        ## bound `R >= 0` should be emitted. (This previously fell through
        ## the `FznIntRange`-only filter and emitted nothing.)
        let src = """
var 1..3: idx :: output_var;
var {0, 5, 10}: R :: var_is_introduced :: is_defined_var :: output_var;
array [1..3] of int: arr = [-1, 5, -1];
constraint array_int_element(idx, arr, R) :: defines_var(R);
solve minimize R;
"""
        let model = parseFzn(src)
        let tr = translate(model)

        check "R" in tr.varPositions
        let rPos = tr.varPositions["R"]
        var foundLowerBound = false
        for c in tr.sys.baseArray.constraints:
            if c.stateType != RelationalType: continue
            let rs = c.relationalState
            if rs.relation != GreaterThanEq: continue
            if rPos in rs.positions:
                foundLowerBound = true
                break
        check foundLowerBound
