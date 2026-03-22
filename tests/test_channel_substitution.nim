## Tests for substituteChannelVarsInClauses() in translatorScheduling.nim.
## Verifies that disjunctive clause terms are simplified by substituting
## known linear channel variable definitions.

import unittest
import std/[sequtils, algorithm, sets, tables, strutils, packedsets]
import crusher
import flatzinc/[parser, translator, output]

suite "Channel Variable Substitution in Disjunctive Clauses":

    test "basic 2-input channel substitution: 4 vars → 2 vars":
        ## Channel: xy = 13*y + x (offset 0).
        ## 3-literal clause with 4-var terms [y1,x1,y2,x2] should be simplified
        ## to 2-var terms [xy1,xy2].
        let src = """
var 0..12: x1 :: output_var;
var 0..12: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 0..129: xy1 :: var_is_introduced :: is_defined_var;
var 0..129: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([13, 1, -1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([13, 1, -1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([13, 1, -13, -1], [y1, x1, y2, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-13, -1, 13, 1], [y1, x1, y2, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1
        let clause = tr.disjunctiveClauses[0]
        check clause.disjuncts.len == 3

        # First two disjuncts should be substituted to use xy1, xy2
        var foundSubstituted = false
        for disjunct in clause.disjuncts:
            let term = disjunct[0]
            if "xy1" in term.varNames and "xy2" in term.varNames:
                foundSubstituted = true
                check term.varNames.len == 2
                let idx1 = term.varNames.find("xy1")
                let idx2 = term.varNames.find("xy2")
                check (term.coeffs[idx1] == 1 and term.coeffs[idx2] == -1) or
                      (term.coeffs[idx1] == -1 and term.coeffs[idx2] == 1)
                break
        check foundSubstituted

        # Third disjunct should be unchanged (only 2 vars, no substitution)
        var foundUnchanged = false
        for disjunct in clause.disjuncts:
            let term = disjunct[0]
            if "x1" in term.varNames and "x2" in term.varNames and term.varNames.len == 2:
                foundUnchanged = true
                break
        check foundUnchanged

    test "no substitution when coefficients don't match":
        ## Channel is xy = 13*y + x, but clause term uses [5,1,-5,-1]
        ## which has scale 5/13 — not integer-divisible. No substitution.
        let src = """
var 0..12: x1 :: output_var;
var 0..12: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 0..129: xy1 :: var_is_introduced :: is_defined_var;
var 0..129: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([13, 1, -1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([13, 1, -1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([5, 1, -5, -1], [y1, x1, y2, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-5, -1, 5, 1], [y1, x1, y2, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        # First two terms should still have 4 variables (no substitution)
        var fourVarTerms = 0
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            for term in disjunct:
                if term.varNames.len == 4:
                    fourVarTerms += 1
        check fourVarTerms == 2

    test "coefficient scaling: term coefficients are multiples of channel coefficients":
        ## Channel: xy = 3*y + x. Term has [6,2,-6,-2] = 2*(3*y + x).
        ## Should substitute with scale factor s=2.
        let src = """
var 0..9: x1 :: output_var;
var 0..9: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 0..36: xy1 :: var_is_introduced :: is_defined_var;
var 0..36: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([3, 1, -1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([3, 1, -1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([6, 2, -6, -2], [y1, x1, y2, x2], -4, b1) :: defines_var(b1);
constraint int_lin_le_reif([-6, -2, 6, 2], [y1, x1, y2, x2], -4, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        var foundScaled = false
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            let term = disjunct[0]
            if "xy1" in term.varNames and "xy2" in term.varNames:
                foundScaled = true
                let idx1 = term.varNames.find("xy1")
                let idx2 = term.varNames.find("xy2")
                check (term.coeffs[idx1] == 2 and term.coeffs[idx2] == -2) or
                      (term.coeffs[idx1] == -2 and term.coeffs[idx2] == 2)
                break
        check foundScaled

    test "channel with zero offset: RHS preserved":
        ## Channel: xy = 3*y + x (offset 0, rhs=0).
        ## Symmetric substitution: offsets cancel. RHS should stay -2.
        let src = """
var 0..9: x1 :: output_var;
var 0..9: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 0..36: xy1 :: var_is_introduced :: is_defined_var;
var 0..36: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([3, 1, -1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([3, 1, -1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([3, 1, -3, -1], [y1, x1, y2, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-3, -1, 3, 1], [y1, x1, y2, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        var foundSubstituted = false
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            let term = disjunct[0]
            if "xy1" in term.varNames and "xy2" in term.varNames:
                foundSubstituted = true
                check term.varNames.len == 2
                check term.rhs == -2  # zero offset → RHS unchanged
                break
        check foundSubstituted

    test "symmetric nonzero offset: offsets cancel in RHS":
        ## Both channels: xy = 3*y + x + 5 (same offset).
        ## Term: 3*y1+x1-3*y2-x2 <= -2.
        ## Substitution: xy1 - xy2 <= -2 (offsets cancel).
        let src = """
var 0..9: x1 :: output_var;
var 0..9: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 5..41: xy1 :: var_is_introduced :: is_defined_var;
var 5..41: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([3, 1, -1], [y1, x1, xy1], -5) :: defines_var(xy1);
constraint int_lin_eq([3, 1, -1], [y2, x2, xy2], -5) :: defines_var(xy2);
constraint int_lin_le_reif([3, 1, -3, -1], [y1, x1, y2, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-3, -1, 3, 1], [y1, x1, y2, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        var foundSubstituted = false
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            let term = disjunct[0]
            if "xy1" in term.varNames and "xy2" in term.varNames:
                foundSubstituted = true
                check term.varNames.len == 2
                # Symmetric offsets cancel: RHS stays -2
                check term.rhs == -2
                break
        check foundSubstituted

    test "asymmetric offsets: RHS adjusted per-channel":
        ## Channel 1: xy1 = 3*y1 + x1 + 5 (offset 5).
        ## Channel 2: xy2 = 3*y2 + x2 + 10 (offset 10).
        ## Term: 3*y1+x1 - 3*y2-x2 <= -2  (i.e., (xy1-5) - (xy2-10) <= -2 → xy1-xy2 <= -7)
        ## Reverse: -3*y1-x1 + 3*y2+x2 <= -2  (i.e., -(xy1-5) + (xy2-10) <= -2 → -xy1+xy2 <= 3)
        let src = """
var 0..9: x1 :: output_var;
var 0..9: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 5..41: xy1 :: var_is_introduced :: is_defined_var;
var 10..46: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([3, 1, -1], [y1, x1, xy1], -5) :: defines_var(xy1);
constraint int_lin_eq([3, 1, -1], [y2, x2, xy2], -10) :: defines_var(xy2);
constraint int_lin_le_reif([3, 1, -3, -1], [y1, x1, y2, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-3, -1, 3, 1], [y1, x1, y2, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        var rhs_forward, rhs_backward: int
        var found_fwd, found_bwd = false
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            let term = disjunct[0]
            if "xy1" in term.varNames and "xy2" in term.varNames:
                let idx1 = term.varNames.find("xy1")
                if term.coeffs[idx1] == 1:
                    rhs_forward = term.rhs
                    found_fwd = true
                elif term.coeffs[idx1] == -1:
                    rhs_backward = term.rhs
                    found_bwd = true

        check found_fwd
        check found_bwd
        check rhs_forward == -7   # xy1 - xy2 <= -7
        check rhs_backward == 3   # -xy1 + xy2 <= 3

    test "no substitution for terms with fewer than 4 variables":
        ## Terms with only 2 variables can't form a 2-input channel pair, so are skipped.
        let src = """
var 0..9: x1 :: output_var;
var 0..9: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 0..99: xy1 :: var_is_introduced :: is_defined_var;
var 0..99: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([3, 1, -1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([3, 1, -1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([1, -1], [x1, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-1, 1], [x1, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [y1, y2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        # All terms should still have 2 variables (no substitution possible)
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            for term in disjunct:
                check term.varNames.len == 2

    test "chCoeff = 1: channel defined with positive coefficient":
        ## int_lin_eq([3, 1, 1], [y, x, xy], 0) → xy = -3y - x (chCoeff=1, scale=-1)
        ## Term [-3,-1,3,1] matches c1=-3, c2=-1 with s=1.
        let src = """
var 0..9: x1 :: output_var;
var 0..9: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var -36..0: xy1 :: var_is_introduced :: is_defined_var;
var -36..0: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([3, 1, 1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([3, 1, 1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([-3, -1, 3, 1], [y1, x1, y2, x2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([3, 1, -3, -1], [y1, x1, y2, x2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [x1, x2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        var foundSubstituted = false
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            let term = disjunct[0]
            if "xy1" in term.varNames and "xy2" in term.varNames:
                foundSubstituted = true
                check term.varNames.len == 2
                break
        check foundSubstituted

    test "partial substitution: only one pair matches a channel":
        ## 6-var term [13,1,-13,-1,1,-1]*[y1,x1,y2,x2,z1,z2].
        ## Channel for (y,x)→xy but not (z1,z2).
        ## Result: [xy1, xy2, z1, z2] (4 vars instead of 6).
        let src = """
var 0..12: x1 :: output_var;
var 0..12: x2 :: output_var;
var 0..9: y1 :: output_var;
var 0..9: y2 :: output_var;
var 0..9: z1 :: output_var;
var 0..9: z2 :: output_var;
var 0..129: xy1 :: var_is_introduced :: is_defined_var;
var 0..129: xy2 :: var_is_introduced :: is_defined_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([13, 1, -1], [y1, x1, xy1], 0) :: defines_var(xy1);
constraint int_lin_eq([13, 1, -1], [y2, x2, xy2], 0) :: defines_var(xy2);
constraint int_lin_le_reif([13, 1, -13, -1, 1, -1], [y1, x1, y2, x2, z1, z2], -2, b1) :: defines_var(b1);
constraint int_lin_le_reif([-13, -1, 13, 1, -1, 1], [y1, x1, y2, x2, z1, z2], -2, b2) :: defines_var(b2);
constraint int_lin_le_reif([1, -1], [z1, z2], -1, b3) :: defines_var(b3);
constraint bool_clause([b1, b2, b3], []);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.disjunctiveClauses.len == 1

        var foundPartial = false
        for disjunct in tr.disjunctiveClauses[0].disjuncts:
            let term = disjunct[0]
            if term.varNames.len == 4 and
               "xy1" in term.varNames and "xy2" in term.varNames and
               "z1" in term.varNames and "z2" in term.varNames:
                foundPartial = true
                break
        check foundPartial
