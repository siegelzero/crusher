## Tests for translatorCanonicalize.canonicalizeLinearReifs.
## Verifies that single-term int_lin_{eq,ne,le}_reif constraints are rewritten
## into their primitive int_{eq,ne,le}_reif equivalents at translation time,
## and that the rewritten model preserves solver semantics.

import unittest
import std/[strutils, tables, sets]
import crusher
import flatzinc/[parser, translator]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

proc countConstraintName(model: FznModel, name: string): int =
    # Test sources don't carry solver prefixes; compare directly.
    for con in model.constraints:
        if con.name == name:
            inc result

proc constraintByName(model: FznModel, name: string): seq[FznConstraint] =
    for con in model.constraints:
        if con.name == name:
            result.add(con)

# ---------------------------------------------------------------------------
# Suite
# ---------------------------------------------------------------------------

suite "Canonicalize single-term linear reifs":

    test "int_lin_eq_reif([1],[x],k,b) → int_eq_reif(x,k,b)":
        let src = """
var 1..5: x;
var bool: b;
constraint int_lin_eq_reif([1], [x], 3, b);
constraint int_eq(x, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        # Original lin_eq_reif must have been rewritten away
        check countConstraintName(tr.model, "int_lin_eq_reif") == 0
        check countConstraintName(tr.model, "int_eq_reif") == 1
        let eq = constraintByName(tr.model, "int_eq_reif")[0]
        check eq.args[0].kind == FznIdent
        check eq.args[0].ident == "x"
        check eq.args[1].kind == FznIntLit
        check eq.args[1].intVal == 3
        check eq.args[2].kind == FznIdent
        check eq.args[2].ident == "b"
        # Solver round-trip: x must end at 3, b must be 1
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["x"]] == 3
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lin_eq_reif([-1],[x],k,b) → int_eq_reif(x,-k,b)":
        # -x = 2 ⟺ x = -2
        let src = """
var -5..5: x;
var bool: b;
constraint int_lin_eq_reif([-1], [x], 2, b);
constraint int_eq(x, -2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_eq_reif") == 0
        let eq = constraintByName(tr.model, "int_eq_reif")[0]
        check eq.args[1].intVal == -2
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1  # x=-2 ⟹ -x=2

    test "int_lin_eq_reif([2],[x],4,b) divisible → int_eq_reif(x,2,b)":
        let src = """
var 0..5: x;
var bool: b;
constraint int_lin_eq_reif([2], [x], 4, b);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_eq_reif") == 0
        let eq = constraintByName(tr.model, "int_eq_reif")[0]
        check eq.args[1].intVal == 2
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lin_eq_reif([2],[x],3,b) non-divisible → left alone":
        # 2x = 3 has no integer solution → presolve will force b=0; canonicalize must skip.
        let src = """
var 0..5: x;
var bool: b;
constraint int_lin_eq_reif([2], [x], 3, b);
solve satisfy;
"""
        let model = parseFzn(src)
        let tr = translate(model)
        # Either it stays as int_lin_eq_reif, or presolve absorbed it as a defining
        # constraint. Both outcomes are acceptable — but it must NOT have been
        # rewritten to a wrong int_eq_reif(x, 1, b) (3 div 2 = 1).
        for con in constraintByName(tr.model, "int_eq_reif"):
            # Defending the negative: any int_eq_reif must not have testVal 1 with x as source.
            if con.args[0].kind == FznIdent and con.args[0].ident == "x":
                check con.args[1].kind == FznIntLit
                check con.args[1].intVal != 1

    test "int_lin_eq_reif([1,1],[x,p],k,b) absorbs parameter":
        # x + p = 7 with p=4 ⟹ x = 3
        let src = """
int: p = 4;
var 0..10: x;
var bool: b;
constraint int_lin_eq_reif([1, 1], [x, p], 7, b);
constraint int_eq(x, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_eq_reif") == 0
        let eq = constraintByName(tr.model, "int_eq_reif")[0]
        check eq.args[1].intVal == 3   # 7 - 1*4 = 3
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lin_eq_reif with int literal in array absorbs constant":
        # x + 5 = 9 ⟹ x = 4
        let src = """
var 0..10: x;
var bool: b;
constraint int_lin_eq_reif([1, 1], [x, 5], 9, b);
constraint int_eq(x, 4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_eq_reif") == 0
        let eq = constraintByName(tr.model, "int_eq_reif")[0]
        check eq.args[1].intVal == 4
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1

    test "int_lin_ne_reif([1],[x],k,b) → int_ne_reif(x,k,b)":
        let src = """
var 1..5: x;
var bool: b;
constraint int_lin_ne_reif([1], [x], 3, b);
constraint int_eq(x, 4);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_ne_reif") == 0
        check countConstraintName(tr.model, "int_ne_reif") == 1
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1  # 4 != 3

    test "int_lin_ne_reif([-1],[x],k,b) → int_ne_reif(x,-k,b)":
        let src = """
var -5..5: x;
var bool: b;
constraint int_lin_ne_reif([-1], [x], 2, b);
constraint int_eq(x, -2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_ne_reif") == 0
        let ne = constraintByName(tr.model, "int_ne_reif")[0]
        check ne.args[1].intVal == -2
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 0  # x=-2, -x=2, so 2!=2 is false

    test "int_lin_le_reif([1],[x],k,b) → int_le_reif(x,k,b)":
        let src = """
var 0..10: x;
var bool: b;
constraint int_lin_le_reif([1], [x], 5, b);
constraint int_eq(x, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_le_reif") == 0
        let le = constraintByName(tr.model, "int_le_reif")[0]
        check le.args[0].kind == FznIdent and le.args[0].ident == "x"
        check le.args[1].intVal == 5
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1  # 3 <= 5

    test "int_lin_le_reif([-1],[x],k,b) → int_le_reif(IntLit(-k), x, b) [args swapped]":
        # -x ≤ 2 ⟺ x ≥ -2 ⟺ -2 ≤ x
        let src = """
var -5..5: x;
var bool: b;
constraint int_lin_le_reif([-1], [x], 2, b);
constraint int_eq(x, 0);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_le_reif") == 0
        let le = constraintByName(tr.model, "int_le_reif")[0]
        # arg0 is the int literal (-k), arg1 is the variable
        check le.args[0].kind == FznIntLit
        check le.args[0].intVal == -2
        check le.args[1].kind == FznIdent and le.args[1].ident == "x"
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1  # 0 ≥ -2

    test "int_lin_le_reif([2],[x],5,b) → int_le_reif(x, floor(5/2)=2, b)":
        # 2x ≤ 5 ⟺ x ≤ 2 (floor div)
        let src = """
var 0..10: x;
var bool: b;
constraint int_lin_le_reif([2], [x], 5, b);
constraint int_eq(x, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_le_reif") == 0
        let le = constraintByName(tr.model, "int_le_reif")[0]
        check le.args[1].intVal == 2  # floor(5/2)=2
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1   # 2*2=4 ≤ 5

    test "int_lin_le_reif([-2],[x],5,b) → int_le_reif(IntLit(ceil(5/-2)=-2), x, b)":
        # -2x ≤ 5 ⟺ x ≥ ceil(5/-2) = ceil(-2.5) = -2
        let src = """
var -10..10: x;
var bool: b;
constraint int_lin_le_reif([-2], [x], 5, b);
constraint int_eq(x, -2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_le_reif") == 0
        let le = constraintByName(tr.model, "int_le_reif")[0]
        check le.args[0].kind == FznIntLit
        check le.args[0].intVal == -2  # ceil(5 / -2) = -2
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.assignment[tr.varPositions["b"]] == 1   # -2*-2=4 ≤ 5

    test "multi-variable int_lin_eq_reif left untouched":
        # Two true variables in the array → fold must not fire.
        let src = """
var 0..10: x;
var 0..10: y;
var bool: b;
constraint int_lin_eq_reif([1, 1], [x, y], 7, b);
solve satisfy;
"""
        let model = parseFzn(src)
        let tr = translate(model)
        check countConstraintName(tr.model, "int_lin_eq_reif") == 1
        check countConstraintName(tr.model, "int_eq_reif") == 0

    test "fold preserves defines_var annotation":
        # int_lin_eq_reif(...) :: defines_var(b) — after fold the resulting
        # int_eq_reif must still carry the same annotation so reif-channel
        # detection picks it up.
        let src = """
var 0..5: x;
var bool: b :: var_is_introduced :: is_defined_var;
constraint int_lin_eq_reif([1], [x], 3, b) :: defines_var(b);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        check countConstraintName(tr.model, "int_lin_eq_reif") == 0
        let eq = constraintByName(tr.model, "int_eq_reif")[0]
        check eq.hasAnnotation("defines_var")
        # And the bool was actually channelized via the eq path
        check "b" in tr.channelVarNames

    test "end-to-end: search exercises folded reif and respects implication":
        # b ↔ x ≤ 5; then enforce b == 1 → x ≤ 5 even though x ranges to 10.
        let src = """
var 0..10: x;
var bool: b;
constraint int_lin_le_reif([1], [x], 5, b);
constraint bool_eq(b, true);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
        let xVal = tr.sys.assignment[tr.varPositions["x"]]
        check xVal <= 5
        check tr.sys.assignment[tr.varPositions["b"]] == 1
