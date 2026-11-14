## Tests for the local existential projection pass (translatorProjection):
## small-domain search variables whose only effect is a few local constraints
## become channels computed from the values those constraints read, and the
## constraints become one graduated lookup on the least penalty.

import unittest
import std/[tables, packedsets]
import crusher
import flatzinc/[parser, translator]

proc pos(tr: FznTranslator, name: string): int = tr.varPositions[name]
proc val(tr: FznTranslator, name: string): int = tr.sys.assignment[tr.varPositions[name]]
proc isChannel(tr: FznTranslator, name: string): bool =
    tr.pos(name) in tr.sys.baseArray.channelPositions

## A shift-add: z = s*x + t with shift s and sign t free (cf. multiple constant
## multiplication: ka*ca = kai_l*cai_l + kai_r*cai_r). x and z have domains
## too large for candidates, so they form the interface.
const ShiftAdd = """
var 1..70: x :: output_var;
var 1..300: z :: output_var;
var {1,2,4,8}: s :: output_var;
var {-1,1}: t :: output_var;
var -560..560: p :: var_is_introduced :: is_defined_var;
constraint int_times(s, x, p) :: defines_var(p);
constraint int_lin_eq([1,1,-1], [p, t, z], 0);
"""

suite "Local existential projection":

    test "shift and sign of a shift-add become channels of its operands":
        var tr = translate(parseFzn(ShiftAdd & "constraint int_le(23, z);\nsolve satisfy;\n"))
        check tr.isChannel("s")
        check tr.isChannel("t")
        check not tr.isChannel("x")
        check not tr.isChannel("z")
        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
        check tr.sys.hasFeasibleSolution
        let (x, z, s, t) = (tr.val("x"), tr.val("z"), tr.val("s"), tr.val("t"))
        check z >= 23
        check s in [1, 2, 4, 8]
        check t in [-1, 1]
        check s * x + t == z

    test "a variable the objective reads is not projected":
        let tr = translate(parseFzn(ShiftAdd & "solve minimize s;\n"))
        check not tr.isChannel("s")

    test "a variable in a wide constraint is not projected":
        # t also enters a sum over six other variables: interface too large.
        let src = ShiftAdd & """
var 0..100: a1 :: output_var;
var 0..100: a2 :: output_var;
var 0..100: a3 :: output_var;
var 0..100: a4 :: output_var;
var 0..100: a5 :: output_var;
var 0..100: a6 :: output_var;
constraint int_lin_le([1,1,1,1,1,1,1], [t, a1, a2, a3, a4, a5, a6], 6);
solve satisfy;
"""
        let tr = translate(parseFzn(src))
        check not tr.isChannel("t")

    test "the witness reaches the only reachable operand pair":
        # x = 1, z >= 9: only s = 8, t = 1 gives 9; every larger z has
        # positive least penalty and must stay rejected.
        var tr = translate(parseFzn(ShiftAdd &
            "constraint int_eq(x, 1);\nconstraint int_le(9, z);\nsolve satisfy;\n"))
        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)
        check tr.sys.hasFeasibleSolution
        check tr.val("z") == 9
        check tr.val("s") == 8
        check tr.val("t") == 1
