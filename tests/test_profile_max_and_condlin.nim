## Tests for peak-load profile channels and conditional linear resolution.
##
## Profile max: array_int_maximum(M, [L_0..L_n]) over pure indicator sums
## L_i = Σ c * [x == i] becomes one ProfileMaxChannelBinding with cached loads.
## M's declared domain, when narrower than the natural range, must stay a
## constraint (nside caps the peak at max(perterb) * days).
##
## Conditional linear: a big-M precedence g*e1 <= d2 + M*(1-g) whose end time
## e1 = d1 + dur is a defined variable must be emitted with e1 substituted;
## it used to be skipped ("unresolved variables"), silently dropping it.

import unittest
import std/[tables]
import crusher
import flatzinc/[parser, translator]
import constraints/[types]

proc profileSrc(mDecl: string): string =
    ## L_i = 3*[x1 == i] + 5*[x2 == i], i in 0..3; M = max_i L_i.
    result = "var 0..3: x1 :: output_var;\nvar 0..3: x2 :: output_var;\n"
    for i in 0..3:
        for w in 1..2:
            result.add "var bool: r" & $w & "_" & $i & " :: var_is_introduced :: is_defined_var;\n"
            result.add "var 0..1: b" & $w & "_" & $i & " :: var_is_introduced :: is_defined_var;\n"
        result.add "var 0..8: L" & $i & " :: var_is_introduced :: is_defined_var;\n"
    result.add "var " & mDecl & ": M :: output_var :: is_defined_var;\n"
    for i in 0..3:
        for w in 1..2:
            result.add "constraint int_eq_reif(x" & $w & ", " & $i & ", r" & $w & "_" & $i &
                       ") :: defines_var(r" & $w & "_" & $i & ");\n"
            result.add "constraint bool2int(r" & $w & "_" & $i & ", b" & $w & "_" & $i &
                       ") :: defines_var(b" & $w & "_" & $i & ");\n"
        result.add "constraint int_lin_eq([3,5,-1],[b1_" & $i & ",b2_" & $i & ",L" & $i &
                   "],0) :: defines_var(L" & $i & ");\n"
    result.add "constraint array_int_maximum(M, [L0,L1,L2,L3]) :: defines_var(M);\n"
    result.add "solve satisfy;\n"

suite "Profile max channels":

    test "pure indicator sums under a max become one profile channel":
        let tr = translate(parseFzn(profileSrc("0..8")))
        check tr.sys.baseArray.profileMaxChannelBindings.len == 1
        let b = tr.sys.baseArray.profileMaxChannelBindings[0]
        check b.channelPosition == tr.varPositions["M"]
        check b.slotBase.len == 4
        check b.groupX.len == 2   # one group per source

    test "binding declared cap on the peak is enforced":
        ## M declared 0..5 while the natural peak reaches 8 (x1 == x2):
        ## the cap must keep x1 != x2, and M must equal the true peak.
        var tr = translate(parseFzn(profileSrc("0..5")))
        check tr.sys.baseArray.profileMaxChannelBindings.len == 1
        tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
        check tr.sys.hasFeasibleSolution
        let x1 = tr.sys.assignment[tr.varPositions["x1"]]
        let x2 = tr.sys.assignment[tr.varPositions["x2"]]
        check x1 != x2
        check tr.sys.assignment[tr.varPositions["M"]] == 5

suite "Conditional linear over defined variables":

    const precSrc = """
var 0..1: g :: output_var;
var 0..10: d1 :: output_var;
var 0..10: d2 :: output_var;
var 2..12: e1 :: var_is_introduced :: is_defined_var;
constraint int_lin_eq([1,-1],[d1,e1],-2) :: defines_var(e1);
constraint int_lin_le([1,-1,12],[e1,d2,g],12);
solve satisfy;
"""

    test "big-M precedence through a defined end time is emitted":
        let tr = translate(parseFzn(precSrc))
        var nCondLin = 0
        for c in tr.sys.baseArray.constraints:
            if c.stateType == ConditionalLinearType: inc nCondLin
        check nCondLin == 1

    test "solutions respect the precedence":
        ## With the constraint dropped, random states violate it about half
        ## the time (g = 1 and d1 + 2 > d2).
        for trial in 0..9:
            var tr = translate(parseFzn(precSrc))
            tr.sys.resolve(parallel = false, tabuThreshold = 1000, verbose = false)
            check tr.sys.hasFeasibleSolution
            let g = tr.sys.assignment[tr.varPositions["g"]]
            let d1 = tr.sys.assignment[tr.varPositions["d1"]]
            let d2 = tr.sys.assignment[tr.varPositions["d2"]]
            check g == 0 or d1 + 2 <= d2
