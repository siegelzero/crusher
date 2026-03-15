## Tests for constant element composition optimization in FlatZinc translation.
## Verifies that downstream constraints can compose through element channels with
## constant arrays, eliminating intermediate variables from the penalty graph.

import unittest
import std/[sequtils, tables]
import crusher
import flatzinc/[parser, translator]

suite "Constant Element Composition (FZN)":

    test "Element channel with downstream int_eq_reif composes from upstream var":
        ## Tests that when element(y, array, x) defines channel x,
        ## and int_eq_reif(x, 10, b) uses that channel,
        ## the binding composes directly from y, skipping the x channel.
        let src = """
array [1..2] of int: arr = [10, 12];
var 1..2: y :: output_var;
var 10..12: x :: var_is_introduced :: is_defined_var;
var bool: b :: output_var;
constraint array_int_element(y, arr, x) :: defines_var(x);
constraint int_eq_reif(x, 10, b) :: defines_var(b);
constraint int_eq(b, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Verify element composition was detected
        check tr.constElementSources.len > 0

        # Solve
        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

        # Verify solution: y in 1..2, x = arr[y], b = (x == 10 ? 1 : 0)
        let yVal = tr.sys.assignment[tr.varPositions["y"]]
        let xVal = tr.sys.assignment[tr.varPositions["x"]]
        let bVal = tr.sys.assignment[tr.varPositions["b"]]

        check yVal in 1..2
        let arr = @[10, 12]
        check xVal == arr[yVal - 1]  # FZN uses 1-based, convert to 0-based
        check bVal == 1  # constraint b = 1, and since x must be in [10, 12], x can be 10
        check xVal == 10  # the only value that satisfies b=1

    test "Composition with constraint on composite variable":
        ## Tests that composition works when a downstream constraint
        ## uses the intermediate element channel variable.
        let src = """
array [1..2] of int: arr = [5, 7];
var 1..2: y :: output_var;
var 5..7: x :: var_is_introduced :: is_defined_var;
var 5..7: z :: output_var;
constraint array_int_element(y, arr, x) :: defines_var(x);
constraint int_eq(x, z);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

        let yVal = tr.sys.assignment[tr.varPositions["y"]]
        let zVal = tr.sys.assignment[tr.varPositions["z"]]

        # Verify: z = arr[y]
        let arr = @[5, 7]
        check zVal == arr[yVal - 1]

    test "Element composition with set membership constraint":
        ## Tests that set_in_reif can compose from element channels.
        let src = """
array [1..2] of int: arr = [10, 12];
var 1..2: y :: output_var;
var 10..12: x :: var_is_introduced :: is_defined_var;
var bool: b :: output_var;
constraint array_int_element(y, arr, x) :: defines_var(x);
constraint set_in_reif(x, 10..11, b) :: defines_var(b);
constraint int_eq(b, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = false, tabuThreshold = 5000, verbose = false)

        let yVal = tr.sys.assignment[tr.varPositions["y"]]
        let xVal = tr.sys.assignment[tr.varPositions["x"]]
        let bVal = tr.sys.assignment[tr.varPositions["b"]]

        # Verify: x = arr[y], b = (x in {10, 11} ? 1 : 0), constraint b=1
        let arr = @[10, 12]
        check xVal == arr[yVal - 1]
        check bVal == 1
        check xVal in {10, 11}  # must be in set for b=1
