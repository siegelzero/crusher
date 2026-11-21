## No-overlap energy lower bound (constrainedArray.noOverlapEnergyFeasible)
## and its use by the optimizer: a proven lower bound on a makespan that
## lets the optimizer stop with a proof when the incumbent reaches it.

import unittest
import std/[strutils, times]

import crusher
import flatzinc/[parser, translator]

const OneMachine = """
predicate crusher_disjunctive_opt(array [int] of var int: s,array [int] of var bool: o,array [int] of var int: d);
var 0..100: s1 :: output_var;
var 0..100: s2 :: output_var;
var 0..100: s3 :: output_var;
var RELEASE..100: s4 :: output_var;
var 0..200: e1 :: is_defined_var;
var 0..200: e2 :: is_defined_var;
var 0..200: e3 :: is_defined_var;
var 0..200: e4 :: is_defined_var;
var 0..200: obj :: output_var :: is_defined_var;
array [1..4] of var int: ss = [s1,s2,s3,s4];
array [1..4] of var bool: oo = [true,true,true,true];
array [1..4] of int: dd = [3,4,5,6];
array [1..4] of var int: ee = [e1,e2,e3,e4];
constraint crusher_disjunctive_opt(ss, oo, dd);
constraint int_lin_eq([1,-1],[e1,s1],3) :: defines_var(e1);
constraint int_lin_eq([1,-1],[e2,s2],4) :: defines_var(e2);
constraint int_lin_eq([1,-1],[e3,s3],5) :: defines_var(e3);
constraint int_lin_eq([1,-1],[e4,s4],6) :: defines_var(e4);
constraint array_int_maximum(obj, ee) :: defines_var(obj);
solve minimize obj;
"""

const Gap = """
predicate crusher_disjunctive_opt(array [int] of var int: s,array [int] of var bool: o,array [int] of var int: d);
var 3..3: sa :: output_var;
var 0..100: sb :: output_var;
var 0..200: obj :: output_var :: is_defined_var;
array [1..2] of var int: ss = [sa,sb];
array [1..2] of var bool: oo = [true,true];
array [1..2] of int: dd = [2,4];
constraint crusher_disjunctive_opt(ss, oo, dd);
constraint int_lin_eq([1,-1],[obj,sb],4) :: defines_var(obj);
solve minimize obj;
"""

proc model(release: int): string = OneMachine.replace("RELEASE", $release)

proc solve(src: string): (int, bool) =
    var tr = translate(parseFzn(src))
    let objExpr = if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
                  elif tr.objectivePos == -1: tr.objectiveDefExpr
                  else: raise newException(ValueError, "No objective")
    minimize(tr.sys, objExpr, parallel = true, tabuThreshold = 2000, verbose = false,
             deadline = epochTime() + 20.0)
    (int(objExpr.evaluate(tr.sys.assignment)), tr.sys.optimalityProven)

suite "No-overlap energy lower bound":

    test "the bound proves an optimal makespan (total work on one machine)":
        let (obj, proven) = solve(model(0))
        check obj == 18
        check proven

    test "propagation through the bound proves a release-bound makespan":
        # s4 >= 20: obj >= e4 = s4 + 6 >= 26, the optimum
        let (obj, proven) = solve(model(20))
        check obj == 26
        check proven

    test "an optimum above every bound is not claimed optimal":
        # A fixed at [3, 5) leaves [0, 3) too short for B (4 long): B ends at
        # 9, while propagation (4) and the energy bound (6) stay below
        let (obj, proven) = solve(Gap)
        check obj == 9
        check not proven

    test "the check accepts every bound a solution meets":
        var tr = translate(parseFzn(model(0)))
        let objExpr = if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
                      else: tr.objectiveDefExpr
        tr.sys.resolve(parallel = false, tabuThreshold = 2000, verbose = false)
        for u in [17, 18, 19, 40]:
            let bc = objExpr <= u
            check noOverlapEnergyFeasible(tr.sys.baseArray, bc.relationalState) == (u >= 18)
