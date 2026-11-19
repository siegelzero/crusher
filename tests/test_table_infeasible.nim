## A table constraint that no tuple can satisfy once its fixed columns are
## filtered emits no constraint; the translator must record the model as
## infeasible (fzcrusher then reports UNKNOWN) instead of letting the search
## print an assignment that violates the dropped table.

import unittest
import std/strutils
import crusher
import flatzinc/[parser, translator]

suite "Table infeasibility":

    test "constant columns match no tuple":
        let src = """
predicate fzn_table_int(array [int] of var int: x,array [int] of int: t);
array [1..12] of int: T = [1,1,1,1,3,2,2,2,3,3,1,1];
var 1..3: z:: output_var;
array [1..3] of var int: A ::var_is_introduced  = [1,2,z];
constraint fzn_table_int(A,T);
solve  satisfy;
"""
        let tr = translate(parseFzn(src))
        check tr.infeasibleReasons.len == 1
        check "table" in tr.infeasibleReasons[0]

    test "singleton-domain columns match no tuple":
        let src = """
predicate fzn_table_int(array [int] of var int: x,array [int] of int: t);
array [1..6] of int: T = [1,1,1,2,3,3];
var 2..2: a:: output_var;
var 1..3: b:: output_var;
array [1..2] of var int: A ::var_is_introduced  = [a,b];
constraint fzn_table_int(A,T);
solve  satisfy;
"""
        let tr = translate(parseFzn(src))
        check tr.infeasibleReasons.len == 1

    test "satisfiable table is not flagged":
        let src = """
predicate fzn_table_int(array [int] of var int: x,array [int] of int: t);
array [1..6] of int: T = [1,1,2,2,3,3];
var 2..2: a:: output_var;
var 1..3: b:: output_var;
array [1..2] of var int: A ::var_is_introduced  = [a,b];
constraint fzn_table_int(A,T);
solve  satisfy;
"""
        let tr = translate(parseFzn(src))
        check tr.infeasibleReasons.len == 0
