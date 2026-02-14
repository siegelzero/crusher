import unittest
import std/[sequtils, strutils]

import flatzinc/parser

suite "FlatZinc Parser":

  test "parse simple variable declarations":
    let src = """
var 1..10: x;
var -5..5: y;
"""
    let model = parseFzn(src)
    check model.variables.len == 2
    check model.variables[0].name == "x"
    check model.variables[0].varType.kind == FznIntRange
    check model.variables[0].varType.lo == 1
    check model.variables[0].varType.hi == 10
    check model.variables[1].name == "y"
    check model.variables[1].varType.lo == -5
    check model.variables[1].varType.hi == 5

  test "parse set domain variable":
    let src = """
var {0,2,3,4}: x;
"""
    let model = parseFzn(src)
    check model.variables.len == 1
    check model.variables[0].varType.kind == FznIntSet
    check model.variables[0].varType.values == @[0, 2, 3, 4]

  test "parse parameter array":
    let src = """
array [1..3] of int: c = [1,-4,2];
"""
    let model = parseFzn(src)
    check model.parameters.len == 1
    check model.parameters[0].name == "c"
    check model.parameters[0].isArray == true
    check model.parameters[0].arraySize == 3
    check model.parameters[0].value.kind == FznArrayLit
    check model.parameters[0].value.elems.len == 3
    check model.parameters[0].value.elems[0].intVal == 1
    check model.parameters[0].value.elems[1].intVal == -4
    check model.parameters[0].value.elems[2].intVal == 2

  test "parse variable array with output_array annotation":
    let src = """
var 1..5: X1;
var 1..5: X2;
var 1..5: X3;
array [1..3] of var int: x:: output_array([1..3]) = [X1,X2,X3];
"""
    let model = parseFzn(src)
    check model.variables.len == 4  # 3 scalar vars + 1 array
    let arrDecl = model.variables[3]
    check arrDecl.name == "x"
    check arrDecl.isArray == true
    check arrDecl.hasAnnotation("output_array")
    check arrDecl.value.kind == FznArrayLit
    check arrDecl.value.elems.len == 3

  test "parse constraint":
    let src = """
var 1..10: x;
var 1..10: y;
constraint int_lin_eq([1,1],[x,y],10);
solve satisfy;
"""
    let model = parseFzn(src)
    check model.constraints.len == 1
    check model.constraints[0].name == "int_lin_eq"
    check model.constraints[0].args.len == 3
    check model.constraints[0].args[0].kind == FznArrayLit
    check model.constraints[0].args[1].kind == FznArrayLit
    check model.constraints[0].args[2].kind == FznIntLit

  test "parse constraint with annotations":
    let src = """
var 1..10: x;
constraint int_lin_eq([1,-1],[x,x],-3):: domain:: defines_var(x);
solve satisfy;
"""
    let model = parseFzn(src)
    check model.constraints.len == 1
    check model.constraints[0].hasAnnotation("domain")
    check model.constraints[0].hasAnnotation("defines_var")

  test "parse solve satisfy":
    let src = """
solve satisfy;
"""
    let model = parseFzn(src)
    check model.solve.kind == Satisfy

  test "parse solve minimize":
    let src = """
var 1..100: obj;
solve minimize obj;
"""
    let model = parseFzn(src)
    check model.solve.kind == Minimize
    check model.solve.objective.kind == FznIdent
    check model.solve.objective.ident == "obj"

  test "parse solve with annotations":
    let src = """
var 1..100: obj;
solve :: int_search([obj], input_order, indomain_min, complete) minimize obj;
"""
    let model = parseFzn(src)
    check model.solve.kind == Minimize
    check model.solve.annotations.len == 1
    check model.solve.annotations[0].name == "int_search"

  test "parse predicate declaration (skip)":
    let src = """
predicate gecode_all_different_int(array [int] of var int: x);
var 1..5: x;
solve satisfy;
"""
    let model = parseFzn(src)
    check model.variables.len == 1
    check model.variables[0].name == "x"

  test "parse comments":
    let src = """
% This is a comment
var 1..5: x;
% Another comment
solve satisfy;
"""
    let model = parseFzn(src)
    check model.variables.len == 1

  test "parse test_negative_gecode.fzn":
    let model = parseFznFile("models/minizinc/test_negative_gecode.fzn")
    check model.variables.len == 6  # 5 scalar vars + 1 array
    check model.parameters.len == 2  # 2 constant arrays
    check model.constraints.len == 4
    check model.solve.kind == Satisfy

    # Check variable domains include negatives
    check model.variables[0].varType.kind == FznIntRange
    check model.variables[0].varType.lo == -10
    check model.variables[0].varType.hi == 10

    # Check constraint types
    check model.constraints[0].name == "gecode_all_different_int"
    check model.constraints[1].name == "int_lin_le"
    check model.constraints[2].name == "int_lin_le"
    check model.constraints[3].name == "int_lin_eq"

  test "parse cumulative_test_gecode.fzn":
    let model = parseFznFile("models/minizinc/cumulative_test_gecode.fzn")
    check model.solve.kind == Minimize
    check model.solve.objective.kind == FznIdent

    # Check it has the cumulative constraint
    var hasCumulative = false
    for c in model.constraints:
      if "cumulative" in c.name.toLowerAscii:
        hasCumulative = true
        break
    check hasCumulative

  test "parse output_var annotation":
    let src = """
var 0..10: limitx:: output_var;
solve satisfy;
"""
    let model = parseFzn(src)
    check model.variables.len == 1
    check model.variables[0].hasAnnotation("output_var")

  test "parse bool variables":
    let src = """
var bool: b;
solve satisfy;
"""
    let model = parseFzn(src)
    check model.variables.len == 1
    check model.variables[0].varType.kind == FznBool

  test "parse multiple annotations on variable":
    let src = """
var 1..20: X_INTRODUCED_37_ ::var_is_introduced :: is_defined_var;
solve satisfy;
"""
    let model = parseFzn(src)
    check model.variables.len == 1
    check model.variables[0].hasAnnotation("var_is_introduced")
    check model.variables[0].hasAnnotation("is_defined_var")
