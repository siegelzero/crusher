import std/[sequtils, tables, unittest]
import crusher
import flatzinc/[parser, translator]

suite "LexOrder":

    test "lexLt - strict lexicographic ordering":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        var y = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(1..5))
        y.setDomain(toSeq(1..5))

        let xpos = toSeq(0..2)
        let ypos = toSeq(3..5)
        sys.addConstraint(lexLt[int](xpos, ypos))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let ax = x.assignment()
        let ay = y.assignment()

        # Verify x is lexicographically < y
        var isLess = false
        for i in 0..<3:
            if ax[i] < ay[i]:
                isLess = true
                break
            elif ax[i] > ay[i]:
                isLess = false
                break
        check isLess

    test "lexLe - non-strict allows equality":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        var y = sys.newConstrainedSequence(3)
        x.setDomain(@[3])
        y.setDomain(@[3])

        let xpos = toSeq(0..2)
        let ypos = toSeq(3..5)
        sys.addConstraint(lexLe[int](xpos, ypos))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let ax = x.assignment()
        let ay = y.assignment()

        # Equal sequences should satisfy lexLe
        check ax == ay


proc isLexLess(a, b: seq[int]): bool =
  for i in 0..<a.len:
    if a[i] < b[i]: return true
    if a[i] > b[i]: return false
  false  # equal

proc isLexLessEq(a, b: seq[int]): bool =
  for i in 0..<a.len:
    if a[i] < b[i]: return true
    if a[i] > b[i]: return false
  true  # equal → <=

suite "LexOrder FlatZinc dispatch":
    ## Round-trip tests for fzn_lex_{less,lesseq}_{int,bool} in translatorCore.nim.
    ## Ensures the native predicate signatures registered in mznlib are wired
    ## through to lexLt/lexLe at the constraint-system level.

    test "fzn_lex_less_int: strict int ordering":
        let src = """
var 1..5: x1 :: output_var;
var 1..5: x2 :: output_var;
var 1..5: x3 :: output_var;
var 1..5: y1 :: output_var;
var 1..5: y2 :: output_var;
var 1..5: y3 :: output_var;
constraint int_eq(x1, 2);
constraint int_eq(x2, 2);
constraint int_eq(x3, 2);
constraint fzn_lex_less_int([x1,x2,x3], [y1,y2,y3]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let xVals = @[
            tr.sys.assignment[tr.varPositions["x1"]],
            tr.sys.assignment[tr.varPositions["x2"]],
            tr.sys.assignment[tr.varPositions["x3"]]]
        let yVals = @[
            tr.sys.assignment[tr.varPositions["y1"]],
            tr.sys.assignment[tr.varPositions["y2"]],
            tr.sys.assignment[tr.varPositions["y3"]]]
        check xVals == @[2, 2, 2]
        check isLexLess(xVals, yVals)

    test "fzn_lex_lesseq_int: non-strict int ordering permits equality":
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 1..3: y1 :: output_var;
var 1..3: y2 :: output_var;
var 1..3: y3 :: output_var;
constraint int_eq(x1, 3);
constraint int_eq(x2, 3);
constraint int_eq(x3, 3);
constraint int_eq(y1, 3);
constraint int_eq(y2, 3);
constraint int_eq(y3, 3);
constraint fzn_lex_lesseq_int([x1,x2,x3], [y1,y2,y3]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let xVals = @[
            tr.sys.assignment[tr.varPositions["x1"]],
            tr.sys.assignment[tr.varPositions["x2"]],
            tr.sys.assignment[tr.varPositions["x3"]]]
        let yVals = @[
            tr.sys.assignment[tr.varPositions["y1"]],
            tr.sys.assignment[tr.varPositions["y2"]],
            tr.sys.assignment[tr.varPositions["y3"]]]
        check xVals == yVals
        check isLexLessEq(xVals, yVals)

    test "fzn_lex_less_bool: strict bool ordering":
        let src = """
var bool: x1 :: output_var;
var bool: x2 :: output_var;
var bool: x3 :: output_var;
var bool: x4 :: output_var;
var bool: y1 :: output_var;
var bool: y2 :: output_var;
var bool: y3 :: output_var;
var bool: y4 :: output_var;
constraint bool_eq(x1, true);
constraint bool_eq(x2, false);
constraint bool_eq(x3, false);
constraint bool_eq(x4, false);
constraint fzn_lex_less_bool([x1,x2,x3,x4], [y1,y2,y3,y4]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let xVals = @[
            tr.sys.assignment[tr.varPositions["x1"]],
            tr.sys.assignment[tr.varPositions["x2"]],
            tr.sys.assignment[tr.varPositions["x3"]],
            tr.sys.assignment[tr.varPositions["x4"]]]
        let yVals = @[
            tr.sys.assignment[tr.varPositions["y1"]],
            tr.sys.assignment[tr.varPositions["y2"]],
            tr.sys.assignment[tr.varPositions["y3"]],
            tr.sys.assignment[tr.varPositions["y4"]]]
        # x is fixed to [1,0,0,0], so y must be strictly greater lexicographically.
        check xVals == @[1, 0, 0, 0]
        check isLexLess(xVals, yVals)

    test "fzn_lex_lesseq_bool: non-strict bool ordering permits equality":
        let src = """
var bool: x1 :: output_var;
var bool: x2 :: output_var;
var bool: x3 :: output_var;
var bool: y1 :: output_var;
var bool: y2 :: output_var;
var bool: y3 :: output_var;
constraint bool_eq(x1, false);
constraint bool_eq(x2, true);
constraint bool_eq(x3, false);
constraint bool_eq(y1, false);
constraint bool_eq(y2, true);
constraint bool_eq(y3, false);
constraint fzn_lex_lesseq_bool([x1,x2,x3], [y1,y2,y3]);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let xVals = @[
            tr.sys.assignment[tr.varPositions["x1"]],
            tr.sys.assignment[tr.varPositions["x2"]],
            tr.sys.assignment[tr.varPositions["x3"]]]
        let yVals = @[
            tr.sys.assignment[tr.varPositions["y1"]],
            tr.sys.assignment[tr.varPositions["y2"]],
            tr.sys.assignment[tr.varPositions["y3"]]]
        check xVals == yVals
