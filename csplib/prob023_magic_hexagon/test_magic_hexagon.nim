## CSPLib prob023: Magic Hexagon
## ============================
##
## Place the integers 1 to 19 in a hexagonal pattern of 19 cells such that
## all 15 lines (5 horizontal rows + 5 left diagonals + 5 right diagonals)
## sum to the magic constant 38.
##
##       a  b  c          (cells 0, 1, 2)
##     d  e  f  g         (cells 3, 4, 5, 6)
##   h  i  j  k  l        (cells 7, 8, 9, 10, 11)
##     m  n  o  p         (cells 12, 13, 14, 15)
##       q  r  s          (cells 16, 17, 18)
##
## Model:
##   - Decision variables: hex[0..18], domain = 1..19
##   - allDifferent(hex)
##   - 15 sum constraints: sum of each line == 38
##
## Rows:       {a,b,c}, {d,e,f,g}, {h,i,j,k,l}, {m,n,o,p}, {q,r,s}
## Left diags:  {a,d,h}, {b,e,i,m}, {c,f,j,n,q}, {g,k,o,r}, {l,p,s}
## Right diags: {c,g,l}, {b,f,k,p}, {a,e,j,o,s}, {d,i,n,r}, {h,m,q}
##
## The magic constant 38 is the only possibility: each value 1..19 appears
## in exactly 3 of the 15 lines, so 3 * sum(1..19) = 3 * 190 = 570 = 15 * 38.
##
## There is essentially one unique solution (up to rotation and reflection),
## discovered by Clifford W. Adams in 1957 and confirmed by computer in 1962.
##
## See: https://www.csplib.org/Problems/prob023/

import std/[sequtils, sets, unittest]
import crusher

const
    MagicConstant = 38

    # All 15 lines that must sum to 38
    Lines = [
        # Rows
        @[0, 1, 2],
        @[3, 4, 5, 6],
        @[7, 8, 9, 10, 11],
        @[12, 13, 14, 15],
        @[16, 17, 18],
        # Left diagonals (upper-left to lower-right)
        @[0, 3, 7],
        @[1, 4, 8, 12],
        @[2, 5, 9, 13, 16],
        @[6, 10, 14, 17],
        @[11, 15, 18],
        # Right diagonals (upper-right to lower-left)
        @[2, 6, 11],
        @[1, 5, 10, 15],
        @[0, 4, 9, 14, 18],
        @[3, 8, 13, 17],
        @[7, 12, 16],
    ]


proc solve(tabuThreshold: int = 5000,
           populationSize: int = 16,
           scatterThreshold: int = 1,
           verbose: bool = true): seq[int] =
    var sys = initConstraintSystem[int]()
    var hex = sys.newConstrainedSequence(19)
    hex.setDomain(toSeq(1..19))

    # All cells must have distinct values
    sys.addConstraint(allDifferent(hex))

    # Each of the 15 lines must sum to 38
    for line in Lines:
        var exprs = newSeq[AlgebraicExpression[int]](line.len)
        for i, idx in line:
            exprs[i] = hex[idx]
        sys.addConstraint(sum(exprs) == MagicConstant)

    sys.resolve(parallel=true, tabuThreshold=tabuThreshold,
                populationSize=populationSize,
                scatterThreshold=scatterThreshold, verbose=verbose)

    return hex.assignment


proc verify(assignment: seq[int]) =
    assert assignment.len == 19, "Expected 19 cells"

    # Check all values are in range 1..19
    for i, v in assignment:
        assert v >= 1 and v <= 19,
            "Cell " & $i & " value " & $v & " out of range 1..19"

    # Check all values are distinct
    assert assignment.toHashSet.len == 19, "Values are not all distinct"

    # Check each line sums to 38
    for line in Lines:
        var s = 0
        for idx in line:
            s += assignment[idx]
        assert s == MagicConstant,
            "Line " & $line & " sums to " & $s & ", expected " & $MagicConstant


proc display(assignment: seq[int]) =
    let f = proc(i: int): string =
        let s = $assignment[i]
        if s.len == 1: " " & s else: s
    echo "      ", f(0), " ", f(1), " ", f(2)
    echo "    ", f(3), " ", f(4), " ", f(5), " ", f(6)
    echo "  ", f(7), " ", f(8), " ", f(9), " ", f(10), " ", f(11)
    echo "    ", f(12), " ", f(13), " ", f(14), " ", f(15)
    echo "      ", f(16), " ", f(17), " ", f(18)


suite "CSPLib prob023: Magic Hexagon":

    test "Magic hexagon - all lines sum to 38":
        let assignment = solve()
        display(assignment)
        verify(assignment)
        check assignment.len == 19
        check assignment.toHashSet == toHashSet(toSeq(1..19))
