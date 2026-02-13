## CSPLib prob006: Golomb Ruler
## ============================
##
## A Golomb ruler is a set of integers (marks) 0 = a(1) < a(2) < ... < a(n)
## such that all pairwise differences a(i) - a(j) (i > j) are distinct.
## The length of the ruler is a(n). We seek the shortest ruler for a given
## number of marks (an optimal Golomb ruler).
##
## Model:
##   - Decision variables: marks[0..n-1], domain = 0..2^(n-1)-1
##   - Auxiliary variables: diffs[0..k-1] where k = n*(n-1)/2, domain = 1..2^(n-1)-1
##   - marks[0] = 0
##   - strictlyIncreasing(marks)
##   - For each pair (i > j): diffs[idx] == marks[i] - marks[j]
##   - allDifferent(diffs)
##   - Symmetry breaking: marks[1] - marks[0] < marks[n-1] - marks[n-2]
##   - Minimize marks[n-1]
##
## Known optimal rulers:
##   n=4: length 6   [0, 1, 4, 6]
##   n=5: length 11  [0, 1, 4, 9, 11] or [0, 2, 7, 8, 11]
##   n=6: length 17  [0, 1, 4, 10, 12, 17]
##   n=7: length 25  [0, 1, 4, 10, 18, 23, 25]
##   n=8: length 34  [0, 1, 4, 9, 15, 22, 32, 34]
##
## See: https://www.csplib.org/Problems/prob006/

import std/[sequtils, sets, unittest]
import crusher

proc solve(n: int,
           tabuThreshold: int = 5000,
           scatterThreshold: int = 1,
           populationSize: int = 16,
           verbose: bool = true): seq[int] =
    var sys = initConstraintSystem[int]()
    var marks = sys.newConstrainedSequence(n)

    let upperBound = (1 shl (n - 1)) - 1  # 2^(n-1) - 1
    marks.setDomain(toSeq(0..upperBound))

    # Auxiliary variables for pairwise differences
    let numDiffs = n * (n - 1) div 2
    var diffs = sys.newConstrainedSequence(numDiffs)
    diffs.setDomain(toSeq(1..upperBound))

    # First mark is 0
    sys.addConstraint(marks[0] == 0)

    # Marks are strictly increasing
    sys.addConstraint(strictlyIncreasing(marks))

    # Link diffs to marks: for each pair (i > j), diffs[idx] == marks[i] - marks[j]
    var idx = 0
    for i in 0..<n:
        for j in 0..<i:
            sys.addConstraint(diffs[idx] == marks[i] - marks[j])
            idx += 1

    # All pairwise differences must be distinct
    sys.addConstraint(allDifferent(diffs))

    # Symmetry breaking: first gap < last gap
    sys.addConstraint(marks[1] - marks[0] < marks[n-1] - marks[n-2])

    # Minimize the ruler length (last mark)
    minimize(sys, marks[n-1], parallel=true, tabuThreshold=tabuThreshold,
             scatterThreshold=scatterThreshold,
             populationSize=populationSize, verbose=verbose)

    return marks.assignment


proc verify(assignment: seq[int]) =
    let n = assignment.len

    # Check first mark is 0
    assert assignment[0] == 0, "First mark must be 0, got " & $assignment[0]

    # Check strictly increasing
    for i in 1..<n:
        assert assignment[i] > assignment[i-1],
            "Marks not strictly increasing at position " & $i &
            ": " & $assignment[i-1] & " >= " & $assignment[i]

    # Check all pairwise differences are distinct
    var diffs = initHashSet[int]()
    for i in 0..<n:
        for j in 0..<i:
            let d = assignment[i] - assignment[j]
            assert d notin diffs,
                "Duplicate difference " & $d & " between marks[" & $i &
                "]=" & $assignment[i] & " and marks[" & $j & "]=" & $assignment[j]
            diffs.incl(d)


suite "CSPLib prob006: Golomb Ruler":

    test "4-mark Golomb ruler (optimal length 6)":
        let assignment = solve(4)
        echo "Solution: ", assignment
        echo "Ruler length: ", assignment[^1]
        verify(assignment)
        check assignment.len == 4
        check assignment[0] == 0
        check assignment[^1] == 6

    test "6-mark Golomb ruler (optimal length 17)":
        let assignment = solve(6, tabuThreshold=10000, scatterThreshold=10)
        echo "Solution: ", assignment
        echo "Ruler length: ", assignment[^1]
        verify(assignment)
        check assignment.len == 6
        check assignment[0] == 0
        check assignment[^1] == 17
