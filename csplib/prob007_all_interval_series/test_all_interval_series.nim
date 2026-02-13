## CSPLib prob007: All-Interval Series
## ====================================
##
## Find a sequence s = (s_0, s_1, ..., s_{n-1}) such that:
##   - s is a permutation of {0, 1, ..., n-1}
##   - The interval vector v = (|s_1 - s_0|, |s_2 - s_1|, ..., |s_{n-1} - s_{n-2}|)
##     is a permutation of {1, 2, ..., n-1}
##
## Originated from music theory (twelve-tone technique): find a sequence of
## pitch-classes where every pitch-class and every interval appears exactly once.
##
## Model:
##   - Decision variables: series[0..n-1], domain = 0..n-1
##   - Auxiliary variables: intervals[0..n-2], domain = 1..n-1
##   - allDifferent(series)
##   - For each i: intervals[i] == abs(series[i+1] - series[i])
##   - allDifferent(intervals)
##   - Symmetry breaking: series[0] < series[n-1]
##
## Known solution counts (not counting symmetries):
##   n=2: 1, n=3: 1, n=4: 2, n=5: 3, n=6: 10, n=8: 36, n=10: 218, n=12: 1060
##
## See: https://www.csplib.org/Problems/prob007/

import std/[sequtils, sets, unittest]
import crusher

proc solve(n: int,
           tabuThreshold: int = 5000,
           scatterThreshold: int = 1,
           populationSize: int = 16,
           verbose: bool = true): seq[int] =
    var sys = initConstraintSystem[int]()
    var series = sys.newConstrainedSequence(n)
    series.setDomain(toSeq(0..<n))

    # Auxiliary variables for intervals between consecutive elements
    let numIntervals = n - 1
    var intervals = sys.newConstrainedSequence(numIntervals)
    intervals.setDomain(toSeq(1..<n))

    # Series is a permutation of 0..n-1
    sys.addConstraint(allDifferent(series))

    # Link intervals to series: intervals[i] == abs(series[i+1] - series[i])
    for i in 0..<numIntervals:
        sys.addConstraint(intervals[i] == abs(series[i+1] - series[i]))

    # All intervals must be distinct
    sys.addConstraint(allDifferent(intervals))

    # Symmetry breaking
    sys.addConstraint(series[0] < series[n-1])
    sys.addConstraint(intervals[0] > intervals[numIntervals - 1])

    sys.resolve(parallel=true, tabuThreshold=tabuThreshold,
                scatterThreshold=scatterThreshold,
                populationSize=populationSize, verbose=verbose)

    return series.assignment


proc verify(assignment: seq[int]) =
    let n = assignment.len

    # Check it's a permutation of 0..n-1
    var values = initHashSet[int]()
    for v in assignment:
        assert v >= 0 and v < n,
            "Value " & $v & " out of range [0, " & $(n-1) & "]"
        assert v notin values,
            "Duplicate value " & $v & " in series"
        values.incl(v)

    # Check all intervals are distinct and cover 1..n-1
    var intervals = initHashSet[int]()
    for i in 0..<n-1:
        let d = abs(assignment[i+1] - assignment[i])
        assert d >= 1 and d < n,
            "Interval " & $d & " out of range [1, " & $(n-1) & "]"
        assert d notin intervals,
            "Duplicate interval " & $d & " between positions " & $i &
            " and " & $(i+1)
        intervals.incl(d)


suite "CSPLib prob007: All-Interval Series":

    test "All-interval series n=8":
        let assignment = solve(8)
        echo "Solution: ", assignment
        verify(assignment)
        check assignment.len == 8

    test "All-interval series n=12":
        let assignment = solve(12, tabuThreshold=10000, scatterThreshold=10)
        echo "Solution: ", assignment
        verify(assignment)
        check assignment.len == 12

    test "All-interval series n=14":
        let assignment = solve(14, tabuThreshold=10000, scatterThreshold=10)
        echo "Solution: ", assignment
        verify(assignment)
        check assignment.len == 14

