## Direct de Bruijn binary sequence test using Crusher's native API.
## Models the problem with only binary variables + expression-based all_different.
##
## de Bruijn sequence B(2,n): a cyclic sequence of 2^n binary digits where
## every n-bit pattern appears exactly once as a contiguous substring.

import std/[sequtils, unittest, algorithm]

import crusher

suite "de Bruijn binary sequence":
  test "B(2,3) - 8 binary digits":
    let n = 3
    let m = 1 shl n  # 2^n = 8

    var sys = initConstraintSystem[int]()
    var b = sys.newConstrainedSequence(m)
    b.setDomain(@[0, 1])

    # Build expressions for the sliding window values:
    # x[i] = sum_j(b[(i+j) mod m] * 2^(n-1-j)) for j=0..n-1
    var windowExprs: seq[AlgebraicExpression[int]]
    for i in 0..<m:
      var expr = (1 shl (n - 1)) * b[(i + 0) mod m]
      for j in 1..<n:
        expr = expr + (1 shl (n - 1 - j)) * b[(i + j) mod m]
      windowExprs.add(expr)

    # All sliding windows must be different (each n-bit pattern appears once)
    sys.addConstraint(allDifferent[int](windowExprs))

    # Equal counts of 0s and 1s
    sys.addConstraint(b.sum() == m div 2)

    sys.resolve(parallel = true, tabuThreshold = 5000)

    let sol = b.assignment()
    echo "B(2,3) solution: ", sol

    # Verify: all 8 windows of width 3 are distinct
    var windows: seq[int]
    for i in 0..<m:
      var w = 0
      for j in 0..<n:
        w = w * 2 + sol[(i + j) mod m]
      windows.add(w)

    echo "Windows: ", windows
    let sorted = windows.sorted()
    check sorted == toSeq(0..<m)
    check sol.foldl(a + b) == m div 2

  test "B(2,7) - 128 binary digits":
    let n = 7
    let m = 1 shl n  # 2^7 = 128

    var sys = initConstraintSystem[int]()
    var b = sys.newConstrainedSequence(m)
    b.setDomain(@[0, 1])

    # Build sliding window expressions
    var windowExprs: seq[AlgebraicExpression[int]]
    for i in 0..<m:
      var expr = (1 shl (n - 1)) * b[(i + 0) mod m]
      for j in 1..<n:
        expr = expr + (1 shl (n - 1 - j)) * b[(i + j) mod m]
      windowExprs.add(expr)

    # All sliding windows must be different
    sys.addConstraint(allDifferent[int](windowExprs))

    # Equal counts
    sys.addConstraint(b.sum() == m div 2)

    sys.resolve(parallel = true, tabuThreshold = 10000, verbose = true)

    let sol = b.assignment()

    # Verify
    var windows: seq[int]
    for i in 0..<m:
      var w = 0
      for j in 0..<n:
        w = w * 2 + sol[(i + j) mod m]
      windows.add(w)

    let sorted = windows.sorted()
    check sorted == toSeq(0..<m)
    check sol.foldl(a + b) == m div 2
