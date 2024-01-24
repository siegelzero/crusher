import std/[os, sequtils, strutils]

import crusher


proc nQueens*(n: int) =
    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(n)
    x.setDomain(toSeq 0..<n)

    var terms: seq[Expression[int]] = @[]
    for i in 0..<n:
        terms.add(x[i])
    sys.addConstraint(allDifferent(terms))

    terms.reset()
    for i in 0..<n:
        terms.add(x[i] - i)
    sys.addConstraint(allDifferent(terms))

    terms.reset()
    for i in 0..<n:
        terms.add(x[i] + i)
    sys.addConstraint(allDifferent(terms))

    sys.resolve()

    echo x


when isMainModule:
    let n = parseInt(paramStr(1))
    nQueens(n)