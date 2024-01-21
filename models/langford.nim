import std/[os, sequtils, strutils]

import crusher


proc langford*(n: int) =
    var sys = initConstraintSystem[int]()
    var position = sys.newConstrainedSequence(2*n)
    position.setDomain(toSeq 0..<(2*n))

    for i in 0..<n:
        sys.addConstraint(position[i + n] - position[i] == i + 2)

    sys.addConstraint(allDifferent(position))
    sys.resolve(1000, 100)

    var lseq = newSeq[int](2*n)
    var ass = position.getAssignment()

    for i in 0..<n:
        lseq[ass[i]] = i + 1
        lseq[ass[i + n]] = i + 1
    echo lseq


when isMainModule:
   let n = parseInt(paramStr(1))
   langford(n)