import std/[os, packedsets, sequtils, strutils]

import ../expressions/expression
import ../constraints/constraint
import ../constraintSystem
import ../constrainedArray
import ../heuristics/tabuSearch


proc langford*(n: int) =
    let tenure = 6
    let threshold = 100000

    var sys = initConstraintSystem[int]()
    var position = sys.newConstrainedSequence(2*n)
    position.setDomain(toSeq 0..<(2*n))

    for i in 0..<n:
        sys.addConstraint(position[i + n] - position[i] == i + 2)

    sys.addConstraint(allDifferent(position))
    sys.resolve(tenure, threshold)

    var lseq = newSeq[int](2*n)
    var ass = position.getAssignment()

    for i in 0..<n:
        lseq[ass[i]] = i + 1
        lseq[ass[i + n]] = i + 1
    echo lseq


when isMainModule:
   let n = parseInt(paramStr(1))
   langford(n)