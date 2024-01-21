import std/[sequtils, strformat, strutils]

import crusher


proc mip*() =
    let n = 5

    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(n)
    x.setDomain(toSeq 0..1)

    sys.addConstraint(-x[0] + 3*x[1] - 5*x[2] - x[3] + 4*x[4] <= -2)
    sys.addConstraint(2*x[0] - 6*x[1] + 3*x[2] + 2*x[3] - 2*x[4] <= 0)
    sys.addConstraint(x[1] - 2*x[2] + x[3] + x[4] <= -1)

    let objective = 5*x[0] + 7*x[1] + 10*x[2] + 3*x[3] + x[4]
    let assignment = sys.minimize(objective)

    doAssert assignment == @[0, 1, 1, 0, 0]


when isMainModule:
    mip()