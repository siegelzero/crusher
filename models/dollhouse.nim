import std/[os, sequtils, strformat, strutils]

import crusher


proc cycleGraph(n: int): seq[seq[int]] =
    var graph = newSeq[seq[int]](n)
    for i in 0..<n:
        graph[i] = newSeq[int](n)
    
    for i in 0..<n-1:
        graph[i][i + 1] = 1
        graph[i + 1][i] = 1
    
    graph[0][n - 1] = 1
    graph[n - 1][0] = 1

    return graph


proc inducedDollhouse*(n: int) =
    var sys = initConstraintSystem[int]()
    var label = sys.newConstrainedSequence(n)
    label.setDomain(toSeq 2..1000)

    sys.addConstraint(allDifferent(label))

    let graph = cycleGraph(n)

    for i in 0..<n:
        for j in 0..<i:
            if graph[i][j] == 1:
                sys.addConstraint(commonFactor(label[i], label[j]))
            else:
                sys.addConstraint(coPrime(label[i], label[j]))
    
    var labelSum = sum(label)
    sys.minimize(labelSum)

    echo fmt"Found labeling: {label}"
    echo fmt"cost: {labelSum.value}"


when isMainModule:
    let n = parseInt(paramStr(1))
    inducedDollhouse(n)
