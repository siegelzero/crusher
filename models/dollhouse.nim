import std/[os, sequtils, strformat, strutils]

import crusher


proc squareFree(n: int): seq[int] =
    var B = newSeq[int](n + 1)
    for i in 2..n:
        B[i] = 1
    
    for i in 2..n:
        if i*i > n:
            break
        if B[i] == 1:
            for mult in countup(i*i, n, i*i):
                B[mult] = 0
    
    for i in 2..n:
        if B[i] == 1:
            result.add(i)


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


proc gridGraph*(n: int): seq[seq[int]] =
    var graph = newSeq[seq[int]](n*n)
    for i in 0..<n*n:
        graph[i] = newSeq[int](n*n)
    
    if n == 2:
        # 0 -- 1
        # |    |
        # 2 -- 3
        # translates to adjacenty matrix
        # 0 1 1 0
        # 1 0 0 1
        # 1 0 0 1
        # 0 1 1 0
        graph[0][1] = 1
        graph[0][2] = 1
        graph[1][0] = 1
        graph[1][3] = 1
        graph[2][0] = 1
        graph[2][3] = 1
        graph[3][1] = 1
        graph[3][2] = 1
    
    elif n == 3:
        # 0 -- 1 -- 2
        # |    |    |
        # 3 -- 4 -- 5
        # |    |    |
        # 6 -- 7 -- 8
        # 0 1 0 1 0 0 0 0 0
        # 1 0 1 0 1 0 0 0 0
        # 0 1 0 0 0 1 0 0 0
        # 1 0 0 0 1 0 1 0 0
        # 0 1 0 1 0 1 0 1 0
        # 0 0 1 0 1 0 0 0 1
        # 0 0 0 1 0 0 0 1 0
        # 0 0 0 0 1 0 1 0 1
        # 0 0 0 0 0 1 0 1 0

        graph[0][1] = 1
        graph[0][3] = 1
        graph[1][0] = 1
        graph[1][2] = 1
        graph[1][4] = 1
        graph[2][1] = 1
        graph[2][5] = 1
        graph[3][0] = 1
        graph[3][4] = 1
        graph[3][6] = 1
        graph[4][1] = 1
        graph[4][3] = 1
        graph[4][5] = 1
        graph[4][7] = 1
        graph[5][2] = 1
        graph[5][4] = 1
        graph[5][8] = 1
        graph[6][3] = 1
        graph[6][7] = 1
        graph[7][4] = 1
        graph[7][6] = 1
        graph[7][8] = 1
        graph[8][5] = 1
        graph[8][7] = 1

    return graph


proc inducedDollhouse*(n, b: int) =
    # let graph = cycleGraph(n)
    let graph = gridGraph(n)

    var sys = initConstraintSystem[int]()
    var label: ConstrainedSequence[int] = sys.newConstrainedSequence(graph.len)
    label.setDomain(squareFree(b))
    sys.addConstraint(allDifferent(label))

    for i in 0..<graph.len:
        for j in 0..<i:
            if graph[i][j] == 1:
                sys.addConstraint(commonFactor(label[i], label[j]))
            else:
                sys.addConstraint(coPrime(label[i], label[j]))
    
    var labelSum: SumExpression[int] = sum(label)
    sys.minimize(labelSum, tabuThreshold=100000, maxAttempts=10, attemptThreshold=10)

    echo fmt"Found labeling: {label}"
    echo fmt"sum: {labelSum}"


when isMainModule:
    let n = parseInt(paramStr(1))
    let b = parseInt(paramStr(2))
    inducedDollhouse(n, b)
