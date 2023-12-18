import std/[packedsets, strformat, times]

import state/[arrayState, domain]
import heuristics/tabuSearch
import models


when isMainModule:
    let
        trials = 1
        n = 30
        # x = ageProblem()
        # x = sendMoreMoney()
        # x = magicSquare(n)
        # x = magicSquare2(n)
        x = latinSquares(n)
    
    let then = epochTime()

    for i in 0..<trials:
        var sol = x.findAssignment(100000)
        for j in 0..<n:
            echo sol[j*n..<(j + 1)*n]
        echo fmt"Found {i + 1} / {trials}"
    # let p = parallelSearch(x, 100000)

    let now = epochTime()
    let diff = now - then

    echo fmt"Average: {diff / float(trials):.3f}"