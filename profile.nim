import std/[packedsets, strformat, times]

import state/[arrayState, domain]
import heuristics/tabuSearch
import models


when isMainModule:
    let
        trials = 1
        n = 5
        # x = ageProblem()
        # x = sendMoreMoney()
        # x = magicSquare(n)
        # x = magicSquare2(n)
        x = latinSquares(30)
    
    let then = cpuTime()

    for i in 0..<trials:
        echo x.findAssignment(100000)
        echo fmt"Found {i + 1} / {trials}"

    let now = cpuTime()
    let diff = now - then

    echo fmt"Average: {diff / float(trials):.3f}"