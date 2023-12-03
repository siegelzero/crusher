import std/[packedsets, strformat, times]

import state/[arrayState, domain]
import heuristics/tabuSearch
import models


when isMainModule:
    let
        trials = 1
        n = 6
        x = magicSquare(n)
        # x = latinSquares(n)
    
    let then = cpuTime()

    for i in 0..<trials:
        echo x.findAssignment(10000)
        echo fmt"Found {i + 1} / {trials}"

    let now = cpuTime()
    let diff = now - then

    echo fmt"Average: {diff / float(trials):.3f}"