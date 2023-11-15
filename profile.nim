import std/[packedsets, strformat, times]
import heuristics
import constrainedArrayState
import models

when isMainModule:
    let
        trials = 100
        n = 30
        # x = magicSquare(n)
        x = latinSquares(n)

    let then = cpuTime()

    for i in 0..<trials:
        echo x.findAssignment(10000)
        echo fmt"Found {i + 1} / {trials}"

    let now = cpuTime()
    let diff = now - then

    echo fmt"Average: {diff / float(trials):.3f}"