## Knight's Tour
##
## Find a closed knight's tour on an NxN board: a Hamiltonian circuit
## where a knight visits every square exactly once and returns to start.
##
## Usage:
##   nim c -r --threads:on --mm:arc --deepcopy:on -d:release models/knights_tour.nim 6

import std/[os, sequtils, strutils, strformat]

import crusher

proc knightsTour*(n: int) =
    let numCells = n * n

    # Knight move offsets
    const dx = [-2, -2, -1, -1, 1, 1, 2, 2]
    const dy = [-1, 1, -2, 2, -2, 2, -1, 1]

    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(numCells)

    # Set per-cell domains: each cell can only go to cells reachable by a knight move
    for row in 0..<n:
        for col in 0..<n:
            let cell = row * n + col
            var moves: seq[int] = @[]
            for k in 0..<8:
                let nr = row + dx[k]
                let nc = col + dy[k]
                if nr >= 0 and nr < n and nc >= 0 and nc < n:
                    moves.add(nr * n + nc + 1)  # 1-based successor values
            let pos = x[cell].node.position
            sys.baseArray.setDomain(pos, moves)

    sys.addConstraint(allDifferent(x))
    sys.addConstraint(circuit(x))

    sys.resolve(parallel=true, tabuThreshold=100000, verbose=true)

    let sol = x.assignment()

    # Display the tour as a numbered board
    var board = newSeq[int](numCells)
    var current = 0
    for step in 0..<numCells:
        board[current] = step + 1
        current = sol[current] - 1

    echo &"\nKnight's tour on {n}x{n} board:"
    let width = len($numCells) + 1
    for row in 0..<n:
        var line = ""
        for col in 0..<n:
            line &= align($board[row * n + col], width)
        echo line


when isMainModule:
    let n = if paramCount() >= 1: parseInt(paramStr(1)) else: 6
    knightsTour(n)
