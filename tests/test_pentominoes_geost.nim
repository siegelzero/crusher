## Pentominoes via DFA placement extraction + Geost constraint
##
## Instead of using regular constraints (which scan all 72 board variables through
## a DFA), this extracts valid placements from each tile's DFA and models the
## problem with one variable per tile (selecting a placement) + geost for non-overlap.
##
## Benefits: 10 variables instead of 72, O(cells_per_piece) moveDelta, smooth landscape.

import std/[unittest, strutils, sequtils, tables, os, strformat, packedsets, algorithm]
import crusher

const dataDir = "minizinc_challenge/2008/pentominoes-int"

# ─── DZN parsing ──────────────────────────────────────────────────────────────

type
    TileInfo = object
        nStates: int     # Q (number of DFA states)
        nInputs: int     # S (number of input symbols)
        fStart: int      # Final state range start (1-indexed)
        fEnd: int        # Final state range end (1-indexed)
        dfaOffset: int   # Offset into dfa array

    DznData = object
        width, height, filled, ntiles, size: int
        tiles: seq[TileInfo]
        dfa: seq[int]

proc parseDzn(filename: string): DznData =
    let content = readFile(filename)

    # Extract simple integer values
    proc getIntVal(name: string): int =
        # Match "name = value;" allowing optional spaces
        var idx = content.find(name)
        while idx >= 0:
            # Ensure it's a standalone identifier (not part of another word)
            let afterName = idx + name.len
            if afterName < content.len and content[afterName] in {' ', '=', '\t'}:
                let eqIdx = content.find("=", afterName)
                let semiIdx = content.find(";", eqIdx)
                return content[eqIdx+1..<semiIdx].strip().parseInt()
            idx = content.find(name, idx + 1)
        return 0

    result.width = getIntVal("width")
    result.height = getIntVal("height")
    result.filled = getIntVal("filled")
    result.ntiles = getIntVal("ntiles")
    result.size = getIntVal("size")

    # Extract all integers from a bracketed array section
    proc extractInts(marker: string): seq[int] =
        let start = content.find(marker)
        let bracketStart = content.find("[", start)
        var depth = 0
        var pos = bracketStart
        var endPos = bracketStart
        while pos < content.len:
            if content[pos] == '[': depth += 1
            elif content[pos] == ']':
                depth -= 1
                if depth == 0:
                    endPos = pos
                    break
            pos += 1

        let section = content[bracketStart..endPos]
        result = @[]
        var num = ""
        for ch in section:
            if ch in {'0'..'9'}:
                num.add(ch)
            elif num.len > 0:
                result.add(num.parseInt())
                num = ""
        if num.len > 0:
            result.add(num.parseInt())

    let tileNums = extractInts("tiles")
    result.tiles = @[]
    for i in 0..<result.ntiles:
        result.tiles.add(TileInfo(
            nStates: tileNums[i*5],
            nInputs: tileNums[i*5+1],
            fStart: tileNums[i*5+2],
            fEnd: tileNums[i*5+3],
            dfaOffset: tileNums[i*5+4]
        ))

    result.dfa = extractInts("dfa")

proc buildTransitionTable(data: DznData, tileIdx: int): seq[seq[int]] =
    ## Build Q×S transition table for tile tileIdx (0-indexed)
    let tile = data.tiles[tileIdx]
    result = newSeqWith(tile.nStates, newSeq[int](tile.nInputs))
    for s in 0..<tile.nStates:
        for i in 0..<tile.nInputs:
            result[s][i] = data.dfa[tile.dfaOffset + s * tile.nInputs + i]

# ─── DFA placement extraction ────────────────────────────────────────────────

proc extractPlacements(
    transition: seq[seq[int]],
    nStates: int,
    fStart, fEnd: int,
    tileValue: int,          # 1-indexed tile number
    boardSize: int,
    isSentinel: seq[bool],
    nInputs: int
): seq[seq[int]] =
    ## Extract all valid placement cell sets for a tile from its DFA.
    ## Returns list of cell sets (0-indexed board positions where the tile appears).
    let tileInputIdx = tileValue - 1
    let sentinelInputIdx = nInputs - 1

    # Choose a non-tile, non-sentinel input for "other" cells
    var otherInputIdx = -1
    for idx in 0..<nInputs:
        if idx != tileInputIdx and idx != sentinelInputIdx:
            otherInputIdx = idx
            break
    assert otherInputIdx >= 0

    # Verify all non-tile, non-sentinel inputs give the same transition
    for s in 0..<nStates:
        let expected = transition[s][otherInputIdx]
        for idx in 0..<nInputs:
            if idx == tileInputIdx or idx == sentinelInputIdx: continue
            if transition[s][idx] != expected:
                echo &"WARNING: DFA distinguishes non-tile inputs at state {s+1}: " &
                     &"input {otherInputIdx} -> {expected}, input {idx} -> {transition[s][idx]}"

    # Final states
    var finalStates = initPackedSet[int]()
    for s in fStart..fEnd:
        finalStates.incl(s)

    # Backward reachability: can (pos, state) reach a final state?
    var reachable = newSeqWith(boardSize + 1, newSeq[bool](nStates + 1))
    for s in fStart..fEnd:
        reachable[boardSize][s] = true

    for pos in countdown(boardSize - 1, 0):
        for s in 1..nStates:
            if isSentinel[pos]:
                let ns = transition[s-1][sentinelInputIdx]
                if ns > 0 and ns <= nStates and reachable[pos+1][ns]:
                    reachable[pos][s] = true
            else:
                let nsT = transition[s-1][tileInputIdx]
                if nsT > 0 and nsT <= nStates and reachable[pos+1][nsT]:
                    reachable[pos][s] = true
                let nsO = transition[s-1][otherInputIdx]
                if nsO > 0 and nsO <= nStates and reachable[pos+1][nsO]:
                    reachable[pos][s] = true

    # DFS to enumerate all accepting paths
    var placements: seq[seq[int]] = @[]
    var cells: seq[int] = @[]
    let initialState = 1

    proc dfs(pos: int, state: int) =
        if pos == boardSize:
            if state in finalStates and cells.len > 0:
                placements.add(cells)
            return

        if isSentinel[pos]:
            let ns = transition[state-1][sentinelInputIdx]
            if ns > 0 and ns <= nStates and reachable[pos+1][ns]:
                dfs(pos + 1, ns)
        else:
            # Branch 1: cell is tile t
            let nsT = transition[state-1][tileInputIdx]
            if nsT > 0 and nsT <= nStates and reachable[pos+1][nsT]:
                cells.add(pos)
                dfs(pos + 1, nsT)
                cells.setLen(cells.len - 1)

            # Branch 2: cell is not tile t
            let nsO = transition[state-1][otherInputIdx]
            if nsO > 0 and nsO <= nStates and reachable[pos+1][nsO]:
                dfs(pos + 1, nsO)

    if reachable[0][initialState]:
        dfs(0, initialState)

    return placements

# ─── Helper to extract placements for all tiles ─────────────────────────────

proc extractAllPlacements(data: DznData): seq[seq[seq[int]]] =
    let boardSize = data.width * data.height
    var isSentinel = newSeq[bool](boardSize)
    for h in 0..<data.height:
        isSentinel[h * data.width + data.width - 1] = true

    result = @[]
    for t in 1..data.ntiles:
        let trans = buildTransitionTable(data, t - 1)
        let tile = data.tiles[t - 1]
        let placements = extractPlacements(
            trans, tile.nStates, tile.fStart, tile.fEnd,
            t, boardSize, isSentinel, tile.nInputs
        )
        result.add(placements)

# ─── Display ─────────────────────────────────────────────────────────────────

proc displayBoard(width, height, ntiles: int, assignments: seq[int],
                  allPlacements: seq[seq[seq[int]]]) =
    let fillableWidth = width - 1
    var board = newSeq[int](fillableWidth * height)

    for t in 0..<ntiles:
        let placementIdx = assignments[t]
        for cell in allPlacements[t][placementIdx]:
            let row = cell div width
            let col = cell mod width
            if col < fillableWidth:
                board[row * fillableWidth + col] = t + 1

    for row in 0..<height:
        var line = ""
        for col in 0..<fillableWidth:
            let val = board[row * fillableWidth + col]
            if val == 0:
                line.add(" . ")
            else:
                line.add(&"{val:3d}")
        echo line

# ─── Reusable solve proc ─────────────────────────────────────────────────────

proc solveInstance(instanceFile: string, tabuThreshold: int = 100000,
                   parallel: bool = true, verbose: bool = true): bool =
    let data = parseDzn(instanceFile)
    echo &"\n=== {instanceFile.extractFilename} ==="
    echo &"Board: {data.width}x{data.height}, {data.ntiles} tiles"

    let allPlacements = extractAllPlacements(data)

    var totalArea = 0
    var totalPlacements = 0
    for t in 0..<data.ntiles:
        let p = allPlacements[t]
        let cellCount = if p.len > 0: p[0].len else: 0
        echo &"  Tile {t+1}: {p.len} placements, {cellCount} cells"
        totalArea += cellCount
        totalPlacements += p.len
        if p.len == 0:
            echo &"  ERROR: Tile {t+1} has no valid placements!"
            return false

    let fillableArea = (data.width - 1) * data.height
    echo &"  Total: {totalPlacements} placements, area={totalArea}, board={fillableArea}"
    assert totalArea == fillableArea, "Total tile area must equal fillable board area"

    # Build model
    var sys = initConstraintSystem[int]()
    var tileVars: seq[ConstrainedVariable[int]] = @[]
    var placementPositions: seq[int] = @[]

    for t in 0..<data.ntiles:
        var v = sys.newConstrainedVariable()
        v.setDomain(toSeq(0..<allPlacements[t].len))
        tileVars.add(v)
        placementPositions.add(v.value.node.position)

    sys.addConstraint(geost[int](placementPositions, allPlacements))

    try:
        sys.resolve(parallel = parallel, tabuThreshold = tabuThreshold, verbose = verbose)
    except NoSolutionFoundError:
        echo "  FAILED: No solution found"
        return false

    # Validate: no overlaps
    var cellCoverage = initTable[int, int]()
    var assignments: seq[int] = @[]
    for t in 0..<data.ntiles:
        let p = tileVars[t].assignment
        assignments.add(p)
        for cell in allPlacements[t][p]:
            let c = cellCoverage.getOrDefault(cell, 0)
            if c > 0:
                echo &"  OVERLAP at cell {cell}!"
                return false
            cellCoverage[cell] = c + 1

    echo "Solution:"
    displayBoard(data.width, data.height, data.ntiles, assignments, allPlacements)
    return true

# ─── Tests ───────────────────────────────────────────────────────────────────

suite "Pentominoes with Geost":
    test "Instance 01 (5x4, 5 tiles)":
        check solveInstance(dataDir / "01.dzn", tabuThreshold = 10000, parallel = false)

    test "Instance 02 (9x8, 10 tiles)":
        check solveInstance(dataDir / "02.dzn")

    test "Instance 03 (11x10, 8 tiles)":
        check solveInstance(dataDir / "03.dzn")

    test "Instance 05 (11x6, 12 tiles)":
        check solveInstance(dataDir / "05.dzn")

    test "Instance 06 (13x5, 12 tiles)":
        check solveInstance(dataDir / "06.dzn")
