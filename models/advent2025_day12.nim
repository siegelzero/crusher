import std/[os, sequtils, strutils, strformat, algorithm]

import ../src/crusher

type
    Shape = seq[seq[int]]

    Region = object
        width, height: int
        shapeCounts: seq[int]

    Placement = object
        cells: seq[int]

proc parseInput(filename: string): (seq[Shape], seq[Region]) =
    var shapes: seq[Shape] = @[]
    var regions: seq[Region] = @[]
    let lines = readFile(filename).splitLines()
    var i = 0

    while i < lines.len:
        let line = lines[i].strip()
        if line.len == 0:
            i += 1
            continue

        if 'x' in line:
            let parts = line.split(":")
            let sizeParts = parts[0].strip().split("x")
            let width = parseInt(sizeParts[0])
            let height = parseInt(sizeParts[1])
            let counts = parts[1].strip().split().mapIt(parseInt(it))
            regions.add(Region(width: width, height: height, shapeCounts: counts))
            i += 1
        elif ':' in line:
            # Parse shape with dynamic size
            var shapeRows: seq[seq[int]] = @[]
            i += 1
            while i < lines.len and lines[i].len > 0 and lines[i][0] in {'#', '.'}:
                var row: seq[int] = @[]
                for c in lines[i]:
                    row.add(if c == '#': 1 else: 0)
                shapeRows.add(row)
                i += 1
            shapes.add(shapeRows)
        else:
            i += 1

    return (shapes, regions)

proc countCells(shape: Shape): int =
    for row in shape:
        for cell in row:
            result += cell

proc shapeHeight(shape: Shape): int = shape.len
proc shapeWidth(shape: Shape): int =
    if shape.len == 0: 0 else: shape[0].len

proc rotateShape(shape: Shape): Shape =
    # Rotate shape 90 degrees clockwise
    let h = shape.shapeHeight
    let w = shape.shapeWidth
    result = newSeqWith(w, newSeq[int](h))
    for r in 0..<h:
        for c in 0..<w:
            result[c][h - 1 - r] = shape[r][c]

proc flipShape(shape: Shape): Shape =
    # Flip shape horizontally
    result = newSeq[seq[int]](shape.len)
    for r in 0..<shape.len:
        result[r] = shape[r].reversed

proc getPlacementCells(shape: Shape, x, y, W: int): seq[int] =
    # Get grid cell indices covered by placing shape at (x, y)
    for r in 0..<shape.shapeHeight:
        for c in 0..<shape.shapeWidth:
            if shape[r][c] == 1:
                result.add((y + r) * W + (x + c))

proc enumeratePlacements(shape: Shape, W, H: int): seq[Placement] =
    ## Enumerate all unique placements (all rotations/flips, all positions)
    var seenCells: seq[seq[int]] = @[]

    # Generate all 8 orientations (4 rotations × 2 flips)
    var orientations: seq[Shape] = @[]
    var current = shape
    for _ in 0..3:
        orientations.add(current)
        orientations.add(current.flipShape)
        current = current.rotateShape

    for orient in orientations:
        let sh = orient.shapeHeight
        let sw = orient.shapeWidth
        for y in 0..(H - sh):
            for x in 0..(W - sw):
                let cells = getPlacementCells(orient, x, y, W)
                if cells notin seenCells:
                    seenCells.add(cells)
                    result.add(Placement(cells: cells))

const
    # ANSI color codes for pieces (background colors)
    Colors = [
        "\e[48;5;196m", # Red
        "\e[48;5;208m", # Orange
        "\e[48;5;226m", # Yellow
        "\e[48;5;46m",  # Green
        "\e[48;5;51m",  # Cyan
        "\e[48;5;21m",  # Blue
        "\e[48;5;129m", # Purple
        "\e[48;5;213m", # Pink
        "\e[48;5;118m", # Lime
        "\e[48;5;87m",  # Turquoise
        "\e[48;5;220m", # Gold
        "\e[48;5;99m",  # Violet
        "\e[48;5;203m", # Salmon
        "\e[48;5;49m",  # Sea green
        "\e[48;5;141m", # Light purple
        "\e[48;5;215m", # Light orange
    ]
    Reset = "\e[0m"
    Empty = "\e[48;5;236m"  # Dark gray for empty cells

proc printGrid(grid: seq[int], W, H: int, pieceToShape: seq[int], showNumbers: bool = false) =
    # Print grid with colors based on shape
    for r in 0..<H:
        var row = ""
        for c in 0..<W:
            let val = grid[r*W + c]
            if val == 0:
                row.add(fmt"{Empty}   {Reset}")
            else:
                let shapeIdx = pieceToShape[val - 1]  # val is 1-indexed
                let color = Colors[shapeIdx mod Colors.len]
                if showNumbers:
                    row.add(fmt"{color}{val:^3}{Reset}")
                else:
                    row.add(fmt"{color}   {Reset}")
        echo row
    echo ""  # Blank line after grid

proc fit*(shapes: seq[Shape], W, H: int, nums: seq[int]): bool =
    echo fmt"Grid: [{W}, {H}]"

    let maxId = nums.foldl(a + b, 0)
    if maxId == 0:
        echo "No pieces to place"
        return true

    var totalCellsNeeded = 0
    for shapeIdx in 0..<nums.len:
        totalCellsNeeded += nums[shapeIdx] * countCells(shapes[shapeIdx])

    let area = W * H
    if totalCellsNeeded > area:
        echo "IMPOSSIBLE: need " & $totalCellsNeeded & " cells but grid has " & $area
        return false

    echo fmt"Pieces: {maxId}, Cells needed: {totalCellsNeeded}, Grid area: {area}"

    # Pre-enumerate placements
    var placementsByShape: seq[seq[Placement]] = @[]
    for shapeIdx in 0..<shapes.len:
        let placements = enumeratePlacements(shapes[shapeIdx], W, H)
        placementsByShape.add(placements)
        echo fmt"Shape {shapeIdx}: {placements.len} unique placements"

    var sys = initConstraintSystem[int]()

    # Create placement variables
    var placementVars: seq[ConstrainedVariable[int]] = @[]
    var pieceShapes: seq[int] = @[]
    var placementPositions: seq[int] = @[]

    for shapeIdx in 0..<nums.len:
        let numPlacements = placementsByShape[shapeIdx].len
        if numPlacements == 0 and nums[shapeIdx] > 0:
            echo fmt"No valid placements for shape {shapeIdx}"
            return false

        for rep in 0..<nums[shapeIdx]:
            var pVar = sys.newConstrainedVariable()
            pVar.setDomain(toSeq(0..<numPlacements))
            placementVars.add(pVar)
            pieceShapes.add(shapeIdx)
            placementPositions.add(pVar.value.node.position)

    let numPieces = placementVars.len
    echo fmt"Created {numPieces} placement variables"

    # Build cellsByPlacement: cellsByPlacement[pieceIdx][placementIdx] = cells covered
    var cellsByPlacement: seq[seq[seq[int]]] = @[]
    for pieceIdx in 0..<numPieces:
        let shapeIdx = pieceShapes[pieceIdx]
        cellsByPlacement.add(placementsByShape[shapeIdx].mapIt(it.cells))

    # Add geost constraint for non-overlapping placement
    sys.addConstraint(geost[int](placementPositions, cellsByPlacement))

    try:
        sys.resolve(tabuThreshold = 10000, parallel = false, verbose = true)
        echo "Solution found!"
        # Reconstruct grid from placements
        var grid = newSeq[int](H * W)
        for pieceIdx in 0..<numPieces:
            let shapeIdx = pieceShapes[pieceIdx]
            let placementIdx = placementVars[pieceIdx].assignment
            let placement = placementsByShape[shapeIdx][placementIdx]
            for cell in placement.cells:
                grid[cell] = pieceIdx + 1

        printGrid(grid, W, H, pieceShapes)

        # Print legend with colored blocks
        echo "Legend:"
        for shapeIdx in 0..<shapes.len:
            let count = nums[shapeIdx]
            if count > 0:
                let color = Colors[shapeIdx mod Colors.len]
                let cellCount = countCells(shapes[shapeIdx])
                let plural = if count > 1: "copies" else: "copy"
                echo fmt"  {color}   {Reset} Shape {shapeIdx} ({cellCount} cells, {count} {plural})"
        return true

    except NoSolutionFoundError:
        echo "No solution found"
        return false

proc main() =
    let inputFile = if paramCount() >= 1: paramStr(1) else: "input.txt"
    echo fmt"Reading input from: {inputFile}"

    let (shapes, regions) = parseInput(inputFile)
    echo fmt"Shapes: {shapes.len}, Regions: {regions.len}"

    var count = 0
    for i, region in regions:
        let size = [region.width, region.height]
        let nums = region.shapeCounts
        var cellsNeeded = 0
        for shapeIdx in 0..<nums.len:
            cellsNeeded += nums[shapeIdx] * countCells(shapes[shapeIdx])
        echo fmt"{i+1} / {regions.len}: {nums}"
        if cellsNeeded > size[0] * size[1]:
            echo "IMPOSSIBLE"
        else:
            if fit(shapes, size[0], size[1], nums):
                count += 1

    echo count

when isMainModule:
    main()
