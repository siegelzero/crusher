import std/[sequtils, strutils, algorithm, tables, unittest]
import crusher

type
    Shape = seq[seq[int]]

    Placement = object
        cells: seq[int]

proc countCells(shape: Shape): int =
    for row in shape:
        for cell in row:
            result += cell

proc shapeHeight(shape: Shape): int = shape.len
proc shapeWidth(shape: Shape): int =
    if shape.len == 0: 0 else: shape[0].len

proc rotateShape(shape: Shape): Shape =
    ## Rotate shape 90 degrees clockwise
    let h = shape.shapeHeight
    let w = shape.shapeWidth
    result = newSeqWith(w, newSeq[int](h))
    for r in 0..<h:
        for c in 0..<w:
            result[c][h - 1 - r] = shape[r][c]

proc flipShape(shape: Shape): Shape =
    ## Flip shape horizontally
    result = newSeq[seq[int]](shape.len)
    for r in 0..<shape.len:
        result[r] = shape[r].reversed

proc getPlacementCells(shape: Shape, x, y, W: int): seq[int] =
    ## Get grid cell indices covered by placing shape at (x, y)
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

proc validateGeostSolution(placements: seq[int], cellsByPlacement: seq[seq[seq[int]]]): bool =
    ## Validates that no cells overlap in the solution
    var cellCoverage = initTable[int, int]()

    for pieceIdx in 0..<placements.len:
        let placementIdx = placements[pieceIdx]
        if placementIdx < cellsByPlacement[pieceIdx].len:
            for cell in cellsByPlacement[pieceIdx][placementIdx]:
                let count = cellCoverage.getOrDefault(cell, 0)
                if count > 0:
                    echo "Overlap at cell ", cell, " - piece ", pieceIdx, " overlaps with existing piece"
                    return false
                cellCoverage[cell] = count + 1

    return true

# Shapes from sample.txt
let shapes: seq[Shape] = @[
    # Shape 0: ###, ##., ##.
    @[@[1, 1, 1], @[1, 1, 0], @[1, 1, 0]],
    # Shape 1: ###, ##., .##
    @[@[1, 1, 1], @[1, 1, 0], @[0, 1, 1]],
    # Shape 2: .##, ###, ##.
    @[@[0, 1, 1], @[1, 1, 1], @[1, 1, 0]],
    # Shape 3: ##., ###, ##.
    @[@[1, 1, 0], @[1, 1, 1], @[1, 1, 0]],
    # Shape 4: ###, #.., ###
    @[@[1, 1, 1], @[1, 0, 0], @[1, 1, 1]],
    # Shape 5: ###, .#., ###
    @[@[1, 1, 1], @[0, 1, 0], @[1, 1, 1]]
]

suite "Geost Constraint Tests":
    test "Shape cell counts":
        # Verify our shapes have the expected cell counts
        check countCells(shapes[0]) == 7  # 3+2+2
        check countCells(shapes[1]) == 7  # 3+2+2
        check countCells(shapes[2]) == 7  # 2+3+2
        check countCells(shapes[3]) == 7  # 2+3+2
        check countCells(shapes[4]) == 7  # 3+1+3
        check countCells(shapes[5]) == 7  # 3+1+3

    test "4x4 grid with 2 copies of shape 4":
        # From sample.txt: 4x4: 0 0 0 0 2 0
        # 2 copies of shape 4 (7 cells each = 14 cells, grid has 16)
        let W = 4
        let H = 4
        let nums = @[0, 0, 0, 0, 2, 0]  # shape counts

        var sys = initConstraintSystem[int]()

        # Pre-enumerate placements
        var placementsByShape: seq[seq[Placement]] = @[]
        for shapeIdx in 0..<shapes.len:
            placementsByShape.add(enumeratePlacements(shapes[shapeIdx], W, H))

        # Create placement variables
        var placementVars: seq[ConstrainedVariable[int]] = @[]
        var pieceShapes: seq[int] = @[]
        var placementPositions: seq[int] = @[]

        for shapeIdx in 0..<nums.len:
            let numPlacements = placementsByShape[shapeIdx].len
            for rep in 0..<nums[shapeIdx]:
                var pVar = sys.newConstrainedVariable()
                pVar.setDomain(toSeq(0..<numPlacements))
                placementVars.add(pVar)
                pieceShapes.add(shapeIdx)
                placementPositions.add(pVar.value.node.position)

        check placementVars.len == 2  # 2 pieces total

        # Build cellsByPlacement
        var cellsByPlacement: seq[seq[seq[int]]] = @[]
        for pieceIdx in 0..<placementVars.len:
            let shapeIdx = pieceShapes[pieceIdx]
            cellsByPlacement.add(placementsByShape[shapeIdx].mapIt(it.cells))

        # Add geost constraint
        sys.addConstraint(geost[int](placementPositions, cellsByPlacement))

        # Solve
        sys.resolve()

        # Validate solution
        var placements: seq[int] = @[]
        for pVar in placementVars:
            placements.add(pVar.assignment)

        check validateGeostSolution(placements, cellsByPlacement)

    test "12x5 grid with shapes 0,2,4,4,5,5":
        # From sample.txt: 12x5: 1 0 1 0 2 2
        # 1×shape0(7) + 1×shape2(7) + 2×shape4(14) + 2×shape5(14) = 42 cells (grid has 60)
        let W = 12
        let H = 5
        let nums = @[1, 0, 1, 0, 2, 2]

        var sys = initConstraintSystem[int]()

        # Pre-enumerate placements
        var placementsByShape: seq[seq[Placement]] = @[]
        for shapeIdx in 0..<shapes.len:
            placementsByShape.add(enumeratePlacements(shapes[shapeIdx], W, H))

        # Create placement variables
        var placementVars: seq[ConstrainedVariable[int]] = @[]
        var pieceShapes: seq[int] = @[]
        var placementPositions: seq[int] = @[]

        for shapeIdx in 0..<nums.len:
            let numPlacements = placementsByShape[shapeIdx].len
            for rep in 0..<nums[shapeIdx]:
                var pVar = sys.newConstrainedVariable()
                pVar.setDomain(toSeq(0..<numPlacements))
                placementVars.add(pVar)
                pieceShapes.add(shapeIdx)
                placementPositions.add(pVar.value.node.position)

        check placementVars.len == 6  # 1+0+1+0+2+2 = 6 pieces

        # Build cellsByPlacement
        var cellsByPlacement: seq[seq[seq[int]]] = @[]
        for pieceIdx in 0..<placementVars.len:
            let shapeIdx = pieceShapes[pieceIdx]
            cellsByPlacement.add(placementsByShape[shapeIdx].mapIt(it.cells))

        # Add geost constraint
        sys.addConstraint(geost[int](placementPositions, cellsByPlacement))

        # Solve
        sys.resolve()

        # Validate solution
        var placements: seq[int] = @[]
        for pVar in placementVars:
            placements.add(pVar.assignment)

        check validateGeostSolution(placements, cellsByPlacement)

    test "Simple 2x2 non-overlapping squares":
        # Two 1x1 squares in a 2x1 grid - should be trivial
        var sys = initConstraintSystem[int]()

        # Each piece can be at position 0 or 1
        var p1 = sys.newConstrainedVariable()
        var p2 = sys.newConstrainedVariable()
        p1.setDomain(@[0, 1])
        p2.setDomain(@[0, 1])

        # Each placement covers just one cell
        let cellsByPlacement = @[
            @[@[0], @[1]],  # piece 0 at pos 0 covers cell 0, at pos 1 covers cell 1
            @[@[0], @[1]]   # piece 1 same
        ]

        sys.addConstraint(geost[int](@[0, 1], cellsByPlacement))

        sys.resolve()

        let placements = @[p1.assignment, p2.assignment]
        check validateGeostSolution(placements, cellsByPlacement)

        # The two squares should be at different positions
        check p1.assignment != p2.assignment
