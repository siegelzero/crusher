# Geost Constraint - Geometric non-overlap constraint for placement problems
#
# This constraint ensures that multiple objects with arbitrary shapes don't overlap
# when placed on a discrete grid. It's a local-search optimized implementation of
# the classic geost constraint from the Global Constraint Catalog.
#
# Key features:
# - Pre-enumerated placements: each object selects from valid (position, orientation) combinations
# - Arbitrary shapes: defined by cell lists
# - Efficient incremental cost: O(cells_per_piece) moveDelta computation
# - Cell coverage tracking: counts how many objects cover each cell
#
# See: https://sofdem.github.io/gccat/gccat/Cgeost.html

import std/[tables, packedsets, sequtils]

################################################################################
# Type definitions
################################################################################

type
    GeostConstraint*[T] = ref object
        numPieces*: int
        positions*: PackedSet[int]        # All placement variable positions
        placementPositions*: seq[int]     # Position of each piece's placement variable
        positionToPiece*: Table[int, int] # position -> pieceIdx for O(1) lookup

        # Pre-computed placement data: cellsByPlacement[piece][placementIdx] = cells covered
        cellsByPlacement*: seq[seq[seq[int]]]

        # Pre-computed index: cellToPlacementIdx[piece][cell] = placement indices covering that cell
        cellToPlacementIdx*: seq[Table[int, seq[int]]]

        # Current state
        currentPlacements*: seq[int]      # Current placement index for each piece
        cellCoverage*: Table[int, int]    # cell -> count of pieces covering it
        cost*: int                        # Number of cells with coverage > 1

        # Track which pieces cover each cell (for efficient neighbor computation)
        piecesAtCell*: Table[int, PackedSet[int]]  # cell -> set of piece indices
        lastAffectedPositions*: PackedSet[int]  # Positions affected by last updatePosition
        lastChangedCells*: PackedSet[int]  # Cells changed by last updatePosition


proc newGeostConstraint*[T](placementPositions: seq[int], cellsByPlacement: seq[seq[seq[int]]]): GeostConstraint[T] =
    # Create a new geost constraint
    assert placementPositions.len == cellsByPlacement.len,
        "placementPositions and cellsByPlacement must have the same length (one entry per piece)"

    result = GeostConstraint[T](
        numPieces: placementPositions.len,
        placementPositions: placementPositions,
        positionToPiece: initTable[int, int](),
        cellsByPlacement: cellsByPlacement,
        currentPlacements: newSeq[int](placementPositions.len),
        cellCoverage: initTable[int, int](),
        cost: 0
    )
    # Build positions set and position-to-piece mapping
    for pieceIdx, pos in placementPositions:
        result.positions.incl(pos)
        result.positionToPiece[pos] = pieceIdx

    # Build cell-to-placement index for getAffectedDomainValues
    result.cellToPlacementIdx = newSeq[Table[int, seq[int]]](result.numPieces)
    for pieceIdx in 0..<result.numPieces:
        result.cellToPlacementIdx[pieceIdx] = initTable[int, seq[int]]()
        for placementIdx, cells in cellsByPlacement[pieceIdx]:
            for cell in cells:
                result.cellToPlacementIdx[pieceIdx].mgetOrPut(cell, @[]).add(placementIdx)


proc initialize*[T](constraint: GeostConstraint[T], assignment: seq[T]) =
    # Initialize the constraint with a complete assignment
    constraint.cellCoverage.clear()
    constraint.piecesAtCell.clear()
    constraint.cost = 0

    # Get current placement for each piece and track cell coverage
    for pieceIdx in 0..<constraint.numPieces:
        let pos = constraint.placementPositions[pieceIdx]
        let placementIdx = assignment[pos].int
        constraint.currentPlacements[pieceIdx] = placementIdx

        # Add cells from this placement to coverage
        if placementIdx < constraint.cellsByPlacement[pieceIdx].len:
            for cell in constraint.cellsByPlacement[pieceIdx][placementIdx]:
                let oldCount = constraint.cellCoverage.getOrDefault(cell, 0)
                constraint.cellCoverage[cell] = oldCount + 1
                # Overlap penalty: each additional covering adds 1
                if oldCount >= 1:
                    constraint.cost += 1
                # Track which pieces cover this cell
                if cell notin constraint.piecesAtCell:
                    constraint.piecesAtCell[cell] = initPackedSet[int]()
                constraint.piecesAtCell[cell].incl(pieceIdx)


proc moveDelta*[T](constraint: GeostConstraint[T], position: int, oldValue, newValue: T): int =
    ## Calculate change in penalty if we change position from oldValue to newValue
    # O(1) lookup for which piece this position belongs to
    if position notin constraint.positionToPiece:
        return 0

    let pieceIdx = constraint.positionToPiece[position]
    let oldPlacement = oldValue.int
    let newPlacement = newValue.int

    if oldPlacement == newPlacement:
        return 0

    # Get cells for old and new placements
    let oldCells = if oldPlacement < constraint.cellsByPlacement[pieceIdx].len:
        constraint.cellsByPlacement[pieceIdx][oldPlacement]
    else:
        @[]

    let newCells = if newPlacement < constraint.cellsByPlacement[pieceIdx].len:
        constraint.cellsByPlacement[pieceIdx][newPlacement]
    else:
        @[]

    # Convert oldCells to PackedSet for O(1) lookup instead of O(n) linear search
    var oldCellsSet = initPackedSet[int]()
    for cell in oldCells:
        oldCellsSet.incl(cell)

    var delta = 0
    # Remove old cells: reducing coverage from N to N-1
    # Penalty decreases if N >= 2 (was overlapping, now less so)
    for cell in oldCells:
        if constraint.cellCoverage.getOrDefault(cell, 0) >= 2:
            delta -= 1  # One less overlap at this cell

    # Add new cells: increasing coverage from N to N+1
    # Penalty increases if N >= 1 (now overlapping)
    # But we need to account for cells that were in oldCells
    for cell in newCells:
        var effectiveCount = constraint.cellCoverage.getOrDefault(cell, 0)
        # If this cell was in oldCells, we've "removed" it already in our calculation
        if cell in oldCellsSet:  # O(1) lookup instead of O(n)
            effectiveCount -= 1
        if effectiveCount >= 1:
            delta += 1  # New overlap at this cell

    return delta


proc updatePosition*[T](constraint: GeostConstraint[T], position: int, newValue: T) =
    # Update the constraint state after a move is applied
    # O(1) lookup for which piece this position belongs to
    if position notin constraint.positionToPiece:
        return

    let pieceIdx = constraint.positionToPiece[position]
    let oldPlacement = constraint.currentPlacements[pieceIdx]
    let newPlacement = newValue.int
    if oldPlacement == newPlacement:
        return

    # Track affected positions and changed cells
    constraint.lastAffectedPositions.clear()
    constraint.lastChangedCells.clear()

    # Collect all changed cells (old ∪ new)
    for cell in constraint.cellsByPlacement[pieceIdx][oldPlacement]:
        constraint.lastChangedCells.incl(cell)
    for cell in constraint.cellsByPlacement[pieceIdx][newPlacement]:
        constraint.lastChangedCells.incl(cell)

    # Remove coverage from old placement
    for cell in constraint.cellsByPlacement[pieceIdx][oldPlacement]:
        # Any piece at this cell is affected
        if cell in constraint.piecesAtCell:
            for otherPiece in constraint.piecesAtCell[cell].items:
                if otherPiece != pieceIdx:
                    constraint.lastAffectedPositions.incl(constraint.placementPositions[otherPiece])

        let oldCount = constraint.cellCoverage.getOrDefault(cell, 0)
        if oldCount >= 2:
            constraint.cost -= 1
        if oldCount > 1:
            constraint.cellCoverage[cell] = oldCount - 1
        else:
            constraint.cellCoverage.del(cell)
        # Update piecesAtCell
        if cell in constraint.piecesAtCell:
            constraint.piecesAtCell[cell].excl(pieceIdx)
            if constraint.piecesAtCell[cell].len == 0:
                constraint.piecesAtCell.del(cell)

    # Add coverage from new placement
    for cell in constraint.cellsByPlacement[pieceIdx][newPlacement]:
        # Any piece at this cell is affected
        if cell in constraint.piecesAtCell:
            for otherPiece in constraint.piecesAtCell[cell].items:
                if otherPiece != pieceIdx:
                    constraint.lastAffectedPositions.incl(constraint.placementPositions[otherPiece])

        let oldCount = constraint.cellCoverage.getOrDefault(cell, 0)
        constraint.cellCoverage[cell] = oldCount + 1
        if oldCount >= 1:
            constraint.cost += 1
        # Update piecesAtCell
        if cell notin constraint.piecesAtCell:
            constraint.piecesAtCell[cell] = initPackedSet[int]()
        constraint.piecesAtCell[cell].incl(pieceIdx)

    constraint.currentPlacements[pieceIdx] = newPlacement


proc penalty*[T](constraint: GeostConstraint[T]): int =
    ## Get current penalty (number of overlapping cell assignments)
    return constraint.cost


proc getAffectedPositions*[T](constraint: GeostConstraint[T]): PackedSet[int] =
    # Return positions that were affected by the last updatePosition call
    # This is used by tabu search for smarter neighbor updates
    return constraint.lastAffectedPositions


proc getAffectedDomainValues*[T](constraint: GeostConstraint[T], position: int): seq[T] =
    ## Returns placement indices that need penalty recalculation at `position`.
    ## Only placements whose cells overlap with the last changed cells are affected.
    if position notin constraint.positionToPiece:
        return @[]
    let pieceIdx = constraint.positionToPiece[position]

    # If the current placement overlaps with changed cells, ALL values are affected
    # because the baseline (removing current placement's cells) changes.
    let curPlacement = constraint.currentPlacements[pieceIdx]
    for cell in constraint.cellsByPlacement[pieceIdx][curPlacement]:
        if cell in constraint.lastChangedCells:
            return @[]

    # Only placements overlapping changed cells need recalculation
    result = @[]
    var seen = initPackedSet[int]()
    for cell in constraint.lastChangedCells.items:
        if cell in constraint.cellToPlacementIdx[pieceIdx]:
            for placementIdx in constraint.cellToPlacementIdx[pieceIdx][cell]:
                if placementIdx notin seen:
                    seen.incl(placementIdx)
                    result.add(T(placementIdx))


proc deepCopy*[T](constraint: GeostConstraint[T]): GeostConstraint[T] =
    # Create a deep copy for parallel search
    result = GeostConstraint[T](
        numPieces: constraint.numPieces,
        positions: constraint.positions,
        placementPositions: constraint.placementPositions,
        positionToPiece: constraint.positionToPiece,  # Safe to share - read-only after construction
        cellsByPlacement: constraint.cellsByPlacement,  # Safe to share - read-only after construction
        cellToPlacementIdx: constraint.cellToPlacementIdx,  # Safe to share - read-only after construction
        currentPlacements: constraint.currentPlacements,  # seq[int] copied by value
        cellCoverage: initTable[int, int](),
        piecesAtCell: initTable[int, PackedSet[int]](),
        lastAffectedPositions: constraint.lastAffectedPositions,  # PackedSet copied by value
        lastChangedCells: constraint.lastChangedCells,
        cost: constraint.cost
    )
    # Deep copy the mutable tables that track runtime state
    for k, v in constraint.cellCoverage.pairs:
        result.cellCoverage[k] = v
    for k, v in constraint.piecesAtCell.pairs:
        result.piecesAtCell[k] = v
