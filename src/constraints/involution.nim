# Involution Constraint
#
# Ensures an array x[0..n-1] of successor variables (1-based by default) is a
# self-inverse permutation: x[x[i]] = i for all i. Combined with domains that
# exclude self-values (x[i] != i), this is exactly a fixed-point-free involution,
# i.e. a perfect matching.
#
# Penalty formula: number of positions i for which the involution property fails
# (x[i] out of range, or x[x[i]] != i).
#
# This is the penalty form of MiniZinc's `inverse(x, x)`. Crusher's inverse
# groups supply efficient involution-preserving *moves*, but those alone do not
# keep the assignment on the involution manifold when other move kinds (e.g.
# column all-different swaps) perturb the same positions. Posting this constraint
# makes leaving the manifold cost something, so cost 0 is a genuine involution.

import std/[tables, packedsets]

type
    InvolutionConstraint*[T] = ref object
        n*: int
        valueOffset*: int                    # subtracted from values -> 0-based index
        positionArray*: seq[int]             # position of x[i], in node order
        positionToIndex*: Table[int, int]    # position -> node index
        currentAssignment*: Table[int, T]    # position -> current value
        positions*: PackedSet[int]
        cost*: int

proc violatesAt[T](constraint: InvolutionConstraint[T], i: int): bool =
    ## True if the fixed-point-free involution property fails at node i:
    ## x[i] out of range, x[i] = i (a fixed point — forbidden for a perfect
    ## matching), or x[x[i]] != i.
    let n = constraint.n
    let vi = int(constraint.currentAssignment[constraint.positionArray[i]]) - constraint.valueOffset
    if vi < 0 or vi >= n:
        return true
    if vi == i:
        return true
    let vj = int(constraint.currentAssignment[constraint.positionArray[vi]]) - constraint.valueOffset
    return vj != i

proc recomputeCost[T](constraint: InvolutionConstraint[T]): int =
    for i in 0..<constraint.n:
        if constraint.violatesAt(i):
            result += 1

proc newInvolutionConstraint*[T](positions: openArray[int],
                                 valueOffset: int = 1): InvolutionConstraint[T] =
    new(result)
    result.n = positions.len
    result.valueOffset = valueOffset
    result.positionArray = @positions
    result.positionToIndex = initTable[int, int]()
    result.currentAssignment = initTable[int, T]()
    result.cost = 0
    var allPos: PackedSet[int]
    for idx, p in positions:
        result.positionToIndex[p] = idx
        allPos.incl(p)
    result.positions = allPos

proc initialize*[T](constraint: InvolutionConstraint[T], assignment: seq[T]) =
    for p in constraint.positions.items:
        constraint.currentAssignment[p] = assignment[p]
    constraint.cost = constraint.recomputeCost()

proc penalty*[T](constraint: InvolutionConstraint[T]): int {.inline.} =
    constraint.cost

proc moveDelta*[T](constraint: InvolutionConstraint[T],
                  position: int, oldValue, newValue: T): int =
    if position notin constraint.positionToIndex:
        return 0
    # Temporarily apply, recompute, restore. n is small for matching problems and
    # only the moved node plus nodes pointing at it/its target can change, but a
    # full O(n) recompute keeps this simple and correct.
    let saved = constraint.currentAssignment[position]
    constraint.currentAssignment[position] = newValue
    let newCost = constraint.recomputeCost()
    constraint.currentAssignment[position] = saved
    return newCost - constraint.cost

proc updatePosition*[T](constraint: InvolutionConstraint[T],
                       position: int, newValue: T) =
    if position notin constraint.positionToIndex:
        return
    constraint.currentAssignment[position] = newValue
    constraint.cost = constraint.recomputeCost()

proc deepCopy*[T](constraint: InvolutionConstraint[T]): InvolutionConstraint[T] =
    new(result)
    result.n = constraint.n
    result.valueOffset = constraint.valueOffset
    result.positionArray = constraint.positionArray
    result.positionToIndex = constraint.positionToIndex
    result.positions = constraint.positions
    result.cost = constraint.cost
    result.currentAssignment = initTable[int, T]()
    for k, v in constraint.currentAssignment.pairs:
        result.currentAssignment[k] = v
