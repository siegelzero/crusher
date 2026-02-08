# IRDCS Constraint - Incongruent Restricted Disjoint Covering System
#
# This constraint ensures that a collection of modulus assignments forms a valid IRDCS:
# - Each position i in [1,n] is assigned a modulus m
# - All positions assigned the same modulus m must have the same residue (mod m)
# - Each modulus that is used must cover at least 2 positions (restricted)
#
# Key concepts:
# - Incongruent: Each modulus defines exactly one congruence class
# - Disjoint: Each position is covered by exactly one modulus (implicit in assignment)
# - Restricted: Each congruence class contains at least 2 numbers
#
# Violation cost:
# - For each modulus m: count pairs of positions (i,j) where i ≢ j (mod m)
# - Add penalty for each modulus used by only 1 position
#
# See: "Odd Incongruent Restricted Disjoint Covering Systems" by Paul Robert Emanuel
# INTEGERS 12A (2012): John Selfridge Memorial Issue

import std/[tables, packedsets, algorithm]

################################################################################
# Type definitions
################################################################################

type
    IrdcsConstraint*[T] = ref object
        n*: int                           # Length of interval [1, n]
        positions*: PackedSet[int]        # Variable positions

        # Current state: position -> assigned modulus
        currentAssignment*: Table[int, T]

        # Tracking: modulus -> list of interval indices (1-indexed)
        indicesByModulus*: Table[T, seq[int]]

        # Residue counts: modulus -> (residue -> count)
        # For efficient O(1) moveDelta calculation
        residueCounts*: Table[T, Table[int, int]]

        cost*: int

        # Penalty weight for singleton moduli (used by only 1 position)
        singletonPenalty*: int

################################################################################
# Helper functions
################################################################################

proc intervalIndex*(position: int): int {.inline.} =
    ## Convert 0-indexed variable position to 1-indexed interval position
    position + 1

proc computeConflictPairs[T](modulus: T, indices: seq[int]): int =
    ## Count pairs of indices that have different residues mod modulus.
    ## Uses residue counting for O(k) instead of O(k^2).
    if indices.len <= 1:
        return 0

    # Group by residue
    var residueCounts: Table[int, int]
    for idx in indices:
        let r = idx mod modulus.int
        residueCounts.mgetOrPut(r, 0) += 1

    # Total pairs = n*(n-1)/2
    let n = indices.len
    let totalPairs = n * (n - 1) div 2

    # Same-residue pairs
    var sameResiduePairs = 0
    for count in residueCounts.values:
        sameResiduePairs += count * (count - 1) div 2

    # Conflict pairs = total - same
    return totalPairs - sameResiduePairs

proc computeModulusCost[T](constraint: IrdcsConstraint[T], modulus: T): int =
    ## Compute the total cost contribution from a single modulus
    let indices = constraint.indicesByModulus.getOrDefault(modulus, @[])

    if indices.len == 0:
        return 0

    if indices.len == 1:
        return constraint.singletonPenalty  # Singleton penalty

    return computeConflictPairs(modulus, indices)

################################################################################
# IrdcsConstraint creation
################################################################################

proc newIrdcsConstraint*[T](n: int, singletonPenalty: int = 1): IrdcsConstraint[T] =
    ## Create a new IRDCS constraint for interval [1, n].
    ## Variable positions are assumed to be 0 to n-1.
    result = IrdcsConstraint[T](
        n: n,
        positions: initPackedSet[int](),
        currentAssignment: initTable[int, T](),
        indicesByModulus: initTable[T, seq[int]](),
        residueCounts: initTable[T, Table[int, int]](),
        cost: 0,
        singletonPenalty: singletonPenalty
    )

    for pos in 0..<n:
        result.positions.incl(pos)

proc newIrdcsConstraint*[T](positions: openArray[int], singletonPenalty: int = 1): IrdcsConstraint[T] =
    ## Create a new IRDCS constraint for the given positions.
    ## The interval indices are derived from position order (first position = index 1, etc.)
    result = IrdcsConstraint[T](
        n: positions.len,
        positions: toPackedSet(positions),
        currentAssignment: initTable[int, T](),
        indicesByModulus: initTable[T, seq[int]](),
        residueCounts: initTable[T, Table[int, int]](),
        cost: 0,
        singletonPenalty: singletonPenalty
    )

################################################################################
# Initialization
################################################################################

proc initialize*[T](constraint: IrdcsConstraint[T], assignment: seq[T]) =
    ## Initialize the constraint with a complete assignment
    constraint.currentAssignment.clear()
    constraint.indicesByModulus.clear()
    constraint.residueCounts.clear()
    constraint.cost = 0

    # Build current assignment and tracking structures
    var posIndex = 0
    for pos in constraint.positions.items:
        let modulus = assignment[pos]
        let idx = intervalIndex(posIndex)  # 1-indexed interval position

        constraint.currentAssignment[pos] = modulus

        # Add to indicesByModulus
        if modulus notin constraint.indicesByModulus:
            constraint.indicesByModulus[modulus] = @[]
            constraint.residueCounts[modulus] = initTable[int, int]()
        constraint.indicesByModulus[modulus].add(idx)

        # Update residue counts
        let r = idx mod modulus.int
        constraint.residueCounts[modulus].mgetOrPut(r, 0) += 1

        posIndex += 1

    # Compute total cost
    for modulus in constraint.indicesByModulus.keys:
        constraint.cost += constraint.computeModulusCost(modulus)

################################################################################
# Move delta calculation
################################################################################

proc moveDelta*[T](constraint: IrdcsConstraint[T], position: int, oldValue, newValue: T): int =
    ## Calculate the change in cost if we change position from oldValue to newValue
    if oldValue == newValue:
        return 0

    if position notin constraint.positions:
        return 0

    # Find the interval index for this position
    var posIndex = 0
    for pos in constraint.positions.items:
        if pos == position:
            break
        posIndex += 1
    let idx = intervalIndex(posIndex)

    var delta = 0

    # === Cost change from removing idx from oldValue ===
    let oldIndices = constraint.indicesByModulus.getOrDefault(oldValue, @[])
    let oldCount = oldIndices.len

    if oldCount > 0:
        let oldResidue = idx mod oldValue.int
        let oldResidueCount = constraint.residueCounts.getOrDefault(oldValue, initTable[int, int]()).getOrDefault(oldResidue, 0)

        # Current cost for oldValue
        var oldCost: int
        if oldCount == 1:
            oldCost = constraint.singletonPenalty
        else:
            # Conflicts this index has with others = others with different residue
            # = (oldCount - 1) - (oldResidueCount - 1) = oldCount - oldResidueCount
            oldCost = constraint.computeModulusCost(oldValue)

        # New cost after removal
        let newCount = oldCount - 1
        var newCostOld: int
        if newCount == 0:
            newCostOld = 0
        elif newCount == 1:
            newCostOld = constraint.singletonPenalty
        else:
            # Recompute with one less index
            # The conflicts removed are those involving idx
            # = number of other indices with different residue
            let conflictsRemoved = (oldCount - 1) - (oldResidueCount - 1)
            newCostOld = oldCost - conflictsRemoved

        delta += newCostOld - oldCost

    # === Cost change from adding idx to newValue ===
    let newIndices = constraint.indicesByModulus.getOrDefault(newValue, @[])
    let newCountBefore = newIndices.len

    let newResidue = idx mod newValue.int
    let newResidueCountBefore = constraint.residueCounts.getOrDefault(newValue, initTable[int, int]()).getOrDefault(newResidue, 0)

    # Current cost for newValue
    var currentCostNew: int
    if newCountBefore == 0:
        currentCostNew = 0
    elif newCountBefore == 1:
        currentCostNew = constraint.singletonPenalty
    else:
        currentCostNew = constraint.computeModulusCost(newValue)

    # New cost after addition
    let newCountAfter = newCountBefore + 1
    var newCostNew: int
    if newCountAfter == 1:
        newCostNew = constraint.singletonPenalty
    elif newCountAfter == 2:
        # Check if both have same residue
        if newCountBefore == 1:
            # There's one existing index
            let existingIdx = newIndices[0]
            let existingResidue = existingIdx mod newValue.int
            if existingResidue == newResidue:
                newCostNew = 0  # Same residue, no conflict
            else:
                newCostNew = 1  # Different residue, 1 conflict pair
        else:
            newCostNew = 0  # Was empty, now singleton... wait, newCountBefore would be 0
    else:
        # Conflicts added are those with different residue
        let conflictsAdded = newCountBefore - newResidueCountBefore
        newCostNew = currentCostNew + conflictsAdded

    delta += newCostNew - currentCostNew

    return delta

################################################################################
# Position update
################################################################################

proc updatePosition*[T](constraint: IrdcsConstraint[T], position: int, newValue: T) =
    ## Update the constraint state after assigning newValue to position
    if position notin constraint.positions:
        return

    let oldValue = constraint.currentAssignment.getOrDefault(position, default(T))
    if oldValue == newValue:
        return

    # Find interval index
    var posIndex = 0
    for pos in constraint.positions.items:
        if pos == position:
            break
        posIndex += 1
    let idx = intervalIndex(posIndex)

    # Remove from old modulus
    if oldValue != default(T) and oldValue in constraint.indicesByModulus:
        # Remove cost contribution
        constraint.cost -= constraint.computeModulusCost(oldValue)

        # Update structures
        let oldResidue = idx mod oldValue.int
        constraint.indicesByModulus[oldValue].delete(constraint.indicesByModulus[oldValue].find(idx))
        constraint.residueCounts[oldValue][oldResidue] -= 1
        if constraint.residueCounts[oldValue][oldResidue] == 0:
            constraint.residueCounts[oldValue].del(oldResidue)

        # Clean up empty entries
        if constraint.indicesByModulus[oldValue].len == 0:
            constraint.indicesByModulus.del(oldValue)
            constraint.residueCounts.del(oldValue)
        else:
            # Add back cost contribution
            constraint.cost += constraint.computeModulusCost(oldValue)

    # Add to new modulus
    constraint.currentAssignment[position] = newValue

    # Remove old cost contribution (if any)
    if newValue in constraint.indicesByModulus:
        constraint.cost -= constraint.computeModulusCost(newValue)

    # Update structures
    if newValue notin constraint.indicesByModulus:
        constraint.indicesByModulus[newValue] = @[]
        constraint.residueCounts[newValue] = initTable[int, int]()

    constraint.indicesByModulus[newValue].add(idx)
    let newResidue = idx mod newValue.int
    constraint.residueCounts[newValue].mgetOrPut(newResidue, 0) += 1

    # Add back cost contribution
    constraint.cost += constraint.computeModulusCost(newValue)

################################################################################
# Utility functions
################################################################################

proc penalty*[T](constraint: IrdcsConstraint[T]): int =
    ## Get current penalty (violation count)
    return constraint.cost

proc isValid*[T](constraint: IrdcsConstraint[T]): bool =
    ## Check if current assignment is a valid IRDCS
    return constraint.cost == 0

proc getCongruenceClasses*[T](constraint: IrdcsConstraint[T]): seq[(T, int)] =
    ## Extract the congruence classes from a valid solution.
    ## Returns list of (modulus, residue) pairs.
    result = @[]
    for modulus, indices in constraint.indicesByModulus.pairs:
        if indices.len > 0:
            let residue = indices[0] mod modulus.int
            result.add((modulus, residue))

proc getAlternateNotation*[T](constraint: IrdcsConstraint[T]): seq[T] =
    ## Get the alternate notation (list of moduli for each position 1 to n)
    result = newSeq[T](constraint.n)
    var posIndex = 0
    for pos in constraint.positions.items:
        result[posIndex] = constraint.currentAssignment[pos]
        posIndex += 1

proc validateSolution*[T](constraint: IrdcsConstraint[T]): bool =
    ## Thoroughly validate that the current assignment is a valid IRDCS
    # Check 1: Each position has a modulus assigned
    for pos in constraint.positions.items:
        if pos notin constraint.currentAssignment:
            return false

    # Check 2: Each modulus used covers at least 2 positions
    for modulus, indices in constraint.indicesByModulus.pairs:
        if indices.len < 2:
            return false

    # Check 3: All positions with same modulus have same residue
    for modulus, indices in constraint.indicesByModulus.pairs:
        if indices.len == 0:
            continue
        let expectedResidue = indices[0] mod modulus.int
        for idx in indices:
            if idx mod modulus.int != expectedResidue:
                return false

    return true

################################################################################
# Deep copy for parallel search
################################################################################

proc deepCopy*[T](constraint: IrdcsConstraint[T]): IrdcsConstraint[T] =
    ## Create a deep copy for parallel search
    result = IrdcsConstraint[T](
        n: constraint.n,
        positions: constraint.positions,  # PackedSet is value type
        currentAssignment: initTable[int, T](),
        indicesByModulus: initTable[T, seq[int]](),
        residueCounts: initTable[T, Table[int, int]](),
        cost: constraint.cost,
        singletonPenalty: constraint.singletonPenalty
    )

    for k, v in constraint.currentAssignment.pairs:
        result.currentAssignment[k] = v

    for k, v in constraint.indicesByModulus.pairs:
        result.indicesByModulus[k] = v  # seq is copied

    for k, v in constraint.residueCounts.pairs:
        result.residueCounts[k] = initTable[int, int]()
        for r, c in v.pairs:
            result.residueCounts[k][r] = c
