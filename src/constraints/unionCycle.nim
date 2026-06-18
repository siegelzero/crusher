# Union-Cycle Constraint
#
# Given two arrays x[0..n-1] and y[0..n-1] of successor variables (1-based by
# default), consider the undirected graph G on nodes 0..n-1 with edges
#   { i — (x[i]-offset) }  ∪  { i — (y[i]-offset) }.
# The constraint is satisfied when G is connected (a single component).
#
# Penalty formula: max(0, numComponents - 1)
#
# This is the matching-level form of MiniZinc's `union_circuit(x, y)` predicate
# (used in the perfect-1-factorization model p1f): when x and y are fixed-point-
# free involutions with x[i] != y[i] (a column-all-different partition), G is a
# simple 2-regular graph, so "connected" is exactly "a single Hamiltonian
# alternating cycle" — i.e. there exists an index assignment making
# circuit([x[i],y[i]][index_i]) hold. Expressing it directly on the two matchings
# removes the per-position index selectors and the derived circuit array, giving
# a clean penalty gradient on the variables that actually matter.
#
# This constraint does NOT enforce that x or y are involutions; post those
# separately (e.g. via inverse groups) along with column all-different.

import std/[tables, packedsets]

type
    UnionCycleConstraint*[T] = ref object
        n*: int                              # number of nodes
        valueOffset*: int                    # subtracted from values -> 0-based node index
        xPositions*: seq[int]                # variable position of x[i]
        yPositions*: seq[int]                # variable position of y[i]
        positions*: PackedSet[int]           # all variable positions (x ∪ y)
        cost*: int                           # cached penalty

        # Flat per-node successor targets (0-based), kept in sync with the
        # assignment. These are read in the hot union-find loop, avoiding Table
        # lookups. posInfo maps a variable position to (isX, node).
        xTarget: seq[int]                    # xTarget[i] = value(x[i]) - offset
        yTarget: seq[int]                    # yTarget[i] = value(y[i]) - offset
        posInfo*: Table[int, tuple[isX: bool, node: int]]

        # When each successor array occupies a contiguous position range (the
        # usual case for a row), position -> (isX, node) is pure arithmetic,
        # avoiding a hash lookup on every moveDelta. -1 base disables the fast path.
        xContigBase, yContigBase: int

        # Committed component labels (representative per node) and their count,
        # refreshed on every updatePosition. moveDelta reads these for an O(1)
        # incremental delta in the common case (see moveDelta).
        comp: seq[int]
        numComponents: int

        # Pre-allocated union-find scratch (avoids per-call heap alloc)
        ufParent: seq[int]

################################################################################
# Union-find helpers
################################################################################

proc ufFind(parent: var seq[int], a: int): int =
    var r = a
    while parent[r] != r:
        r = parent[r]
    # path compression
    var x = a
    while parent[x] != x:
        let nx = parent[x]
        parent[x] = r
        x = nx
    return r

proc ufUnion(parent: var seq[int], a, b: int) =
    let ra = ufFind(parent, a)
    let rb = ufFind(parent, b)
    if ra != rb:
        parent[ra] = rb

################################################################################
# Component counting
################################################################################

proc countComponents[T](constraint: UnionCycleConstraint[T],
                        ovIsX: bool, ovNode: int, ovTarget: int): int =
    ## Number of connected components of G. When ovNode >= 0, substitute the
    ## target of that node's x-edge (ovIsX) or y-edge with ovTarget.
    let n = constraint.n
    for i in 0..<n:
        constraint.ufParent[i] = i

    for i in 0..<n:
        var xt = constraint.xTarget[i]
        if ovNode == i and ovIsX: xt = ovTarget
        if xt >= 0 and xt < n:
            ufUnion(constraint.ufParent, i, xt)

        var yt = constraint.yTarget[i]
        if ovNode == i and not ovIsX: yt = ovTarget
        if yt >= 0 and yt < n:
            ufUnion(constraint.ufParent, i, yt)

    var comps = 0
    for i in 0..<n:
        if ufFind(constraint.ufParent, i) == i:
            comps += 1
    return comps

proc rebuildComponents[T](constraint: UnionCycleConstraint[T]) =
    ## Recompute committed component labels and count over the current targets.
    let n = constraint.n
    for i in 0..<n:
        constraint.ufParent[i] = i
    for i in 0..<n:
        let xt = constraint.xTarget[i]
        if xt >= 0 and xt < n: ufUnion(constraint.ufParent, i, xt)
        let yt = constraint.yTarget[i]
        if yt >= 0 and yt < n: ufUnion(constraint.ufParent, i, yt)
    var comps = 0
    for i in 0..<n:
        let root = ufFind(constraint.ufParent, i)
        constraint.comp[i] = root
        if root == i: comps += 1
    constraint.numComponents = comps

################################################################################
# Constructor
################################################################################

proc newUnionCycleConstraint*[T](xPositions, yPositions: openArray[int],
                                 valueOffset: int = 1): UnionCycleConstraint[T] =
    assert xPositions.len == yPositions.len
    new(result)
    result.n = xPositions.len
    result.valueOffset = valueOffset
    result.xPositions = @xPositions
    result.yPositions = @yPositions
    result.ufParent = newSeq[int](result.n)
    result.xTarget = newSeq[int](result.n)
    result.yTarget = newSeq[int](result.n)
    result.comp = newSeq[int](result.n)
    result.posInfo = initTable[int, tuple[isX: bool, node: int]]()
    result.cost = 0

    var allPos: PackedSet[int]
    for i, p in xPositions:
        allPos.incl(p)
        result.posInfo[p] = (isX: true, node: i)
    for i, p in yPositions:
        allPos.incl(p)
        result.posInfo[p] = (isX: false, node: i)
    result.positions = allPos

    # Detect contiguous ranges so position lookup can be arithmetic.
    proc contigBase(ps: openArray[int]): int =
        result = ps[0]
        for i, p in ps:
            if p != result + i: return -1
    result.xContigBase = contigBase(xPositions)
    result.yContigBase = contigBase(yPositions)

################################################################################
# Initialize / penalty / moveDelta / updatePosition
################################################################################

proc initialize*[T](constraint: UnionCycleConstraint[T], assignment: seq[T]) =
    for i in 0..<constraint.n:
        constraint.xTarget[i] = int(assignment[constraint.xPositions[i]]) - constraint.valueOffset
        constraint.yTarget[i] = int(assignment[constraint.yPositions[i]]) - constraint.valueOffset
    constraint.rebuildComponents()
    constraint.cost = max(0, constraint.numComponents - 1)

proc penalty*[T](constraint: UnionCycleConstraint[T]): int {.inline.} =
    constraint.cost

proc infoFor[T](constraint: UnionCycleConstraint[T], position: int): tuple[isX: bool, node: int] {.inline.} =
    ## position -> (isX, node), via O(1) arithmetic when ranges are contiguous.
    let n = constraint.n
    if constraint.xContigBase >= 0:
        let d = position - constraint.xContigBase
        if d >= 0 and d < n: return (isX: true, node: d)
    if constraint.yContigBase >= 0:
        let d = position - constraint.yContigBase
        if d >= 0 and d < n: return (isX: false, node: d)
    if constraint.xContigBase >= 0 and constraint.yContigBase >= 0:
        return (isX: false, node: -1)        # both contiguous and not matched
    return constraint.posInfo.getOrDefault(position, (isX: false, node: -1))

proc moveDelta*[T](constraint: UnionCycleConstraint[T],
                  position: int, oldValue, newValue: T): int =
    let info = constraint.infoFor(position)
    if info.node < 0:
        return 0
    let n = constraint.n
    let i = info.node
    let oldTarget = int(oldValue) - constraint.valueOffset
    let newTarget = int(newValue) - constraint.valueOffset

    # Fast path: if the edge being changed has its reverse still present (the
    # matching is locally valid, x[oldTarget]=i), then i—oldTarget persists via
    # oldTarget's own edge, so this move only *adds* edge i—newTarget. The
    # component count drops by one iff i and newTarget were in different
    # committed components — O(1) from the cached labels. (Adding an already
    # present edge, incl. newTarget pointing back at i, is a no-op merge.)
    var reverseExists = false
    if oldTarget >= 0 and oldTarget < n:
        reverseExists = if info.isX: constraint.xTarget[oldTarget] == i
                        else: constraint.yTarget[oldTarget] == i
    if reverseExists and newTarget >= 0 and newTarget < n:
        let merge = if constraint.comp[i] != constraint.comp[newTarget]: 1 else: 0
        let newComps = constraint.numComponents - merge
        return max(0, newComps - 1) - constraint.cost

    # Fallback: the edge is genuinely swapped (matching broken locally) — a full
    # recomputation with the substituted edge.
    let newComps = constraint.countComponents(info.isX, i, newTarget)
    return max(0, newComps - 1) - constraint.cost

proc updatePosition*[T](constraint: UnionCycleConstraint[T],
                       position: int, newValue: T) =
    let info = constraint.infoFor(position)
    if info.node < 0:
        return
    let t = int(newValue) - constraint.valueOffset
    if info.isX: constraint.xTarget[info.node] = t
    else: constraint.yTarget[info.node] = t
    constraint.rebuildComponents()
    constraint.cost = max(0, constraint.numComponents - 1)

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](constraint: UnionCycleConstraint[T]): UnionCycleConstraint[T] =
    new(result)
    result.n = constraint.n
    result.valueOffset = constraint.valueOffset
    result.xPositions = constraint.xPositions
    result.yPositions = constraint.yPositions
    result.positions = constraint.positions
    result.posInfo = constraint.posInfo
    result.cost = constraint.cost
    result.ufParent = newSeq[int](constraint.n)
    result.xTarget = constraint.xTarget
    result.yTarget = constraint.yTarget
    result.comp = constraint.comp
    result.numComponents = constraint.numComponents
    result.xContigBase = constraint.xContigBase
    result.yContigBase = constraint.yContigBase
