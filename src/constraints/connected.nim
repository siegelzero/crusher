# Connected Constraint Implementation
#
# Ensures that the active nodes in a graph form a single connected component.
# Used for Hitori-style puzzles where white cells must be connected.
#
# Input: A graph defined by edges (from[], to[]) plus boolean variables for
# node activity (ns[]) and edge activity (es[]).
# Edge activity is computed internally: edge e is active iff both endpoints are active.
#
# Penalty formula: max(0, numComponents - 1)
# where numComponents counts connected components among active nodes.
# Special case: 0 active nodes → penalty 0 (vacuously connected).

import std/[tables, packedsets]

################################################################################
# Type definitions
################################################################################

type
    ConnectedConstraint*[T] = ref object
        # Graph structure (immutable after construction)
        numNodes*: int
        numEdges*: int
        adjacency*: seq[seq[int]]        # adjacency[node] = list of neighbor nodes
        edgeFrom*: seq[int]              # 0-based source node per edge
        edgeTo*: seq[int]                # 0-based target node per edge

        # Position mappings
        nodePositions*: seq[int]         # variable position for each node
        edgePositions*: seq[int]         # variable position for each edge
        nodePositionToIndex*: Table[int, int]  # position -> node index
        positions*: PackedSet[int]       # node variable positions only

        # Mutable state
        cost*: int
        nodeActive*: seq[bool]
        numComponents*: int

        # Scratch space for BFS (avoids allocation)
        scratchVisited*: seq[bool]
        scratchQueue*: seq[int]

################################################################################
# BFS-based component counting
################################################################################

proc computeComponents*[T](constraint: ConnectedConstraint[T]): int =
    ## Count connected components among active nodes using BFS.
    ## Returns 0 if no nodes are active.
    let n = constraint.numNodes

    # Reset visited
    for i in 0..<n:
        constraint.scratchVisited[i] = false

    var components = 0

    for startNode in 0..<n:
        if not constraint.nodeActive[startNode]:
            continue
        if constraint.scratchVisited[startNode]:
            continue

        # BFS from startNode
        components += 1
        constraint.scratchQueue.setLen(0)
        constraint.scratchQueue.add(startNode)
        constraint.scratchVisited[startNode] = true
        var qIdx = 0

        while qIdx < constraint.scratchQueue.len:
            let current = constraint.scratchQueue[qIdx]
            qIdx += 1
            for neighbor in constraint.adjacency[current]:
                if constraint.nodeActive[neighbor] and not constraint.scratchVisited[neighbor]:
                    constraint.scratchVisited[neighbor] = true
                    constraint.scratchQueue.add(neighbor)

    return components

################################################################################
# Constructor
################################################################################

proc newConnectedConstraint*[T](nodePositions, edgePositions: openArray[int],
                                edgeFrom, edgeTo: openArray[int]): ConnectedConstraint[T] =
    new(result)
    result.numNodes = nodePositions.len
    result.numEdges = edgePositions.len
    result.nodePositions = @nodePositions
    result.edgePositions = @edgePositions
    result.edgeFrom = @edgeFrom
    result.edgeTo = @edgeTo

    # Build adjacency list
    result.adjacency = newSeq[seq[int]](result.numNodes)
    for i in 0..<result.numNodes:
        result.adjacency[i] = @[]
    for e in 0..<result.numEdges:
        let u = edgeFrom[e]
        let v = edgeTo[e]
        result.adjacency[u].add(v)
        result.adjacency[v].add(u)

    # Position mappings
    result.nodePositionToIndex = initTable[int, int]()
    for i, pos in nodePositions:
        result.nodePositionToIndex[pos] = i

    # Only node positions — edge activity is derived, so edges don't affect penalty
    result.positions = initPackedSet[int]()
    for pos in nodePositions:
        result.positions.incl(pos)

    # Mutable state
    result.cost = 0
    result.nodeActive = newSeq[bool](result.numNodes)
    result.numComponents = 0

    # Scratch space
    result.scratchVisited = newSeq[bool](result.numNodes)
    result.scratchQueue = newSeqOfCap[int](result.numNodes)

################################################################################
# Initialize
################################################################################

proc initialize*[T](constraint: ConnectedConstraint[T], assignment: seq[T]) =
    ## Set node activity from assignment and compute initial cost.
    for i in 0..<constraint.numNodes:
        let pos = constraint.nodePositions[i]
        constraint.nodeActive[i] = (assignment[pos] != T(0))

    constraint.numComponents = constraint.computeComponents()
    constraint.cost = max(0, constraint.numComponents - 1)

################################################################################
# Penalty
################################################################################

proc penalty*[T](constraint: ConnectedConstraint[T]): int {.inline.} =
    return constraint.cost

################################################################################
# moveDelta
################################################################################

proc moveDelta*[T](constraint: ConnectedConstraint[T], position: int, oldValue, newValue: T): int =
    ## Compute cost change for toggling a node.
    ## Edge positions are ignored (edge activity is derived from node activity).
    if position notin constraint.nodePositionToIndex:
        return 0

    let nodeIdx = constraint.nodePositionToIndex[position]
    let wasActive = constraint.nodeActive[nodeIdx]
    let willBeActive = (newValue != T(0))

    if wasActive == willBeActive:
        return 0

    # Temporarily toggle, recompute, untoggle.
    # Safe: each thread gets its own deep copy, so no concurrent access.
    constraint.nodeActive[nodeIdx] = willBeActive
    let newComponents = constraint.computeComponents()
    constraint.nodeActive[nodeIdx] = wasActive

    let newCost = max(0, newComponents - 1)
    return newCost - constraint.cost

################################################################################
# updatePosition
################################################################################

proc updatePosition*[T](constraint: ConnectedConstraint[T], position: int, newValue: T) =
    ## Apply a change and recompute components.
    if position in constraint.nodePositionToIndex:
        let nodeIdx = constraint.nodePositionToIndex[position]
        constraint.nodeActive[nodeIdx] = (newValue != T(0))
        constraint.numComponents = constraint.computeComponents()
        constraint.cost = max(0, constraint.numComponents - 1)

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](constraint: ConnectedConstraint[T]): ConnectedConstraint[T] =
    ## Creates a deep copy for parallel search.
    new(result)
    # Share read-only graph structure
    result.numNodes = constraint.numNodes
    result.numEdges = constraint.numEdges
    result.adjacency = constraint.adjacency  # seq of seqs, but read-only
    result.edgeFrom = constraint.edgeFrom
    result.edgeTo = constraint.edgeTo
    result.nodePositions = constraint.nodePositions
    result.edgePositions = constraint.edgePositions
    result.nodePositionToIndex = constraint.nodePositionToIndex
    result.positions = constraint.positions

    # Deep copy mutable state
    result.cost = constraint.cost
    result.nodeActive = newSeq[bool](constraint.numNodes)
    for i in 0..<constraint.numNodes:
        result.nodeActive[i] = constraint.nodeActive[i]
    result.numComponents = constraint.numComponents

    # Fresh scratch space
    result.scratchVisited = newSeq[bool](constraint.numNodes)
    result.scratchQueue = newSeqOfCap[int](constraint.numNodes)
