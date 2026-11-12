# Connected Constraint Implementation
#
# Ensures that the active nodes in a graph form a single connected component.
# Used for Hitori-style puzzles where white cells must be connected.
#
# Input: A graph defined by edges (from[], to[]) plus boolean variables for
# node activity (ns[]) and edge activity (es[]).
# With edgesInduced (the edge variables are known to equal the AND of their
# endpoints), edge activity is derived from node activity and edge variables are
# ignored. Otherwise edge e is active iff its variable is non-0 and both endpoints
# are active, and edge positions are tracked too.
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
        adjEdge*: seq[seq[int]]          # adjEdge[node][k] = edge index of adjacency[node][k]
        edgesInduced*: bool
        edgeFrom*: seq[int]              # 0-based source node per edge
        edgeTo*: seq[int]                # 0-based target node per edge

        # Position mappings
        nodePositions*: seq[int]         # variable position for each node
        edgePositions*: seq[int]         # variable position for each edge
        nodePositionToIndex*: Table[int, int]  # position -> node index
        edgePositionToIndices*: Table[int, seq[int]]  # position -> edge indices (edge-aware mode)
        positions*: PackedSet[int]       # node positions, plus edge positions in edge-aware mode

        # Mutable state
        cost*: int
        nodeActive*: seq[bool]
        edgeActive*: seq[bool]           # edge variable values (edge-aware mode only)
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
            for k, neighbor in constraint.adjacency[current]:
                if not constraint.edgesInduced and
                        not constraint.edgeActive[constraint.adjEdge[current][k]]:
                    continue
                if constraint.nodeActive[neighbor] and not constraint.scratchVisited[neighbor]:
                    constraint.scratchVisited[neighbor] = true
                    constraint.scratchQueue.add(neighbor)

    return components

################################################################################
# Constructor
################################################################################

proc newConnectedConstraint*[T](nodePositions, edgePositions: openArray[int],
                                edgeFrom, edgeTo: openArray[int],
                                edgesInduced = true): ConnectedConstraint[T] =
    new(result)
    result.edgesInduced = edgesInduced
    result.numNodes = nodePositions.len
    result.numEdges = edgePositions.len
    result.nodePositions = @nodePositions
    result.edgePositions = @edgePositions
    result.edgeFrom = @edgeFrom
    result.edgeTo = @edgeTo

    # Build adjacency list
    result.adjacency = newSeq[seq[int]](result.numNodes)
    result.adjEdge = newSeq[seq[int]](result.numNodes)
    for e in 0..<result.numEdges:
        let u = edgeFrom[e]
        let v = edgeTo[e]
        result.adjacency[u].add(v)
        result.adjEdge[u].add(e)
        if v != u:
            result.adjacency[v].add(u)
            result.adjEdge[v].add(e)

    # Position mappings
    result.nodePositionToIndex = initTable[int, int]()
    for i, pos in nodePositions:
        result.nodePositionToIndex[pos] = i

    result.positions = initPackedSet[int]()
    for pos in nodePositions:
        result.positions.incl(pos)
    result.edgePositionToIndices = initTable[int, seq[int]]()
    if not edgesInduced:
        for e, pos in edgePositions:
            result.edgePositionToIndices.mgetOrPut(pos, @[]).add e
            result.positions.incl(pos)

    # Mutable state
    result.cost = 0
    result.nodeActive = newSeq[bool](result.numNodes)
    result.edgeActive = newSeq[bool](result.numEdges)
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
    if not constraint.edgesInduced:
        for e in 0..<constraint.numEdges:
            constraint.edgeActive[e] = (assignment[constraint.edgePositions[e]] != T(0))

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
    ## Compute cost change for toggling a node (or, in edge-aware mode, an edge).
    ## Temporarily apply, recompute, revert. Safe: each thread gets its own
    ## deep copy, so no concurrent access.
    if (oldValue != T(0)) == (newValue != T(0)):
        return 0
    let active = newValue != T(0)
    var changed = false
    let nodeIdx = constraint.nodePositionToIndex.getOrDefault(position, -1)
    if nodeIdx >= 0 and constraint.nodeActive[nodeIdx] != active:
        constraint.nodeActive[nodeIdx] = active
        changed = true
    var edgeFlipped: seq[int]
    if not constraint.edgesInduced:
        constraint.edgePositionToIndices.withValue(position, edges):
            for e in edges[]:
                if constraint.edgeActive[e] != active:
                    constraint.edgeActive[e] = active
                    edgeFlipped.add e
    if not changed and edgeFlipped.len == 0:
        return 0

    let newComponents = constraint.computeComponents()
    if changed: constraint.nodeActive[nodeIdx] = not active
    for e in edgeFlipped: constraint.edgeActive[e] = not active

    let newCost = max(0, newComponents - 1)
    return newCost - constraint.cost

################################################################################
# updatePosition
################################################################################

proc updatePosition*[T](constraint: ConnectedConstraint[T], position: int, newValue: T) =
    ## Apply a change and recompute components.
    var changed = false
    let nodeIdx = constraint.nodePositionToIndex.getOrDefault(position, -1)
    if nodeIdx >= 0:
        constraint.nodeActive[nodeIdx] = (newValue != T(0))
        changed = true
    if not constraint.edgesInduced:
        constraint.edgePositionToIndices.withValue(position, edges):
            for e in edges[]:
                constraint.edgeActive[e] = (newValue != T(0))
            changed = true
    if changed:
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
    result.adjEdge = constraint.adjEdge
    result.edgesInduced = constraint.edgesInduced
    result.edgePositionToIndices = constraint.edgePositionToIndices
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
    result.edgeActive = constraint.edgeActive
    result.numComponents = constraint.numComponents

    # Fresh scratch space
    result.scratchVisited = newSeq[bool](constraint.numNodes)
    result.scratchQueue = newSeqOfCap[int](constraint.numNodes)
