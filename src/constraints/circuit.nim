# Circuit Constraint Implementation
#
# Ensures a list of n decision variables forms a single Hamiltonian circuit.
# Uses 1-based convention: value j at position i means "from node i, go to node j."
#
# Penalty formula: max(0, numCycles - 1) + numTailNodes
# - numCycles: distinct cycles found by traversing the functional graph
# - numTailNodes: nodes not on any cycle (happens when assignment is not a permutation)
# - Valid single circuit: 1 cycle, 0 tails -> penalty = 0
#
# This constraint does NOT implicitly enforce allDifferent. Users must add both:
#   sys.addConstraint(allDifferent(x))
#   sys.addConstraint(circuit(x))

import std/[tables, packedsets, algorithm]

################################################################################
# Type definitions
################################################################################

type
    NodeColor = enum
        White, Gray, Black

    CircuitConstraint*[T] = ref object
        n*: int                              # number of nodes
        positions*: PackedSet[int]           # all variable positions
        sortedPositions*: seq[int]           # sorted positions array
        positionToIndex*: Table[int, int]    # position -> 0-based node index
        successorArray*: seq[int]            # 0-based successors (working copy)
        cost*: int                           # cached penalty
        currentAssignment*: Table[int, T]    # position -> current value

        # Incremental tracking
        componentId: seq[int]        # which component each node belongs to
        cycleId: seq[int]            # which cycle each node is on (-1 if tail)
        numCycles: int               # global cycle count
        numTailNodes: int            # global tail node count
        nextComponentId: int         # monotonic counter for assigning component IDs
        nextCycleId: int             # monotonic counter for assigning cycle IDs

        # Pre-allocated scratch space (avoids heap alloc per moveDelta call)
        scratchColor: seq[NodeColor]
        scratchInAffected: seq[bool]
        scratchPath: seq[int]

################################################################################
# Cycle counting algorithm (three-color traversal) - used for full recomputation
################################################################################

proc computePenalty*[T](constraint: CircuitConstraint[T]): int =
    ## Counts cycles and tail nodes via three-color traversal.
    ## Returns max(0, numCycles - 1) + numTailNodes.
    let n = constraint.n
    var color = newSeq[NodeColor](n)
    var numCycles = 0
    var numTailNodes = 0

    for startNode in 0..<n:
        if color[startNode] != White:
            continue

        # Follow the chain from startNode, collecting the path
        var path: seq[int] = @[]
        var current = startNode

        while true:
            if color[current] != White:
                break
            color[current] = Gray
            path.add(current)
            let succ = constraint.successorArray[current]
            if succ < 0 or succ >= n:
                # Out of bounds - set current to succ so post-loop bounds check fails
                current = succ
                break
            current = succ

        if current >= 0 and current < n and color[current] == Gray:
            # We hit a Gray node - found a cycle
            numCycles += 1
            # Find where the cycle starts in the path
            var cycleStart = 0
            for i in 0..<path.len:
                if path[i] == current:
                    cycleStart = i
                    break
            # Nodes before cycle start are tail nodes
            numTailNodes += cycleStart
            # Mark cycle nodes as Black
            for i in cycleStart..<path.len:
                color[path[i]] = Black
            # Mark tail nodes as Black
            for i in 0..<cycleStart:
                color[path[i]] = Black
        else:
            # We hit a Black node or went out of bounds - all path nodes are tails
            numTailNodes += path.len
            for node in path:
                color[node] = Black

    return max(0, numCycles - 1) + numTailNodes

################################################################################
# Component/cycle metadata traversal
################################################################################

proc computeMetadata[T](constraint: CircuitConstraint[T]) =
    ## Full O(n) traversal to populate componentId, cycleId, numCycles, numTailNodes.
    ## Components are weakly connected components: tail nodes inherit the componentId
    ## of the node they eventually reach.
    let n = constraint.n
    constraint.numCycles = 0
    constraint.numTailNodes = 0

    var color = newSeq[NodeColor](n)
    var path = newSeqOfCap[int](n)

    for startNode in 0..<n:
        if color[startNode] != White:
            continue

        path.setLen(0)
        var current = startNode

        while true:
            if color[current] != White:
                break
            color[current] = Gray
            path.add(current)
            let succ = constraint.successorArray[current]
            if succ < 0 or succ >= n:
                current = succ
                break
            current = succ

        if current >= 0 and current < n and color[current] == Gray:
            # Found a cycle - assign a new component for this cycle + its tails
            let compId = constraint.nextComponentId
            constraint.nextComponentId += 1
            constraint.numCycles += 1
            let cId = constraint.nextCycleId
            constraint.nextCycleId += 1
            var cycleStart = 0
            for i in 0..<path.len:
                if path[i] == current:
                    cycleStart = i
                    break
            constraint.numTailNodes += cycleStart
            for i in cycleStart..<path.len:
                color[path[i]] = Black
                constraint.componentId[path[i]] = compId
                constraint.cycleId[path[i]] = cId
            for i in 0..<cycleStart:
                color[path[i]] = Black
                constraint.componentId[path[i]] = compId
                constraint.cycleId[path[i]] = -1
        elif current >= 0 and current < n and color[current] == Black:
            # Hit an already-visited node - join its component
            let compId = constraint.componentId[current]
            constraint.numTailNodes += path.len
            for node in path:
                color[node] = Black
                constraint.componentId[node] = compId
                constraint.cycleId[node] = -1
        else:
            # Out of bounds - these tails form their own component
            let compId = constraint.nextComponentId
            constraint.nextComponentId += 1
            constraint.numTailNodes += path.len
            for node in path:
                color[node] = Black
                constraint.componentId[node] = compId
                constraint.cycleId[node] = -1

################################################################################
# Incremental helper: count cycles and tails among affected nodes
################################################################################

proc countCyclesAndTails[T](constraint: CircuitConstraint[T],
                            affectedNodes: openArray[int],
                            affectedCount: int): (int, int) =
    ## Mini-traverse only the affected nodes using scratchColor.
    ## Returns (newCycles, newTails) among just these nodes.
    let n = constraint.n
    var newCycles = 0
    var newTails = 0

    # Reset scratch color for affected nodes
    for i in 0..<affectedCount:
        constraint.scratchColor[affectedNodes[i]] = White

    for i in 0..<affectedCount:
        let startNode = affectedNodes[i]
        if constraint.scratchColor[startNode] != White:
            continue

        constraint.scratchPath.setLen(0)
        var current = startNode

        while true:
            if constraint.scratchColor[current] != White:
                break
            constraint.scratchColor[current] = Gray
            constraint.scratchPath.add(current)
            let succ = constraint.successorArray[current]
            if succ < 0 or succ >= n:
                # Out of bounds - all path nodes are tails
                current = succ
                break
            if not constraint.scratchInAffected[succ]:
                # Successor is outside affected set - path nodes are tails
                current = -1  # force tail treatment
                break
            current = succ

        if current >= 0 and current < n and constraint.scratchColor[current] == Gray:
            # Found a cycle within affected set
            newCycles += 1
            var cycleStart = 0
            for j in 0..<constraint.scratchPath.len:
                if constraint.scratchPath[j] == current:
                    cycleStart = j
                    break
            newTails += cycleStart
            for j in cycleStart..<constraint.scratchPath.len:
                constraint.scratchColor[constraint.scratchPath[j]] = Black
            for j in 0..<cycleStart:
                constraint.scratchColor[constraint.scratchPath[j]] = Black
        else:
            # All path nodes are tails
            newTails += constraint.scratchPath.len
            for node in constraint.scratchPath:
                constraint.scratchColor[node] = Black

    return (newCycles, newTails)

################################################################################
# Constructor
################################################################################

proc newCircuitConstraint*[T](positions: openArray[int]): CircuitConstraint[T] =
    new(result)
    result.n = positions.len
    result.sortedPositions = sorted(@positions)
    result.positions = toPackedSet[int](positions)
    result.positionToIndex = initTable[int, int]()
    result.currentAssignment = initTable[int, T]()
    result.successorArray = newSeq[int](result.n)
    result.cost = 0

    # Incremental tracking
    result.componentId = newSeq[int](result.n)
    result.cycleId = newSeq[int](result.n)
    result.numCycles = 0
    result.numTailNodes = 0
    result.nextComponentId = 0
    result.nextCycleId = 0

    # Pre-allocated scratch space
    result.scratchColor = newSeq[NodeColor](result.n)
    result.scratchInAffected = newSeq[bool](result.n)
    result.scratchPath = newSeqOfCap[int](result.n)

    for i, pos in result.sortedPositions:
        result.positionToIndex[pos] = i

################################################################################
# Initialize
################################################################################

proc initialize*[T](constraint: CircuitConstraint[T], assignment: seq[T]) =
    ## Build successor array from assignment and compute initial cost + metadata.
    for i, pos in constraint.sortedPositions:
        let value = assignment[pos]
        constraint.currentAssignment[pos] = value
        # Convert 1-based value to 0-based index
        constraint.successorArray[i] = int(value) - 1

    # Reset metadata counters
    constraint.nextComponentId = 0
    constraint.nextCycleId = 0
    constraint.computeMetadata()
    constraint.cost = max(0, constraint.numCycles - 1) + constraint.numTailNodes

################################################################################
# moveDelta (incremental)
################################################################################

proc moveDelta*[T](constraint: CircuitConstraint[T], position: int, oldValue, newValue: T): int =
    ## Incremental moveDelta: only re-traverses affected components.
    if position notin constraint.positionToIndex:
        return 0
    let nodeIdx = constraint.positionToIndex[position]
    let newSucc = int(newValue) - 1
    let n = constraint.n

    # Identify affected components
    let comp1 = constraint.componentId[nodeIdx]
    var comp2 = -1
    if newSucc >= 0 and newSucc < n:
        comp2 = constraint.componentId[newSucc]

    # Gather affected nodes into scratch, count old cycles/tails
    var affectedCount = 0
    var oldAffectedCycles = 0
    var oldAffectedTails = 0

    # Track distinct cycle IDs among affected nodes
    var seenCycleIds: seq[int] = @[]

    for i in 0..<n:
        if constraint.componentId[i] == comp1 or
           (comp2 >= 0 and constraint.componentId[i] == comp2):
            constraint.scratchInAffected[i] = true
            constraint.scratchPath.setLen(0) # reuse as temp
            affectedCount += 1
            # Track old cycle/tail status
            if constraint.cycleId[i] == -1:
                oldAffectedTails += 1
            else:
                var found = false
                for cid in seenCycleIds:
                    if cid == constraint.cycleId[i]:
                        found = true
                        break
                if not found:
                    seenCycleIds.add(constraint.cycleId[i])
        else:
            constraint.scratchInAffected[i] = false

    oldAffectedCycles = seenCycleIds.len

    # Build list of affected nodes
    var affectedNodes = newSeqOfCap[int](affectedCount)
    for i in 0..<n:
        if constraint.scratchInAffected[i]:
            affectedNodes.add(i)

    # Temporarily set successor
    let oldSucc = constraint.successorArray[nodeIdx]
    constraint.successorArray[nodeIdx] = newSucc

    # Mini-traverse affected nodes
    let (newAffectedCycles, newAffectedTails) =
        constraint.countCyclesAndTails(affectedNodes, affectedCount)

    # Restore successor
    constraint.successorArray[nodeIdx] = oldSucc

    # Clean scratch
    for i in 0..<affectedCount:
        constraint.scratchInAffected[affectedNodes[i]] = false

    # Compute delta
    let newTotalCycles = constraint.numCycles - oldAffectedCycles + newAffectedCycles
    let newTotalTails = constraint.numTailNodes - oldAffectedTails + newAffectedTails
    let newPenalty = max(0, newTotalCycles - 1) + newTotalTails
    return newPenalty - constraint.cost

################################################################################
# updatePosition (incremental)
################################################################################

proc updatePosition*[T](constraint: CircuitConstraint[T], position: int, newValue: T) =
    ## Apply a move and incrementally update metadata.
    if position notin constraint.positionToIndex:
        return
    let nodeIdx = constraint.positionToIndex[position]
    let newSucc = int(newValue) - 1
    let n = constraint.n

    constraint.currentAssignment[position] = newValue

    # Identify affected components
    let comp1 = constraint.componentId[nodeIdx]
    var comp2 = -1
    if newSucc >= 0 and newSucc < n:
        comp2 = constraint.componentId[newSucc]

    # Gather affected nodes, count old cycles/tails
    var affectedCount = 0
    var oldAffectedCycles = 0
    var oldAffectedTails = 0
    var seenCycleIds: seq[int] = @[]

    for i in 0..<n:
        if constraint.componentId[i] == comp1 or
           (comp2 >= 0 and constraint.componentId[i] == comp2):
            constraint.scratchInAffected[i] = true
            affectedCount += 1
            if constraint.cycleId[i] == -1:
                oldAffectedTails += 1
            else:
                var found = false
                for cid in seenCycleIds:
                    if cid == constraint.cycleId[i]:
                        found = true
                        break
                if not found:
                    seenCycleIds.add(constraint.cycleId[i])
        else:
            constraint.scratchInAffected[i] = false

    oldAffectedCycles = seenCycleIds.len

    var affectedNodes = newSeqOfCap[int](affectedCount)
    for i in 0..<n:
        if constraint.scratchInAffected[i]:
            affectedNodes.add(i)

    # Apply the change
    constraint.successorArray[nodeIdx] = newSucc

    # Mini-traverse to get new cycle/tail counts and update metadata
    # We do the traversal inline here so we can update componentId/cycleId
    var newCycles = 0
    var newTails = 0

    # Reset scratch color for affected nodes
    for i in 0..<affectedCount:
        constraint.scratchColor[affectedNodes[i]] = White

    for i in 0..<affectedCount:
        let startNode = affectedNodes[i]
        if constraint.scratchColor[startNode] != White:
            continue

        constraint.scratchPath.setLen(0)
        var current = startNode
        var joinNode = -1  # node whose component to inherit (-1 = none)

        while true:
            if constraint.scratchColor[current] != White:
                break
            constraint.scratchColor[current] = Gray
            constraint.scratchPath.add(current)
            let succ = constraint.successorArray[current]
            if succ < 0 or succ >= n:
                current = succ
                break
            if not constraint.scratchInAffected[succ]:
                # Successor is outside affected set - inherit its component
                joinNode = succ
                current = -1
                break
            current = succ

        if current >= 0 and current < n and constraint.scratchColor[current] == Gray:
            # Found a cycle within affected set
            let compId = constraint.nextComponentId
            constraint.nextComponentId += 1
            newCycles += 1
            let cId = constraint.nextCycleId
            constraint.nextCycleId += 1
            var cycleStart = 0
            for j in 0..<constraint.scratchPath.len:
                if constraint.scratchPath[j] == current:
                    cycleStart = j
                    break
            newTails += cycleStart
            for j in cycleStart..<constraint.scratchPath.len:
                let node = constraint.scratchPath[j]
                constraint.scratchColor[node] = Black
                constraint.componentId[node] = compId
                constraint.cycleId[node] = cId
            for j in 0..<cycleStart:
                let node = constraint.scratchPath[j]
                constraint.scratchColor[node] = Black
                constraint.componentId[node] = compId
                constraint.cycleId[node] = -1
        else:
            # All path nodes are tails - inherit component from target
            let compId = if joinNode >= 0:
                # Exited to non-affected node, inherit its component
                constraint.componentId[joinNode]
            elif current >= 0 and current < n and constraint.scratchColor[current] == Black:
                # Hit a Black (already processed) affected node, inherit its component
                constraint.componentId[current]
            else:
                # Out of bounds - new component
                let c = constraint.nextComponentId
                constraint.nextComponentId += 1
                c
            newTails += constraint.scratchPath.len
            for node in constraint.scratchPath:
                constraint.scratchColor[node] = Black
                constraint.componentId[node] = compId
                constraint.cycleId[node] = -1

    # Clean scratch
    for i in 0..<affectedCount:
        constraint.scratchInAffected[affectedNodes[i]] = false

    # Update global counts
    constraint.numCycles = constraint.numCycles - oldAffectedCycles + newCycles
    constraint.numTailNodes = constraint.numTailNodes - oldAffectedTails + newTails
    constraint.cost = max(0, constraint.numCycles - 1) + constraint.numTailNodes

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](constraint: CircuitConstraint[T]): CircuitConstraint[T] =
    ## Creates a deep copy for parallel search.
    new(result)
    result.n = constraint.n
    result.positions = constraint.positions  # PackedSet is value type
    result.sortedPositions = constraint.sortedPositions  # Read-only after construction
    result.positionToIndex = constraint.positionToIndex  # Read-only after construction
    result.cost = constraint.cost

    # Deep copy mutable state
    result.successorArray = newSeq[int](constraint.n)
    for i in 0..<constraint.n:
        result.successorArray[i] = constraint.successorArray[i]

    result.currentAssignment = initTable[int, T]()
    for k, v in constraint.currentAssignment.pairs:
        result.currentAssignment[k] = v

    # Deep copy incremental tracking
    result.componentId = newSeq[int](constraint.n)
    result.cycleId = newSeq[int](constraint.n)
    for i in 0..<constraint.n:
        result.componentId[i] = constraint.componentId[i]
        result.cycleId[i] = constraint.cycleId[i]
    result.numCycles = constraint.numCycles
    result.numTailNodes = constraint.numTailNodes
    result.nextComponentId = constraint.nextComponentId
    result.nextCycleId = constraint.nextCycleId

    # Re-allocate scratch arrays fresh (no meaningful state)
    result.scratchColor = newSeq[NodeColor](constraint.n)
    result.scratchInAffected = newSeq[bool](constraint.n)
    result.scratchPath = newSeqOfCap[int](constraint.n)
