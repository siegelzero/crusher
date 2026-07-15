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

import std/[tables, packedsets]

################################################################################
# Type definitions
################################################################################

type
    NodeColor = enum
        White, Gray, Black

    CircuitConstraint*[T] = ref object
        n*: int                              # number of nodes
        valueOffset*: int                    # subtracted from values to get 0-based index (1 for 1-based, 0 for 0-based)
        positions*: PackedSet[int]           # all variable positions
        positionArray*: seq[int]             # position per node index (input order)
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
        # Cycle geometry for O(1) moveDelta: ordinal of each cycle node along
        # its cycle (ord[succ(x)] = (ord[x]+1) mod len) and the cycle length.
        # Only meaningful for nodes with cycleId >= 0; stale values remain on
        # tail nodes and are never read.
        ordOnCycle: seq[int32]
        cycleLenAt: seq[int32]
        # Dense position -> node index lookup (-1 when position not in circuit)
        posToIdxDense: seq[int32]

        # Pre-allocated scratch space (avoids heap alloc per updatePosition call)
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
            let cycLen = int32(path.len - cycleStart)
            for i in cycleStart..<path.len:
                color[path[i]] = Black
                constraint.componentId[path[i]] = compId
                constraint.cycleId[path[i]] = cId
                constraint.ordOnCycle[path[i]] = int32(i - cycleStart)
                constraint.cycleLenAt[path[i]] = cycLen
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
# Constructor
################################################################################

proc newCircuitConstraint*[T](positions: openArray[int], valueOffset: int = 1): CircuitConstraint[T] =
    new(result)
    result.n = positions.len
    result.valueOffset = valueOffset
    result.positionArray = @positions  # Keep input order — node i = positions[i]
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
    result.ordOnCycle = newSeq[int32](result.n)
    result.cycleLenAt = newSeq[int32](result.n)

    # Pre-allocated scratch space
    result.scratchColor = newSeq[NodeColor](result.n)
    result.scratchInAffected = newSeq[bool](result.n)
    result.scratchPath = newSeqOfCap[int](result.n)

    var maxPos = -1
    for pos in positions:
        if pos > maxPos: maxPos = pos
    result.posToIdxDense = newSeq[int32](maxPos + 1)
    for i in 0..<result.posToIdxDense.len:
        result.posToIdxDense[i] = -1
    for i, pos in result.positionArray:
        result.positionToIndex[pos] = i
        result.posToIdxDense[pos] = int32(i)

################################################################################
# Initialize
################################################################################

proc initialize*[T](constraint: CircuitConstraint[T], assignment: seq[T]) =
    ## Build successor array from assignment and compute initial cost + metadata.
    for i, pos in constraint.positionArray:
        let value = assignment[pos]
        constraint.currentAssignment[pos] = value
        # Convert value to 0-based index (offset=1 for 1-based values, 0 for 0-based)
        constraint.successorArray[i] = int(value) - constraint.valueOffset

    # Reset metadata counters
    constraint.nextComponentId = 0
    constraint.nextCycleId = 0
    constraint.computeMetadata()
    constraint.cost = max(0, constraint.numCycles - 1) + constraint.numTailNodes

################################################################################
# moveDelta (incremental)
################################################################################

proc moveDelta*[T](constraint: CircuitConstraint[T], position: int, oldValue, newValue: T): int =
    ## O(1) moveDelta using the ρ-shape structure of functional graphs: each
    ## component holds at most one cycle, so redirecting one edge changes the
    ## cycle/tail counts in a closed form over cycle ordinals. Only moves that
    ## can create a cycle out of tail nodes need a short walk along the tail
    ## chain; everything else is arithmetic on the maintained metadata.
    if position >= constraint.posToIdxDense.len or constraint.posToIdxDense[position] < 0:
        return 0
    let u = int(constraint.posToIdxDense[position])
    let s1 = int(newValue) - constraint.valueOffset
    let s0 = constraint.successorArray[u]
    if s1 == s0:
        return 0
    let n = constraint.n
    let cidU = constraint.cycleId[u]

    var dCycles = 0
    var dTails = 0
    if cidU >= 0:
        # u is on a cycle of length L. Removing u→s0 opens it; the new edge
        # u→s1 decides what survives.
        let L = int(constraint.cycleLenAt[u])
        if s1 >= 0 and s1 < n and constraint.cycleId[s1] == cidU:
            # Re-close within the same cycle: the arc s1→…→u stays a cycle,
            # the remaining L - arc nodes become tails feeding into s1.
            let d = int(constraint.ordOnCycle[u]) - int(constraint.ordOnCycle[s1])
            let arc = (d + L) mod L + 1
            dTails = L - arc
        elif s1 >= 0 and s1 < n and constraint.componentId[s1] == constraint.componentId[u]:
            # s1 is a tail in u's own component: its chain re-enters the old
            # cycle at some node e, forming a new cycle s1→…→e→…→u→s1.
            # Walk the tail chain to find e (tails always reach the cycle).
            var walked = 0
            var x = s1
            while x >= 0 and x < n and constraint.cycleId[x] < 0:
                inc walked
                x = constraint.successorArray[x]
            doAssert x >= 0 and x < n and constraint.cycleId[x] == cidU,
                "circuit metadata inconsistent: tail chain must reach its component's cycle"
            let d = int(constraint.ordOnCycle[u]) - int(constraint.ordOnCycle[x])
            let arc = (d + L) mod L + 1
            dTails = (L - arc) - walked
        else:
            # s1 is in another component or out of bounds: the cycle fully
            # opens, all its L nodes become tails.
            dCycles = -1
            dTails = L
    else:
        # u is a tail: counts change only if the new edge closes a cycle,
        # i.e. s1's chain (tails only) reaches u before leaving.
        if s1 >= 0 and s1 < n and constraint.componentId[s1] == constraint.componentId[u] and
           constraint.cycleId[s1] < 0:
            var steps = 0
            var x = s1
            while true:
                if x == u:
                    # New cycle u→s1→…→u of steps+1 former tail nodes
                    dCycles = 1
                    dTails = -(steps + 1)
                    break
                x = constraint.successorArray[x]
                inc steps
                if x < 0 or x >= n or constraint.cycleId[x] >= 0:
                    break

    if dCycles == 0 and dTails == 0:
        return 0
    let newPenalty = max(0, constraint.numCycles + dCycles - 1) +
                     constraint.numTailNodes + dTails
    return newPenalty - constraint.cost

################################################################################
# updatePosition (incremental)
################################################################################

proc updatePosition*[T](constraint: CircuitConstraint[T], position: int, newValue: T) =
    ## Apply a move and incrementally update metadata.
    if position >= constraint.posToIdxDense.len or constraint.posToIdxDense[position] < 0:
        return
    let nodeIdx = int(constraint.posToIdxDense[position])
    let newSucc = int(newValue) - constraint.valueOffset
    let n = constraint.n

    constraint.currentAssignment[position] = newValue

    # Identify affected components: comp1 (moved node) and comp2 (new successor).
    # The OLD successor is already in comp1 (nodeIdx → oldSucc is an edge).
    let comp1 = constraint.componentId[nodeIdx]
    let oldSucc = constraint.successorArray[nodeIdx]
    assert oldSucc < 0 or oldSucc >= n or constraint.componentId[oldSucc] == comp1
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
            let cycLen = int32(constraint.scratchPath.len - cycleStart)
            for j in cycleStart..<constraint.scratchPath.len:
                let node = constraint.scratchPath[j]
                constraint.scratchColor[node] = Black
                constraint.componentId[node] = compId
                constraint.cycleId[node] = cId
                constraint.ordOnCycle[node] = int32(j - cycleStart)
                constraint.cycleLenAt[node] = cycLen
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
# Cycle-structure accessors (for circuit-repair move neighborhoods)
################################################################################

proc distinctCycleCount*[T](constraint: CircuitConstraint[T]): int =
    ## Number of disjoint cycles in the current functional graph. A satisfied
    ## circuit has exactly 1; >= 2 means there are subtours that must be merged.
    constraint.numCycles

proc nodeCycleIds*[T](constraint: CircuitConstraint[T]): seq[tuple[pos, cycleId: int]] =
    ## Current cycle membership of every node, as (variable position, cycleId).
    ## cycleId == -1 marks a tail node (one not on any cycle). Reflects the
    ## incrementally-maintained metadata, so it is O(n) with no traversal.
    result = newSeqOfCap[tuple[pos, cycleId: int]](constraint.n)
    for nodeIdx in 0..<constraint.n:
        result.add((constraint.positionArray[nodeIdx], constraint.cycleId[nodeIdx]))

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](constraint: CircuitConstraint[T]): CircuitConstraint[T] =
    ## Creates a deep copy for parallel search.
    new(result)
    result.n = constraint.n
    result.valueOffset = constraint.valueOffset
    result.positions = constraint.positions  # PackedSet is value type
    result.positionArray = constraint.positionArray  # Read-only after construction
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
    result.ordOnCycle = newSeq[int32](constraint.n)
    result.cycleLenAt = newSeq[int32](constraint.n)
    for i in 0..<constraint.n:
        result.componentId[i] = constraint.componentId[i]
        result.cycleId[i] = constraint.cycleId[i]
        result.ordOnCycle[i] = constraint.ordOnCycle[i]
        result.cycleLenAt[i] = constraint.cycleLenAt[i]
    result.numCycles = constraint.numCycles
    result.numTailNodes = constraint.numTailNodes
    result.nextComponentId = constraint.nextComponentId
    result.nextCycleId = constraint.nextCycleId
    result.posToIdxDense = constraint.posToIdxDense  # read-only after construction

    # Re-allocate scratch arrays fresh (no meaningful state)
    result.scratchColor = newSeq[NodeColor](constraint.n)
    result.scratchInAffected = newSeq[bool](constraint.n)
    result.scratchPath = newSeqOfCap[int](constraint.n)
