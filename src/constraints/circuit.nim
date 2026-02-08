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
    CircuitConstraint*[T] = ref object
        n*: int                              # number of nodes
        positions*: PackedSet[int]           # all variable positions
        sortedPositions*: seq[int]           # sorted positions array
        positionToIndex*: Table[int, int]    # position -> 0-based node index
        successorArray*: seq[int]            # 0-based successors (working copy)
        cost*: int                           # cached penalty
        currentAssignment*: Table[int, T]    # position -> current value

################################################################################
# Cycle counting algorithm (three-color traversal)
################################################################################

type
    NodeColor = enum
        White, Gray, Black

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
                # Out of bounds - all path nodes are tails
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

    for i, pos in result.sortedPositions:
        result.positionToIndex[pos] = i

################################################################################
# Initialize
################################################################################

proc initialize*[T](constraint: CircuitConstraint[T], assignment: seq[T]) =
    ## Build successor array from assignment and compute initial cost.
    for i, pos in constraint.sortedPositions:
        let value = assignment[pos]
        constraint.currentAssignment[pos] = value
        # Convert 1-based value to 0-based index
        constraint.successorArray[i] = int(value) - 1
    constraint.cost = constraint.computePenalty()

################################################################################
# moveDelta
################################################################################

proc moveDelta*[T](constraint: CircuitConstraint[T], position: int, oldValue, newValue: T): int =
    ## Temporarily modify successor array, recount penalty, restore, return delta.
    if position notin constraint.positionToIndex:
        return 0
    let nodeIdx = constraint.positionToIndex[position]
    let oldSucc = constraint.successorArray[nodeIdx]
    constraint.successorArray[nodeIdx] = int(newValue) - 1
    let newCost = constraint.computePenalty()
    constraint.successorArray[nodeIdx] = oldSucc
    return newCost - constraint.cost

################################################################################
# updatePosition
################################################################################

proc updatePosition*[T](constraint: CircuitConstraint[T], position: int, newValue: T) =
    ## Apply a move and recompute penalty.
    if position notin constraint.positionToIndex:
        return
    let nodeIdx = constraint.positionToIndex[position]
    constraint.currentAssignment[position] = newValue
    constraint.successorArray[nodeIdx] = int(newValue) - 1
    constraint.cost = constraint.computePenalty()

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](constraint: CircuitConstraint[T]): CircuitConstraint[T] =
    ## Creates a deep copy for parallel search.
    new(result)
    result.n = constraint.n
    result.positions = constraint.positions
    result.sortedPositions = constraint.sortedPositions
    result.positionToIndex = constraint.positionToIndex
    result.successorArray = constraint.successorArray
    result.cost = constraint.cost
    result.currentAssignment = constraint.currentAssignment
