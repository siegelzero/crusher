## Circuit with Time Propagation constraint.
##
## Combines Hamiltonian circuit validation with time-window propagation.
## Given predecessor variables pred[l], a distance matrix, and time windows
## [early[l], late[l]], this constraint:
##
## 1. Checks circuit validity: penalty for non-Hamiltonian cycles/tails
## 2. Traverses the tour from the depot to compute arrival/departure times:
##    arrival[l] = departure[pred[l]] + distance[l][pred[l]]
##    departure[l] = max(arrival[l], early[l])
## 3. Penalizes time window violations: departure[l] > late[l]
##
## The circuit penalty is weighted by n (number of nodes) to ensure circuit
## repair takes priority over time window adjustments.

import std/[tables, packedsets]

type
    CircuitTimePropConstraint*[T] = ref object
        n*: int
        valueOffset*: int                    # 1 for 1-based values, 0 for 0-based
        positions*: PackedSet[int]           # pred positions (for constraint interface)
        positionArray*: seq[int]             # pred position per node (0-based)
        positionToIndex*: Table[int, int]    # pred position -> 0-based node index

        # Problem data (immutable)
        distanceMatrix*: seq[seq[T]]         # dist[to][from], 0-based
        earlyTimes*: seq[T]
        lateTimes*: seq[T]
        depotIndex*: int                     # 0-based
        depotDeparture*: T

        # Output positions (channel positions for computed values)
        arrivalPositions*: seq[int]          # system positions of arrival[l], -1 if none
        departurePositions*: seq[int]        # system positions of departure[l], -1 if none

        # Mutable state
        predecessorOf*: seq[int]             # 0-based predecessor for each node
        cost*: int                           # cached total penalty

        # Time state
        arrivalTime*: seq[T]
        departureTime*: seq[T]
        circuitPenalty*: int
        timeWindowPenalty*: int
        circuitWeight*: int                  # weight for circuit violations

        # Scratch space
        scratchInAffected*: seq[bool]
        scratchPath*: seq[int]
        scratchPred*: seq[int]               # temporary predecessor array for moveDelta
        scratchArrival*: seq[T]
        scratchDeparture*: seq[T]

        # Optional objective bound (set by optimizer)
        objectiveNodeIdx*: int               # 0-based node index for objective (arrival at this node)
        objectiveUpperBound*: T              # upper bound on arrival at objective node (-1 = no bound)
        objectiveBoundActive*: bool


proc newCircuitTimePropConstraint*[T](
        predPositions: openArray[int],
        distanceMatrix: seq[seq[T]],
        earlyTimes, lateTimes: seq[T],
        depotIndex: int,
        depotDeparture: T,
        arrivalPositions, departurePositions: seq[int],
        valueOffset: int = 1
    ): CircuitTimePropConstraint[T] =
    new(result)
    let n = predPositions.len
    result.n = n
    result.valueOffset = valueOffset
    result.positionArray = @predPositions
    result.positions = toPackedSet[int](predPositions)
    result.positionToIndex = initTable[int, int]()
    for i, pos in predPositions:
        result.positionToIndex[pos] = i

    result.distanceMatrix = distanceMatrix
    result.earlyTimes = earlyTimes
    result.lateTimes = lateTimes
    result.depotIndex = depotIndex
    result.depotDeparture = depotDeparture
    result.arrivalPositions = arrivalPositions
    result.departurePositions = departurePositions

    # Circuit weight: moderate scaling so circuit violations are significant
    # but not so overwhelming that the solver can't explore through them.
    # Use n (number of nodes) as a balanced weight — each circuit violation
    # is equivalent to n time-penalty units.
    result.circuitWeight = n

    result.predecessorOf = newSeq[int](n)
    result.arrivalTime = newSeq[T](n)
    result.departureTime = newSeq[T](n)
    result.scratchInAffected = newSeq[bool](n)
    result.scratchPath = newSeqOfCap[int](n)
    result.scratchPred = newSeq[int](n)
    result.scratchArrival = newSeq[T](n)
    result.scratchDeparture = newSeq[T](n)
    result.objectiveNodeIdx = depotIndex  # default: objective = arrival at depot
    result.objectiveUpperBound = T(0)
    result.objectiveBoundActive = false
    result.cost = 0


proc computePenalties*[T](c: CircuitTimePropConstraint[T],
                           pred: openArray[int],
                           arrival: var openArray[T],
                           departure: var openArray[T]): tuple[circPen, twPen: int] =
    ## Combined circuit penalty + time computation in a single traversal.
    ## Circuit penalty = nodes NOT reachable from depot (+ 1 if tour doesn't close).
    ## Time penalty = sum of max(0, departure[l] - late[l]).
    let n = c.n

    # Build successor mapping: succ[k] = l where pred[l] = k
    c.scratchPath.setLen(n)
    for i in 0..<n:
        c.scratchPath[i] = -1
        c.scratchInAffected[i] = false  # used as "visited" marker
    for l in 0..<n:
        let p = pred[l]
        if p >= 0 and p < n:
            c.scratchPath[p] = l

    # Traverse from depot computing times
    departure[c.depotIndex] = c.depotDeparture
    arrival[c.depotIndex] = c.depotDeparture
    c.scratchInAffected[c.depotIndex] = true

    var visited = 1
    var current = c.depotIndex
    var twPenalty = 0

    for step in 1..<n:
        let next = c.scratchPath[current]
        if next < 0 or next >= n or c.scratchInAffected[next]:
            break  # broken or cycle back to non-depot

        arrival[next] = departure[current] + c.distanceMatrix[next][current]
        departure[next] = max(arrival[next], c.earlyTimes[next])
        if departure[next] > c.lateTimes[next]:
            twPenalty += int(departure[next] - c.lateTimes[next])
        c.scratchInAffected[next] = true
        inc visited
        current = next

    # Check tour closure and compute depot arrival
    var circPenalty = n - visited
    if visited == n:
        let lastSucc = c.scratchPath[current]
        if lastSucc != c.depotIndex:
            circPenalty = 1  # all visited but doesn't close
        else:
            arrival[c.depotIndex] = departure[current] + c.distanceMatrix[c.depotIndex][current]
            if arrival[c.depotIndex] > c.lateTimes[c.depotIndex]:
                twPenalty += int(arrival[c.depotIndex] - c.lateTimes[c.depotIndex])

    return (circPen: circPenalty, twPen: twPenalty)


proc initialize*[T](c: CircuitTimePropConstraint[T], assignment: seq[T]) =
    let n = c.n
    for i, pos in c.positionArray:
        let value = assignment[pos]
        c.predecessorOf[i] = int(value) - c.valueOffset

    let pens = c.computePenalties(c.predecessorOf, c.arrivalTime, c.departureTime)
    c.circuitPenalty = pens.circPen
    c.timeWindowPenalty = pens.twPen
    var objPenalty = 0
    if c.objectiveBoundActive:
        let objArrival = c.arrivalTime[c.objectiveNodeIdx]
        if objArrival > c.objectiveUpperBound:
            objPenalty = int(objArrival - c.objectiveUpperBound)
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty + objPenalty


proc setObjectiveBound*[T](c: CircuitTimePropConstraint[T], upperBound: T) =
    ## Set the upper bound on the objective (arrival at depot).
    ## Recomputes cost to include the objective penalty.
    c.objectiveUpperBound = upperBound
    c.objectiveBoundActive = true
    # Recompute cost with the new bound
    var objPenalty = 0
    let objArrival = c.arrivalTime[c.objectiveNodeIdx]
    if objArrival > upperBound:
        objPenalty = int(objArrival - upperBound)
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty + objPenalty


proc clearObjectiveBound*[T](c: CircuitTimePropConstraint[T]) =
    c.objectiveBoundActive = false
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty


proc moveDelta*[T](c: CircuitTimePropConstraint[T],
                    position: int, oldValue, newValue: T): int =
    if position notin c.positionToIndex:
        return 0
    let nodeIdx = c.positionToIndex[position]
    let n = c.n

    # Build temporary predecessor array with the change
    for i in 0..<n:
        c.scratchPred[i] = c.predecessorOf[i]
    c.scratchPred[nodeIdx] = int(newValue) - c.valueOffset

    # Compute penalties with the hypothetical change
    let newPens = c.computePenalties(c.scratchPred, c.scratchArrival, c.scratchDeparture)
    let newCircuitPenalty = newPens.circPen
    let newTimePenalty = newPens.twPen
    var newObjPenalty = 0
    if c.objectiveBoundActive:
        let objArrival = c.scratchArrival[c.objectiveNodeIdx]
        if objArrival > c.objectiveUpperBound:
            newObjPenalty = int(objArrival - c.objectiveUpperBound)

    let newCost = newCircuitPenalty * c.circuitWeight + newTimePenalty + newObjPenalty
    return newCost - c.cost


proc updatePosition*[T](c: CircuitTimePropConstraint[T],
                         position: int, newValue: T) =
    if position notin c.positionToIndex:
        return
    let nodeIdx = c.positionToIndex[position]
    c.predecessorOf[nodeIdx] = int(newValue) - c.valueOffset

    let pens = c.computePenalties(c.predecessorOf, c.arrivalTime, c.departureTime)
    c.circuitPenalty = pens.circPen
    c.timeWindowPenalty = pens.twPen
    var objPenalty = 0
    if c.objectiveBoundActive:
        let objArrival = c.arrivalTime[c.objectiveNodeIdx]
        if objArrival > c.objectiveUpperBound:
            objPenalty = int(objArrival - c.objectiveUpperBound)
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty + objPenalty


proc deepCopy*[T](c: CircuitTimePropConstraint[T]): CircuitTimePropConstraint[T] =
    new(result)
    result.n = c.n
    result.valueOffset = c.valueOffset
    result.positions = c.positions
    result.positionArray = c.positionArray
    result.positionToIndex = c.positionToIndex

    result.distanceMatrix = c.distanceMatrix
    result.earlyTimes = c.earlyTimes
    result.lateTimes = c.lateTimes
    result.depotIndex = c.depotIndex
    result.depotDeparture = c.depotDeparture
    result.arrivalPositions = c.arrivalPositions
    result.departurePositions = c.departurePositions
    result.circuitWeight = c.circuitWeight

    # Deep copy mutable state
    result.predecessorOf = newSeq[int](c.n)
    result.arrivalTime = newSeq[T](c.n)
    result.departureTime = newSeq[T](c.n)
    for i in 0..<c.n:
        result.predecessorOf[i] = c.predecessorOf[i]
        result.arrivalTime[i] = c.arrivalTime[i]
        result.departureTime[i] = c.departureTime[i]

    result.cost = c.cost
    result.circuitPenalty = c.circuitPenalty
    result.timeWindowPenalty = c.timeWindowPenalty
    result.objectiveNodeIdx = c.objectiveNodeIdx
    result.objectiveUpperBound = c.objectiveUpperBound
    result.objectiveBoundActive = c.objectiveBoundActive

    # Fresh scratch space
    result.scratchInAffected = newSeq[bool](c.n)
    result.scratchPath = newSeqOfCap[int](c.n)
    result.scratchPred = newSeq[int](c.n)
    result.scratchArrival = newSeq[T](c.n)
    result.scratchDeparture = newSeq[T](c.n)
