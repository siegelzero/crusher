## Circuit with Time Propagation constraint.
##
## Combines Hamiltonian circuit validation with time propagation along the tour.
## Works in two orientations:
##
##   backward (legacy, forward=false): positions hold predecessor variables
##     pred[l]; the successor map is derived by inversion each evaluation.
##   forward (forward=true): positions hold successor variables succ[l]; the
##     walk follows them directly. Nodes whose link is a FlatZinc literal
##     (fixed successor/predecessor) have positionArray[l] = -1 and their link
##     value baked in at construction.
##
## Given a distance matrix and time windows [early[l], late[l]], this constraint:
##
## 1. Checks circuit validity: penalty for non-Hamiltonian cycles/tails
## 2. Traverses the tour from the depot computing arrival/departure times:
##      arrival[next]   = departure[cur] + distance[next][cur]   (if the arc out
##                        of cur carries a time constraint, see outConstrained)
##      arrival[next]   = early[next]                            (otherwise: the
##                        clock resets, e.g. multi-vehicle giant-tour depot wraps)
##      departure[next] = max(arrival[next], early[next])
## 3. Penalizes time window violations: departure[l] > late[l]
##
## Service times are folded into the distance matrix by the translator
## (dist'[to][from] = dist[to][from] + service[from]).
##
## The circuit penalty is weighted by n (number of nodes) to ensure circuit
## repair takes priority over time window adjustments.
##
## Objective hooks (set by the optimizer during bound tightening):
##   useMaxMetric=false: metric = arrival at objectiveNodeIdx (TSPTW makespan)
##   useMaxMetric=true:  metric = max departure over the tour (VRP latest time)
## objectiveWeight/objectiveMetricLo/objectiveConstOffset describe how the
## metric enters a linear minimized objective (objective = sum w_i*metric_i +
## offset across instances), letting the optimizer distribute a global bound.

import std/[tables, packedsets]

type
    CircuitTimePropConstraint*[T] = ref object
        n*: int
        valueOffset*: int                    # 1 for 1-based values, 0 for 0-based
        forward*: bool                       # positions hold successors instead of predecessors
        positions*: PackedSet[int]           # link positions (for constraint interface)
        positionArray*: seq[int]             # link position per node (0-based), -1 if fixed
        positionToIndex*: Table[int, int]    # link position -> 0-based node index

        # Problem data (immutable)
        distanceMatrix*: seq[seq[T]]         # dist[to][from], 0-based
        earlyTimes*: seq[T]
        lateTimes*: seq[T]
        outConstrained*: seq[bool]           # arc out of node carries a time constraint
        depotIndex*: int                     # 0-based
        depotDeparture*: T

        # Output positions (channel positions for computed values)
        arrivalPositions*: seq[int]          # system positions of arrival[l], -1 if none
        departurePositions*: seq[int]        # system positions of departure[l], -1 if none

        # Mutable state
        links*: seq[int]                     # 0-based link value per node (pred or succ)
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
        scratchLinks*: seq[int]              # temporary link array for moveDelta
        scratchArrival*: seq[T]
        scratchDeparture*: seq[T]

        # Optional objective bound (set by optimizer)
        objectiveNodeIdx*: int               # 0-based node index for objective (arrival at this node)
        useMaxMetric*: bool                  # metric = max departure instead of arrival at node
        objectiveMetric*: T                  # cached metric for the current assignment
        objectiveUpperBound*: T              # upper bound on the metric (-1 = no bound)
        objectiveBoundActive*: bool
        objectiveWeight*: int                # weight of metric in the minimized objective (0 = unlinked)
        objectiveMetricLo*: T                # static lower bound of the metric
        objectiveConstOffset*: T             # constant term of the linear objective


proc newCircuitTimePropConstraint*[T](
        linkPositions: openArray[int],
        distanceMatrix: seq[seq[T]],
        earlyTimes, lateTimes: seq[T],
        depotIndex: int,
        depotDeparture: T,
        arrivalPositions, departurePositions: seq[int],
        valueOffset: int = 1,
        forward: bool = false,
        fixedLinks: seq[int] = @[],
        outConstrained: seq[bool] = @[],
        useMaxMetric: bool = false,
        objectiveWeight: int = 0,
        objectiveMetricLo: T = T(0),
        objectiveConstOffset: T = T(0)
    ): CircuitTimePropConstraint[T] =
    new(result)
    let n = linkPositions.len
    result.n = n
    result.valueOffset = valueOffset
    result.forward = forward
    result.positionArray = @linkPositions
    result.positions = initPackedSet[int]()
    result.positionToIndex = initTable[int, int]()
    for i, pos in linkPositions:
        if pos >= 0:
            result.positions.incl(pos)
            result.positionToIndex[pos] = i

    result.distanceMatrix = distanceMatrix
    result.earlyTimes = earlyTimes
    result.lateTimes = lateTimes
    result.depotIndex = depotIndex
    result.depotDeparture = depotDeparture
    result.arrivalPositions = arrivalPositions
    result.departurePositions = departurePositions
    if outConstrained.len == n:
        result.outConstrained = outConstrained
    else:
        result.outConstrained = newSeq[bool](n)
        for i in 0..<n: result.outConstrained[i] = true

    # Circuit weight: moderate scaling so circuit violations are significant
    # but not so overwhelming that the solver can't explore through them.
    # Use n (number of nodes) as a balanced weight — each circuit violation
    # is equivalent to n time-penalty units.
    result.circuitWeight = n

    result.links = newSeq[int](n)
    if fixedLinks.len == n:
        for i in 0..<n: result.links[i] = fixedLinks[i]
    result.arrivalTime = newSeq[T](n)
    result.departureTime = newSeq[T](n)
    result.scratchInAffected = newSeq[bool](n)
    result.scratchPath = newSeqOfCap[int](n)
    result.scratchLinks = newSeq[int](n)
    result.scratchArrival = newSeq[T](n)
    result.scratchDeparture = newSeq[T](n)
    result.objectiveNodeIdx = depotIndex  # default: objective = arrival at depot
    result.useMaxMetric = useMaxMetric
    result.objectiveMetric = T(0)
    result.objectiveUpperBound = T(0)
    result.objectiveBoundActive = false
    result.objectiveWeight = objectiveWeight
    result.objectiveMetricLo = objectiveMetricLo
    result.objectiveConstOffset = objectiveConstOffset
    result.cost = 0


proc computePenalties*[T](c: CircuitTimePropConstraint[T],
                           links: openArray[int],
                           arrival: var openArray[T],
                           departure: var openArray[T]): tuple[circPen, twPen: int, metric: T] =
    ## Combined circuit penalty + time computation in a single traversal.
    ## Circuit penalty = nodes NOT reachable from depot (+ 1 if tour doesn't close).
    ## Time penalty = sum of max(0, departure[l] - late[l]).
    ## Metric = max departure seen (useMaxMetric) or arrival at objectiveNodeIdx.
    let n = c.n

    # Build successor mapping. Forward orientation: links ARE successors.
    # Backward orientation: succ[k] = l where pred[l] = k.
    c.scratchPath.setLen(n)
    for i in 0..<n:
        c.scratchPath[i] = -1
        c.scratchInAffected[i] = false  # used as "visited" marker
    if c.forward:
        for l in 0..<n:
            let s = links[l]
            if s >= 0 and s < n:
                c.scratchPath[l] = s
    else:
        for l in 0..<n:
            let p = links[l]
            if p >= 0 and p < n:
                c.scratchPath[p] = l

    # Traverse from depot computing times
    departure[c.depotIndex] = c.depotDeparture
    arrival[c.depotIndex] = c.depotDeparture
    c.scratchInAffected[c.depotIndex] = true

    var visited = 1
    var current = c.depotIndex
    var twPenalty = 0
    var maxTime = c.depotDeparture

    for step in 1..<n:
        let next = c.scratchPath[current]
        if next < 0 or next >= n or c.scratchInAffected[next]:
            break  # broken or cycle back to non-depot

        if c.outConstrained[current]:
            arrival[next] = departure[current] + c.distanceMatrix[next][current]
        else:
            # No time constraint on this arc: the clock resets (e.g. giant-tour
            # wrap from one vehicle's end depot to the next vehicle's start).
            arrival[next] = c.earlyTimes[next]
        departure[next] = max(arrival[next], c.earlyTimes[next])
        if departure[next] > c.lateTimes[next]:
            twPenalty += int(departure[next] - c.lateTimes[next])
        if departure[next] > maxTime:
            maxTime = departure[next]
        c.scratchInAffected[next] = true
        inc visited
        current = next

    # Check tour closure and compute depot arrival
    var circPenalty = n - visited
    if visited == n:
        let lastSucc = c.scratchPath[current]
        if lastSucc != c.depotIndex:
            circPenalty = 1  # all visited but doesn't close
        elif c.outConstrained[current]:
            arrival[c.depotIndex] = departure[current] + c.distanceMatrix[c.depotIndex][current]
            if arrival[c.depotIndex] > c.lateTimes[c.depotIndex]:
                twPenalty += int(arrival[c.depotIndex] - c.lateTimes[c.depotIndex])
            if arrival[c.depotIndex] > maxTime:
                maxTime = arrival[c.depotIndex]

    let metric = if c.useMaxMetric: maxTime
                 else: arrival[c.objectiveNodeIdx]
    return (circPen: circPenalty, twPen: twPenalty, metric: metric)


proc objPenaltyFor[T](c: CircuitTimePropConstraint[T], metric: T): int =
    if c.objectiveBoundActive and metric > c.objectiveUpperBound:
        int(metric - c.objectiveUpperBound)
    else:
        0


proc initialize*[T](c: CircuitTimePropConstraint[T], assignment: seq[T]) =
    for i, pos in c.positionArray:
        if pos >= 0:
            c.links[i] = int(assignment[pos]) - c.valueOffset

    let pens = c.computePenalties(c.links, c.arrivalTime, c.departureTime)
    c.circuitPenalty = pens.circPen
    c.timeWindowPenalty = pens.twPen
    c.objectiveMetric = pens.metric
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty +
             c.objPenaltyFor(pens.metric)


proc setObjectiveBound*[T](c: CircuitTimePropConstraint[T], upperBound: T) =
    ## Set the upper bound on the objective metric.
    ## Recomputes cost to include the objective penalty.
    c.objectiveUpperBound = upperBound
    c.objectiveBoundActive = true
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty +
             c.objPenaltyFor(c.objectiveMetric)


proc clearObjectiveBound*[T](c: CircuitTimePropConstraint[T]) =
    c.objectiveBoundActive = false
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty


proc moveDelta*[T](c: CircuitTimePropConstraint[T],
                    position: int, oldValue, newValue: T): int =
    if position notin c.positionToIndex:
        return 0
    let nodeIdx = c.positionToIndex[position]
    let n = c.n

    # Build temporary link array with the change
    for i in 0..<n:
        c.scratchLinks[i] = c.links[i]
    c.scratchLinks[nodeIdx] = int(newValue) - c.valueOffset

    # Compute penalties with the hypothetical change
    let newPens = c.computePenalties(c.scratchLinks, c.scratchArrival, c.scratchDeparture)
    let newCost = newPens.circPen * c.circuitWeight + newPens.twPen +
                  c.objPenaltyFor(newPens.metric)
    return newCost - c.cost


proc updatePosition*[T](c: CircuitTimePropConstraint[T],
                         position: int, newValue: T) =
    if position notin c.positionToIndex:
        return
    let nodeIdx = c.positionToIndex[position]
    c.links[nodeIdx] = int(newValue) - c.valueOffset

    let pens = c.computePenalties(c.links, c.arrivalTime, c.departureTime)
    c.circuitPenalty = pens.circPen
    c.timeWindowPenalty = pens.twPen
    c.objectiveMetric = pens.metric
    c.cost = c.circuitPenalty * c.circuitWeight + c.timeWindowPenalty +
             c.objPenaltyFor(pens.metric)


proc deepCopy*[T](c: CircuitTimePropConstraint[T]): CircuitTimePropConstraint[T] =
    new(result)
    result.n = c.n
    result.valueOffset = c.valueOffset
    result.forward = c.forward
    result.positions = c.positions
    result.positionArray = c.positionArray
    result.positionToIndex = c.positionToIndex

    result.distanceMatrix = c.distanceMatrix
    result.earlyTimes = c.earlyTimes
    result.lateTimes = c.lateTimes
    result.outConstrained = c.outConstrained
    result.depotIndex = c.depotIndex
    result.depotDeparture = c.depotDeparture
    result.arrivalPositions = c.arrivalPositions
    result.departurePositions = c.departurePositions
    result.circuitWeight = c.circuitWeight

    # Deep copy mutable state
    result.links = newSeq[int](c.n)
    result.arrivalTime = newSeq[T](c.n)
    result.departureTime = newSeq[T](c.n)
    for i in 0..<c.n:
        result.links[i] = c.links[i]
        result.arrivalTime[i] = c.arrivalTime[i]
        result.departureTime[i] = c.departureTime[i]

    result.cost = c.cost
    result.circuitPenalty = c.circuitPenalty
    result.timeWindowPenalty = c.timeWindowPenalty
    result.objectiveNodeIdx = c.objectiveNodeIdx
    result.useMaxMetric = c.useMaxMetric
    result.objectiveMetric = c.objectiveMetric
    result.objectiveUpperBound = c.objectiveUpperBound
    result.objectiveBoundActive = c.objectiveBoundActive
    result.objectiveWeight = c.objectiveWeight
    result.objectiveMetricLo = c.objectiveMetricLo
    result.objectiveConstOffset = c.objectiveConstOffset

    # Fresh scratch space
    result.scratchInAffected = newSeq[bool](c.n)
    result.scratchPath = newSeqOfCap[int](c.n)
    result.scratchLinks = newSeq[int](c.n)
    result.scratchArrival = newSeq[T](c.n)
    result.scratchDeparture = newSeq[T](c.n)
