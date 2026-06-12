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
## equalityChain mode (resource accumulators, e.g. CVRP load chains
## A[succ[n]] = A[n] + demand[n]): values are exact, so there is no
## wait-at-node clamping (departure = arrival) and BOTH window violations are
## penalized (departure < early as well as departure > late) — the windows
## are the variables' domain bounds.
##
## The circuit penalty is weighted by n (number of nodes) to ensure circuit
## repair takes priority over time window adjustments.
##
## Objective hooks (set by the optimizer during bound tightening):
##   useSumMetric=true:  metric = sum of sumMetricWeights[l] * departure[l]
##                       (CVRP-style objective: weighted sum of observed times;
##                       unvisited nodes contribute their earliest time)
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
        equalityChain*: bool                 # exact accumulator: no clamping, two-sided windows
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
        scratchSegNodes*: seq[int]           # equality walk: open segment nodes
        scratchSegCum*: seq[T]               # equality walk: cumulative offsets

        # Incremental move evaluation (forward orientation only): caches over
        # the committed walk, rebuilt on initialize/updatePosition. moveDelta
        # then reuses the unchanged prefix up to the changed node and only
        # re-walks the suffix — O(1) when the new link splices back into the
        # prefix (the walk breaks immediately).
        incValid*: bool
        tourPos*: seq[int]                   # node -> step in committed walk, -1 unvisited
        tourSeq*: seq[int]                   # step -> node
        tourLen*: int
        preTw*: seq[int]                     # legacy walk: cumulative tw penalty through step
        preMax*: seq[T]                      # legacy walk: max departure through step
        preWSum*: seq[T]                     # sum metric: cumulative w*departure through step
        preWEarly*: seq[T]                   # sum metric: cumulative w*early over visited
        totalWEarly*: T                      # sum metric: w*early over ALL nodes
        peqCum*: seq[int]                    # equality walk: cumulative per-node window penalty
        segStartStep*: seq[int]              # equality walk: step of open segment's first node
        cumOff*: seq[T]                      # equality walk: cumulative offset within segment
        visitStamp*: seq[int]                # epoch-stamped visited marks for moveDelta
        curStamp*: int

        # Optional objective bound (set by optimizer)
        objectiveNodeIdx*: int               # 0-based node index for objective (arrival at this node)
        useMaxMetric*: bool                  # metric = max departure instead of arrival at node
        useSumMetric*: bool                  # metric = weighted sum of departures (overrides useMaxMetric)
        sumMetricWeights*: seq[T]            # per-node weight in the sum metric (empty unless useSumMetric)
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
        objectiveConstOffset: T = T(0),
        useSumMetric: bool = false,
        sumMetricWeights: seq[T] = @[],
        equalityChain: bool = false
    ): CircuitTimePropConstraint[T] =
    new(result)
    let n = linkPositions.len
    result.n = n
    result.valueOffset = valueOffset
    result.forward = forward
    result.equalityChain = equalityChain
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
    result.scratchSegNodes = newSeqOfCap[int](n)
    result.scratchSegCum = newSeqOfCap[T](n)
    result.incValid = false
    result.tourPos = newSeq[int](n)
    result.tourSeq = newSeq[int](n)
    result.preTw = newSeq[int](n)
    result.preMax = newSeq[T](n)
    result.preWSum = newSeq[T](n)
    result.preWEarly = newSeq[T](n)
    result.peqCum = newSeq[int](n)
    result.segStartStep = newSeq[int](n)
    result.cumOff = newSeq[T](n)
    result.visitStamp = newSeq[int](n)
    result.curStamp = 0
    result.totalWEarly = T(0)
    if useSumMetric and sumMetricWeights.len == n:
        for i in 0..<n:
            result.totalWEarly += sumMetricWeights[i] * earlyTimes[i]
    result.objectiveNodeIdx = depotIndex  # default: objective = arrival at depot
    result.useMaxMetric = useMaxMetric
    result.useSumMetric = useSumMetric and sumMetricWeights.len == n
    result.sumMetricWeights = sumMetricWeights
    result.objectiveMetric = T(0)
    result.objectiveUpperBound = T(0)
    result.objectiveBoundActive = false
    result.objectiveWeight = objectiveWeight
    result.objectiveMetricLo = objectiveMetricLo
    result.objectiveConstOffset = objectiveConstOffset
    result.cost = 0


proc computePenaltiesEquality[T](c: CircuitTimePropConstraint[T],
                                 links: openArray[int],
                                 arrival: var openArray[T],
                                 departure: var openArray[T]): tuple[circPen, twPen: int, metric: T] =
    ## Equality-chain walk: values are exact, propagated within maximal chained
    ## segments and anchored at a fixed end — forward from a fixed first node
    ## (CVRP load chains anchored at start depots), else backward from a fixed
    ## last node (vehicle-painting chains anchored at end depots). A node is
    ## "fixed" when its window is a point (early == late). Unanchored segments
    ## (possible only on broken tours) contribute no window penalty — the
    ## circuit penalty already dominates there.
    let n = c.n
    c.scratchPath.setLen(n)
    for i in 0..<n:
        c.scratchPath[i] = -1
        c.scratchInAffected[i] = false
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

    var twPenalty = 0
    c.scratchSegNodes.setLen(0)
    c.scratchSegCum.setLen(0)

    template segFixed(v: int): bool =
        c.earlyTimes[v] == c.lateTimes[v]

    # ghostLast: the last entry is the depot reached over the closure arc —
    # check/penalize its value but keep its start-of-walk departure.
    template closeSegment(ghostLast: bool) =
        if c.scratchSegNodes.len > 0:
            let firstV = c.scratchSegNodes[0]
            let lastV = c.scratchSegNodes[^1]
            var anchored = true
            var base: T
            if segFixed(firstV):
                base = c.earlyTimes[firstV] - c.scratchSegCum[0]
            elif segFixed(lastV):
                base = c.earlyTimes[lastV] - c.scratchSegCum[^1]
            else:
                anchored = false
            for j in 0..<c.scratchSegNodes.len:
                let v = c.scratchSegNodes[j]
                let isGhost = ghostLast and j == c.scratchSegNodes.len - 1
                if anchored:
                    let val = base + c.scratchSegCum[j]
                    arrival[v] = val
                    if not isGhost:
                        departure[v] = val
                    if val < c.earlyTimes[v]:
                        twPenalty += int(c.earlyTimes[v] - val)
                    elif val > c.lateTimes[v]:
                        twPenalty += int(val - c.lateTimes[v])
                elif not isGhost:
                    arrival[v] = c.earlyTimes[v]
                    departure[v] = c.earlyTimes[v]
            c.scratchSegNodes.setLen(0)
            c.scratchSegCum.setLen(0)

    var cum = T(0)
    c.scratchSegNodes.add(c.depotIndex)
    c.scratchSegCum.add(T(0))
    arrival[c.depotIndex] = c.depotDeparture
    departure[c.depotIndex] = c.depotDeparture
    c.scratchInAffected[c.depotIndex] = true

    var visited = 1
    var current = c.depotIndex
    for step in 1..<n:
        let next = c.scratchPath[current]
        if next < 0 or next >= n or c.scratchInAffected[next]:
            break
        if c.outConstrained[current]:
            cum += c.distanceMatrix[next][current]
        else:
            closeSegment(false)
            cum = T(0)
        c.scratchSegNodes.add(next)
        c.scratchSegCum.add(cum)
        c.scratchInAffected[next] = true
        inc visited
        current = next

    var circPenalty = n - visited
    if visited == n:
        let lastSucc = c.scratchPath[current]
        if lastSucc != c.depotIndex:
            circPenalty = 1
        elif c.outConstrained[current]:
            cum += c.distanceMatrix[c.depotIndex][current]
            c.scratchSegNodes.add(c.depotIndex)
            c.scratchSegCum.add(cum)
            closeSegment(true)
    closeSegment(false)

    return (circPen: circPenalty, twPen: twPenalty, metric: T(0))


proc computePenalties*[T](c: CircuitTimePropConstraint[T],
                           links: openArray[int],
                           arrival: var openArray[T],
                           departure: var openArray[T]): tuple[circPen, twPen: int, metric: T] =
    ## Combined circuit penalty + time computation in a single traversal.
    ## Circuit penalty = nodes NOT reachable from depot (+ 1 if tour doesn't close).
    ## Time penalty = sum of max(0, departure[l] - late[l]).
    ## Metric = max departure seen (useMaxMetric) or arrival at objectiveNodeIdx.
    if c.equalityChain:
        return c.computePenaltiesEquality(links, arrival, departure)
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

    var metric: T
    if c.useSumMetric:
        # Weighted sum of departures over observed nodes. Unvisited nodes (broken
        # tour) contribute their earliest time, keeping the metric an optimistic
        # lower bound so objective-bound pressure never stacks on circuit repair.
        metric = T(0)
        for i in 0..<n:
            let w = c.sumMetricWeights[i]
            if w != T(0):
                metric += w * (if c.scratchInAffected[i]: departure[i]
                               else: c.earlyTimes[i])
    elif c.useMaxMetric:
        metric = maxTime
    else:
        metric = arrival[c.objectiveNodeIdx]
    return (circPen: circPenalty, twPen: twPenalty, metric: metric)


proc objPenaltyFor[T](c: CircuitTimePropConstraint[T], metric: T): int =
    if c.objectiveBoundActive and metric > c.objectiveUpperBound:
        int(metric - c.objectiveUpperBound)
    else:
        0


proc rebuildIncCache[T](c: CircuitTimePropConstraint[T]) =
    ## Rebuild the committed-walk caches used by incremental moveDelta. Must
    ## run right after computePenalties has refreshed c.arrivalTime /
    ## c.departureTime for the committed links. Forward orientation only —
    ## a backward (predecessor) link change rewires two successor arcs, so the
    ## prefix argument doesn't hold there.
    c.incValid = c.forward and
                 (c.equalityChain or c.useMaxMetric or c.useSumMetric)
    if not c.incValid: return
    let n = c.n
    for i in 0..<n:
        c.tourPos[i] = -1
    var step = 0
    var cur = c.depotIndex
    var twAcc = 0
    var maxAcc = c.depotDeparture
    var wSumAcc = T(0)
    var wEarlyAcc = T(0)
    var peqAcc = 0
    var segStart = 0
    var cum = T(0)
    while true:
        c.tourPos[cur] = step
        c.tourSeq[step] = cur
        if step > 0:
            let d = c.departureTime[cur]
            if d > c.lateTimes[cur]:
                twAcc += int(d - c.lateTimes[cur])
            if d > maxAcc: maxAcc = d
            if d < c.earlyTimes[cur]:
                peqAcc += int(c.earlyTimes[cur] - d)
            elif d > c.lateTimes[cur]:
                peqAcc += int(d - c.lateTimes[cur])
        if c.useSumMetric:
            let w = c.sumMetricWeights[cur]
            if w != T(0):
                wSumAcc += w * c.departureTime[cur]
                wEarlyAcc += w * c.earlyTimes[cur]
        c.preTw[step] = twAcc
        c.preMax[step] = maxAcc
        c.preWSum[step] = wSumAcc
        c.preWEarly[step] = wEarlyAcc
        c.peqCum[step] = peqAcc
        c.segStartStep[step] = segStart
        c.cumOff[step] = cum
        let nxt = c.links[cur]
        if nxt < 0 or nxt >= n or c.tourPos[nxt] >= 0:
            break
        if c.outConstrained[cur]:
            cum += c.distanceMatrix[nxt][cur]
        else:
            segStart = step + 1
            cum = T(0)
        inc step
        cur = nxt
    c.tourLen = step + 1


proc moveDeltaIncLegacy[T](c: CircuitTimePropConstraint[T],
                           nodeIdx, newLink: int): int =
    ## Incremental legacy (inequality) walk: prefix through the changed node is
    ## unchanged; re-walk only the suffix along committed links.
    let n = c.n
    let p = c.tourPos[nodeIdx]
    if p < 0:
        return 0   # node unreachable from depot: the walk is unchanged
    inc c.curStamp
    let stamp = c.curStamp
    var visited = p + 1
    var twPen = c.preTw[p]
    var maxT = c.preMax[p]
    var wSum = c.preWSum[p]
    var wEarly = c.preWEarly[p]
    var current = nodeIdx
    var dep = c.departureTime[nodeIdx]
    var nextL = newLink
    while true:
        if nextL < 0 or nextL >= n: break
        if (c.tourPos[nextL] >= 0 and c.tourPos[nextL] <= p) or
           c.visitStamp[nextL] == stamp:
            break
        var arr: T
        if c.outConstrained[current]:
            arr = dep + c.distanceMatrix[nextL][current]
        else:
            arr = c.earlyTimes[nextL]
        let d = max(arr, c.earlyTimes[nextL])
        if d > c.lateTimes[nextL]:
            twPen += int(d - c.lateTimes[nextL])
        if d > maxT: maxT = d
        if c.useSumMetric:
            let w = c.sumMetricWeights[nextL]
            if w != T(0):
                wSum += w * d
                wEarly += w * c.earlyTimes[nextL]
        c.visitStamp[nextL] = stamp
        inc visited
        current = nextL
        dep = d
        nextL = c.links[current]
        if visited >= n: break
    var circPen = n - visited
    if visited == n:
        let lastSucc = if current == nodeIdx: newLink else: c.links[current]
        if lastSucc != c.depotIndex:
            circPen = 1
        elif c.outConstrained[current]:
            let arrD = dep + c.distanceMatrix[c.depotIndex][current]
            if arrD > c.lateTimes[c.depotIndex]:
                twPen += int(arrD - c.lateTimes[c.depotIndex])
            if arrD > maxT: maxT = arrD
    let metric = if c.useSumMetric: wSum + (c.totalWEarly - wEarly)
                 else: maxT
    let newCost = circPen * c.circuitWeight + twPen + c.objPenaltyFor(metric)
    return newCost - c.cost


proc moveDeltaIncEquality[T](c: CircuitTimePropConstraint[T],
                             nodeIdx, newLink: int): int =
    ## Incremental equality (accumulator) walk: penalty of segments closed
    ## before the changed node's segment is cached; re-walk that open segment
    ## plus the suffix, evaluating window penalties without write-backs.
    let n = c.n
    let p = c.tourPos[nodeIdx]
    if p < 0:
        return 0
    inc c.curStamp
    let stamp = c.curStamp
    let segStart = c.segStartStep[p]
    var twPen = if segStart > 0: c.peqCum[segStart - 1] else: 0

    template segFixed(v: int): bool =
        c.earlyTimes[v] == c.lateTimes[v]

    c.scratchSegNodes.setLen(0)
    c.scratchSegCum.setLen(0)
    for s in segStart..p:
        c.scratchSegNodes.add(c.tourSeq[s])
        c.scratchSegCum.add(c.cumOff[s])

    template flushSeg(ghostLast: bool) =
        if c.scratchSegNodes.len > 0:
            let firstV = c.scratchSegNodes[0]
            let lastV = c.scratchSegNodes[^1]
            var anchored = true
            var base: T
            if segFixed(firstV):
                base = c.earlyTimes[firstV] - c.scratchSegCum[0]
            elif segFixed(lastV):
                base = c.earlyTimes[lastV] - c.scratchSegCum[^1]
            else:
                anchored = false
            if anchored:
                for j in 0..<c.scratchSegNodes.len:
                    let v = c.scratchSegNodes[j]
                    let val = base + c.scratchSegCum[j]
                    if val < c.earlyTimes[v]:
                        twPen += int(c.earlyTimes[v] - val)
                    elif val > c.lateTimes[v]:
                        twPen += int(val - c.lateTimes[v])
            c.scratchSegNodes.setLen(0)
            c.scratchSegCum.setLen(0)

    var visited = p + 1
    var cum = c.cumOff[p]
    var current = nodeIdx
    var nextL = newLink
    while true:
        if nextL < 0 or nextL >= n: break
        if (c.tourPos[nextL] >= 0 and c.tourPos[nextL] <= p) or
           c.visitStamp[nextL] == stamp:
            break
        if c.outConstrained[current]:
            cum += c.distanceMatrix[nextL][current]
        else:
            flushSeg(false)
            cum = T(0)
        c.scratchSegNodes.add(nextL)
        c.scratchSegCum.add(cum)
        c.visitStamp[nextL] = stamp
        inc visited
        current = nextL
        nextL = c.links[current]
        if visited >= n: break
    var circPen = n - visited
    if visited == n:
        let lastSucc = if current == nodeIdx: newLink else: c.links[current]
        if lastSucc != c.depotIndex:
            circPen = 1
        elif c.outConstrained[current]:
            cum += c.distanceMatrix[c.depotIndex][current]
            c.scratchSegNodes.add(c.depotIndex)
            c.scratchSegCum.add(cum)
            flushSeg(true)
    flushSeg(false)
    let newCost = circPen * c.circuitWeight + twPen
    return newCost - c.cost


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
    c.rebuildIncCache()


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
    if c.incValid:
        let newLink = int(newValue) - c.valueOffset
        if c.equalityChain:
            return c.moveDeltaIncEquality(nodeIdx, newLink)
        return c.moveDeltaIncLegacy(nodeIdx, newLink)
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
    c.rebuildIncCache()


proc deepCopy*[T](c: CircuitTimePropConstraint[T]): CircuitTimePropConstraint[T] =
    new(result)
    result.n = c.n
    result.valueOffset = c.valueOffset
    result.forward = c.forward
    result.equalityChain = c.equalityChain
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
    result.useSumMetric = c.useSumMetric
    result.sumMetricWeights = c.sumMetricWeights
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
    result.scratchSegNodes = newSeqOfCap[int](c.n)
    result.scratchSegCum = newSeqOfCap[T](c.n)

    # Incremental caches: copy committed-walk state, fresh stamps
    result.incValid = c.incValid
    result.tourPos = c.tourPos
    result.tourSeq = c.tourSeq
    result.tourLen = c.tourLen
    result.preTw = c.preTw
    result.preMax = c.preMax
    result.preWSum = c.preWSum
    result.preWEarly = c.preWEarly
    result.totalWEarly = c.totalWEarly
    result.peqCum = c.peqCum
    result.segStartStep = c.segStartStep
    result.cumOff = c.cumOff
    result.visitStamp = newSeq[int](c.n)
    result.curStamp = 0
