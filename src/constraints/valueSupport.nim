## ValueSupportConstraint: native constraint for the "neighbours" pattern.
##
## For a cell with value N > 1, all values 1..N-1 must appear among the cell's
## grid neighbours. Penalty = count of predecessor values missing from neighbours.

import std/[packedsets, sequtils, tables]

type
    ValueSupportConstraint*[T] = ref object
        cellPos*: int
        neighbourPositions*: seq[int]
        maxVal*: T
        cost*: int
        cellValue*: T                        # cached current cell value
        neighbourValues*: seq[T]             # cached values (parallel to neighbourPositions)
        valueCounts*: seq[int]               # valueCounts[v] = #neighbours with value v (index 0..maxVal)
        allPositions*: PackedSet[int]

func newValueSupportConstraint*[T](cellPos: int, neighbourPositions: seq[int],
                                    maxVal: T): ValueSupportConstraint[T] =
    new(result)
    result.cellPos = cellPos
    result.neighbourPositions = neighbourPositions
    result.maxVal = maxVal
    result.cost = 0
    result.cellValue = T(0)
    result.neighbourValues = newSeq[T](neighbourPositions.len)
    result.valueCounts = newSeq[int](int(maxVal) + 1)
    result.allPositions = initPackedSet[int]()
    result.allPositions.incl(cellPos)
    for p in neighbourPositions:
        result.allPositions.incl(p)

func computeCost*[T](state: ValueSupportConstraint[T]): int {.inline.} =
    ## Count values in 1..cellValue-1 that are missing from neighbours.
    result = 0
    let cv = int(state.cellValue)
    for v in 1..<cv:
        if state.valueCounts[v] == 0:
            inc result

func initialize*[T](state: ValueSupportConstraint[T], assignment: seq[T]) =
    state.cellValue = assignment[state.cellPos]
    for i in 0..<state.neighbourPositions.len:
        let v = assignment[state.neighbourPositions[i]]
        state.neighbourValues[i] = v
    # Reset and rebuild valueCounts
    for i in 0..int(state.maxVal):
        state.valueCounts[i] = 0
    for v in state.neighbourValues:
        let iv = int(v)
        if iv >= 0 and iv <= int(state.maxVal):
            state.valueCounts[iv] += 1
    state.cost = state.computeCost()

func moveDelta*[T](state: ValueSupportConstraint[T],
                    position: int, oldValue, newValue: T): int {.inline.} =
    if oldValue == newValue: return 0

    if position == state.cellPos:
        # Cell value is changing — recount missing predecessors for newValue
        var newCost = 0
        let nv = int(newValue)
        for v in 1..<nv:
            if state.valueCounts[v] == 0:
                inc newCost
        return newCost - state.cost
    else:
        # A neighbour is changing value
        let cv = int(state.cellValue)
        if cv <= 1: return 0  # No predecessors needed

        var delta = 0
        let ov = int(oldValue)
        let nv = int(newValue)

        # Losing oldValue from neighbours
        if ov >= 1 and ov < cv:
            if state.valueCounts[ov] == 1:
                delta += 1  # Was sole provider, now missing

        # Gaining newValue in neighbours
        if nv >= 1 and nv < cv:
            if state.valueCounts[nv] == 0:
                delta -= 1  # Fills a gap

        return delta

func updatePosition*[T](state: ValueSupportConstraint[T],
                          position: int, newValue: T) {.inline.} =
    if position == state.cellPos:
        state.cellValue = newValue
        state.cost = state.computeCost()
    else:
        # Find neighbour index and update
        for i in 0..<state.neighbourPositions.len:
            if state.neighbourPositions[i] == position:
                let oldVal = state.neighbourValues[i]
                if oldVal == newValue: return
                state.neighbourValues[i] = newValue
                # Update valueCounts
                let ov = int(oldVal)
                if ov >= 0 and ov <= int(state.maxVal):
                    state.valueCounts[ov] -= 1
                let nv = int(newValue)
                if nv >= 0 and nv <= int(state.maxVal):
                    state.valueCounts[nv] += 1
                state.cost = state.computeCost()
                return

proc batchMovePenalty*[T](state: ValueSupportConstraint[T],
                          position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    ## Batch-compute penalty deltas for all domain values at a position.
    result = newSeq[int](domain.len)
    let currentCost = state.cost

    if position == state.cellPos:
        # For each candidate cell value, count missing predecessors
        for i in 0..<domain.len:
            let v = int(domain[i])
            var newCost = 0
            for k in 1..<v:
                if state.valueCounts[k] == 0:
                    inc newCost
            result[i] = newCost - currentCost
    else:
        # Neighbour position: compute delta for changing from currentValue to each domain value
        let cv = int(state.cellValue)
        if cv <= 1:
            return  # All zeros

        let curV = int(currentValue)
        # Pre-compute: does removing currentValue create a gap?
        let losingCurrent = curV >= 1 and curV < cv and state.valueCounts[curV] == 1

        for i in 0..<domain.len:
            let nv = int(domain[i])
            if nv == curV:
                result[i] = 0
                continue
            var delta = 0
            # Losing currentValue
            if losingCurrent:
                if nv != curV:  # already checked above but explicit
                    delta += 1
            # Gaining newValue
            if nv >= 1 and nv < cv:
                if state.valueCounts[nv] == 0:
                    delta -= 1
                elif nv == curV and state.valueCounts[nv] == 1:
                    # We'd be removing curV and adding nv==curV — net zero for this value
                    discard
            result[i] = delta

proc deepCopy*[T](state: ValueSupportConstraint[T]): ValueSupportConstraint[T] =
    result = newValueSupportConstraint[T](
        state.cellPos, state.neighbourPositions, state.maxVal)
    result.cost = state.cost
    result.cellValue = state.cellValue
    result.neighbourValues = state.neighbourValues
    result.valueCounts = state.valueCounts
