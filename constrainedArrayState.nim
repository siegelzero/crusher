import std/[packedsets, random, sequtils, tables]
import constraints/constraint
import constrainedArray

################################################################################
# Type definitions
################################################################################

type
    ArrayState*[T] = object
        carray*: ConstrainedArray[T]
        constraintsAtPosition*: seq[seq[Constraint[T]]]

        neighbors*: seq[seq[int]]

        penaltyMap*: seq[Table[T, int]]

        currentAssignment*: seq[T]
        cost*: int

        bestAssignment*: seq[T]
        bestCost*: int

        iteration*: int
        tabu*: seq[Table[T, int]]

        maxTenure*, minTenure*, tenure*: int

################################################################################
# ConstrainedArray Methods
################################################################################

func updatePenaltyMap*[T](state: var ArrayState[T], position: int) =
    var
        oldValue: T
        penalty: int

    for nbr in state.neighbors[position]:
        oldValue = state.currentAssignment[nbr]
        for newValue in state.carray.domain[nbr]:
            penalty = 0
            state.currentAssignment[nbr] = newValue
            for cons in state.constraintsAtPosition[nbr]:
                penalty += cons.penalty(state.currentAssignment)
            state.penaltyMap[nbr][newValue] = penalty
        state.currentAssignment[nbr] = oldValue


proc initArrayState*[T](carray: ConstrainedArray[T]): ArrayState[T] =
    result.carray = carray
    result.iteration = 0
    result.minTenure = 5
    result.maxTenure = 100
    result.tenure = result.minTenure

    result.constraintsAtPosition = newSeq[seq[Constraint[T]]](carray.len)
    result.neighbors = newSeq[seq[int]](carray.len)

    # Group constraints involving each position
    for idx, constraint in carray.constraints:
        for pos in constraint.positions:
            result.constraintsAtPosition[pos].add(constraint)
    
    # Build neighbors of each position
    var neighborSet: PackedSet[int] = toPackedSet[int]([])
    for pos in carray.allPositions():
        neighborSet.clear()
        for cons in result.constraintsAtPosition[pos]:
            neighborSet.incl(cons.positions)
        neighborSet.excl(pos)
        result.neighbors[pos] = toSeq(neighborSet)

    # Random assignment
    result.currentAssignment = newSeq[T](carray.len)
    for pos in carray.allPositions():
        result.currentAssignment[pos] = sample(carray.domain[pos])

    for cons in carray.constraints:
        result.cost += cons.penalty(result.currentAssignment)

    result.bestCost = result.cost
    result.bestAssignment = result.currentAssignment

    result.penaltyMap = newSeq[Table[T, int]](result.carray.len)
    var penalty: int
    var oldValue: T

    # Construct penalty map for each location and value
    for pos in result.carray.allPositions():
        oldValue = result.currentAssignment[pos]
        for newValue in result.carray.domain[pos]:
            penalty = 0
            result.currentAssignment[pos] = newValue
            for cons in result.constraintsAtPosition[pos]:
                penalty += cons.penalty(result.currentAssignment)
            result.penaltyMap[pos][newValue] = penalty
        result.currentAssignment[pos] = oldValue
    
    result.tabu = newSeq[Table[T, int]](carray.len)

    for i in 0..<carray.len:
        result.tabu[i] = initTable[T, int]()
        for d in carray.domain[i]:
            result.tabu[i][d] = 0