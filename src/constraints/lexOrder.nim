## Lexicographic Order Constraint Implementation
##
## Enforces lexicographic ordering between two sequences of variables.
## lexLt: L < R (strict), lexLe: L <= R (non-strict)
##
## **Penalty**: Graduated penalty based on first differing position

import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    LexOrderType* = enum
        Strict,     # lexLt: L < R
        NonStrict    # lexLe: L <= R

    LexOrderConstraint*[T] = ref object
        leftPositions*: seq[int]
        rightPositions*: seq[int]
        n*: int
        lexType*: LexOrderType
        positions*: PackedSet[int]
        positionToSide*: Table[int, seq[(int, int)]]  # position -> [(side 0=left/1=right, index)]
        currentAssignment*: Table[int, T]
        cost*: int

################################################################################
# Constructor
################################################################################

proc newLexOrderConstraint*[T](leftPositions, rightPositions: openArray[int],
                                lexType: LexOrderType): LexOrderConstraint[T] =
    assert leftPositions.len == rightPositions.len, "left and right must have same length"
    new(result)
    result.n = leftPositions.len
    result.leftPositions = @leftPositions
    result.rightPositions = @rightPositions
    result.lexType = lexType
    result.currentAssignment = initTable[int, T]()
    result.cost = 0

    result.positions = initPackedSet[int]()
    result.positionToSide = initTable[int, seq[(int, int)]]()

    for i in 0..<result.n:
        result.positions.incl(leftPositions[i])
        result.positions.incl(rightPositions[i])

        if leftPositions[i] notin result.positionToSide:
            result.positionToSide[leftPositions[i]] = @[]
        result.positionToSide[leftPositions[i]].add((0, i))

        if rightPositions[i] notin result.positionToSide:
            result.positionToSide[rightPositions[i]] = @[]
        result.positionToSide[rightPositions[i]].add((1, i))

################################################################################
# Penalty computation
################################################################################

proc computePenalty[T](state: LexOrderConstraint[T]): int =
    ## Find first differing position, compute penalty
    for k in 0..<state.n:
        let lv = state.currentAssignment[state.leftPositions[k]]
        let rv = state.currentAssignment[state.rightPositions[k]]
        if lv < rv:
            return 0  # L < R at position k, satisfied
        elif lv > rv:
            return lv - rv  # graduated penalty
    # All equal
    if state.lexType == Strict:
        return 1  # strict requires L < R, all equal violates
    return 0  # non-strict allows L == R

################################################################################
# Initialization and updates
################################################################################

proc initialize*[T](state: LexOrderConstraint[T], assignment: seq[T]) =
    for pos in state.positions.items:
        state.currentAssignment[pos] = assignment[pos]
    state.cost = state.computePenalty()


proc updatePosition*[T](state: LexOrderConstraint[T], position: int, newValue: T) =
    state.currentAssignment[position] = newValue
    state.cost = state.computePenalty()


proc moveDelta*[T](state: LexOrderConstraint[T], position: int, oldValue, newValue: T): int =
    if oldValue == newValue:
        return 0
    # Temporarily change and recompute
    state.currentAssignment[position] = newValue
    let newCost = state.computePenalty()
    state.currentAssignment[position] = oldValue
    return newCost - state.cost
