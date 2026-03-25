## ConditionalLinear constraint: a linear inequality that is only enforced
## when a guard variable takes a specific value.
##
## Semantics: if guard == guardActiveValue then sum(coeffs[i] * x[positions[i]]) <= rhs
##            else: no constraint (penalty = 0)
##
## Penalty = if guard == guardActiveValue: max(0, currentSum - rhs) else: 0
##
## This provides magnitude-aware penalties (gradient information) for conditional
## constraints, unlike binary bool_clause which only gives 0/1 penalty.

import std/[packedsets, tables]

type
    ConditionalLinearConstraint*[T] = ref object
        coeffs*: seq[T]           # coefficients for linear terms
        linPositions*: seq[int]   # positions of linear term variables
        rhs*: T                   # right-hand side bound
        guardPosition*: int       # position of the guard variable
        guardActiveValue*: T      # value of guard that activates the constraint
        currentSum*: T            # cached sum(coeffs[i] * assignment[linPositions[i]])
        currentGuard*: T          # cached assignment[guardPosition]
        cost*: int
        # Map from position -> coefficient for O(1) lookup in moveDelta/updatePosition
        posCoeff*: Table[int, T]
        # Current values at each position (for incremental updatePosition)
        currentValues*: Table[int, T]

func computeCost[T](s: ConditionalLinearConstraint[T]): int {.inline.} =
    if s.currentGuard == s.guardActiveValue:
        let violation = int(s.currentSum) - int(s.rhs)
        if violation > 0: violation else: 0
    else:
        0

func newConditionalLinearConstraint*[T](
    coeffs: seq[T], linPositions: seq[int], rhs: T,
    guardPosition: int, guardActiveValue: T
): ConditionalLinearConstraint[T] =
    new(result)
    result.coeffs = coeffs
    result.linPositions = linPositions
    result.rhs = rhs
    result.guardPosition = guardPosition
    result.guardActiveValue = guardActiveValue
    result.currentSum = T(0)
    result.currentGuard = T(0)
    result.cost = 0
    result.posCoeff = initTable[int, T]()
    result.currentValues = initTable[int, T]()
    for i in 0..<coeffs.len:
        result.posCoeff[linPositions[i]] = coeffs[i]

func initialize*[T](s: ConditionalLinearConstraint[T], assignment: seq[T]) =
    s.currentSum = T(0)
    for i in 0..<s.coeffs.len:
        let pos = s.linPositions[i]
        s.currentSum += s.coeffs[i] * assignment[pos]
        s.currentValues[pos] = assignment[pos]
    s.currentGuard = assignment[s.guardPosition]
    s.currentValues[s.guardPosition] = s.currentGuard
    s.cost = s.computeCost()

func moveDelta*[T](s: ConditionalLinearConstraint[T],
                    position: int, oldValue, newValue: T): int {.inline.} =
    if oldValue == newValue: return 0

    var newSum = s.currentSum
    var newGuard = s.currentGuard

    if position == s.guardPosition:
        newGuard = newValue
    elif position in s.posCoeff:
        newSum += s.posCoeff[position] * (newValue - oldValue)

    # Compute new cost
    let newCost = if newGuard == s.guardActiveValue:
        let violation = int(newSum) - int(s.rhs)
        if violation > 0: violation else: 0
    else:
        0

    return newCost - s.cost

func updatePosition*[T](s: ConditionalLinearConstraint[T],
                          position: int, newValue: T) {.inline.} =
    if position == s.guardPosition:
        s.currentGuard = newValue
        s.currentValues[position] = newValue
    elif position in s.posCoeff:
        let oldValue = s.currentValues.getOrDefault(position, T(0))
        s.currentSum += s.posCoeff[position] * (newValue - oldValue)
        s.currentValues[position] = newValue
    s.cost = s.computeCost()

func getAffectedPositions*[T](s: ConditionalLinearConstraint[T]): PackedSet[int] =
    # All positions may need penalty recalculation when guard or any linear var changes
    result = initPackedSet[int]()
    for pos in s.linPositions:
        result.incl(pos)
    result.incl(s.guardPosition)

func getAffectedDomainValues*[T](s: ConditionalLinearConstraint[T], position: int): seq[T] =
    return @[]  # all values may be affected

proc batchMovePenalty*[T](s: ConditionalLinearConstraint[T],
                          position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    result = newSeq[int](domain.len)
    let currentCost = s.cost

    if position == s.guardPosition:
        # Changing the guard: sum stays the same, guard changes
        let violation = int(s.currentSum) - int(s.rhs)
        let activeViolation = if violation > 0: violation else: 0
        for i in 0..<domain.len:
            let newCost = if domain[i] == s.guardActiveValue: activeViolation else: 0
            result[i] = newCost - currentCost
    elif position in s.posCoeff:
        let coeff = s.posCoeff[position]
        let baseSum = int(s.currentSum) - int(coeff) * int(currentValue)
        if s.currentGuard == s.guardActiveValue:
            for i in 0..<domain.len:
                let newSum = baseSum + int(coeff) * int(domain[i])
                let violation = newSum - int(s.rhs)
                let newCost = if violation > 0: violation else: 0
                result[i] = newCost - currentCost
        # else: guard inactive, all deltas are 0 (already initialized)

proc deepCopy*[T](s: ConditionalLinearConstraint[T]): ConditionalLinearConstraint[T] =
    new(result)
    result.coeffs = s.coeffs           # immutable, share
    result.linPositions = s.linPositions # immutable, share
    result.rhs = s.rhs
    result.guardPosition = s.guardPosition
    result.guardActiveValue = s.guardActiveValue
    result.posCoeff = s.posCoeff       # immutable, share
    result.currentSum = T(0)
    result.currentGuard = T(0)
    result.cost = 0
    result.currentValues = initTable[int, T]()
