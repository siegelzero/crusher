## PseudoBoolLinLe Constraint Implementation
## ==========================================
##
## Specialized constraint for linear inequalities over binary variables:
##   sum(coefficients[i] * x[positions[i]]) <= rhs
## where each x[i] ∈ {0, 1}.
##
## Maintains the weighted sum incrementally. O(1) moveDelta and updatePosition.
## Graduated penalty: cost = max(0, currentSum - rhs).
##
## The getAffectedPositions optimization uses a boundary check: if the sum
## didn't cross the rhs threshold by more than maxAbsCoeff, neighbors'
## moveDelta values may have changed and need recalculation.

import std/[packedsets, tables]

################################################################################
# Type definitions
################################################################################

type
    PseudoBoolLinLeConstraint*[T] = ref object
        positions*: PackedSet[int]
        coeffAtPosition*: Table[int, T]   # position -> coefficient
        rhs*: T
        currentSum*: T
        cost*: int
        lastOldSum*: T        # sum before last updatePosition
        lastNewSum*: T        # sum after last updatePosition
        maxAbsCoeff*: T       # max |coefficient| — max sum change from a single binary flip

################################################################################
# Constructor
################################################################################

proc newPseudoBoolLinLeConstraint*[T](posSeq: openArray[int], coefficients: openArray[T], rhs: T): PseudoBoolLinLeConstraint[T] =
    new(result)
    result.positions = toPackedSet[int](posSeq)
    result.coeffAtPosition = initTable[int, T]()
    result.rhs = rhs
    result.currentSum = 0
    result.cost = 0
    result.lastOldSum = 0
    result.lastNewSum = 0
    result.maxAbsCoeff = 0
    for i in 0..<posSeq.len:
        let c = coefficients[i]
        if posSeq[i] in result.coeffAtPosition:
            # Multiple terms at the same position: sum the coefficients
            result.coeffAtPosition[posSeq[i]] += c
        else:
            result.coeffAtPosition[posSeq[i]] = c
        let absC = abs(c)
        if absC > result.maxAbsCoeff:
            result.maxAbsCoeff = absC

################################################################################
# Initialization and updates
################################################################################

proc initialize*[T](state: PseudoBoolLinLeConstraint[T], assignment: seq[T]) =
    state.currentSum = 0
    for pos, coeff in state.coeffAtPosition.pairs:
        state.currentSum += coeff * assignment[pos]
    state.cost = max(0, state.currentSum - state.rhs)

proc updatePosition*[T](state: PseudoBoolLinLeConstraint[T], position: int, newValue: T) {.inline.} =
    state.lastOldSum = state.currentSum
    if position notin state.coeffAtPosition:
        state.lastNewSum = state.currentSum
        return
    let coeff = state.coeffAtPosition[position]
    # For binary variables: newValue - oldValue is either +1 or -1
    # oldValue = 1 - newValue (binary flip)
    # delta = coeff * (newValue - oldValue) = coeff * (2*newValue - 1)
    let delta = coeff * (2 * newValue - 1)
    state.currentSum += delta
    state.cost = max(0, state.currentSum - state.rhs)
    state.lastNewSum = state.currentSum

proc moveDelta*[T](state: PseudoBoolLinLeConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    if oldValue == newValue:
        return 0
    if position notin state.coeffAtPosition:
        return 0
    let coeff = state.coeffAtPosition[position]
    let delta = coeff * (newValue - oldValue)
    let newSum = state.currentSum + delta
    let newCost = max(0, newSum - state.rhs)
    return newCost - state.cost

proc batchMovePenalty*[T](state: PseudoBoolLinLeConstraint[T], position: int,
                          oldValue: T, domain: seq[T]): seq[int] =
    ## Batch-compute moveDelta for all domain values.
    result = newSeq[int](domain.len)
    if position notin state.coeffAtPosition:
        return  # all zeros
    let coeff = state.coeffAtPosition[position]
    let baseCost = state.cost
    for i in 0..<domain.len:
        if domain[i] == oldValue:
            result[i] = 0
        else:
            let delta = coeff * (domain[i] - oldValue)
            let newSum = state.currentSum + delta
            let newCost = max(0, newSum - state.rhs)
            result[i] = newCost - baseCost

################################################################################
# Affected positions and domain values
################################################################################

proc getAffectedPositions*[T](state: PseudoBoolLinLeConstraint[T]): PackedSet[int] =
    ## Returns positions needing penalty recalculation after the last updatePosition.
    ##
    ## For sum(c_i * x_i) <= rhs, the moveDelta at neighbor position j is:
    ##   max(0, currentSum + c_j*(v-x_j) - rhs) - max(0, currentSum - rhs)
    ## This only changes when currentSum moves relative to rhs such that the
    ## max(0, ...) boundary is crossed for some coefficient value.
    ##
    ## Slack-based optimization (analogous to RelationalConstraint.maxNetDelta):
    ## If the constraint is satisfied and both old and new slack >= maxAbsCoeff,
    ## then no single-variable flip at any neighbor can create a violation from
    ## either the old or new state. All moveDelta values remain 0, so no
    ## penalty map updates are needed.
    let oldSum = state.lastOldSum
    let newSum = state.lastNewSum
    if oldSum == newSum:
        return initPackedSet[int]()
    let threshold = state.maxAbsCoeff
    let oldSlack = state.rhs - oldSum
    let newSlack = state.rhs - newSum
    if oldSlack >= threshold and newSlack >= threshold:
        # Both old and new states have enough slack — no neighbor's delta changed
        return initPackedSet[int]()
    return state.positions

proc getAffectedDomainValues*[T](state: PseudoBoolLinLeConstraint[T], position: int): seq[T] =
    ## Returns empty (meaning all values need recalculation).
    ## For binary domains this is just 2 values, so no benefit from narrowing.
    return @[]

################################################################################
# Deep copy
################################################################################

proc deepCopy*[T](state: PseudoBoolLinLeConstraint[T]): PseudoBoolLinLeConstraint[T] =
    new(result)
    result.positions = state.positions  # PackedSet is value type
    result.coeffAtPosition = initTable[int, T]()
    for k, v in state.coeffAtPosition.pairs:
        result.coeffAtPosition[k] = v
    result.rhs = state.rhs
    result.currentSum = 0
    result.cost = 0
    result.lastOldSum = 0
    result.lastNewSum = 0
    result.maxAbsCoeff = state.maxAbsCoeff
