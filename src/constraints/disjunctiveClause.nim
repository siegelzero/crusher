## DisjunctiveClauseConstraint: efficient evaluation for disjunctions of linear inequality conjunctions.
##
## Each disjunct is a conjunction of linear inequality terms (coeffs·vars <= rhs).
## The constraint is satisfied when at least one disjunct has all its terms satisfied.
## Penalty = min over disjuncts of (sum over terms of max(0, coeffs·vars - rhs)).

import std/[packedsets, tables]

type
    DCTermState*[T] = object
        ## A single linear inequality term: sum(coeffs[i] * values[positions[i]]) <= rhs
        coeffs*: seq[T]
        positions*: seq[int]
        rhs*: T
        currentSum*: T  # cached sum(coeffs[i] * assignment[positions[i]])

    DisjunctiveClauseConstraint*[T] = ref object
        ## Disjunction of conjunctions of linear inequality terms.
        ## disjuncts[d][t] is term t of disjunct d.
        disjuncts*: seq[seq[DCTermState[T]]]
        cost*: int
        # Maps position -> list of (disjunctIdx, termIdx, coefficient) for incremental update
        positionEntries*: Table[int, seq[tuple[di, ti: int, coeff: T]]]
        # Current assignment values for positions in this constraint (for updatePosition old value)
        currentAssignment*: Table[int, T]

func computePenalty*[T](state: DisjunctiveClauseConstraint[T]): int {.inline.} =
    result = high(int)
    for d in 0..<state.disjuncts.len:
        var conjPenalty = 0
        for t in 0..<state.disjuncts[d].len:
            let violation = state.disjuncts[d][t].currentSum - state.disjuncts[d][t].rhs
            if violation > 0:
                conjPenalty += violation
        if conjPenalty < result:
            result = conjPenalty
            if result == 0:
                return 0

func newDisjunctiveClauseConstraint*[T](
    disjuncts: seq[seq[tuple[coeffs: seq[T], positions: seq[int], rhs: T]]]
): DisjunctiveClauseConstraint[T] =
    new(result)
    result.disjuncts = newSeq[seq[DCTermState[T]]](disjuncts.len)
    for d in 0..<disjuncts.len:
        result.disjuncts[d] = newSeq[DCTermState[T]](disjuncts[d].len)
        for t in 0..<disjuncts[d].len:
            let term = disjuncts[d][t]
            result.disjuncts[d][t] = DCTermState[T](
                coeffs: term.coeffs,
                positions: term.positions,
                rhs: term.rhs,
                currentSum: T(0))
            for ci in 0..<term.positions.len:
                let pos = term.positions[ci]
                result.positionEntries.mgetOrPut(pos, @[]).add(
                    (di: d, ti: t, coeff: term.coeffs[ci]))

func initialize*[T](state: DisjunctiveClauseConstraint[T], assignment: seq[T]) =
    for d in 0..<state.disjuncts.len:
        for t in 0..<state.disjuncts[d].len:
            var s: T = 0
            for i in 0..<state.disjuncts[d][t].coeffs.len:
                let pos = state.disjuncts[d][t].positions[i]
                s += state.disjuncts[d][t].coeffs[i] * assignment[pos]
                state.currentAssignment[pos] = assignment[pos]
            state.disjuncts[d][t].currentSum = s
    state.cost = state.computePenalty()

func moveDelta*[T](state: DisjunctiveClauseConstraint[T],
                    position: int, oldValue, newValue: T): int {.inline.} =
    let valueDelta = newValue - oldValue
    if valueDelta == 0: return 0

    if position notin state.positionEntries:
        return 0

    let entries = state.positionEntries[position]

    # Compute new penalty with affected terms updated
    var newPenalty = high(int)
    for d in 0..<state.disjuncts.len:
        var conjPenalty = 0
        for t in 0..<state.disjuncts[d].len:
            let violation = state.disjuncts[d][t].currentSum - state.disjuncts[d][t].rhs
            if violation > 0:
                conjPenalty += violation
        # Adjust for affected terms in this disjunct
        for entry in entries:
            if entry.di == d:
                let oldS = state.disjuncts[d][entry.ti].currentSum
                let newS = oldS + entry.coeff * valueDelta
                let oldViolation = max(T(0), oldS - state.disjuncts[d][entry.ti].rhs)
                let newViolation = max(T(0), newS - state.disjuncts[d][entry.ti].rhs)
                conjPenalty += int(newViolation - oldViolation)
        if conjPenalty < newPenalty:
            newPenalty = conjPenalty
            if newPenalty == 0:
                return -state.cost

    return newPenalty - state.cost

func updatePosition*[T](state: DisjunctiveClauseConstraint[T],
                         position: int, newValue: T) {.inline.} =
    let oldValue = state.currentAssignment.getOrDefault(position, T(0))
    let valueDelta = newValue - oldValue
    if valueDelta == 0: return
    state.currentAssignment[position] = newValue
    if position in state.positionEntries:
        for entry in state.positionEntries[position]:
            state.disjuncts[entry.di][entry.ti].currentSum += entry.coeff * valueDelta
    state.cost = state.computePenalty()

proc batchMovePenalty*[T](state: DisjunctiveClauseConstraint[T],
                          position: int, currentValue: T,
                          domain: seq[T]): seq[int] =
    ## Batch-compute penalty deltas for all domain values at a position.
    result = newSeq[int](domain.len)
    let currentCost = state.cost

    if position notin state.positionEntries:
        return

    let entries = state.positionEntries[position]

    # Pre-compute base and coefficient for each term (with position contribution removed)
    type TermInfo = tuple[base, coeff, rhs: int]
    var termInfos = newSeq[seq[TermInfo]](state.disjuncts.len)
    for d in 0..<state.disjuncts.len:
        termInfos[d] = newSeq[TermInfo](state.disjuncts[d].len)
        for t in 0..<state.disjuncts[d].len:
            termInfos[d][t] = (
                base: int(state.disjuncts[d][t].currentSum),
                coeff: 0,
                rhs: int(state.disjuncts[d][t].rhs))

    for entry in entries:
        let c = int(entry.coeff)
        termInfos[entry.di][entry.ti].base -= c * int(currentValue)
        termInfos[entry.di][entry.ti].coeff += c

    # Tight batch loop
    for i in 0..<domain.len:
        let v = int(domain[i])
        var minPenalty = high(int)
        for d in 0..<termInfos.len:
            var conjPenalty = 0
            for t in 0..<termInfos[d].len:
                let s = termInfos[d][t].base + termInfos[d][t].coeff * v
                let violation = s - termInfos[d][t].rhs
                if violation > 0:
                    conjPenalty += violation
            if conjPenalty < minPenalty:
                minPenalty = conjPenalty
                if minPenalty == 0:
                    break
        result[i] = minPenalty - currentCost

proc deepCopy*[T](state: DisjunctiveClauseConstraint[T]): DisjunctiveClauseConstraint[T] =
    new(result)
    result.disjuncts = newSeq[seq[DCTermState[T]]](state.disjuncts.len)
    for d in 0..<state.disjuncts.len:
        result.disjuncts[d] = newSeq[DCTermState[T]](state.disjuncts[d].len)
        for t in 0..<state.disjuncts[d].len:
            result.disjuncts[d][t] = DCTermState[T](
                coeffs: state.disjuncts[d][t].coeffs,
                positions: state.disjuncts[d][t].positions,
                rhs: state.disjuncts[d][t].rhs,
                currentSum: state.disjuncts[d][t].currentSum)
    result.cost = state.cost
    result.positionEntries = state.positionEntries  # shared (immutable after construction)
    result.currentAssignment = initTable[int, T]()
    for k, v in state.currentAssignment.pairs:
        result.currentAssignment[k] = v
