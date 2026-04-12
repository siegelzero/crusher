## Linear equality repair via iterative relaxation (Gauss-Seidel style).
## Included from tabu.nim — not a standalone module.
##
## Provides two entry points:
## 1. repairLinearEqualities: for initialization, fixes flow conservation violations
## 2. tryLinearRepairMove: for use during search stagnation, coordinates multi-variable
##    adjustments on violated EqualTo constraints

proc repairLinearEqualities*[T](state: TabuState[T], verbose: bool, id: int) =
    ## Initialization repair: iteratively fix violated EqualTo constraints.
    ## Skips if constraints are already satisfied.
    let carray = state.carray

    type
        EqTerm = tuple[pos: int, coeff: T]
        EqInfo = object
            searchTerms: seq[EqTerm]
            allTerms: seq[EqTerm]
            constant: T
            rhs: T

    var eqInfos: seq[EqInfo]

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo:
            continue
        if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue

        var info = EqInfo(
            constant: rc.leftExpr.sumExpr.constant,
            rhs: rc.rightExpr.constantValue
        )
        var hasSearch = false
        for pos, coeff in rc.leftExpr.sumExpr.coefficient.pairs:
            info.allTerms.add((pos: pos, coeff: coeff))
            if pos notin carray.channelPositions and pos notin carray.fixedPositions:
                info.searchTerms.add((pos: pos, coeff: coeff))
                hasSearch = true

        if hasSearch:
            eqInfos.add(info)

    if eqInfos.len == 0:
        return

    # Check initial total residual; skip if already near-feasible
    var initialResidual: T = 0
    for info in eqInfos:
        var r = info.constant - info.rhs
        for term in info.allTerms:
            r += term.coeff * state.assignment[term.pos]
        initialResidual += abs(r)

    if initialResidual == T(0):
        return

    # Gauss-Seidel passes
    const MaxPasses = 50
    var nAdjustments = 0
    var prevResidual = initialResidual

    for pass in 0..<MaxPasses:
        var passImproved = false

        for i in 0..<eqInfos.len:
            let info = eqInfos[i]

            var residual = info.constant - info.rhs
            for term in info.allTerms:
                residual += term.coeff * state.assignment[term.pos]

            if residual == T(0):
                continue

            var bestPos = -1
            var bestNewVal: T = 0
            var bestReduction: T = 0

            for term in info.searchTerms:
                let pos = term.pos
                let coeff = term.coeff
                if coeff == T(0): continue

                let dom = state.sharedDomain[][pos]
                if dom.len == 0: continue

                let oldVal = state.assignment[pos]
                let idealDelta = -(residual div coeff)
                let idealNewVal = oldVal + idealDelta
                let clampedVal = max(dom[0], min(dom[^1], idealNewVal))
                let actualDelta = clampedVal - oldVal
                if actualDelta == T(0): continue

                let reduction = abs(coeff * actualDelta)
                if reduction > bestReduction:
                    bestReduction = reduction
                    bestPos = pos
                    bestNewVal = clampedVal

            if bestPos >= 0:
                state.assignment[bestPos] = bestNewVal
                inc nAdjustments
                passImproved = true

        if not passImproved:
            break

        if pass mod 10 == 9:
            var totalResidual: T = 0
            for info in eqInfos:
                var r = info.constant - info.rhs
                for term in info.allTerms:
                    r += term.coeff * state.assignment[term.pos]
                totalResidual += abs(r)
            if totalResidual >= prevResidual:
                break
            prevResidual = totalResidual

    if nAdjustments > 0 and verbose and id == 0:
        var totalResidual: T = 0
        for info in eqInfos:
            var r = info.constant - info.rhs
            for term in info.allTerms:
                r += term.coeff * state.assignment[term.pos]
            totalResidual += abs(r)
        echo "[Init] Linear equality repair: " & $eqInfos.len & " equations, " &
             $nAdjustments & " adjustments, residual " & $initialResidual &
             " -> " & $totalResidual


proc tryLinearRepairMoves*[T](state: TabuState[T]): bool =
    ## During search: find violated EqualTo constraints and make coordinated
    ## single-position adjustments via assignValue to reduce violations.
    ## Returns true if any improvement was made.
    let carray = state.carray
    var improved = false

    for constraint in state.constraints:
        if constraint.stateType != RelationalType:
            continue
        let rc = constraint.relationalState
        if rc.relation != EqualTo or not rc.graduated:
            continue
        if rc.computeCost(rc.leftValue, rc.rightValue) == 0:
            continue  # Already satisfied
        if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased:
            continue
        if rc.rightExpr.kind != ConstantExpr:
            continue

        let residual = rc.leftValue - rc.rightValue
        if residual == 0:
            continue

        # Find the best search position to adjust
        var bestPos = -1
        var bestNewVal: T = 0
        var bestCostDelta = 0  # Must be negative to improve

        for pos, coeff in rc.leftExpr.sumExpr.coefficient.pairs:
            if coeff == T(0): continue
            if pos in carray.channelPositions or pos in carray.fixedPositions:
                continue

            let dom = state.sharedDomain[][pos]
            if dom.len == 0: continue

            let oldVal = state.assignment[pos]
            let idealDelta = -(T(residual) div coeff)
            let idealNewVal = oldVal + idealDelta
            let clampedVal = max(dom[0], min(dom[^1], idealNewVal))
            if clampedVal == oldVal: continue

            # Evaluate full cost delta for this move
            let delta = state.costDelta(pos, clampedVal)
            if delta < bestCostDelta:
                bestCostDelta = delta
                bestPos = pos
                bestNewVal = clampedVal

        if bestPos >= 0 and bestCostDelta < 0:
            state.assignValue(bestPos, bestNewVal)
            state.updateNeighborPenalties(bestPos)
            improved = true

    return improved
