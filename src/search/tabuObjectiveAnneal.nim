## Objective annealing for optimizer asks that start from the incumbent.
## Included from tabu.nim — not a standalone module.
##
## An ask seeded with the incumbent starts with only the objective bound
## violated. The tabu walk then scores the whole neighbourhood every iteration
## through the objective's channel cascade: gbac UD1 (307 courses, objective =
## sum of squared curriculum-load deviations) ran at ~230 iterations/s and
## stood at 740 after 1200 s, where a plain simulated annealing over single
## moves and swaps reaches ~260 in 30 s (best known 232). Here such states
## anneal instead: random single moves and neighbour exchanges (the
## nbSwapPartners of tabuSwapMoves), each simulated with assignValueLean,
## rejected when it adds a hard violation, else accepted by the Metropolis
## rule on the raw objective. The state stays feasible, so every gain is a
## solution of the original problem and reaching the ask's target ends the
## run like any tabu solution.
##
## The schedule is wall-clock and shared by all states of one optimizer run
## (ConstrainedArray.anneal): a chain that reaches its target hands the next
## ask a state at the current temperature, and that ask's chains continue the
## same cooling from it. Each schedule cools geometrically from T0 to T1 over
## AnnealScheduleSecs: T0 is the median uphill delta of random feasible moves
## at the incumbent where the schedule starts, T1 the smallest one / ln 1000.
## A schedule that ends ends its ask (its siblings share it); the next ask
## starts a new one from the incumbent. Repeated 60 s schedules beat one
## long cooling (300 s runs: UD1 288 vs 319, UD6 66 vs 105) and 30 s ones
## (326 / 63), and the median beat the 10th-percentile delta as T0 (UD6 66
## vs 85).
##
## Once a schedule runs, an ask seeds one state per worker with the
## incumbent: state 0 keeps the plain tabu descent, the others anneal.

const AnnealScheduleSecs = 60.0
const AnnealCalibrationMoves = 4000
const AnnealCalibrationSecs = 2.0
const AnnealMinUphill = 20   # fewer uphill feasible moves in calibration: no annealing

proc annealSeedCount*(a: ptr AnnealShared, workers: int): int =
    ## States of an optimizer ask to seed with the incumbent.
    if a == nil: return 1
    withLock a.lock:
        if a.disabled or not a.calibrated: return 1
    max(1, workers)

proc annealApplicable[T](state: TabuState[T]): bool =
    let a = state.carray.anneal
    if a == nil: return false
    withLock a.lock:
        if a.disabled: return false
        # With several seeded states, state 0 keeps the plain tabu descent
        # from the incumbent (gbac csplib12: optimum in 0.5 s by tabu, 10 s
        # by chains still hot from the first schedule).
        if state.id == 0 and a.seeded > 1: return false
    state.boundConstraint != nil and
        state.boundConstraint.stateType == RelationalType and
        not state.scaledObjectiveBound() and
        state.cost > 0 and state.cost == state.boundConstraint.penalty() and
        state.searchPositions.len >= 2

proc annealPick[T](state: TabuState[T], movable: seq[int],
                   p1: var int, v1: var T, p2: var int, v2: var T): bool =
    ## A random single move or, half the time when partners exist, a random
    ## neighbour exchange (p2 = -1 for a single move).
    if state.nbSwapPartners.len > 0 and rand(1) == 0:
        let i = rand(state.nbSwapPartners.len - 1)
        let parts {.cursor.} = state.nbSwapPartners[i]
        if parts.len == 0: return false
        p1 = state.searchPositions[i]
        p2 = parts[rand(parts.len - 1)]
        v1 = state.assignment[p2]
        v2 = state.assignment[p1]
        if v1 == v2: return false
        if state.domIdx(p1, v1) < 0 or state.domIdx(p2, v2) < 0: return false
        return true
    p1 = movable[rand(movable.len - 1)]
    let dom {.cursor.} = state.sharedDomain[][p1]
    v1 = dom[rand(dom.len - 1)]
    let old = state.assignment[p1]
    if v1 == old: return false
    p2 = -1
    # Prefilter before the cascade: a move that breaks a constraint on its own
    # position is almost never repaired through channels.
    for c in state.constraintsAtPosition[p1]:
        if c != state.boundConstraint and c.moveDelta(p1, old, v1) > 0:
            return false
    true

proc annealTry[T](state: TabuState[T], p1: int, v1: T, p2: int, v2: T,
                  hard: var int, d: var T) =
    ## Apply the move; `hard` = change of the non-bound cost, `d` = change of
    ## the raw objective (bound slack).
    let baseCost = state.cost
    let baseBound = state.boundConstraint.penalty()
    let baseSlack = state.boundSlack()
    state.assignValueLean(p1, v1)
    if p2 >= 0: state.assignValueLean(p2, v2)
    hard = (state.cost - baseCost) - (state.boundConstraint.penalty() - baseBound)
    d = state.boundSlack() - baseSlack

proc annealUndo[T](state: TabuState[T], p1: int, o1: T, p2: int, o2: T) =
    if p2 >= 0: state.assignValueLean(p2, o2)
    state.assignValueLean(p1, o1)

proc annealCalibrate[T](state: TabuState[T], movable: seq[int]): (float, float, int, int) =
    ## (T0, T1, feasible moves, uphill moves) from random moves at this
    ## state; T0 = 0 when too few feasible moves go uphill.
    var deltas: seq[float]
    var tries, feas = 0
    let t0 = epochTime()
    while tries < AnnealCalibrationMoves and epochTime() - t0 < AnnealCalibrationSecs:
        inc tries
        var p1, p2: int
        var v1, v2: T
        if not state.annealPick(movable, p1, v1, p2, v2): continue
        let o1 = state.assignment[p1]
        let o2 = if p2 >= 0: state.assignment[p2] else: T(0)
        var hard: int
        var d: T
        state.annealTry(p1, v1, p2, v2, hard, d)
        state.annealUndo(p1, o1, p2, o2)
        if hard > 0: continue
        inc feas
        if d > 0: deltas.add(float(d))
    if deltas.len < AnnealMinUphill:
        return (0.0, 0.0, feas, deltas.len)
    deltas.sort()
    (deltas[deltas.len div 2], deltas[0] / ln(1000.0), feas, deltas.len)

proc objectiveAnneal[T](state: TabuState[T], deadline: float): bool =
    ## Anneal until the ask's target is reached (state.cost = 0), the shared
    ## schedule ends, a sibling stops the ask or the deadline nears. Leaves
    ## the state at the best objective it saw. True when the run should end
    ## (target reached or schedule over).
    if not state.nbSwapBuilt: state.buildNeighborSwapPartners()
    var movable: seq[int]
    for p in state.searchPositions:
        if p notin state.carray.fixedPositions and state.sharedDomain[][p].len >= 2:
            movable.add(p)
    if movable.len == 0: return false
    let a = state.carray.anneal
    var t0, t1, schedStart, schedLen: float
    withLock a.lock:
        t0 = a.t0; t1 = a.t1; schedStart = a.schedStart; schedLen = a.schedLen
    if schedStart == 0.0:
        # New schedule, calibrated at this (incumbent) state
        let (c0, c1, feas, up) = state.annealCalibrate(movable)
        let now = epochTime()
        var n: int
        var disabled: bool
        withLock a.lock:
            if a.schedStart == 0.0:
                a.calibrated = true
                if c0 <= 0.0:
                    if a.schedules == 0: a.disabled = true
                else:
                    a.t0 = c0
                    a.t1 = c1
                    a.schedStart = now
                    a.schedLen = if deadline > 0: min(AnnealScheduleSecs, max(5.0, deadline - now))
                                 else: AnnealScheduleSecs
                    inc a.schedules
            t0 = a.t0; t1 = a.t1; schedStart = a.schedStart; schedLen = a.schedLen
            n = a.schedules; disabled = a.disabled
        if state.verbose:
            echo &"[Anneal S{state.id}] schedule {n}: feasible={feas} uphill={up} T0={t0:.3f} T1={t1:.4f} len={schedLen:.0f}s" &
                (if disabled: " (disabled)" else: "")
        if schedStart == 0.0: return false

    let startSlack = state.boundSlack()
    var bestSlack = startSlack
    var curSlack = startSlack
    var bestAssignment = state.assignment
    var tries, evals, accepted = 0
    var reached, schedDone = false
    let ratio = t1 / t0
    var temp = t0
    let tStart = epochTime()
    while true:
        if (tries and 255) == 0:
            let now = epochTime()
            if (deadline > 0 and now > deadline - 0.5) or
               (state.stopSignal != nil and state.stopSignal[].load()):
                break
            let u = now - schedStart
            if u >= schedLen:
                schedDone = true
                break
            temp = t0 * pow(ratio, u / schedLen)
        inc tries
        var p1, p2: int
        var v1, v2: T
        if not state.annealPick(movable, p1, v1, p2, v2): continue
        inc evals
        let o1 = state.assignment[p1]
        let o2 = if p2 >= 0: state.assignment[p2] else: T(0)
        var hard: int
        var d: T
        state.annealTry(p1, v1, p2, v2, hard, d)
        if hard > 0 or (d > 0 and rand(1.0) >= exp(-float(d) / temp)):
            state.annealUndo(p1, o1, p2, o2)
            continue
        inc accepted
        curSlack += d
        if curSlack < bestSlack:
            bestSlack = curSlack
            if state.cost == 0:
                reached = true
                break
            bestAssignment = state.assignment
    if schedDone:
        withLock a.lock:
            if a.schedStart == schedStart: a.schedStart = 0.0
        # The siblings anneal on the same schedule: end the ask
        if state.stopSignal != nil: state.stopSignal[].store(true)
    if not reached and bestSlack < curSlack:
        for p in state.searchPositions:
            if state.assignment[p] != bestAssignment[p]:
                state.assignValueLean(p, bestAssignment[p])
    if state.verbose:
        let spent = epochTime() - tStart
        echo &"[Anneal S{state.id}] {spent:.1f}s moves={evals} ({float(evals) / max(spent, 1e-6):.0f}/s) accepted={accepted} T={temp:.3f} slack {startSlack}->{bestSlack}" &
            (if reached: " target reached" elif schedDone: " schedule over" else: "")
    reached or schedDone
