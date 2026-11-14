## Objective polish moves for optimizer probes with a scaled objective bound.
## Included from tabu.nim — not a standalone module.
##
## A scaled bound (costScale > 1) counts one cost unit per costScale objective
## units, so local search sees most objective-improving moves as neutral and
## the objective random-walks under the bound (warehouse: supply cost 33k where
## a greedy assignment over the same open facilities pays 11.5k). These moves
## read the raw objective directly: a move is taken only when it adds no hard
## violation and lowers the raw objective, so a feasible state stays feasible
## and the near-feasible tracking sees every gain.

proc scaledBoundTieBreak[T](state: TabuState[T]): bool {.inline.} =
    state.boundConstraint != nil and
        state.boundConstraint.stateType == RelationalType and
        state.boundConstraint.relationalState.costScale > 1

proc boundSlack[T](state: TabuState[T]): T {.inline.} =
    ## Signed raw distance of the objective-bound constraint from its target
    ## (negative = inside the bound).
    let rc = state.boundConstraint.relationalState
    case rc.relation
    of LessThan, LessThanEq: rc.leftValue - rc.rightValue
    of GreaterThan, GreaterThanEq: rc.rightValue - rc.leftValue
    else: T(0)

const PolishMaxValues = 256   # values tried per position (sampled beyond)
const PolishFruitlessMin = 50  # positions a sweep scans without a move before giving up

type PolishMode = enum
    pmPolish   ## no added hard violation, lower raw objective: key (objective, hard)
    pmEvict    ## must leave its value: key (hard, objective)
    pmRepair   ## must remove a hard violation: key (hard, objective)

proc buildPolishEstimates[T](state: TabuState[T]) =
    ## Per search position, the linear part of the raw objective that it
    ## drives: its own coefficient in the bound sum and the element channels
    ## (constant arrays) whose outputs the sum reads. Used only
    ## to order and prefilter polish candidates; every move is still scored
    ## by simulation.
    state.polishEstBuilt = true
    template carray: untyped = state.carray
    let rc = state.boundConstraint.relationalState
    if rc.leftExpr.kind != SumExpr or rc.leftExpr.sumExpr.evalMethod != PositionBased or
       rc.rightExpr.kind != ConstantExpr:
        return
    let sign: T = case rc.relation
        of LessThan, LessThanEq: T(1)
        of GreaterThan, GreaterThanEq: T(-1)
        else: T(0)
    if sign == 0: return
    let coef {.cursor.} = rc.leftExpr.sumExpr.coefficient
    state.polishDirect = newSeq[T](carray.len)
    state.polishElems = newSeq[seq[(int, T)]](carray.len)
    state.polishHasEst = newSeq[bool](carray.len)
    for p in state.searchPositions:
        let c = coef.getOrDefault(p, T(0))
        if c != 0:
            state.polishDirect[p] = sign * c
            state.polishHasEst[p] = true
        if p in carray.channelsAtPosition:
            for bi in carray.channelsAtPosition[p]:
                let b {.cursor.} = carray.channelBindings[bi]
                let cc = coef.getOrDefault(b.channelPosition, T(0))
                if cc == 0: continue
                var allConst = true
                for e in b.arrayElements:
                    if not e.isConstant:
                        allConst = false
                        break
                if not allConst: continue
                state.polishElems[p].add((bi, sign * cc))
                state.polishHasEst[p] = true

proc polishEstimate[T](state: TabuState[T], pos: int, v: T): T =
    ## Estimated raw slack change of moving `pos` to `v` (see buildPolishEstimates).
    let old = state.assignment[pos]
    result = state.polishDirect[pos] * (v - old)
    for (bi, c) in state.polishElems[pos]:
        let b {.cursor.} = state.carray.channelBindings[bi]
        let i0 = int(b.evalIndex(state.assignment))
        state.assignment[pos] = v
        let i1 = int(b.evalIndex(state.assignment))
        state.assignment[pos] = old
        let n = b.arrayElements.len
        if i0 < 0 or i0 >= n or i1 < 0 or i1 >= n: continue
        result += c * (b.arrayElements[i1].constantValue - b.arrayElements[i0].constantValue)

proc polishBestValue[T](state: TabuState[T], pos: int, excluded: T, mode: PolishMode):
        tuple[found: bool, value: T, hard: int, slack: T] =
    ## Best value for `pos` other than its current one and `excluded`, scored
    ## by its hard-violation delta and the raw objective after the move. With
    ## an objective estimate, candidates are simulated cheapest first and the
    ## scan stops at the first that adds no hard violation (polish) or removes
    ## one (evict/repair).
    let old = state.assignment[pos]
    let baseCost = state.cost
    let baseBound = state.boundConstraint.penalty()
    let baseSlack = state.boundSlack()
    result = (false, old, 0, baseSlack)
    var bestHard = high(int)
    var bestSlack = high(T)
    var ties = 0
    let domain {.cursor.} = state.sharedDomain[][pos]
    let n = domain.len
    if not state.polishEstBuilt: state.buildPolishEstimates()
    let hasEst = state.polishHasEst.len > 0 and state.polishHasEst[pos]
    # Candidate domain indices, in simulation order
    var order: seq[int]
    if hasEst:
        var est: seq[(T, int)]
        for di in 0..<n:
            let v = domain[di]
            if v == old or v == excluded: continue
            let e = state.polishEstimate(pos, v)
            if mode == pmPolish and e >= 0: continue
            est.add((e, di))
        shuffle(est)
        est.sort(proc (a, b: (T, int)): int = cmp(a[0], b[0]))
        for (_, di) in est: order.add(di)
    elif n > PolishMaxValues:
        for k in 0..<PolishMaxValues: order.add(rand(n - 1))
    else:
        order = toSeq(0..<n)
    # Outside a simulation the penalty map holds each move's exact total
    # delta; a polish move adds no hard violation and does not raise the
    # bound, so its total is never positive.
    let usePm = mode == pmPolish and not state.leanSearch and not state.isLazy[pos] and
        state.penaltyMap[pos].len == n
    for di in order:
        let v = domain[di]
        if v == old or v == excluded: continue
        if usePm and state.penaltyMap[pos][di] > 0: continue
        state.assignValueLean(pos, v)
        let hard = (state.cost - baseCost) - (state.boundConstraint.penalty() - baseBound)
        let slack = state.boundSlack()
        state.assignValueLean(pos, old)
        var better, tie: bool
        case mode
        of pmPolish:
            if hard > 0 or slack > baseSlack or (slack == baseSlack and hard >= 0): continue
            better = slack < bestSlack or (slack == bestSlack and hard < bestHard)
            tie = slack == bestSlack and hard == bestHard
        of pmEvict, pmRepair:
            if mode == pmRepair and hard >= 0: continue
            better = hard < bestHard or (hard == bestHard and slack < bestSlack)
            tie = hard == bestHard and slack == bestSlack
        if better:
            bestHard = hard; bestSlack = slack; ties = 1
            result = (true, v, hard, slack)
        elif tie:
            inc ties
            if rand(ties - 1) == 0: result = (true, v, hard, slack)
        if hasEst and (if mode == pmPolish: hard <= 0 else: hard < 0):
            break

proc commitPolish[T](state: TabuState[T], pos: int, value: T) =
    let old = state.assignment[pos]
    let oldIdx = state.domIdx(pos, old)
    if oldIdx >= 0 and not state.isLazy[pos]:
        state.tabu[pos][oldIdx] = state.iteration + 1 + state.iteration mod 10
    state.commitValue(pos, value)

proc tryObjectivePolish[T](state: TabuState[T], budget: float): int =
    ## Sweeps the search positions, moving each to its best raw-objective
    ## value that adds no hard violation, until a sweep finds nothing or the
    ## time budget runs out. Returns the number of moves made.
    if not state.scaledBoundTieBreak(): return 0
    let t0 = epochTime()
    var positions = state.searchPositions
    # A sweep whose first tenth finds nothing gives up: on problems where
    # the objective has no single-move slack (unit commitment) a full
    # fruitless sweep per probe state cost most of a 12 s budget.
    let fruitlessCap = max(PolishFruitlessMin, positions.len div 10)
    var improved = true
    while improved and epochTime() - t0 < budget:
        improved = false
        shuffle(positions)
        var sinceMove = 0
        for i, p in positions:
            if (i and 15) == 0 and epochTime() - t0 > budget: break
            if sinceMove >= fruitlessCap: break
            inc sinceMove
            if p in state.carray.fixedPositions: continue
            let r = state.polishBestValue(p, state.assignment[p], pmPolish)
            if r.found:
                state.commitPolish(p, r.value)
                inc result
                improved = true
                sinceMove = 0
    inc state.polishCalls
    state.polishMoves += result

const DropRepairRounds = 3

template hardSince[T](state: TabuState[T], baseCost, baseBound: int): int =
    (state.cost - baseCost) - (state.boundConstraint.penalty() - baseBound)

proc simLean[T](state: TabuState[T], changes: var seq[(int, T)], pos: int, v: T) {.inline.} =
    changes.add((pos, state.assignment[pos]))
    state.assignValueLean(pos, v)

proc settleSim[T](state: TabuState[T], changes: seq[(int, T)], keep: bool) =
    ## Undo a lean simulation; when `keep`, commit its final values as moves.
    var finalMoves: seq[(int, T)]
    if keep:
        for (pos, _) in changes: finalMoves.add((pos, state.assignment[pos]))
    for i in countdown(changes.len - 1, 0):
        state.assignValueLean(changes[i][0], changes[i][1])
    for (pos, x) in finalMoves:
        if x != state.assignment[pos]: state.commitPolish(pos, x)

proc guardInactive[T](state: TabuState[T], c: GuardedCountConstraint[T], s: int): (bool, T) =
    for x in state.sharedDomain[][c.guardPositions[s]]:
        if x != c.guardActive[s]: return (true, x)
    (false, c.guardActive[s])

proc slotMovable[T](state: TabuState[T], c: GuardedCountConstraint[T], s: int,
                    inputs: var seq[int]): bool =
    ## Inputs currently on slot `s`'s value; false if one cannot move.
    let v = c.values[s]
    inputs.setLen(0)
    for p in c.inputPositions:
        if state.assignment[p] == v:
            if p in state.carray.fixedPositions or p in state.carray.channelPositions:
                return false
            inputs.add(p)
    true

proc simEvictSlot[T](state: TabuState[T], c: GuardedCountConstraint[T], s: int,
                     changes: var seq[(int, T)], baseCost, baseBound: int): bool =
    ## Lean-simulates closing slot `s`: activate its guard, move its inputs
    ## to their best (hard, raw objective) values, then eject inputs off the
    ## destination values while that removes violations (the evicted inputs
    ## can land next to incompatible groups or on full capacity). Returns
    ## false when an input has nowhere to go.
    let v = c.values[s]
    var inputs: seq[int]
    if not state.slotMovable(c, s, inputs): return false
    state.simLean(changes, c.guardPositions[s], c.guardActive[s])
    shuffle(inputs)
    for i in 0..<(inputs.len - max(0, c.ubs[s])):
        let r = state.polishBestValue(inputs[i], v, pmEvict)
        if not r.found: return false
        state.simLean(changes, inputs[i], r.value)
    if state.hardSince(baseCost, baseBound) > 0:
        var dests: HashSet[T]
        for p in inputs: dests.incl(state.assignment[p])
        for round in 0..<DropRepairRounds:
            if state.hardSince(baseCost, baseBound) <= 0: break
            var cand: seq[int]
            for q in c.inputPositions:
                if state.assignment[q] in dests and q notin state.carray.fixedPositions:
                    cand.add(q)
            shuffle(cand)
            var progress = false
            for q in cand:
                if state.hardSince(baseCost, baseBound) <= 0: break
                let r = state.polishBestValue(q, v, pmRepair)
                if r.found:
                    state.simLean(changes, q, r.value)
                    dests.incl(r.value)
                    progress = true
            if not progress: break
    true

proc guardedSlots[T](state: TabuState[T]): seq[(int, int)] =
    for ci in state.gvIndices:
        let c = state.constraints[ci].guardedCountState
        for s in 0..<c.values.len: result.add((ci, s))
    shuffle(result)

proc tryGuardedValueDrop[T](state: TabuState[T], budget: float): int =
    ## Facility close: activate one GuardedCount guard (count <= ub, e.g.
    ## is_open = 0) and move the inputs on its value away (simEvictSlot).
    ## Kept only when no hard violation is added and the raw objective falls
    ## (the fixed cost saved exceeds the moved inputs' extra cost). Tries the
    ## open slots in random order until the budget runs out. Returns the
    ## number of slots closed.
    if not state.scaledBoundTieBreak() or state.gvIndices.len == 0: return 0
    let t0 = epochTime()
    for (ci, s) in state.guardedSlots():
        if epochTime() - t0 > budget: break
        let c = state.constraints[ci].guardedCountState
        let g = c.guardPositions[s]
        if state.assignment[g] == c.guardActive[s]: continue
        if state.domIdx(g, c.guardActive[s]) < 0: continue
        inc state.dropTries
        let baseCost = state.cost
        let baseBound = state.boundConstraint.penalty()
        let baseSlack = state.boundSlack()
        var changes: seq[(int, T)]
        let ok = state.simEvictSlot(c, s, changes, baseCost, baseBound)
        let keep = ok and state.hardSince(baseCost, baseBound) <= 0 and
            state.boundSlack() < baseSlack
        state.settleSim(changes, keep)
        if keep: inc result
    state.dropApplied += result

proc tryGuardedValueSwap[T](state: TabuState[T], budget: float): int =
    ## Facility swap: deactivate a closed slot's guard (open it), move the
    ## inputs that get cheaper there onto it, then close the open slot that
    ## lost the most of its inputs (simEvictSlot). Kept only when no hard
    ## violation is added and the raw objective falls. Returns the number of
    ## swaps made.
    if not state.scaledBoundTieBreak() or state.gvIndices.len == 0: return 0
    let t0 = epochTime()
    for (ci, k) in state.guardedSlots():
        if epochTime() - t0 > budget: break
        let c = state.constraints[ci].guardedCountState
        let gk = c.guardPositions[k]
        if state.assignment[gk] != c.guardActive[k]: continue
        let (hasOpen, openVal) = state.guardInactive(c, k)
        if not hasOpen: continue
        inc state.swapTries
        let vk = c.values[k]
        var slotOf = initTable[T, int]()
        for s, v in c.values: slotOf[v] = s
        let baseCost = state.cost
        let baseBound = state.boundConstraint.penalty()
        let baseSlack = state.boundSlack()
        var changes: seq[(int, T)]
        state.simLean(changes, gk, openVal)
        var lost = newSeq[int](c.values.len)   # inputs moved off each slot
        var anyLost = false
        var inputs = c.inputPositions
        shuffle(inputs)
        for p in inputs:
            let old = state.assignment[p]
            if old == vk or p in state.carray.fixedPositions or
               p in state.carray.channelPositions or state.domIdx(p, vk) < 0:
                continue
            let cost0 = state.cost
            let bound0 = state.boundConstraint.penalty()
            let slack0 = state.boundSlack()
            state.assignValueLean(p, vk)
            if state.hardSince(cost0, bound0) <= 0 and state.boundSlack() < slack0:
                changes.add((p, old))
                let so = slotOf.getOrDefault(old, -1)
                if so >= 0:
                    inc lost[so]
                    anyLost = true
            else:
                state.assignValueLean(p, old)
        var keep = false
        if anyLost:
            # Close the source slot left with the fewest inputs
            var bestS = -1
            var bestLoad = high(int)
            for s in 0..<lost.len:
                if lost[s] == 0: continue
                let g = c.guardPositions[s]
                if state.assignment[g] == c.guardActive[s] or
                   state.domIdx(g, c.guardActive[s]) < 0: continue
                var load = 0
                for p in c.inputPositions:
                    if state.assignment[p] == c.values[s]: inc load
                if load < bestLoad:
                    bestLoad = load; bestS = s
            if bestS >= 0 and state.simEvictSlot(c, bestS, changes, baseCost, baseBound):
                keep = state.hardSince(baseCost, baseBound) <= 0 and
                    state.boundSlack() < baseSlack
        state.settleSim(changes, keep)
        if keep: inc result
    state.swapApplied += result

proc objectiveHillClimb[T](state: TabuState[T], budget: float) =
    ## Polish, facility closes and facility swaps in turn until a round gains
    ## nothing or the budget runs out. Only from states where the bound is the
    ## sole violation: there every gain is a better solution of the original
    ## problem, while pushing the objective of a state that still violates
    ## hard constraints steers its repair (unit commitment, 380k hard cost:
    ## 0.56-1.57M instead of 0.25-0.45M).
    if not state.scaledBoundTieBreak(): return
    if state.cost != state.boundConstraint.penalty(): return
    let t0 = epochTime()
    while true:
        let before = state.boundSlack()
        let left = budget - (epochTime() - t0)
        if left <= 0: break
        discard state.tryObjectivePolish(left / 2)
        discard state.tryGuardedValueDrop((budget - (epochTime() - t0)) / 2)
        discard state.tryGuardedValueSwap(budget - (epochTime() - t0))
        if state.boundSlack() >= before: break
