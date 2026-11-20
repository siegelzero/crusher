## Schedule compaction of a feasible state under the optimizer's bound.
## Included from tabu.nim — not a standalone module.
##
## A tabu walk on start times stops at the first state inside the bound, and
## such a schedule is mostly idle time: on saeling (one worker doing every
## load and unload) the worker was busy 1323 of 3013 minutes, and starting
## every operation as early as its current machine, worker and job orders
## allow gives 1529. Single moves rarely find this, since pulling the last
## operation earlier first needs everything before it to move.
##
## The pass visits the no-overlap tasks in start order and moves each to the
## earliest start that keeps the state feasible: a shift (start alone), or a
## stretch (start earlier, duration longer, end kept: the operation anchored
## to the end, an unload, stays put) when its duration is a search variable;
## then it shortens that duration as far as it can. Candidate starts are the
## start domain's minimum and the current ends of all no-overlap tasks. A
## move is kept only when it adds no violation besides the objective bound's
## and the raw objective does not get worse, so the pass is safe for any
## objective. It also runs on the incumbent that seeds a retry ask (only the
## bound violated), which often lands it inside the bound at once.

const CompactMaxDurScan = 256   # duration values tried per task (sampled beyond)

proc ensureKeepEndTables[T](state: TabuState[T]) =
    ## No-overlap tasks with a movable start (keepEndStartOf) and those whose
    ## duration is movable too (keepEndTasks).
    if state.keepEndBuilt: return
    state.keepEndBuilt = true
    var seen: PackedSet[int]
    template movable(p: int): bool =
        p >= 0 and p notin state.carray.channelPositions and p notin state.carray.fixedPositions
    for ci, c in state.constraints:
        if c.stateType != MultiMachineNoOverlapType: continue
        state.compactMmno.add(ci)
        let mc = c.multiMachineNoOverlapState
        for t in 0..<mc.taskCount:
            let sp = mc.startPositions[t]
            if not sp.movable: continue
            state.keepEndStartOf.mgetOrPut(sp, @[]).add((ci, t))
            let dp = mc.durPositions[t]
            if dp.movable and sp notin seen:
                seen.incl(sp)
                state.keepEndTasks.add((sp: sp, dp: dp))

proc compactSortedDomain[T](state: TabuState[T], pos: int): lent seq[T] =
    if pos notin state.compactDom:
        state.compactDom[pos] = state.sharedDomain[][pos].sorted()
    state.compactDom[pos]

proc compactSchedule[T](state: TabuState[T], budget: float): int =
    ## Compacts a state whose only violation, if any, is the relational
    ## objective bound (a solution, or the incumbent seeding a retry ask);
    ## returns the number of moves made. Stops when a pass moves nothing or
    ## the budget runs out.
    let bc = state.boundConstraint
    if bc == nil or bc.stateType != RelationalType: return 0
    if state.cost != bc.penalty(): return 0
    state.ensureKeepEndTables()
    if state.keepEndStartOf.len == 0: return 0
    let t0 = epochTime()
    var durOf = initTable[int, int]()
    for (sp, dp) in state.keepEndTasks: durOf[sp] = dp
    var units = toSeq(state.keepEndStartOf.keys)
    var cands: seq[T]

    template fits(slack0: T): bool =
        state.cost == bc.penalty() and state.boundSlack() <= slack0

    proc keep(state: TabuState[T], moves: openArray[(int, T, T)]) =
        ## Undo the lean simulation of `moves` (pos, old, new) and commit them.
        for i in countdown(moves.len - 1, 0):
            state.assignValueLean(moves[i][0], moves[i][1])
        for (p, _, v) in moves: state.commitValue(p, v)

    var changed = true
    while changed and epochTime() - t0 < budget:
        changed = false
        units.sort(proc (a, b: int): int = cmp(state.assignment[a], state.assignment[b]))
        for i, sp in units:
            if (i and 7) == 0 and epochTime() - t0 > budget: break
            let dp = durOf.getOrDefault(sp, -1)
            let s0 = state.assignment[sp]
            let sDom {.cursor.} = state.compactSortedDomain(sp)
            # Earlier start: shift, or stretch keeping the end
            cands.setLen(0)
            if sDom.len > 0 and sDom[0] < s0: cands.add(sDom[0])
            for ci in state.compactMmno:
                let mc = state.constraints[ci].multiMachineNoOverlapState
                for u in 0..<mc.taskCount:
                    let e = T(int(mc.currentStarts[u]) + mc.currentDurs[u])
                    if e < s0: cands.add(e)
            cands.sort()
            var last = T(-1)
            var moved = false
            for v in cands:
                if v == last: continue
                last = v
                if sDom.binarySearch(v) < 0: continue
                let slack0 = state.boundSlack()
                state.assignValueLean(sp, v)
                if fits(slack0):
                    state.keep([(sp, s0, v)])
                    moved = true
                    break
                if dp >= 0:
                    let d0 = state.assignment[dp]
                    let d = d0 + (s0 - v)
                    if state.compactSortedDomain(dp).binarySearch(d) >= 0:
                        state.assignValueLean(dp, d)
                        if fits(slack0):
                            state.keep([(sp, s0, v), (dp, d0, d)])
                            moved = true
                            break
                        state.assignValueLean(dp, d0)
                state.assignValueLean(sp, s0)
            if moved:
                inc result
                changed = true
            # Shorter duration (the end, and what is anchored to it, earlier)
            if dp >= 0:
                let d0 = state.assignment[dp]
                let dDom {.cursor.} = state.compactSortedDomain(dp)
                var n = 0
                while n < dDom.len and dDom[n] < d0: inc n
                let stride = max(1, n div CompactMaxDurScan)
                var k = 0
                while k < n:
                    let d = dDom[k]
                    let slack0 = state.boundSlack()
                    state.assignValueLean(dp, d)
                    if fits(slack0):
                        state.keep([(dp, d0, d)])
                        inc result
                        changed = true
                        break
                    state.assignValueLean(dp, d0)
                    k += stride
    inc state.compactCalls
    state.compactMoves += result
