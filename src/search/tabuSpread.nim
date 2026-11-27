## Spread construction: list scheduling of a multi-machine no-overlap with
## the machines chosen as it goes, on a capped set of machine values.
## Included from tabu.nim — not a standalone module.
##
## workforce-alloc minimizes the teams used (weight sum(duration)) plus the
## spread of their working times; instance_19 needs 5 teams and the walk
## (14-30 it/s through ~7800 channels) never got below 6 (10830), nor does
## Gecode with the model's search. Every task can start only 30-60 after its
## release, so placing the tasks by latest start, each on the machine of a
## fixed set of K where it can start earliest, finds 5-team schedules in
## about one try of 6 (instance_71: one of 58; Python prototype, 3000 tries)
## and dispersion 0 among them. Opening a machine only when no open one
## fits does not: it ends at 6 teams, crusher's old value. constructSchedule
## (tabuCompaction) keeps the machines and cannot empty one.
##
## A try picks K = the machine values of the kept build (or of the state),
## or one fewer, takes a value of every task group whose domain misses the
## set, fills the set at random, and places the tasks by noisy latest start
## (start domain maximum), each after the tasks it shares a constraint
## between starts with that must start earlier. The start is the first
## value of the start domain at or after the earliest one the constraints
## with the placed tasks allow, clear of the placed tasks and fixed blocks
## on the machine; the machine is the candidate of least key, its earliest
## such start or (sometimes) its load. Constraints between placed tasks are
## checked through the state; those another search position reaches are
## left to a repair of those positions after the build, and a build counts
## only when the whole state costs 0 (objective bound included).

const
    SpreadMaxSecs = 5.0         # budget per call
    SpreadEarliestShare = 0.7   # per candidate machine: keyed by its earliest start, else by its load
    SpreadFewerShare = 0.5      # K = machines of the kept build (or state) - 1, else as many
    SpreadLevelTries = 200      # tries at one machine fewer before that level counts as out of reach
    SpreadMoreMin = 100         # after the first build: tries without a better one before stopping
    SpreadMoreFactor = 4        # ... or this many times the tries the first build took
    SpreadAuxMaxDom = 64        # repair: other search positions of at most this many values
    SpreadPolishFails = 100     # polish: moves in a row without a gain before it stops

proc ensureSpreadTables[T](state: TabuState[T]) =
    ## The no-overlap the construction applies to (spreadCi, -1: none) and
    ## the constraints each task's start and machine reach.
    if state.spreadBuilt: return
    state.spreadBuilt = true
    state.spreadCi = -1
    var found = -1
    for ci, c in state.constraints:
        if c.stateType != MultiMachineNoOverlapType: continue
        if found >= 0: return            # one no-overlap only
        found = ci
    if found < 0: return
    let mc = state.constraints[found].multiMachineNoOverlapState
    if mc.taskCount < 2 or mc.setupMatrix.len > 0 or mc.ignoreMachine >= 0: return
    template movable(p: int): bool =
        p >= 0 and p notin state.carray.channelPositions and p notin state.carray.fixedPositions
    for t in 0..<mc.taskCount:
        if mc.durPositions[t] >= 0 or mc.durations[t] < 0: return
        if not movable(mc.startPositions[t]) or not movable(mc.machinePositions[t]): return
    var cIndex = initTable[pointer, int]()
    for ci, c in state.constraints: cIndex[cast[pointer](c)] = ci
    let bc = state.boundConstraint
    let bci = if bc != nil: cIndex.getOrDefault(cast[pointer](bc), -1) else: -1
    proc reach(p: int): seq[int] =
        ## p and the positions that move with it (probed)
        result = @[p]
        let dom {.cursor.} = state.compactSortedDomain(p)
        if dom.len < 2: return
        let v0 = state.assignment[p]
        let v1 = if dom[^1] != v0: dom[^1] else: dom[0]
        let before = state.assignment
        state.assignValueLean(p, v1)
        for q in 0..<before.len:
            if q != p and state.assignment[q] != before[q]: result.add(q)
        state.assignValueLean(p, v0)
    proc consAt(ps: seq[int]): seq[int] =
        for q in ps:
            for c in state.constraintsAtPosition[q]:
                let ci = cIndex[cast[pointer](c)]
                if ci != found and ci != bci and ci notin result: result.add(ci)
    let wasLean = state.leanSearch
    state.leanSearch = true
    state.spreadConsS = newSeq[seq[int]](mc.taskCount)
    state.spreadConsM = newSeq[seq[int]](mc.taskCount)
    var mReach = initTable[int, seq[int]]()
    for t in 0..<mc.taskCount:
        let mp = mc.machinePositions[t]
        if mp notin mReach: mReach[mp] = consAt(reach(mp))
        let sCons = consAt(reach(mc.startPositions[t]))
        let mCons {.cursor.} = mReach[mp]
        for ci in sCons:
            if ci notin mCons: state.spreadConsS[t].add ci
        state.spreadConsM[t] = mCons
        for ci in sCons: state.spreadConsM[t].add ci
    state.leanSearch = wasLean
    var taskPos: PackedSet[int]
    for t in 0..<mc.taskCount:
        taskPos.incl mc.startPositions[t]
        taskPos.incl mc.machinePositions[t]
    state.leanSearch = true
    for p in 0..<state.assignment.len:
        if p in taskPos or not movable(p): continue
        let dom = state.compactSortedDomain(p)
        if dom.len < 2 or dom.len > SpreadAuxMaxDom: continue
        # The constraints p reaches, probed over its whole domain
        var ps: seq[int]
        let v0 = state.assignment[p]
        let before = state.assignment
        for v in dom:
            if v == v0: continue
            state.assignValueLean(p, v)
            for q in 0..<before.len:
                if state.assignment[q] != before[q] and q notin ps: ps.add q
            state.assignValueLean(p, v0)
        state.spreadAux.add p
        state.spreadAuxCons.add consAt(ps)
    state.leanSearch = wasLean
    # Constraints another search position reaches are left to the repair
    # and the final check (workforce-alloc: a dropped team's indicator only
    # follows its set-element boolean, which the repair moves)
    var auxCons: PackedSet[int]
    for cs in state.spreadAuxCons:
        for ci in cs: auxCons.incl ci
    for t in 0..<mc.taskCount:
        state.spreadConsS[t] = state.spreadConsS[t].filterIt(it notin auxCons)
        state.spreadConsM[t] = state.spreadConsM[t].filterIt(it notin auxCons)
    state.spreadTasksOf = initTable[int, seq[int]]()
    for t in 0..<mc.taskCount:
        for ci in state.spreadConsM[t]:
            let ts = state.spreadTasksOf.mgetOrPut(ci, @[])
            if t notin ts: state.spreadTasksOf[ci].add t
    state.spreadCi = found

proc spreadRepairAux[T](state: TabuState[T], log: var seq[(int, T)]) =
    ## After a construction: the other search positions (no task's start or
    ## machine) that reach a violated constraint move, best first, to their
    ## domain's value of least cost, each at most once; cost-neutral moves
    ## count, since a dropped machine can need two (workforce-alloc: the
    ## team's set-element boolean, then the team count matching their sum).
    ## Changes go to log.
    var moved = newSeq[bool](state.spreadAux.len)
    while state.cost > 0:
        var bestK = -1
        var bestV: T
        var bestCost = high(int)
        for k, p in state.spreadAux:
            if moved[k]: continue
            var hit = false
            for ci in state.spreadAuxCons[k]:
                if state.constraints[ci].penalty() > 0:
                    hit = true
                    break
            if not hit: continue
            let v0 = state.assignment[p]
            for v in state.compactSortedDomain(p):
                if v == v0: continue
                state.assignValueLean(p, v)
                if state.cost < bestCost:
                    bestCost = state.cost
                    bestK = k
                    bestV = v
            state.assignValueLean(p, v0)
        if bestK < 0 or bestCost > state.cost: return
        let p = state.spreadAux[bestK]
        log.add((p, state.assignment[p]))
        state.assignValueLean(p, bestV)
        moved[bestK] = true

proc spreadSchedule[T](state: TabuState[T], budget: float): bool =
    ## Construction tries (see above). A build that leaves the state at cost 0
    ## is kept when its objective (bound slack) beats the kept one's; tries
    ## then go on from it, at its machine count and one fewer, until
    ## SpreadMoreMin (or SpreadMoreFactor times the first build's) tries bring
    ## no better one or the budget runs out. True with the best build in the
    ## state, else false with the state unchanged.
    state.ensureSpreadTables()
    if state.spreadCi < 0: return false
    let mc = state.constraints[state.spreadCi].multiMachineNoOverlapState
    let n = mc.taskCount
    let t0 = epochTime()
    # Groups: tasks sharing a machine position (same-allocation)
    var groupOf = newSeq[int](n)
    var groupPos: seq[int]
    var gIndex = initTable[int, int]()
    for t in 0..<n:
        let mp = mc.machinePositions[t]
        if mp notin gIndex:
            gIndex[mp] = groupPos.len
            groupPos.add mp
        groupOf[t] = gIndex[mp]
    var used: PackedSet[int]
    var allValues: seq[int]
    for g, mp in groupPos:
        used.incl int(state.assignment[mp])
        for v in state.compactSortedDomain(mp):
            if int(v) notin allValues: allValues.add int(v)
    let m = used.len
    var byDomSize = toSeq(0..<groupPos.len)
    byDomSize.sort(proc (a, b: int): int =
        cmp(state.compactSortedDomain(groupPos[a]).len, state.compactSortedDomain(groupPos[b]).len))
    var durs = newSeq[int](n)
    for t in 0..<n: durs[t] = mc.durations[t]
    var sortedDurs = durs
    sortedDurs.sort()
    let noise = max(1.0, 0.5 * float(sortedDurs[n div 2]))
    var log: seq[(int, T)]
    template sim(p: int, v: T) =
        log.add((p, state.assignment[p]))
        state.assignValueLean(p, v)
    template undoTo(mark: int) =
        for k in countdown(log.len - 1, mark):
            state.assignValueLean(log[k][0], log[k][1])
        log.setLen(mark)
    var unplacedIn = initTable[int, int]()      # constraint -> tasks of it not placed
    proc consOk(t: int, cons: seq[int]): bool =
        ## The constraints in cons (all of them t's) whose other tasks are all
        ## placed hold; t counts as unplaced until it is committed
        for ci in cons:
            if unplacedIn[ci] == 1 and state.constraints[ci].penalty() > 0: return false
        true
    # Placement order: latest start first (start domain maximum, plus noise;
    # by the propagated earliest start, instance_71 never fits 5 teams: a
    # same-team successor that must follow its predecessor at once comes
    # after the tasks that fill the gap), and a task waits for the tasks it
    # shares a constraint between starts with whose latest start is earlier
    # (a precedence's predecessor)
    var baseKey = newSeq[int](n)
    for t in 0..<n: baseKey[t] = int(state.compactSortedDomain(mc.startPositions[t])[^1])
    var waitFor = newSeq[seq[int]](n)
    for t in 0..<n:
        for ci in state.spreadConsS[t]:
            for u in state.spreadTasksOf.getOrDefault(ci, @[]):
                if u != t and (baseKey[u] < baseKey[t] or (baseKey[u] == baseKey[t] and u < t)) and
                        u notin waitFor[t]:
                    waitFor[t].add u
    var isPlaced = newSeq[bool](n)
    var groupTasks = newSeq[seq[int]](groupPos.len)
    for t in 0..<n: groupTasks[groupOf[t]].add t
    proc polish(chosen: seq[int]) =
        ## Moves a group of tasks to another machine of the build, or swaps
        ## two, each task at the start nearest its own that is clear there
        ## and keeps its constraints with the others; a move stays when the
        ## state still costs 0 and the objective (bound slack) drops, until
        ## SpreadPolishFails moves in a row bring nothing
        for ci, v in unplacedIn.mpairs: v = 1          # every other task placed
        var tasksOn = initTable[int, seq[int]]()
        for v in chosen: tasksOn[v] = @[]
        for t in 0..<n: tasksOn.mgetOrPut(int(state.assignment[mc.machinePositions[t]]), @[]).add t
        var cur = state.boundSlack()
        proc moveGroup(g, b: int, excl: seq[int]): bool =
            ## g's tasks onto machine b, b's tasks of the groups in excl ignored
            sim(groupPos[g], T(b))
            var moved: seq[(int, int)]
            var ts = groupTasks[g]
            ts.sort(proc (x, y: int): int = cmp(state.assignment[mc.startPositions[x]], state.assignment[mc.startPositions[y]]))
            for t in ts:
                let sp = mc.startPositions[t]
                let dom {.cursor.} = state.compactSortedDomain(sp)
                let s0 = int(state.assignment[sp])
                var busy: seq[(int, int)]
                for y in tasksOn[b]:
                    if groupOf[y] notin excl:
                        let sy = int(state.assignment[mc.startPositions[y]])
                        busy.add((sy, sy + durs[y]))
                for (x, sx) in moved: busy.add((sx, sx + durs[x]))
                if b >= 0 and b < mc.fixedBlocks.len:
                    for (bs, bd) in mc.fixedBlocks[b]:
                        if bd > 0: busy.add((bs, bs + bd))
                var cands = @[s0]
                for (bs, be) in busy:
                    cands.add be
                    cands.add bs - durs[t]
                cands.sort(proc (x, y: int): int = cmp(abs(x - s0), abs(y - s0)))
                var placedAt = -1
                for c in cands:
                    if dom.binarySearch(T(c)) < 0: continue
                    var clash = false
                    for (bs, be) in busy:
                        if bs < c + durs[t] and c < be:
                            clash = true
                            break
                    if clash: continue
                    sim(sp, T(c))
                    if consOk(t, state.spreadConsS[t]):
                        placedAt = c
                        break
                if placedAt < 0: return false
                moved.add((t, placedAt))
            true
        var fails = 0
        while fails < SpreadPolishFails:
            inc fails
            let g = rand(groupPos.len - 1)
            let a = int(state.assignment[groupPos[g]])
            let mDom {.cursor.} = state.compactSortedDomain(groupPos[g])
            var targets: seq[int]
            for v in chosen:
                if v != a and mDom.binarySearch(T(v)) >= 0: targets.add v
            if targets.len == 0: continue
            let b = targets[rand(targets.len - 1)]
            var h = -1
            if rand(1.0) < 0.5 and tasksOn[b].len > 0:
                h = groupOf[tasksOn[b][rand(tasksOn[b].len - 1)]]
                if state.compactSortedDomain(groupPos[h]).binarySearch(T(a)) < 0: h = -1
            let mark = log.len
            var ok = moveGroup(g, b, (if h >= 0: @[g, h] else: @[g]))
            if ok and h >= 0: ok = moveGroup(h, a, @[h])
            if ok and state.cost > 0: state.spreadRepairAux(log)
            if ok and state.cost == 0 and state.boundSlack() < cur:
                cur = state.boundSlack()
                fails = 0
                for t in groupTasks[g]:
                    tasksOn[a].delete(tasksOn[a].find(t))
                    tasksOn[b].add t
                if h >= 0:
                    for t in groupTasks[h]:
                        tasksOn[b].delete(tasksOn[b].find(t))
                        tasksOn[a].add t
                inc state.spreadPolishGains
            else:
                undoTo(mark)
    let bc = state.boundConstraint
    let slackOk = bc != nil and bc.stateType == RelationalType
    var tries, wins, sinceGain = 0
    var bestK = -1                  # machines of the kept build (-1: none)
    var bestSlack: T
    var floorK = 0                  # K below this failed SpreadLevelTries times
    var levelTries = 0
    var firstWinTries = 0
    while epochTime() - t0 < budget:
        if bestK >= 0 and sinceGain >= max(SpreadMoreMin, SpreadMoreFactor * firstWinTries): break
        inc tries
        inc sinceGain
        inc state.spreadTries
        # K: one machine fewer than the kept build (or the state), or as many
        let top = if bestK >= 0: bestK else: m
        let lower = top - 1 >= max(1, floorK) and rand(1.0) < SpreadFewerShare
        let k = if lower: top - 1 else: top
        if lower: inc levelTries
        # The machine set: a value of every group whose domain misses it, then random
        var chosen: seq[int]
        for g in byDomSize:
            let dom {.cursor.} = state.compactSortedDomain(groupPos[g])
            var hit = false
            for v in dom:
                if int(v) in chosen:
                    hit = true
                    break
            if not hit: chosen.add int(dom[rand(dom.len - 1)])
        var rest = allValues.filterIt(it notin chosen)
        shuffle(rest)
        for v in rest:
            if chosen.len >= k: break
            chosen.add v
        var timeline = initTable[int, seq[(int, int)]]()
        var load = initTable[int, int]()
        for v in chosen:
            timeline[v] = @[]
            load[v] = 0
            if v >= 0 and v < mc.fixedBlocks.len:
                for (bs, bd) in mc.fixedBlocks[v]:
                    if bd > 0: timeline[v].add((bs, bs + bd))
        for ci, ts in state.spreadTasksOf.pairs: unplacedIn[ci] = ts.len
        var groupVal = newSeqWith(groupPos.len, low(int))
        var pending = toSeq(0..<n)
        var key = newSeq[float](n)
        for t in 0..<n:
            key[t] = float(baseKey[t]) + rand(noise)
            isPlaced[t] = false
        pending.sort(proc (a, b: int): int = cmp(key[a], key[b]))
        let mark0 = log.len
        var ok = true
        while pending.len > 0:
            # The first pending task in noisy order whose waits are placed
            var pi = 0
            block pick:
                for i, u in pending:
                    var ready = true
                    for w in waitFor[u]:
                        if not isPlaced[w]:
                            ready = false
                            break
                    if ready:
                        pi = i
                        break pick
            let t = pending[pi]
            pending.delete(pi)
            let sp = mc.startPositions[t]
            let dom {.cursor.} = state.compactSortedDomain(sp)
            # Earliest start the constraints with placed tasks allow
            # (galloping, then bisection; they fail below some value)
            let markS = log.len
            var a = 0
            sim(sp, dom[a])
            if not consOk(t, state.spreadConsS[t]):
                var b = 1
                var step = 1
                while b < dom.len:
                    sim(sp, dom[b])
                    if consOk(t, state.spreadConsS[t]): break
                    a = b
                    step *= 2
                    b = a + step
                if b >= dom.len:
                    b = dom.len - 1
                    sim(sp, dom[b])
                    if not consOk(t, state.spreadConsS[t]):
                        ok = false
                        break
                while b - a > 1:
                    let mid = (a + b) div 2
                    sim(sp, dom[mid])
                    if consOk(t, state.spreadConsS[t]): b = mid else: a = mid
                a = b
            undoTo(markS)
            let lo = int(dom[a])
            # Candidate machines with their earliest clear start
            var cands: seq[(float, int, int)]      # (key, value, start)
            let g = groupOf[t]
            let mDom {.cursor.} = state.compactSortedDomain(groupPos[g])
            for v in chosen:
                if groupVal[g] != low(int) and v != groupVal[g]: continue
                if groupVal[g] == low(int) and mDom.binarySearch(T(v)) < 0: continue
                var i = dom.lowerBound(T(lo))
                var s = -1
                while i < dom.len:
                    let x = int(dom[i])
                    var clash = low(int)
                    for (bs, be) in timeline[v]:
                        if bs < x + durs[t] and x < be: clash = max(clash, be)
                    if clash == low(int):
                        s = x
                        break
                    i = dom.lowerBound(T(clash))
                if s < 0: continue
                let kk = if rand(1.0) < SpreadEarliestShare: float(s) + rand(1.0)
                         else: float(load[v]) + rand(noise)
                cands.add((kk, v, s))
            cands.sort(proc (x, y: (float, int, int)): int = cmp(x[0], y[0]))
            var done = false
            for (_, v, s) in cands:
                let markP = log.len
                if groupVal[g] == low(int): sim(groupPos[g], T(v))
                sim(sp, T(s))
                if consOk(t, state.spreadConsM[t]):
                    done = true
                    if groupVal[g] == low(int): groupVal[g] = v
                    timeline[v].add((s, s + durs[t]))
                    load[v] += durs[t]
                    for ci in state.spreadConsM[t]: dec unplacedIn[ci]
                    isPlaced[t] = true
                    break
                undoTo(markP)
            if not done:
                ok = false
                break
        if ok and state.cost > 0: state.spreadRepairAux(log)
        if ok and state.cost == 0 and slackOk: polish(chosen)
        if ok and state.cost == 0:
            let sl = if slackOk: state.boundSlack() else: T(0)
            if bestK < 0 or sl < bestSlack:
                # Keep it: later tries start from here and undo back to it
                if bestK < 0: firstWinTries = tries
                if bestK < 0 or chosen.len < bestK: levelTries = 0
                bestK = chosen.len
                bestSlack = sl
                inc wins
                sinceGain = 0
                log.setLen(0)
                if not slackOk: break
                continue
        undoTo(mark0)
        if lower and levelTries >= SpreadLevelTries: floorK = top
    if bestK >= 0:
        inc state.spreadWins
        if state.verbose:
            let secs = epochTime() - t0
            echo &"[Tabu S{state.id}] Spread: {wins} builds, best {bestK} machines (of {m}), slack {bestSlack}, " &
                 &"{tries} tries ({secs:.2f}s)"
        return true
    if state.verbose:
        let secs = epochTime() - t0
        echo &"[Tabu S{state.id}] Spread: none in {tries} tries ({secs:.2f}s)"
    false
