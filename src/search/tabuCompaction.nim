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

## Reordering. Compaction keeps every resource's task order; the remaining
## idle time is in the order itself (saeling j0050_m003: reordering the
## worker's loads and unloads of a compacted 1533 schedule reaches 1359).
## The order is a list of events: each task's start and, when its duration
## is a search variable, its end (the start of the task anchored to it, the
## unload, or else its end). A trial moves one event a few places and decodes
## the schedule from there: the tasks whose start comes later are parked
## (translated right past every end, which keeps them consistent among
## themselves), the tasks already started but not yet ended are opened (their
## anchored task parked far right, which keeps their machine busy), then the
## events are replayed in the new order, each at the earliest start or
## shortest duration that overlaps no task left of the parking area and makes
## no other constraint worse. The trial is a lean simulation, kept when the
## decoded state violates at most the objective bound and the raw objective
## is no worse (sideways moves cross plateaus). Only an end-anchored unload
## needs the second event: placing it right after its own start (one event
## per task) decodes that schedule to 2100.

## Reassignment trials change a task's machine instead (any search position
## whose change moves the machine of the task's no-overlap tasks: a worker,
## a machine, or a cut mode choosing the machine; found by probing each
## position once), repair what the change breaks through the task's other
## such positions (worker-machine compatibility), and decode from the task's
## start event in the same order (saeling j0050_m003: the prototype reaches
## 1248, the worker workload bound, from 1359 for reordering alone).

const ReorderWindow = 12        # event move distance in the order
const ReorderMaxStarts = 48     # start candidates per start event
const ReorderMaxDurs = 48       # duration candidates per end event
const ReorderStallTrials = 10000 # trials without a strict gain before giving up
const ReassignShare = 0.3       # share of reassignment trials
const ReassignMaxProbe = 20000  # search positions probed for reassignment at most


proc compactAnchored[T](state: TabuState[T], dp: int): seq[(int, int)] =
    ## No-overlap tasks whose start moves with the duration `dp`, one for one
    ## (saeling: the unload, anchored to the end of its LCU). Found by a lean
    ## probe of dp, whatever kind of channel defines those starts.
    if dp in state.compactAnchors: return state.compactAnchors[dp]
    let d0 = state.assignment[dp]
    let dDom {.cursor.} = state.compactSortedDomain(dp)
    var d1 = d0
    for v in dDom:
        if v != d0:
            d1 = v
            break
    if d1 != d0:
        var before: seq[seq[T]]
        for ci in state.compactMmno:
            before.add(state.constraints[ci].multiMachineNoOverlapState.currentStarts)
        state.assignValueLean(dp, d1)
        for k, ci in state.compactMmno:
            let mc = state.constraints[ci].multiMachineNoOverlapState
            for u in 0..<mc.taskCount:
                if mc.startPositions[u] in state.carray.channelPositions and
                   int(mc.currentStarts[u]) - int(before[k][u]) == int(d1) - int(d0):
                    result.add((ci, u))
        state.assignValueLean(dp, d0)
    state.compactAnchors[dp] = result

proc buildReassign[T](state: TabuState[T], units: seq[int], durOf: seq[int]) =
    ## compactReassign: for each unit's start position, the search positions
    ## whose change moves the machine of one of its no-overlap tasks (own or
    ## anchored). One lean probe per position.
    if state.compactReassignBuilt: return
    state.compactReassignBuilt = true
    if state.searchPositions.len > ReassignMaxProbe: return
    var unitOf = initTable[(int, int), int]()
    var skip: PackedSet[int]
    for u, sp in units:
        skip.incl(sp)
        for (ci, x) in state.keepEndStartOf.getOrDefault(sp, @[]): unitOf[(ci, x)] = u
        if durOf[u] >= 0:
            skip.incl(durOf[u])
            for (ci, x) in state.compactAnchored(durOf[u]): unitOf[(ci, x)] = u
    for (sp, dp) in state.keepEndTasks: skip.incl(dp)
    var before: seq[seq[T]]
    for ci in state.compactMmno:
        before.add(state.constraints[ci].multiMachineNoOverlapState.currentMachines)
    for p in state.searchPositions:
        if p in skip or p in state.carray.fixedPositions: continue
        let dom {.cursor.} = state.compactSortedDomain(p)
        if dom.len < 2: continue
        let v0 = state.assignment[p]
        let v1 = if dom[0] != v0: dom[0] else: dom[1]
        state.assignValueLean(p, v1)
        for k, ci in state.compactMmno:
            let mc = state.constraints[ci].multiMachineNoOverlapState
            for x in 0..<mc.taskCount:
                if mc.currentMachines[x] != before[k][x]:
                    let u = unitOf.getOrDefault((ci, x), -1)
                    if u >= 0:
                        let lst = addr state.compactReassign.mgetOrPut(units[u], @[])
                        if p notin lst[]: lst[].add(p)
        state.assignValueLean(p, v0)

proc mmnoMachine[T](mc: MultiMachineNoOverlapConstraint[T], x: int): int {.inline.} =
    if mc.machinePositions[x] >= 0: int(mc.currentMachines[x]) else: mc.fixedMachines[x]

proc nearOverlap[T](state: TabuState[T], ci, x: int, farStart: int): bool =
    ## Task x of no-overlap constraint ci overlaps a task starting before
    ## farStart (or a fixed block) on its machine.
    let mc = state.constraints[ci].multiMachineNoOverlapState
    let m = mc.mmnoMachine(x)
    if m == mc.ignoreMachine or mc.currentDurs[x] <= 0: return false
    let s = int(mc.currentStarts[x])
    let e = s + mc.currentDurs[x]
    for u in 0..<mc.taskCount:
        if u == x or mc.currentDurs[u] <= 0: continue
        let su = int(mc.currentStarts[u])
        if su >= farStart or mc.mmnoMachine(u) != m: continue
        if su < e and s < su + mc.currentDurs[u]: return true
    if m < mc.fixedBlocks.len:
        for (bs, bd) in mc.fixedBlocks[m]:
            if bd > 0 and bs < e and s < bs + bd: return true
    false

proc appendBound[T](state: TabuState[T], ci, x: int, farStart: int): int =
    ## Latest end on task x's machine among the tasks starting before
    ## farStart (the placed ones): x goes after them (order = machine order).
    let mc = state.constraints[ci].multiMachineNoOverlapState
    let m = mc.mmnoMachine(x)
    if m == mc.ignoreMachine: return low(int)
    result = low(int)
    for u in 0..<mc.taskCount:
        if u == x or mc.currentDurs[u] <= 0: continue
        let su = int(mc.currentStarts[u])
        if su >= farStart or mc.mmnoMachine(u) != m: continue
        result = max(result, su + mc.currentDurs[u])

type ReorderEvent = tuple[isEnd: bool, unit: int]

proc reorderTrial[T](state: TabuState[T], events: seq[ReorderEvent], units: seq[int],
                     durOf: seq[int], i, j: int, log: var seq[(int, T)],
                     rp = -1, rv = T(0)): bool =
    ## Lean-simulates moving events[i] to place j (with rp >= 0: setting rp
    ## to rv first, a reassignment of events[i]'s unit) and decoding the
    ## schedule after it; the simulation stays applied (undo with `log`).
    ## False when the new order is invalid or an event could not be placed.
    ## durOf[u] is the duration position of unit u when it has an anchored
    ## task, else -1.
    template sim(p: int, v: T) =
        log.add((p, state.assignment[p]))
        state.assignValueLean(p, v)
    proc otherHard(state: TabuState[T]): int =
        ## Violation outside the objective bound and the no-overlaps
        result = state.cost - state.boundConstraint.penalty()
        for ci in state.compactMmno: result -= state.constraints[ci].penalty()
    if rp >= 0:
        # Reassign, then repair what it broke through the unit's other
        # reassignment positions (worker-machine compatibility)
        let h0 = state.otherHard()
        sim(rp, rv)
        if state.otherHard() > h0:
            # Greedy: each other position takes its value with the least
            # violation (a machine change can break both workers)
            for q in state.compactReassign.getOrDefault(units[events[i].unit], @[]):
                if q == rp: continue
                let q0 = state.assignment[q]
                var bestH = state.otherHard()
                var bestW = q0
                for w in state.compactSortedDomain(q):
                    if w == q0: continue
                    sim(q, w)
                    let h = state.otherHard()
                    if h < bestH:
                        bestH = h
                        bestW = w
                if state.assignment[q] != bestW: sim(q, bestW)
                if bestH <= h0: break
            if state.otherHard() > h0: return false
    var order = events
    let ev = order[i]
    order.delete(i)
    order.insert(ev, j)
    let k0 = min(i, j)
    # Valid: every end after its own start
    var startedAt = newSeq[int](units.len)
    for k in 0..<units.len: startedAt[k] = -1
    for k, e in order:
        if not e.isEnd: startedAt[e.unit] = k
        elif startedAt[e.unit] < 0: return false
    var maxEnd = 0
    var maxDur = 0
    var maxTime = high(int)
    for ci in state.compactMmno:
        let mc = state.constraints[ci].multiMachineNoOverlapState
        maxTime = min(maxTime, mc.maxTime)
        for u in 0..<mc.taskCount:
            maxEnd = max(maxEnd, int(mc.currentStarts[u]) + mc.currentDurs[u])
            maxDur = max(maxDur, mc.currentDurs[u])
    # Units started before k0 and ended after are opened; units started
    # after k0 are parked past the open anchors
    var parked = newSeq[bool](units.len)
    var open = newSeq[bool](units.len)
    var minS = high(int)
    for k in k0..<order.len:
        let e = order[k]
        if not e.isEnd:
            parked[e.unit] = true
            minS = min(minS, int(state.assignment[units[e.unit]]))
        elif startedAt[e.unit] < k0:
            open[e.unit] = true
    if minS == high(int): minS = maxEnd + 1
    # The open anchors go at farStart and the parked tasks after them (shift
    # = farStart + maxDur + 1 - minS), all inside the constraints' time range
    # (their profiles are sized from maxTime): farStart as far right as that
    # allows, since the replayed events may run past the current ends and an
    # open duration must stay longer than its task's minimum
    let farStart = maxTime - maxEnd - maxDur - 1 + minS
    if farStart <= maxEnd + maxDur: return false
    let shift = max(0, farStart + maxDur + 1 - minS)
    template anchorOff(u: int): int =
        ## start + duration - start of the anchored task (its fixed offset)
        block:
            let (aci, ax) = state.compactAnchored(durOf[u])[0]
            int(state.assignment[units[u]]) + int(state.assignment[durOf[u]]) -
                int(state.constraints[aci].multiMachineNoOverlapState.currentStarts[ax])
    template openDur(u: int): T =
        ## Duration putting unit u's anchored task at farStart
        T(farStart - int(state.assignment[units[u]]) + anchorOff(u))
    for u in 0..<units.len:
        if open[u]:
            sim(durOf[u], openDur(u))
        elif parked[u]:
            let sp = units[u]
            sim(sp, T(int(state.assignment[sp]) + shift))
    var hardRef = state.otherHard()
    var prevT = if k0 > 0: int(state.assignment[units[order[k0 - 1].unit]]) else: low(int)
    var cands: seq[int]
    proc unitFits(state: TabuState[T], sp, dp: int, withAnchors: bool, farStart: int): bool =
        for (ci, x) in state.keepEndStartOf.getOrDefault(sp, @[]):
            if state.nearOverlap(ci, x, farStart): return false
        if withAnchors:
            for (ci, x) in state.compactAnchored(dp):
                if state.nearOverlap(ci, x, farStart): return false
        true
    for k in k0..<order.len:
        let e = order[k]
        let sp = units[e.unit]
        let dp = durOf[e.unit]
        var placed = false
        if not e.isEnd:
            # Start event: earliest start, the duration kept open
            let sDom {.cursor.} = state.compactSortedDomain(sp)
            let cur = int(state.assignment[sp])
            var lo = int(sDom[0])
            # Append: after the placed tasks on each of the unit's machines
            for (ci, x) in state.keepEndStartOf.getOrDefault(sp, @[]):
                lo = max(lo, state.appendBound(ci, x, farStart))
            cands.setLen(0)
            if lo < cur: cands.add(lo)
            for ci in state.compactMmno:
                let mc = state.constraints[ci].multiMachineNoOverlapState
                for u in 0..<mc.taskCount:
                    let su = int(mc.currentStarts[u])
                    if su >= farStart: continue
                    let en = su + mc.currentDurs[u]
                    if en >= lo and en < cur: cands.add(en)
            cands.sort()
            var tried = 0
            var last = -1
            for v in cands:
                if v == last: continue
                last = v
                if sDom.binarySearch(T(v)) < 0: continue
                inc tried
                if tried > ReorderMaxStarts: break
                sim(sp, T(v))
                if dp >= 0: sim(dp, openDur(e.unit))
                if state.unitFits(sp, dp, false, farStart) and state.otherHard() <= hardRef:
                    placed = true
                    break
            if not placed:
                return false
            prevT = int(state.assignment[sp])
            if prevT + maxDur >= farStart: return false
        else:
            # End event: shortest duration, the anchored task right after
            # another task's end
            let dDom {.cursor.} = state.compactSortedDomain(dp)
            let s0 = int(state.assignment[sp])
            let off = anchorOff(e.unit)
            # Append: the anchored task after the placed tasks on its machine
            var dLo = int(dDom[0])
            for (ci, x) in state.compactAnchored(dp):
                let b = state.appendBound(ci, x, farStart)
                if b != low(int): dLo = max(dLo, b - s0 + off)
            # ... and no shorter than the other constraints allow (a lower
            # bound: load + cut + unload), searched only when needed
            block:
                var a = dDom.lowerBound(T(dLo))
                if a < dDom.len:
                    sim(dp, dDom[a])
                    if state.otherHard() > hardRef:
                        inc a
                        var b = dDom.len
                        while a < b:
                            let mid = (a + b) div 2
                            sim(dp, dDom[mid])
                            if state.otherHard() <= hardRef: b = mid else: a = mid + 1
                    if a < dDom.len: dLo = max(dLo, int(dDom[a]))
            cands.setLen(0)
            cands.add(dLo)
            for (ci, _) in state.compactAnchored(dp):
                let mc = state.constraints[ci].multiMachineNoOverlapState
                for u in 0..<mc.taskCount:
                    let su = int(mc.currentStarts[u])
                    if su >= farStart: continue
                    let d = su + mc.currentDurs[u] - s0 + off
                    if d > dLo: cands.add(d)
            cands.sort()
            var tried = 0
            var last = -1
            for d in cands:
                if d == last: continue
                last = d
                if dDom.binarySearch(T(d)) < 0: continue
                inc tried
                if tried > ReorderMaxDurs: break
                sim(dp, T(d))
                if state.unitFits(sp, dp, true, farStart) and state.otherHard() <= hardRef:
                    placed = true
                    break
            if not placed: return false
            prevT = s0 + int(state.assignment[dp]) - off
            if prevT + maxDur >= farStart: return false
        hardRef = state.otherHard()
    true

proc reorderSchedule[T](state: TabuState[T], budget: float): int =
    ## Reorder trials (see above) on a state violating at most the objective
    ## bound, until the budget or ReorderStallTrials trials without a strict
    ## gain; returns the number of strict gains.
    let bc = state.boundConstraint
    if bc == nil or bc.stateType != RelationalType: return 0
    if state.cost != bc.penalty(): return 0
    state.ensureKeepEndTables()
    if state.keepEndStartOf.len < 3: return 0
    for ci in state.compactMmno:
        if state.constraints[ci].multiMachineNoOverlapState.setupMatrix.len > 0: return 0
    let t0 = epochTime()
    let units = toSeq(state.keepEndStartOf.keys)
    var dpOf = initTable[int, int]()
    for (sp, dp) in state.keepEndTasks: dpOf[sp] = dp
    var durOf = newSeq[int](units.len)
    var events: seq[ReorderEvent]
    for u, sp in units:
        let dp = dpOf.getOrDefault(sp, -1)
        durOf[u] = (if dp >= 0 and state.compactAnchored(dp).len > 0: dp else: -1)
        events.add((false, u))
        if durOf[u] >= 0: events.add((true, u))
    proc eventTime(state: TabuState[T], e: ReorderEvent): int =
        if not e.isEnd: return int(state.assignment[units[e.unit]])
        let (aci, ax) = state.compactAnchored(durOf[e.unit])[0]
        int(state.constraints[aci].multiMachineNoOverlapState.currentStarts[ax])
    state.buildReassign(units, durOf)
    var reassignable: seq[int]   # units with reassignment positions
    for u, sp in units:
        if state.compactReassign.getOrDefault(sp, @[]).len > 0: reassignable.add(u)
    var startAt = newSeq[int](units.len)   # event index of each unit's start
    var log: seq[(int, T)]
    var finals: seq[(int, T)]
    var seen: PackedSet[int]
    var stall = 0
    # The event order is the search state: sorted by time once, then moved
    # by the kept trials (a kept trial that leaves the schedule unchanged
    # still changes the order: drift on the plateau)
    block:
        var keyed = newSeq[(int, int, int)](events.len)
        for k, e in events: keyed[k] = (state.eventTime(e), ord(e.isEnd), k)
        keyed.sort()
        let old = events
        for k in 0..<keyed.len: events[k] = old[keyed[k][2]]
        for k, e in events:
            if not e.isEnd: startAt[e.unit] = k
    while stall < ReorderStallTrials and epochTime() - t0 < budget:
        var i, j: int
        var rp = -1
        var rv = T(0)
        if reassignable.len > 0 and rand(1.0) < ReassignShare:
            # Reassignment: a new value for one of a unit's positions
            let u = reassignable[rand(reassignable.len - 1)]
            let ps {.cursor.} = state.compactReassign[units[u]]
            rp = ps[rand(ps.len - 1)]
            let dom {.cursor.} = state.compactSortedDomain(rp)
            rv = dom[rand(dom.len - 1)]
            if rv == state.assignment[rp]: continue
            i = startAt[u]
            j = i
            inc state.reassignTrials
        else:
            i = rand(events.len - 1)
            j = clamp(i + rand(2 * ReorderWindow) - ReorderWindow, 0, events.len - 1)
            if i == j: continue
            inc state.reorderTrials
        let slack0 = state.boundSlack()
        log.setLen(0)
        let ok = state.reorderTrial(events, units, durOf, i, j, log, rp, rv)
        let keep = ok and state.cost == bc.penalty() and state.boundSlack() <= slack0
        let gain = keep and state.boundSlack() < slack0
        finals.setLen(0)
        if keep and not state.leanSearch:
            seen.clear()
            for k in countdown(log.len - 1, 0):
                let p = log[k][0]
                if p notin seen:
                    seen.incl(p)
                    finals.add((p, state.assignment[p]))
        if not keep or not state.leanSearch:
            # Undo; a kept lean trial already is its committed state
            for k in countdown(log.len - 1, 0):
                state.assignValueLean(log[k][0], log[k][1])
        if keep:
            if not state.leanSearch:
                for (p, v) in finals:
                    if state.assignment[p] != v: state.commitValue(p, v)
            if rp >= 0: inc state.reassignKept
            else:
                inc state.reorderKept
                let ev = events[i]
                events.delete(i)
                events.insert(ev, j)
                for k, e in events:
                    if not e.isEnd: startAt[e.unit] = k
        if gain:
            inc result
            stall = 0
        else:
            inc stall
    state.reorderGains += result
