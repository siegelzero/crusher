## Guarded value counts: for each guarded value v of a shared input array,
##
##     guard_v == active_v  →  |{i : x[i] = v}| <= ub_v
##
## cost = Σ_v [guard_v == active_v] * max(0, count_v - ub_v)
##
## This is the search-variable form of `count_v <= cap_v * is_open_v` where
## count_v is a GCC count channel and is_open_v a search bool (facility
## location: tokens may only use open facilities). Evaluated through the
## channel cascade, every token move re-ran a conditional linear constraint
## per touched facility; here both token moves and guard flips are O(1).

import std/[packedsets, tables]

type
    GuardedCountConstraint*[T] = ref object
        inputPositions*: seq[int]
        values*: seq[T]           # slot -> guarded value
        guardPositions*: seq[int] # slot -> guard position
        guardActive*: seq[T]      # slot -> guard value that activates the bound
        ubs*: seq[int]            # slot -> bound on the count when active
        lo, hi: T                 # value universe of the inputs
        slotOfValue: seq[int32]   # (v - lo) -> slot or -1
        slotOfGuard: Table[int, int]  # guard position -> slot
        inputBase: int
        isInput: seq[bool]        # (pos - inputBase) -> member of inputs
        inputVals: seq[T]         # (pos - inputBase) -> current value
        counts: seq[int]          # slot -> count of inputs at the value
        guardVals: seq[T]         # slot -> current guard value
        positions*: PackedSet[int]
        inputSet: PackedSet[int]
        cost*: int
        # Last accepted move
        lastKind: int             # 0 none, 1 input move, 2 guard flip
        lastSlotA, lastSlotB: int # input move: slots of old/new value (-1 if unguarded)
        lastInputsAffected: bool
        lastOld, lastNew: T
        lastGuardSlot: int

func slotOf[T](c: GuardedCountConstraint[T], v: T): int {.inline.} =
    if v < c.lo or v > c.hi: -1 else: int(c.slotOfValue[int(v - c.lo)])

func contrib[T](c: GuardedCountConstraint[T], slot: int, count: int): int {.inline.} =
    if slot < 0: return 0
    if c.guardVals[slot] != c.guardActive[slot]: return 0
    max(0, count - c.ubs[slot])

func newGuardedCountConstraint*[T](
    inputPositions: seq[int], values: seq[T], guardPositions: seq[int],
    guardActive: seq[T], ubs: seq[int]): GuardedCountConstraint[T] =
    assert values.len == guardPositions.len and values.len == ubs.len and values.len == guardActive.len
    var lo = T(0)
    var hi = T(-1)
    if values.len > 0:
        lo = values[0]; hi = values[0]
        for v in values:
            lo = min(lo, v); hi = max(hi, v)
    var slotOfValue = newSeq[int32](max(0, int(hi - lo) + 1))
    for i in 0 ..< slotOfValue.len: slotOfValue[i] = -1
    var slotOfGuard: Table[int, int]
    for s, v in values:
        slotOfValue[int(v - lo)] = int32(s)
        slotOfGuard[guardPositions[s]] = s
    var minPos = int.high
    var maxPos = -1
    var positions = initPackedSet[int]()
    var inputSet = initPackedSet[int]()
    for p in inputPositions:
        positions.incl(p); inputSet.incl(p)
        minPos = min(minPos, p); maxPos = max(maxPos, p)
    for p in guardPositions: positions.incl(p)
    if maxPos < 0: minPos = 0
    var isInput = newSeq[bool](maxPos - minPos + 1)
    for p in inputPositions: isInput[p - minPos] = true
    result = GuardedCountConstraint[T](
        inputPositions: inputPositions, values: values,
        guardPositions: guardPositions, guardActive: guardActive, ubs: ubs,
        lo: lo, hi: hi, slotOfValue: slotOfValue, slotOfGuard: slotOfGuard,
        inputBase: minPos, isInput: isInput,
        inputVals: newSeq[T](maxPos - minPos + 1),
        counts: newSeq[int](values.len), guardVals: newSeq[T](values.len),
        positions: positions, inputSet: inputSet, cost: 0, lastKind: 0)

proc initialize*[T](c: GuardedCountConstraint[T], assignment: seq[T]) =
    for s in 0 ..< c.counts.len:
        c.counts[s] = 0
        c.guardVals[s] = assignment[c.guardPositions[s]]
    for p in c.inputPositions:
        let v = assignment[p]
        c.inputVals[p - c.inputBase] = v
        let s = c.slotOf(v)
        if s >= 0: inc c.counts[s]
    c.cost = 0
    for s in 0 ..< c.counts.len:
        c.cost += c.contrib(s, c.counts[s])
    c.lastKind = 0

proc moveDelta*[T](c: GuardedCountConstraint[T],
                    position: int, oldValue, newValue: T): int =
    if oldValue == newValue: return 0
    let rel = position - c.inputBase
    if rel >= 0 and rel < c.isInput.len and c.isInput[rel]:
        let so = c.slotOf(oldValue)
        let sn = c.slotOf(newValue)
        var d = 0
        if sn >= 0: d += c.contrib(sn, c.counts[sn] + 1) - c.contrib(sn, c.counts[sn])
        if so >= 0: d += c.contrib(so, c.counts[so] - 1) - c.contrib(so, c.counts[so])
        return d
    let s = c.slotOfGuard.getOrDefault(position, -1)
    if s < 0: return 0
    let wasActive = c.guardVals[s] == c.guardActive[s]
    let nowActive = newValue == c.guardActive[s]
    if wasActive == nowActive: return 0
    let over = max(0, c.counts[s] - c.ubs[s])
    if nowActive: over else: -over

proc updatePosition*[T](c: GuardedCountConstraint[T], position: int, newValue: T) =
    let rel = position - c.inputBase
    if rel >= 0 and rel < c.isInput.len and c.isInput[rel]:
        let oldValue = c.inputVals[rel]
        if oldValue == newValue: return
        c.inputVals[rel] = newValue
        let so = c.slotOf(oldValue)
        let sn = c.slotOf(newValue)
        c.lastKind = 1
        c.lastOld = oldValue
        c.lastNew = newValue
        c.lastSlotA = so
        c.lastSlotB = sn
        c.lastInputsAffected = false
        # A neighbour's delta to value v is active_v * [count_v >= ub_v]; a
        # neighbour leaving value v pays active_v * [count_v >= ub_v + 1]. Only
        # a count crossing one of those thresholds changes any input's delta.
        template crossed(slot, before, after: int) =
            if slot >= 0 and c.guardVals[slot] == c.guardActive[slot]:
                let ub = c.ubs[slot]
                if (before >= ub) != (after >= ub): c.lastInputsAffected = true
                if min(before, after) >= 1 and (before >= ub + 1) != (after >= ub + 1):
                    c.lastInputsAffected = true
        if so >= 0:
            c.cost -= c.contrib(so, c.counts[so])
            dec c.counts[so]
            c.cost += c.contrib(so, c.counts[so])
            crossed(so, c.counts[so] + 1, c.counts[so])
        if sn >= 0:
            c.cost -= c.contrib(sn, c.counts[sn])
            inc c.counts[sn]
            c.cost += c.contrib(sn, c.counts[sn])
            crossed(sn, c.counts[sn] - 1, c.counts[sn])
        return
    let s = c.slotOfGuard.getOrDefault(position, -1)
    if s < 0: return
    c.cost -= c.contrib(s, c.counts[s])
    let wasActive = c.guardVals[s] == c.guardActive[s]
    c.guardVals[s] = newValue
    c.cost += c.contrib(s, c.counts[s])
    let nowActive = newValue == c.guardActive[s]
    c.lastKind = if wasActive != nowActive: 2 else: 0
    c.lastGuardSlot = s

proc getAffectedPositions*[T](c: GuardedCountConstraint[T]): PackedSet[int] =
    case c.lastKind
    of 1:
        if c.lastInputsAffected:
            result = c.inputSet
        else:
            result = initPackedSet[int]()
        if c.lastSlotA >= 0: result.incl(c.guardPositions[c.lastSlotA])
        if c.lastSlotB >= 0: result.incl(c.guardPositions[c.lastSlotB])
    of 2:
        result = c.inputSet
    else:
        result = initPackedSet[int]()

proc getAffectedDomainValues*[T](c: GuardedCountConstraint[T], position: int): seq[T] =
    let rel = position - c.inputBase
    if rel >= 0 and rel < c.isInput.len and c.isInput[rel]:
        case c.lastKind
        of 1: return @[c.lastOld, c.lastNew]
        of 2:
            let v = c.values[c.lastGuardSlot]
            if c.inputVals[rel] == v: return @[]   # leaving term changed: all values
            return @[v]
        else: return @[]
    @[]   # guards are binary: recompute both values

proc deepCopy*[T](c: GuardedCountConstraint[T]): GuardedCountConstraint[T] =
    newGuardedCountConstraint[T](c.inputPositions, c.values, c.guardPositions,
                                 c.guardActive, c.ubs)
