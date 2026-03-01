## PairwiseFairness Constraint Implementation
## ============================================
##
## Consolidates C(n,2) int_lin_le constraints encoding pairwise fairness:
##   |coeffA[p]*countA + coeffB[p]*countB| <= threshold * bt
## into a single constraint per bt variable.
##
## From the on-call rostering FZN chain:
##   int_lin_eq([wl_i, -wl_j, -1], [count_j, count_i, inner_v], 0) :: defines_var(inner_v)
##   int_abs(inner_v, abs_v)                                         :: defines_var(abs_v)
##   int_lin_le([1, -T], [abs_v, bt_v], 0)                          # abs_v <= T * bt_v
##
## Penalty for pair p: max(0, |coeffA[p]*countA + coeffB[p]*countB| - threshold * bt)
## Total cost: sum of all pair penalties.
##
## moveDelta:
##   bt position: iterate ALL pairs, O(nPairs)
##   count position: iterate pairsForPosition[pos], O(n-1) pairs

import std/[packedsets, tables]

type
    PairwiseFairnessConstraint*[T] = ref object
        nPairs*: int
        pairCoeffA*: seq[int]      # linear coefficient for first count var per pair
        pairCoeffB*: seq[int]      # linear coefficient for second count var per pair
        pairPosA*: seq[int]        # position of first count variable per pair
        pairPosB*: seq[int]        # position of second count variable per pair
        btPosition*: int           # position of the tolerance (bt) variable
        threshold*: int            # multiplier T (e.g. 100)
        pairsForPosition*: Table[int, seq[int]]  # count position → pair indices
        currentAssignment*: Table[int, T]
        pairAbsDiffs*: seq[int]    # cached |coeffA*countA + coeffB*countB| per pair
        cost*: int
        lastChangeAffectedCost*: bool
        allPositions*: PackedSet[int]

func newPairwiseFairnessConstraint*[T](
    pairCoeffA, pairCoeffB: seq[int],
    pairPosA, pairPosB: seq[int],
    btPosition: int,
    threshold: int): PairwiseFairnessConstraint[T] =
  new(result)
  let n = pairCoeffA.len
  result.nPairs = n
  result.pairCoeffA = pairCoeffA
  result.pairCoeffB = pairCoeffB
  result.pairPosA = pairPosA
  result.pairPosB = pairPosB
  result.btPosition = btPosition
  result.threshold = threshold
  result.pairAbsDiffs = newSeq[int](n)
  result.cost = 0
  result.currentAssignment = initTable[int, T]()
  result.allPositions = initPackedSet[int]()
  result.allPositions.incl(btPosition)
  result.pairsForPosition = initTable[int, seq[int]]()
  for p in 0..<n:
    result.allPositions.incl(pairPosA[p])
    result.allPositions.incl(pairPosB[p])
    if pairPosA[p] notin result.pairsForPosition:
      result.pairsForPosition[pairPosA[p]] = @[]
    result.pairsForPosition[pairPosA[p]].add(p)
    if pairPosB[p] != pairPosA[p]:
      if pairPosB[p] notin result.pairsForPosition:
        result.pairsForPosition[pairPosB[p]] = @[]
      result.pairsForPosition[pairPosB[p]].add(p)
  result.lastChangeAffectedCost = false

proc initialize*[T](state: PairwiseFairnessConstraint[T], assignment: seq[T]) =
  for pos in state.allPositions.items:
    state.currentAssignment[pos] = assignment[pos]
  let bt = state.currentAssignment[state.btPosition]
  state.cost = 0
  for p in 0..<state.nPairs:
    let a = state.currentAssignment[state.pairPosA[p]]
    let b = state.currentAssignment[state.pairPosB[p]]
    state.pairAbsDiffs[p] = abs(state.pairCoeffA[p] * a + state.pairCoeffB[p] * b)
    state.cost += max(0, state.pairAbsDiffs[p] - state.threshold * bt)

proc updatePosition*[T](state: PairwiseFairnessConstraint[T], position: int, newValue: T) =
  let oldValue = state.currentAssignment[position]
  if oldValue == newValue:
    state.lastChangeAffectedCost = false
    return
  state.currentAssignment[position] = newValue

  let oldCost = state.cost
  if position == state.btPosition:
    # bt changed — recompute all pair penalties
    state.cost = 0
    for p in 0..<state.nPairs:
      state.cost += max(0, state.pairAbsDiffs[p] - state.threshold * newValue)
  else:
    # A count variable changed — update affected pairs
    let pairs = state.pairsForPosition.getOrDefault(position, @[])
    let bt = state.currentAssignment[state.btPosition]
    for p in pairs:
      let oldAbsDiff = state.pairAbsDiffs[p]
      let a = state.currentAssignment[state.pairPosA[p]]
      let b = state.currentAssignment[state.pairPosB[p]]
      let newAbsDiff = abs(state.pairCoeffA[p] * a + state.pairCoeffB[p] * b)
      state.pairAbsDiffs[p] = newAbsDiff
      let oldPen = max(0, oldAbsDiff - state.threshold * bt)
      let newPen = max(0, newAbsDiff - state.threshold * bt)
      state.cost += newPen - oldPen

  state.lastChangeAffectedCost = (state.cost != oldCost)

proc moveDelta*[T](state: PairwiseFairnessConstraint[T], position: int, oldValue, newValue: T): int =
  if oldValue == newValue:
    return 0

  let bt = state.currentAssignment[state.btPosition]

  if position == state.btPosition:
    # bt changed — recompute total cost with new bt value
    var newCost = 0
    for p in 0..<state.nPairs:
      newCost += max(0, state.pairAbsDiffs[p] - state.threshold * newValue)
    return newCost - state.cost
  else:
    # Count variable changed — only affected pairs
    var delta = 0
    let pairs = state.pairsForPosition.getOrDefault(position, @[])
    let threshBt = state.threshold * bt
    for p in pairs:
      let oldAbsDiff = state.pairAbsDiffs[p]
      var a = state.currentAssignment[state.pairPosA[p]]
      var b = state.currentAssignment[state.pairPosB[p]]
      if state.pairPosA[p] == position:
        a = newValue
      if state.pairPosB[p] == position:
        b = newValue
      let newAbsDiff = abs(state.pairCoeffA[p] * a + state.pairCoeffB[p] * b)
      let oldPen = max(0, oldAbsDiff - threshBt)
      let newPen = max(0, newAbsDiff - threshBt)
      delta += newPen - oldPen
    return delta

proc getAffectedPositions*[T](state: PairwiseFairnessConstraint[T]): PackedSet[int] =
  if not state.lastChangeAffectedCost:
    return initPackedSet[int]()
  return state.allPositions

proc getAffectedDomainValues*[T](state: PairwiseFairnessConstraint[T], position: int): seq[T] =
  return @[]

proc deepCopy*[T](state: PairwiseFairnessConstraint[T]): PairwiseFairnessConstraint[T] =
  new(result)
  result.nPairs = state.nPairs
  result.pairCoeffA = state.pairCoeffA
  result.pairCoeffB = state.pairCoeffB
  result.pairPosA = state.pairPosA
  result.pairPosB = state.pairPosB
  result.btPosition = state.btPosition
  result.threshold = state.threshold
  result.pairAbsDiffs = state.pairAbsDiffs
  result.cost = state.cost
  result.currentAssignment = initTable[int, T]()
  for k, v in state.currentAssignment.pairs:
    result.currentAssignment[k] = v
  result.allPositions = state.allPositions
  result.pairsForPosition = state.pairsForPosition
  result.lastChangeAffectedCost = state.lastChangeAffectedCost
