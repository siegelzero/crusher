import std/[packedsets, tables]

type
  WeightedSameValuePair*[T] = tuple[posA, posB: int, coeff: T]

  WeightedSameValueExpression*[T] = ref object
    value*: T
    constant*: T
    positions*: PackedSet[int]
    currentAssignment*: Table[int, T]
    pairs*: seq[WeightedSameValuePair[T]]
    pairsAtPosition*: Table[int, seq[int]]

func newWeightedSameValueExpression*[T](
    pairs: seq[WeightedSameValuePair[T]],
    constant: T = 0): WeightedSameValueExpression[T] =
  var positions = initPackedSet[int]()
  var pairsAtPosition = initTable[int, seq[int]]()
  var filteredPairs: seq[WeightedSameValuePair[T]]
  var adjustedConstant = constant
  for pair in pairs:
    if pair.posA == pair.posB:
      # Self-pairs always match — fold into constant
      adjustedConstant += pair.coeff
      continue
    filteredPairs.add(pair)
  for i, pair in filteredPairs:
    positions.incl(pair.posA)
    positions.incl(pair.posB)
    if pair.posA notin pairsAtPosition:
      pairsAtPosition[pair.posA] = @[]
    pairsAtPosition[pair.posA].add(i)
    if pair.posB notin pairsAtPosition:
      pairsAtPosition[pair.posB] = @[]
    pairsAtPosition[pair.posB].add(i)

  result = WeightedSameValueExpression[T](
    value: 0,
    constant: adjustedConstant,
    positions: positions,
    currentAssignment: initTable[int, T](),
    pairs: filteredPairs,
    pairsAtPosition: pairsAtPosition
  )

func computeValue*[T](state: WeightedSameValueExpression[T]): T {.inline.} =
  result = state.constant
  for pair in state.pairs:
    if state.currentAssignment[pair.posA] == state.currentAssignment[pair.posB]:
      result += pair.coeff

func initialize*[T](state: WeightedSameValueExpression[T], assignment: seq[T]) =
  state.currentAssignment.clear()
  for pos in state.positions.items:
    state.currentAssignment[pos] = assignment[pos]
  state.value = state.computeValue()

func evaluate*[T](state: WeightedSameValueExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
  result = state.constant
  for pair in state.pairs:
    if assignment[pair.posA] == assignment[pair.posB]:
      result += pair.coeff

func updatePosition*[T](state: WeightedSameValueExpression[T], position: int, newValue: T) {.inline.} =
  if position notin state.pairsAtPosition:
    return
  let oldValue = state.currentAssignment[position]
  state.currentAssignment[position] = newValue
  for pairIdx in state.pairsAtPosition[position]:
    let pair = state.pairs[pairIdx]
    let otherPos = if pair.posA == position: pair.posB else: pair.posA
    let otherVal = state.currentAssignment[otherPos]
    let wasMatch = (oldValue == otherVal)
    let isMatch = (newValue == otherVal)
    if isMatch and not wasMatch:
      state.value += pair.coeff
    elif wasMatch and not isMatch:
      state.value -= pair.coeff

func moveDelta*[T](state: WeightedSameValueExpression[T], position: int,
                    oldValue, newValue: T): T {.inline.} =
  if position notin state.pairsAtPosition:
    return 0
  result = 0
  for pairIdx in state.pairsAtPosition[position]:
    let pair = state.pairs[pairIdx]
    let otherPos = if pair.posA == position: pair.posB else: pair.posA
    let otherVal = state.currentAssignment[otherPos]
    let wasMatch = (oldValue == otherVal)
    let isMatch = (newValue == otherVal)
    if isMatch and not wasMatch:
      result += pair.coeff
    elif wasMatch and not isMatch:
      result -= pair.coeff

proc deepCopy*[T](state: WeightedSameValueExpression[T]): WeightedSameValueExpression[T] =
  result = WeightedSameValueExpression[T](
    value: state.value,
    constant: state.constant,
    positions: state.positions,
    currentAssignment: state.currentAssignment,
    pairs: state.pairs,
    pairsAtPosition: state.pairsAtPosition
  )
