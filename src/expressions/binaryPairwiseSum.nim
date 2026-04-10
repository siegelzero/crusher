import std/[packedsets, tables]

type
  BinaryPairwiseSumPair*[T] = tuple[posA, posB: int, coeff: T]
  BinaryPairwiseSumLinear*[T] = tuple[pos: int, coeff: T]

  BinaryPairwiseSumExpression*[T] = ref object
    ## Computes: constant + Σ coeff_k * x_{posA_k} * x_{posB_k} + Σ coeff_m * x_{pos_m}
    ## Optimized for binary (0/1) variables but works correctly for any integer values.
    ## moveDelta is O(pairs_at_position + linear_at_position) per position change.
    value*: T
    constant*: T
    positions*: PackedSet[int]
    currentAssignment*: Table[int, T]
    pairs*: seq[BinaryPairwiseSumPair[T]]
    pairsAtPosition*: Table[int, seq[int]]
    linearTerms*: seq[BinaryPairwiseSumLinear[T]]
    linearAtPosition*: Table[int, seq[int]]

func newBinaryPairwiseSumExpression*[T](
    pairs: seq[BinaryPairwiseSumPair[T]],
    linearTerms: seq[BinaryPairwiseSumLinear[T]] = @[],
    constant: T = 0): BinaryPairwiseSumExpression[T] =
  var positions = initPackedSet[int]()
  var pairsAtPosition = initTable[int, seq[int]]()
  var linearAtPosition = initTable[int, seq[int]]()
  var filteredPairs: seq[BinaryPairwiseSumPair[T]]
  var adjustedConstant = constant

  # Filter self-pairs (posA == posB means coeff * x^2; for binary x, x^2 = x → fold to linear)
  var extraLinear: seq[BinaryPairwiseSumLinear[T]]
  for pair in pairs:
    if pair.posA == pair.posB:
      extraLinear.add((pos: pair.posA, coeff: pair.coeff))
    else:
      filteredPairs.add(pair)

  # Build pair index
  for i, pair in filteredPairs:
    positions.incl(pair.posA)
    positions.incl(pair.posB)
    pairsAtPosition.mgetOrPut(pair.posA, @[]).add(i)
    pairsAtPosition.mgetOrPut(pair.posB, @[]).add(i)

  # Build linear index (merge original + self-pair-derived)
  let allLinear = linearTerms & extraLinear
  for i, lt in allLinear:
    positions.incl(lt.pos)
    linearAtPosition.mgetOrPut(lt.pos, @[]).add(i)

  result = BinaryPairwiseSumExpression[T](
    value: 0,
    constant: adjustedConstant,
    positions: positions,
    currentAssignment: initTable[int, T](),
    pairs: filteredPairs,
    pairsAtPosition: pairsAtPosition,
    linearTerms: allLinear,
    linearAtPosition: linearAtPosition
  )

func computeValue*[T](state: BinaryPairwiseSumExpression[T]): T {.inline.} =
  result = state.constant
  for pair in state.pairs:
    result += pair.coeff * state.currentAssignment[pair.posA] * state.currentAssignment[pair.posB]
  for lt in state.linearTerms:
    result += lt.coeff * state.currentAssignment[lt.pos]

func initialize*[T](state: BinaryPairwiseSumExpression[T], assignment: seq[T]) =
  state.currentAssignment.clear()
  for pos in state.positions.items:
    state.currentAssignment[pos] = assignment[pos]
  state.value = state.computeValue()

func evaluate*[T](state: BinaryPairwiseSumExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
  result = state.constant
  for pair in state.pairs:
    result += pair.coeff * assignment[pair.posA] * assignment[pair.posB]
  for lt in state.linearTerms:
    result += lt.coeff * assignment[lt.pos]

func updatePosition*[T](state: BinaryPairwiseSumExpression[T], position: int, newValue: T) {.inline.} =
  let oldValue = state.currentAssignment.getOrDefault(position, 0)
  if oldValue == newValue: return
  state.currentAssignment[position] = newValue
  let diff = newValue - oldValue
  # Update from pairs: delta += coeff * partner * diff
  if position in state.pairsAtPosition:
    for pairIdx in state.pairsAtPosition[position]:
      let pair = state.pairs[pairIdx]
      let otherPos = if pair.posA == position: pair.posB else: pair.posA
      let otherVal = state.currentAssignment[otherPos]
      state.value += pair.coeff * otherVal * diff
  # Update from linear terms: delta += coeff * diff
  if position in state.linearAtPosition:
    for ltIdx in state.linearAtPosition[position]:
      let lt = state.linearTerms[ltIdx]
      state.value += lt.coeff * diff

func moveDelta*[T](state: BinaryPairwiseSumExpression[T], position: int,
                    oldValue, newValue: T): T {.inline.} =
  result = 0
  let diff = newValue - oldValue
  # Pairs contribution: coeff * partner_val * (newValue - oldValue)
  if position in state.pairsAtPosition:
    for pairIdx in state.pairsAtPosition[position]:
      let pair = state.pairs[pairIdx]
      let otherPos = if pair.posA == position: pair.posB else: pair.posA
      let otherVal = state.currentAssignment[otherPos]
      result += pair.coeff * otherVal * diff
  # Linear contribution: coeff * (newValue - oldValue)
  if position in state.linearAtPosition:
    for ltIdx in state.linearAtPosition[position]:
      let lt = state.linearTerms[ltIdx]
      result += lt.coeff * diff

proc deepCopy*[T](state: BinaryPairwiseSumExpression[T]): BinaryPairwiseSumExpression[T] =
  result = BinaryPairwiseSumExpression[T](
    value: state.value,
    constant: state.constant,
    positions: state.positions,
    currentAssignment: state.currentAssignment,
    pairs: state.pairs,
    pairsAtPosition: state.pairsAtPosition,
    linearTerms: state.linearTerms,
    linearAtPosition: state.linearAtPosition
  )
