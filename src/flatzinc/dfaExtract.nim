## DFA placement extraction for regular-to-geost conversion.
##
## Given a DFA (from a regular constraint), extracts the set of valid placements
## for a particular tile value. Each placement is a list of board cell indices
## where the tile appears.

import std/[packedsets, strformat]

proc identifyTileInput*(transition: seq[seq[int]], nStates, nInputs: int): int =
  ## Determines which input symbol (0-indexed) is the "tile" input by finding
  ## the unique non-sentinel input with distinct transitions from state 1.
  ## The sentinel is always the last input (nInputs-1).
  ## Returns -1 if ambiguous (multiple distinct non-sentinel inputs).
  let sentinelIdx = nInputs - 1

  # From initial state (state 1, index 0), check which inputs produce unique transitions
  # Non-tile inputs all produce the same transition; the tile input differs.
  if nInputs < 3:
    return -1  # Need at least: tile, other, sentinel

  # Collect transitions from state 0 (initial state) for non-sentinel inputs
  var transFromInit: seq[int]
  for inp in 0..<sentinelIdx:
    transFromInit.add(transition[0][inp])

  # Find the input whose transition differs from the majority
  # Most inputs are "other" (non-tile) and share the same transition
  var counts: seq[int] = newSeq[int](nStates + 1)
  for t in transFromInit:
    if t >= 0 and t <= nStates:
      counts[t] += 1

  # Find the most common transition (that's the "other" group)
  var maxCount = 0
  var commonTrans = -1
  for s in 0..nStates:
    if counts[s] > maxCount:
      maxCount = counts[s]
      commonTrans = s

  # The tile input is the one that differs from the common transition
  var tileInput = -1
  for inp in 0..<sentinelIdx:
    if transFromInit[inp] != commonTrans:
      if tileInput != -1:
        return -1  # Multiple distinct inputs - ambiguous
      tileInput = inp

  return tileInput

proc extractPlacementsFromDfa*(
    nStates, nInputs: int,
    transition: seq[seq[int]],
    initialState: int,
    finalStates: seq[int],
    tileInputIdx: int,
    boardSize: int,
    sentinelPositions: PackedSet[int]
): seq[seq[int]] =
  ## DFS with backward reachability pruning to enumerate all valid cell sets
  ## for a tile. Returns list of cell sets (0-indexed board positions).
  ##
  ## tileInputIdx: 0-indexed input symbol for this tile
  ## sentinelPositions: board indices that are sentinel columns
  let sentinelInputIdx = nInputs - 1

  # Choose a non-tile, non-sentinel input for "other" cells
  var otherInputIdx = -1
  for idx in 0..<nInputs:
    if idx != tileInputIdx and idx != sentinelInputIdx:
      otherInputIdx = idx
      break
  if otherInputIdx < 0:
    return @[]

  # Final states as packed set
  var finalSet = initPackedSet[int]()
  for s in finalStates:
    finalSet.incl(s)

  # Backward reachability: can (pos, state) reach a final state?
  var reachable = newSeq[seq[bool]](boardSize + 1)
  for i in 0..boardSize:
    reachable[i] = newSeq[bool](nStates + 1)
  for s in finalStates:
    reachable[boardSize][s] = true

  for pos in countdown(boardSize - 1, 0):
    for s in 1..nStates:
      if pos in sentinelPositions:
        let ns = transition[s-1][sentinelInputIdx]
        if ns > 0 and ns <= nStates and reachable[pos+1][ns]:
          reachable[pos][s] = true
      else:
        let nsT = transition[s-1][tileInputIdx]
        if nsT > 0 and nsT <= nStates and reachable[pos+1][nsT]:
          reachable[pos][s] = true
        let nsO = transition[s-1][otherInputIdx]
        if nsO > 0 and nsO <= nStates and reachable[pos+1][nsO]:
          reachable[pos][s] = true

  # DFS to enumerate all accepting paths
  var placements: seq[seq[int]] = @[]
  var cells: seq[int] = @[]

  proc dfs(pos: int, state: int) =
    if pos == boardSize:
      if state in finalSet and cells.len > 0:
        placements.add(cells)
      return

    if pos in sentinelPositions:
      let ns = transition[state-1][sentinelInputIdx]
      if ns > 0 and ns <= nStates and reachable[pos+1][ns]:
        dfs(pos + 1, ns)
    else:
      # Branch 1: cell is tile
      let nsT = transition[state-1][tileInputIdx]
      if nsT > 0 and nsT <= nStates and reachable[pos+1][nsT]:
        cells.add(pos)
        dfs(pos + 1, nsT)
        cells.setLen(cells.len - 1)

      # Branch 2: cell is not tile
      let nsO = transition[state-1][otherInputIdx]
      if nsO > 0 and nsO <= nStates and reachable[pos+1][nsO]:
        dfs(pos + 1, nsO)

  if reachable[0][initialState]:
    dfs(0, initialState)

  return placements
