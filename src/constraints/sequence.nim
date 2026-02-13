import std/[tables, sets, sequtils, algorithm]
import std/packedsets

import ../expressions/expressions

################################################################################
# SequenceConstraint - Global Constraint
#
# The sequence constraint ensures that among any windowSize consecutive variables
# in the sequence, at least minInSet and at most maxInSet variables take their
# values from the target set S.
#
# Mathematical form: ∀i ∈ [0, n-windowSize] :
#   minInSet ≤ |{j ∈ [i, i+windowSize-1] : x[j] ∈ S}| ≤ maxInSet
#
# Applications:
# - Work scheduling with rest period requirements
# - Resource management with consecutive usage limits
# - Quality control with regular inspection patterns
# - Manufacturing with setup change restrictions
################################################################################

type
    SequenceConstraint*[T] = ref object
        # Sequence constraint: sequence(l, u, q, S, x)
        # Among any q consecutive variables in sequence x, at least l and at most u
        # variables must take their values in set S
        currentAssignment*: Table[int, T]
        cost*: int
        minInSet*: int      # l - minimum occurrences in set S within any q consecutive
        maxInSet*: int      # u - maximum occurrences in set S within any q consecutive
        windowSize*: int    # q - size of consecutive window
        targetSet*: HashSet[T]  # S - target set of values
        lastChangedPosition*: int  # Track last changed position for smart neighbor updates
        sortedPositions*: seq[int]  # Cached sorted position list
        positionIndex*: Table[int, int]  # position -> index in sortedPositions
        windowCounts*: seq[int]  # windowCounts[i] = count of values in targetSet for window i
        lastChangeAffectedWindows*: bool  # did the last update change any window counts?
        lastOldValue*: T  # For getAffectedDomainValues
        lastNewValue*: T  # For getAffectedDomainValues
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions*: PackedSet[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# SequenceConstraint creation
################################################################################

func buildPositionIndex[T](state: SequenceConstraint[T]) =
    state.positionIndex = initTable[int, int]()
    for i, pos in state.sortedPositions:
        state.positionIndex[pos] = i

func newSequenceConstraint*[T](positions: openArray[int], minInSet, maxInSet, windowSize: int, targetSet: openArray[T]): SequenceConstraint[T] =
    # Allocates and initializes new SequenceConstraint[T] for positions
    doAssert windowSize > 0, "window size must be positive"
    doAssert minInSet >= 0, "minimum occurrences must be non-negative"
    doAssert maxInSet >= minInSet, "maximum must be >= minimum"
    doAssert positions.len >= windowSize, "sequence must be at least as long as window size"
    new(result)

    var setTable = initHashSet[T]()
    for value in targetSet:
        setTable.incl(value)

    result = SequenceConstraint[T](
        cost: 0,
        evalMethod: PositionBased,
        positions: toPackedSet[int](positions),
        minInSet: minInSet,
        maxInSet: maxInSet,
        windowSize: windowSize,
        targetSet: setTable,
        currentAssignment: initTable[int, T](),
        lastChangedPosition: -1,
        sortedPositions: toSeq(positions).sorted(),
        lastChangeAffectedWindows: true,
    )
    result.buildPositionIndex()

func newSequenceConstraint*[T](expressions: seq[AlgebraicExpression[T]], minInSet, maxInSet, windowSize: int, targetSet: openArray[T]): SequenceConstraint[T] =
    # Allocates and initializes new SequenceConstraint[T] for expressions
    doAssert windowSize > 0, "window size must be positive"
    doAssert minInSet >= 0, "minimum occurrences must be non-negative"
    doAssert maxInSet >= minInSet, "maximum must be >= minimum"
    doAssert expressions.len >= windowSize, "sequence must be at least as long as window size"
    new(result)

    var setTable = initHashSet[T]()
    for value in targetSet:
        setTable.incl(value)

    result = SequenceConstraint[T](
        cost: 0,
        evalMethod: ExpressionBased,
        expressionsAtPosition: initTable[int, seq[int]](),
        expressions: expressions,
        minInSet: minInSet,
        maxInSet: maxInSet,
        windowSize: windowSize,
        targetSet: setTable,
        currentAssignment: initTable[int, T](),
        lastChangedPosition: -1,
        sortedPositions: @[],
        lastChangeAffectedWindows: true,
    )

################################################################################
# SequenceConstraint utility functions
################################################################################

func windowViolation(count, minInSet, maxInSet: int): int {.inline.} =
    ## Returns the violation cost for a window with the given count of target values
    if count < minInSet:
        return minInSet - count
    elif count > maxInSet:
        return count - maxInSet
    else:
        return 0

func countInSet[T](values: openArray[T], targetSet: HashSet[T]): int {.inline.} =
    ## Counts how many values from the array are in the target set
    result = 0
    for value in values:
        if value in targetSet:
            result += 1

func getWindowViolation[T](state: SequenceConstraint[T], window: openArray[T]): int {.inline.} =
    ## Returns the violation cost for a single window
    let countInTargetSet = countInSet(window, state.targetSet)
    return windowViolation(countInTargetSet, state.minInSet, state.maxInSet)

################################################################################
# SequenceConstraint initialization and updates
################################################################################

proc initialize*[T](state: SequenceConstraint[T], assignment: seq[T]) =
    # Clear previous state
    state.currentAssignment.clear()
    state.cost = 0

    var value: T
    case state.evalMethod:
        of PositionBased:
            # Store current assignment for positions
            for pos in state.positions:
                value = assignment[pos]
                state.currentAssignment[pos] = value

            # Calculate cost and build windowCounts
            let nWindows = max(0, state.sortedPositions.len - state.windowSize + 1)
            state.windowCounts = newSeq[int](nWindows)
            for i in 0..<nWindows:
                var count = 0
                for j in 0..<state.windowSize:
                    if assignment[state.sortedPositions[i + j]] in state.targetSet:
                        count += 1
                state.windowCounts[i] = count
                state.cost += windowViolation(count, state.minInSet, state.maxInSet)

        of ExpressionBased:
            # Store assignment for all positions that affect expressions
            for pos in state.expressionsAtPosition.keys:
                state.currentAssignment[pos] = assignment[pos]

            # Evaluate expressions and calculate cost
            if state.expressions.len >= state.windowSize:
                for i in 0..(state.expressions.len - state.windowSize):
                    var window = newSeq[T](state.windowSize)
                    for j in 0..<state.windowSize:
                        window[j] = state.expressions[i + j].evaluate(state.currentAssignment)
                    state.cost += getWindowViolation(state, window)

proc updatePosition*[T](state: SequenceConstraint[T], position: int, newValue: T) =
    # State Update assigning newValue to position
    state.lastChangedPosition = position
    let oldValue = state.currentAssignment.getOrDefault(position, T(0))
    state.lastOldValue = oldValue
    state.lastNewValue = newValue
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue

                let posIdx = state.positionIndex.getOrDefault(position, -1)
                if posIdx >= 0:
                    let oldInSet = oldValue in state.targetSet
                    let newInSet = newValue in state.targetSet
                    state.lastChangeAffectedWindows = (oldInSet != newInSet)

                    if oldInSet != newInSet:
                        let countDelta = if newInSet: 1 else: -1
                        let nWindows = state.sortedPositions.len - state.windowSize + 1
                        let startW = max(0, posIdx - state.windowSize + 1)
                        let endW = min(posIdx, nWindows - 1)

                        for i in startW..endW:
                            let oldCount = state.windowCounts[i]
                            let newCount = oldCount + countDelta
                            state.cost -= windowViolation(oldCount, state.minInSet, state.maxInSet)
                            state.cost += windowViolation(newCount, state.minInSet, state.maxInSet)
                            state.windowCounts[i] = newCount
                    # else: no window counts change, cost stays the same

            of ExpressionBased:
                state.currentAssignment[position] = newValue
                state.lastChangeAffectedWindows = true  # conservative for expressions

                # Recalculate cost for all windows that are affected by this position change
                if position in state.expressionsAtPosition:
                    # Find all expressions affected by this position
                    for expIndex in state.expressionsAtPosition[position]:
                        # Find all windows that include this expression
                        let startWindow = max(0, expIndex - state.windowSize + 1)
                        let endWindow = min(expIndex, state.expressions.len - state.windowSize)

                        # Recalculate affected windows
                        for i in startWindow..endWindow:
                            # Calculate old window cost (with old value)
                            state.currentAssignment[position] = oldValue
                            var oldWindow = newSeq[T](state.windowSize)
                            for j in 0..<state.windowSize:
                                oldWindow[j] = state.expressions[i + j].evaluate(state.currentAssignment)
                            state.cost -= getWindowViolation(state, oldWindow)

                            # Calculate new window cost (with new value)
                            state.currentAssignment[position] = newValue
                            var newWindow = newSeq[T](state.windowSize)
                            for j in 0..<state.windowSize:
                                newWindow[j] = state.expressions[i + j].evaluate(state.currentAssignment)
                            state.cost += getWindowViolation(state, newWindow)
    else:
        state.lastChangeAffectedWindows = false

func simulateWindowChange[T](state: SequenceConstraint[T], position: int, oldValue, newValue: T): int =
    ## Helper function to simulate cost change when updating a position
    var delta = 0
    case state.evalMethod:
        of PositionBased:
            let oldInSet = oldValue in state.targetSet
            let newInSet = newValue in state.targetSet
            if oldInSet == newInSet:
                return 0  # No window counts change → delta is always 0

            let countDelta = if newInSet: 1 else: -1
            let posIdx = state.positionIndex.getOrDefault(position, -1)
            if posIdx >= 0:
                let nWindows = state.sortedPositions.len - state.windowSize + 1
                let startW = max(0, posIdx - state.windowSize + 1)
                let endW = min(posIdx, nWindows - 1)

                for i in startW..endW:
                    let oldCount = state.windowCounts[i]
                    let newCount = oldCount + countDelta
                    delta -= windowViolation(oldCount, state.minInSet, state.maxInSet)
                    delta += windowViolation(newCount, state.minInSet, state.maxInSet)

        of ExpressionBased:
            if position in state.expressionsAtPosition:
                # Save original value
                let originalValue = state.currentAssignment[position]

                for expIndex in state.expressionsAtPosition[position]:
                    # Find all windows that include this expression
                    let startWindow = max(0, expIndex - state.windowSize + 1)
                    let endWindow = min(expIndex, state.expressions.len - state.windowSize)

                    for i in startWindow..endWindow:
                        # Calculate old window cost
                        state.currentAssignment[position] = oldValue
                        var oldWindow = newSeq[T](state.windowSize)
                        for j in 0..<state.windowSize:
                            oldWindow[j] = state.expressions[i + j].evaluate(state.currentAssignment)
                        delta -= getWindowViolation(state, oldWindow)

                        # Calculate new window cost
                        state.currentAssignment[position] = newValue
                        var newWindow = newSeq[T](state.windowSize)
                        for j in 0..<state.windowSize:
                            newWindow[j] = state.expressions[i + j].evaluate(state.currentAssignment)
                        delta += getWindowViolation(state, newWindow)

                # Restore original value
                state.currentAssignment[position] = originalValue

    return delta

func moveDelta*[T](state: SequenceConstraint[T], position: int, oldValue, newValue: T): int =
    # Returns cost delta for changing position from oldValue to newValue
    return simulateWindowChange(state, position, oldValue, newValue)


proc getAffectedPositions*[T](state: SequenceConstraint[T]): PackedSet[int] =
    ## Returns positions affected by the last updatePosition call.
    ## Only positions sharing a window with lastChangedPosition need updates:
    ## positions within [posIndex - windowSize + 1, posIndex + windowSize - 1]
    ## in the sorted position list.
    if state.lastChangedPosition < 0:
        return state.positions

    # If the last change didn't affect any window counts, no neighbors need updating
    if not state.lastChangeAffectedWindows:
        return initPackedSet[int]()

    case state.evalMethod:
        of PositionBased:
            let posIndex = state.positionIndex.getOrDefault(state.lastChangedPosition, -1)
            if posIndex < 0:
                return state.positions

            let startIdx = max(0, posIndex - state.windowSize + 1)
            let endIdx = min(state.sortedPositions.len - 1, posIndex + state.windowSize - 1)

            result = initPackedSet[int]()
            for i in startIdx..endIdx:
                result.incl(state.sortedPositions[i])

        of ExpressionBased:
            # For expression-based, fall back to all positions
            return state.positions

proc getAffectedDomainValues*[T](state: SequenceConstraint[T], position: int): seq[T] =
    ## Returns domain values that need penalty recalculation.
    ## When window counts changed (target-set membership flipped), ALL values at
    ## neighbor positions need recalculation because the baseline window counts shifted.
    ## When window counts didn't change, nothing needs recalculation — but that case
    ## is already handled by getAffectedPositions returning empty.
    ## Return empty = "all values need recalculation" (the default).
    return @[]

