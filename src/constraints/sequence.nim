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
        case evalMethod*: StateEvalMethod
            of PositionBased:
                positions*: PackedSet[int]
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]

################################################################################
# SequenceConstraint creation
################################################################################

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
    )

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
    )

################################################################################
# SequenceConstraint utility functions
################################################################################

func countInSet[T](values: openArray[T], targetSet: HashSet[T]): int {.inline.} =
    ## Counts how many values from the array are in the target set
    result = 0
    for value in values:
        if value in targetSet:
            result += 1

func getWindowViolation[T](state: SequenceConstraint[T], window: openArray[T]): int {.inline.} =
    ## Returns the violation cost for a single window
    let countInTargetSet = countInSet(window, state.targetSet)
    if countInTargetSet < state.minInSet:
        return state.minInSet - countInTargetSet
    elif countInTargetSet > state.maxInSet:
        return countInTargetSet - state.maxInSet
    else:
        return 0

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

            # Calculate cost by checking all consecutive windows
            let positionList = state.positions.toSeq().sorted()
            if positionList.len >= state.windowSize:
                for i in 0..(positionList.len - state.windowSize):
                    var window = newSeq[T](state.windowSize)
                    for j in 0..<state.windowSize:
                        window[j] = assignment[positionList[i + j]]
                    state.cost += getWindowViolation(state, window)

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
    let oldValue = state.currentAssignment.getOrDefault(position, T(0))
    if oldValue != newValue:
        case state.evalMethod:
            of PositionBased:
                state.currentAssignment[position] = newValue

                # Recalculate cost for all windows that include this position
                let positionList = state.positions.toSeq().sorted()
                let posIndex = positionList.find(position)
                if posIndex >= 0:
                    # Find all windows that include this position
                    let startWindow = max(0, posIndex - state.windowSize + 1)
                    let endWindow = min(posIndex, positionList.len - state.windowSize)

                    # Subtract old window costs and add new ones
                    for i in startWindow..endWindow:
                        # Calculate old window cost
                        var oldWindow = newSeq[T](state.windowSize)
                        for j in 0..<state.windowSize:
                            if positionList[i + j] == position:
                                oldWindow[j] = oldValue
                            else:
                                oldWindow[j] = state.currentAssignment[positionList[i + j]]
                        state.cost -= getWindowViolation(state, oldWindow)

                        # Calculate new window cost
                        var newWindow = newSeq[T](state.windowSize)
                        for j in 0..<state.windowSize:
                            newWindow[j] = state.currentAssignment[positionList[i + j]]
                        state.cost += getWindowViolation(state, newWindow)

            of ExpressionBased:
                state.currentAssignment[position] = newValue

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

func simulateWindowChange[T](state: SequenceConstraint[T], position: int, oldValue, newValue: T): int =
    ## Helper function to simulate cost change when updating a position
    var delta = 0
    case state.evalMethod:
        of PositionBased:
            let positionList = state.positions.toSeq().sorted()
            let posIndex = positionList.find(position)
            if posIndex >= 0:
                # Find all windows that include this position
                let startWindow = max(0, posIndex - state.windowSize + 1)
                let endWindow = min(posIndex, positionList.len - state.windowSize)

                for i in startWindow..endWindow:
                    # Calculate old window cost
                    var oldWindow = newSeq[T](state.windowSize)
                    for j in 0..<state.windowSize:
                        if positionList[i + j] == position:
                            oldWindow[j] = oldValue
                        else:
                            oldWindow[j] = state.currentAssignment[positionList[i + j]]
                    delta -= getWindowViolation(state, oldWindow)

                    # Calculate new window cost
                    var newWindow = newSeq[T](state.windowSize)
                    for j in 0..<state.windowSize:
                        if positionList[i + j] == position:
                            newWindow[j] = newValue
                        else:
                            newWindow[j] = state.currentAssignment[positionList[i + j]]
                    delta += getWindowViolation(state, newWindow)

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