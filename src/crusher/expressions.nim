import std/[packedsets, tables, algorithm]

################################################################################
# Type definitions for ExpressionNode
################################################################################

type
    UnaryOperation = enum
        Negation,
        AbsoluteValue

    BinaryOperation* = enum
        Addition,
        Subtraction,
        Multiplication

    NodeType* = enum
        LiteralNode,
        RefNode,
        UnaryOpNode,
        BinaryOpNode

    ExpressionNode*[T] = ref object
        case kind*: NodeType
            of LiteralNode:
                value*: T
            of RefNode:
                position*: int
            of UnaryOpNode:
                unaryOp*: UnaryOperation
                target*: ExpressionNode[T]
            of BinaryOpNode:
                binaryOp*: BinaryOperation
                left*, right*: ExpressionNode[T]

    AlgebraicExpression*[T] = ref object
        positions*: PackedSet[int]
        node*: ExpressionNode[T]
        linear*: bool

################################################################################
# Evaluation
################################################################################

func evaluate*[T](node: ExpressionNode[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    case node.kind:
        of LiteralNode:
            return node.value
        of RefNode:
            return assignment[node.position]
        of UnaryOpNode:
            let target = node.target.evaluate(assignment)

            case node.unaryOp:
                of AbsoluteValue:
                    return abs(target)
                of Negation:
                    return -target

        of BinaryOpNode:
            let left = node.left.evaluate(assignment)
            let right = node.right.evaluate(assignment)

            case node.binaryOp:
                of Addition:
                    return left + right
                of Subtraction:
                    return left - right
                of Multiplication:
                    return left * right


func evaluate*[T](expression: AlgebraicExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    expression.node.evaluate(assignment)

################################################################################
# AlgebraicExpression Creation
################################################################################

func init*[T](expression: AlgebraicExpression[T],
              positions: PackedSet[T],
              node: ExpressionNode[T],
              linear: bool) =
    expression.positions = positions
    expression.node = node
    expression.linear = linear

func newAlgebraicExpression*[T](positions: PackedSet[T],
                                node: ExpressionNode[T],
                                linear: bool): AlgebraicExpression[T] =
    new(result)
    result.init(positions, node, linear)

# Unary Expression Operations

func `-`*[T](expression: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} = -1*expression

################################################################################
# Binary (Expression, Expression) Operations
################################################################################

template ExpExpOp(op, opref: untyped) =
    func `op`*[T](left, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
        let linear = case opref:
            of Addition:
                left.linear and right.linear
            of Subtraction:
                left.linear and right.linear
            of Multiplication:
                (left.linear and right.positions.len == 0) or (left.positions.len == 0 and right.linear)

        newAlgebraicExpression[T](
            positions=left.positions + right.positions,
            node=ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: left.node,
                right: right.node
            ),
            linear=linear
        )

ExpExpOp(`+`, Addition)
ExpExpOp(`*`, Multiplication)
ExpExpOp(`-`, Subtraction)

################################################################################
# Binary (Expression, Value) Operations
################################################################################

template ExpValOp(op, opref: untyped) =
    func `op`*[T](left: AlgebraicExpression[T], right: T): AlgebraicExpression[T] {.inline.} =
        newAlgebraicExpression[T](
            positions=left.positions,
            node=ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: left.node,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            ),
            linear=left.linear
        )

    func `op`*[T](left: T, right: AlgebraicExpression[T]): AlgebraicExpression[T] {.inline.} =
        newAlgebraicExpression[T](
            positions=right.positions,
            node=ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: opref,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.node
            ),
            linear=right.linear
        )

ExpValOp(`+`, Addition)
ExpValOp(`*`, Multiplication)
ExpValOp(`-`, Subtraction)

################################################################################
# Type definitions for LinearCombination
################################################################################

type
    LinearCombination*[T] = ref object
        value*: T
        constant*: T
        positions*: PackedSet[int]
        coefficient*: Table[int, T]
        currentAssignment*: Table[int, T]

# LinearCombinationState Creation

func init*[T](state: LinearCombination[T], positions: openArray[T]) =
    state.value = 0
    state.constant = 0
    state.positions = toPackedSet[int](positions)
    state.coefficient = initTable[int, T]()
    state.currentAssignment = initTable[int, T]()

    for pos in positions:
        state.coefficient[pos] = 1

func init*[T](state: LinearCombination[T], coefficients: Table[int, T], constant: T) =
    state.value = constant
    state.constant = constant
    state.positions = initPackedSet[int]()
    state.coefficient = initTable[int, T]()
    state.currentAssignment = initTable[int, T]()

    for pos, coeff in coefficients.pairs:
        state.positions.incl(pos)
        state.coefficient[pos] = coeff

func newLinearCombination*[T](positions: openArray[int]): LinearCombination[T] =
    new(result)
    result.init(positions)

func newLinearCombination*[T](coefficients: Table[int, T], constant: T = 0): LinearCombination[T] =
    new(result)
    result.init(coefficients, constant)

# LinearCombinationState Initialization

func initialize*[T](state: LinearCombination[T], assignment: seq[T]) =
    # Initizialize the Linear Combination with the given assignment, and updates the value.
    var value: T = state.constant
    state.value = 0
    for pos in state.positions:
        value = assignment[pos]
        state.value += state.coefficient[pos]*value
        state.currentAssignment[pos] = value

func evaluate*[T](expression: LinearCombination[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    # Computes the value of the Linear Combination given the variable assignment.
    for pos in expression.positions:
        result += expression.coefficient[pos]*assignment[pos]

func `$`*[T](state: LinearCombination[T]): string = $(state.value)

# LinearCombinationState Updates

func updatePosition*[T](state: LinearCombination[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    let oldValue = state.currentAssignment[position]
    state.value += state.coefficient[position]*(newValue - oldValue)
    state.currentAssignment[position] = newValue

func moveDelta*[T](state: LinearCombination[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns the change in value obtained by reassigning position from oldValue to newValue.
    state.coefficient[position]*(newValue - oldValue)

proc deepCopy*[T](state: LinearCombination[T]): LinearCombination[T] =
    # Creates a deep copy of a LinearCombination for thread-safe parallel processing
    new(result)
    result.value = state.value
    result.constant = state.constant
    result.positions = state.positions  # PackedSet is a value type, safe to copy
    result.coefficient = state.coefficient  # Table is a value type, safe to copy
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy

func linearize*[T](expression: AlgebraicExpression[T]): LinearCombination[T] =
    # Converts linear expression to a LinearCombination
    var constant: T
    var coefficients, assignment: Table[int, T]
    # evaluate with all variables zero to get constant coefficient
    for pos in expression.positions:
        assignment[pos] = 0

    constant = expression.evaluate(assignment)
    # extract each coefficient
    for pos in expression.positions:
        assignment[pos] = 1
        coefficients[pos] = expression.evaluate(assignment) - constant
        assignment[pos] = 0

    return newLinearCombination[T](coefficients, constant)

################################################################################
# Type definitions for MinExpression
################################################################################

type
    MinEvalMethod = enum
        PositionBased,
        ExpressionBased

    MinExpression*[T] = ref object
        value*: T
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        case evalMethod*: MinEvalMethod
            of PositionBased:
                discard  # positions and currentAssignment are sufficient
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]  # position -> list of expression indices

# MinExpression creation

func newMinExpression*[T](positions: openArray[int]): MinExpression[T] =
    result = MinExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T]()
    )

func newMinExpression*[T](expressions: seq[AlgebraicExpression[T]]): MinExpression[T] =
    var expressionsAtPos = initTable[int, seq[int]]()
    var allPositions = initPackedSet[int]()

    # Collect all positions involved in the expressions
    for i, exp in expressions:
        allPositions.incl(exp.positions)
        # Map each position to which expressions depend on it
        for pos in exp.positions:
            if pos notin expressionsAtPos:
                expressionsAtPos[pos] = @[]
            expressionsAtPos[pos].add(i)

    result = MinExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[int, T](),
        expressions: expressions,
        expressionsAtPosition: expressionsAtPos
    )

# MinExpression initialization

func initialize*[T](state: MinExpression[T], assignment: seq[T]) =
    # Initialize the MinExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]

    var minValue: T = high(T)
    case state.evalMethod:
        of PositionBased:
            # For position-based: minimum of variable values directly
            for pos in state.positions:
                minValue = min(minValue, assignment[pos])
        of ExpressionBased:
            # For expression-based: minimum of expression evaluations
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                minValue = min(minValue, expValue)

    state.value = minValue

func evaluate*[T](state: MinExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var minValue: T = high(T)
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                minValue = min(minValue, assignment[pos])
        of ExpressionBased:
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                minValue = min(minValue, expValue)
    return minValue

func `$`*[T](state: MinExpression[T]): string = $(state.value)

# MinExpression updates

func updatePosition*[T](state: MinExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    let oldValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue

    case state.evalMethod:
        of PositionBased:
            # For position-based: use smart updating logic
            if newValue < state.value:
                # New value is smaller than current min, so it becomes the new min
                state.value = newValue
            elif oldValue == state.value and newValue > oldValue:
                # We're replacing the current minimum with a larger value
                # Need to find the new minimum among all values
                var minValue: T = high(T)
                for val in state.currentAssignment.values:
                    if val < minValue:
                        minValue = val
                state.value = minValue
            # Otherwise, the minimum doesn't change

        of ExpressionBased:
            # For expression-based: need to recalculate affected expressions
            # This is less efficient but more general
            var minValue: T = high(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(state.currentAssignment)
                minValue = min(minValue, expValue)
            state.value = minValue

func moveDelta*[T](state: MinExpression[T], position: int, oldValue, newValue: T): T {.inline.} =
    # Returns the change in minimum value obtained by reassigning position from oldValue to newValue.
    let currentMin = state.value

    case state.evalMethod:
        of PositionBased:
            # Use optimized logic for position-based
            if newValue < currentMin:
                # New value becomes the minimum
                return newValue - currentMin
            elif oldValue == currentMin and newValue > oldValue:
                # We're changing the current minimum to a larger value
                # Need to find what the new minimum would be among remaining values
                var newMin: T = high(T)
                for pos in state.positions:
                    let val = if pos == position: newValue else: state.currentAssignment[pos]
                    if val < newMin:
                        newMin = val
                return newMin - currentMin
            else:
                # Minimum doesn't change
                return 0

        of ExpressionBased:
            # For expression-based: compute new minimum by evaluating all expressions
            var tempAssignment = state.currentAssignment
            tempAssignment[position] = newValue

            var newMin: T = high(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(tempAssignment)
                newMin = min(newMin, expValue)

            return newMin - currentMin

proc deepCopy*[T](state: MinExpression[T]): MinExpression[T] =
    # Creates a deep copy of a MinExpression for thread-safe parallel processing
    new(result)
    result.value = state.value
    result.positions = state.positions  # PackedSet is a value type, safe to copy
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy
    result.evalMethod = state.evalMethod

    case state.evalMethod:
        of PositionBased:
            # All fields already copied - no additional mutable state
            discard
        of ExpressionBased:
            result.expressions = state.expressions  # seq[AlgebraicExpression] should be immutable
            result.expressionsAtPosition = state.expressionsAtPosition  # Table is a value type, safe to copy

################################################################################
# Type definitions for MaxExpression
################################################################################

type
    MaxEvalMethod = enum
        PositionBased,
        ExpressionBased

    MaxExpression*[T] = ref object
        value*: T
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        case evalMethod*: MaxEvalMethod
            of PositionBased:
                discard  # positions and currentAssignment are sufficient
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]  # position -> list of expression indices

# MaxExpression creation

func newMaxExpression*[T](positions: openArray[int]): MaxExpression[T] =
    result = MaxExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T]()
    )

func newMaxExpression*[T](expressions: seq[AlgebraicExpression[T]]): MaxExpression[T] =  
    var expressionsAtPos = initTable[int, seq[int]]()
    var allPositions = initPackedSet[int]()

    # Collect all positions involved in the expressions
    for i, exp in expressions:
        allPositions.incl(exp.positions)
        # Map each position to which expressions depend on it
        for pos in exp.positions:
            if pos notin expressionsAtPos:
                expressionsAtPos[pos] = @[]
            expressionsAtPos[pos].add(i)

    result = MaxExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[int, T](),
        expressions: expressions,
        expressionsAtPosition: expressionsAtPos
    )

# MaxExpression initialization

func initialize*[T](state: MaxExpression[T], assignment: seq[T]) =
    # Initialize the MaxExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]

    var maxValue: T = low(T)
    case state.evalMethod:
        of PositionBased:
            # For position-based: maximum of variable values directly
            for pos in state.positions:
                maxValue = max(maxValue, assignment[pos])
        of ExpressionBased:
            # For expression-based: maximum of expression evaluations
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                maxValue = max(maxValue, expValue)

    state.value = maxValue

func evaluate*[T](state: MaxExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var maxValue: T = low(T)
    case state.evalMethod:
        of PositionBased:
            for pos in state.positions:
                maxValue = max(maxValue, assignment[pos])
        of ExpressionBased:
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                maxValue = max(maxValue, expValue)
    return maxValue

func `$`*[T](state: MaxExpression[T]): string = $(state.value)

# MaxExpression updates

func updatePosition*[T](state: MaxExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    let oldValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue

    case state.evalMethod:
        of PositionBased:
            # For position-based: use smart updating logic
            if newValue > state.value:
                # New value is larger than current max, so it becomes the new max
                state.value = newValue
            elif oldValue == state.value and newValue < oldValue:
                # We're replacing the current maximum with a smaller value
                # Need to find the new maximum among all values
                var maxValue: T = low(T)
                for val in state.currentAssignment.values:
                    if val > maxValue:
                        maxValue = val
                state.value = maxValue
            # Otherwise, the maximum doesn't change

        of ExpressionBased:
            # For expression-based: need to recalculate affected expressions
            # This is less efficient but more general
            var maxValue: T = low(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(state.currentAssignment)
                maxValue = max(maxValue, expValue)
            state.value = maxValue

func moveDelta*[T](state: MaxExpression[T], position: int, oldValue, newValue: T): T {.inline.} =
    # Returns the change in maximum value obtained by reassigning position from oldValue to newValue.
    let currentMax = state.value

    case state.evalMethod:
        of PositionBased:
            # Use optimized logic for position-based
            if newValue > currentMax:
                # New value becomes the maximum
                return newValue - currentMax
            elif oldValue == currentMax and newValue < oldValue:
                # We're changing the current maximum to a smaller value
                # Need to find what the new maximum would be among remaining values
                var newMax: T = low(T)
                for pos in state.positions:
                    let val = if pos == position: newValue else: state.currentAssignment[pos]
                    if val > newMax:
                        newMax = val
                return newMax - currentMax
            else:
                # Maximum doesn't change
                return 0

        of ExpressionBased:
            # For expression-based: compute new maximum by evaluating all expressions
            var tempAssignment = state.currentAssignment
            tempAssignment[position] = newValue

            var newMax: T = low(T)
            for exp in state.expressions:
                let expValue = exp.evaluate(tempAssignment)
                newMax = max(newMax, expValue)

            return newMax - currentMax

proc deepCopy*[T](state: MaxExpression[T]): MaxExpression[T] =
    # Creates a deep copy of a MaxExpression for thread-safe parallel processing
    new(result)
    result.value = state.value
    result.positions = state.positions  # PackedSet is a value type, safe to copy
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy
    result.evalMethod = state.evalMethod

    case state.evalMethod:
        of PositionBased:
            # All fields already copied - no additional mutable state
            discard
        of ExpressionBased:
            result.expressions = state.expressions  # seq[AlgebraicExpression] should be immutable
            result.expressionsAtPosition = state.expressionsAtPosition  # Table is a value type, safe to copy

################################################################################
# Type definitions for SumExpression
################################################################################

type
    SumEvalMethod = enum
        PositionBased,
        ExpressionBased

    SumExpression*[T] = ref object
        value*: T
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]
        case evalMethod*: SumEvalMethod
            of PositionBased:
                linearComb*: LinearCombination[T]  # Reuse existing efficient implementation
            of ExpressionBased:
                expressions*: seq[AlgebraicExpression[T]]
                expressionsAtPosition*: Table[int, seq[int]]  # position -> list of expression indices

# SumExpression creation

func newSumExpression*[T](positions: openArray[int]): SumExpression[T] =
    result = SumExpression[T](
        evalMethod: PositionBased,
        value: 0,
        positions: toPackedSet[int](positions),
        currentAssignment: initTable[int, T](),
        linearComb: newLinearCombination[T](positions)
    )

func newSumExpression*[T](expressions: seq[AlgebraicExpression[T]]): SumExpression[T] =  
    var expressionsAtPos = initTable[int, seq[int]]()
    var allPositions = initPackedSet[int]()

    # Collect all positions involved in the expressions
    for i, exp in expressions:
        allPositions.incl(exp.positions)
        # Map each position to which expressions depend on it
        for pos in exp.positions:
            if pos notin expressionsAtPos:
                expressionsAtPos[pos] = @[]
            expressionsAtPos[pos].add(i)

    result = SumExpression[T](
        evalMethod: ExpressionBased,
        value: 0,
        positions: allPositions,
        currentAssignment: initTable[int, T](),
        expressions: expressions,
        expressionsAtPosition: expressionsAtPos
    )

# SumExpression initialization

func initialize*[T](state: SumExpression[T], assignment: seq[T]) =
    # Initialize the SumExpression with the given assignment, and updates the value.
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]

    case state.evalMethod:
        of PositionBased:
            # Use efficient LinearCombination
            state.linearComb.initialize(assignment)
            state.value = state.linearComb.value
        of ExpressionBased:
            # Sum all expression evaluations
            state.value = 0
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                state.value += expValue

func evaluate*[T](state: SumExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    case state.evalMethod:
        of PositionBased:
            return state.linearComb.evaluate(assignment)
        of ExpressionBased:
            var sumValue: T = 0
            for exp in state.expressions:
                let expValue = exp.evaluate(assignment)
                sumValue += expValue
            return sumValue

func `$`*[T](state: SumExpression[T]): string = $(state.value)

# SumExpression updates

func updatePosition*[T](state: SumExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    case state.evalMethod:
        of PositionBased:
            # Use efficient LinearCombination update
            state.linearComb.updatePosition(position, newValue)
            state.value = state.linearComb.value

        of ExpressionBased:
            # Only update expressions affected by the changed position
            if position in state.expressionsAtPosition:
                let oldValue = state.currentAssignment[position]
                state.currentAssignment[position] = newValue

                # Calculate delta for each affected expression and apply to sum
                for expIndex in state.expressionsAtPosition[position]:
                    let exp = state.expressions[expIndex]
                    let oldExpValue = exp.evaluate(state.currentAssignment)
                    # Temporarily set back to old value for comparison
                    state.currentAssignment[position] = oldValue
                    let oldExpValueActual = exp.evaluate(state.currentAssignment)
                    # Set back to new value
                    state.currentAssignment[position] = newValue

                    state.value += (oldExpValue - oldExpValueActual)
            else:
                # Position doesn't affect any expressions, just update assignment
                state.currentAssignment[position] = newValue

func moveDelta*[T](state: SumExpression[T], position: int, oldValue, newValue: T): T {.inline.} =
    # Returns the change in sum value obtained by reassigning position from oldValue to newValue.
    case state.evalMethod:
        of PositionBased:
            # Use efficient LinearCombination delta calculation
            return state.linearComb.moveDelta(position, oldValue, newValue)

        of ExpressionBased:
            # Only recalculate expressions that depend on the changed position
            var totalDelta: T = 0

            if position in state.expressionsAtPosition:
                var tempAssignment = state.currentAssignment
                tempAssignment[position] = newValue

                # Calculate delta for each affected expression
                for expIndex in state.expressionsAtPosition[position]:
                    let exp = state.expressions[expIndex]
                    let oldExpValue = exp.evaluate(state.currentAssignment)
                    let newExpValue = exp.evaluate(tempAssignment)
                    totalDelta += (newExpValue - oldExpValue)

            return totalDelta

################################################################################
# Type definitions for CumulativeExpression
################################################################################

type
    TaskParam*[T] = object
        case isConstant*: bool
        of true:
            constantValue*: T
        of false:
            variablePosition*: int

    TimePoint[T] = object
        time*: T
        deltaChange*: T  # Net resource change at this time (+demand at start, -demand at end)

    CumulativeExpression*[T] = ref object
        # Task parameters (positions or constants)
        startTimes*: seq[TaskParam[T]]
        durations*: seq[TaskParam[T]]
        demands*: seq[TaskParam[T]]
        capacity*: TaskParam[T]  # Can be variable or constant
        
        # Efficient state tracking
        timePoints*: seq[TimePoint[T]]  # Sorted time points with resource changes
        currentMaxUsage*: T             # Current peak resource usage
        violatingTimePoint*: int        # Index of first time point exceeding capacity, -1 if none
        currentAssignment*: Table[int, T]
        positions*: PackedSet[int]      # All variable positions involved

# CumulativeExpression creation

func newTaskParam*[T](constantValue: T): TaskParam[T] =
    TaskParam[T](isConstant: true, constantValue: constantValue)

func newTaskParam*[T](variablePosition: int): TaskParam[T] =
    TaskParam[T](isConstant: false, variablePosition: variablePosition)

func newCumulativeExpression*[T](startTimes, durations, demands: seq[TaskParam[T]], capacity: TaskParam[T]): CumulativeExpression[T] =
    new(result)
    result.startTimes = startTimes
    result.durations = durations
    result.demands = demands
    result.capacity = capacity
    result.timePoints = @[]
    result.currentMaxUsage = T(0)
    result.violatingTimePoint = -1
    result.currentAssignment = initTable[int, T]()
    result.positions = initPackedSet[int]()
    
    # Collect all variable positions
    for param in startTimes:
        if not param.isConstant:
            result.positions.incl(param.variablePosition)
    for param in durations:
        if not param.isConstant:
            result.positions.incl(param.variablePosition)
    for param in demands:
        if not param.isConstant:
            result.positions.incl(param.variablePosition)
    if not capacity.isConstant:
        result.positions.incl(capacity.variablePosition)

# CumulativeExpression utility functions

func getTaskParam*[T](param: TaskParam[T], assignment: Table[int, T]): T {.inline.} =
    if param.isConstant:
        param.constantValue
    else:
        assignment[param.variablePosition]

func getTaskParam*[T](param: TaskParam[T], assignment: seq[T]): T {.inline.} =
    if param.isConstant:
        param.constantValue
    else:
        assignment[param.variablePosition]

# CumulativeExpression initialization

func initialize*[T](state: CumulativeExpression[T], assignment: seq[T]) =
    # Initialize assignments
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
    
    # Build time points from current assignment
    state.timePoints.setLen(0)
    
    for i in 0..<state.startTimes.len:
        let startTime = getTaskParam(state.startTimes[i], assignment)
        let duration = getTaskParam(state.durations[i], assignment)
        let demand = getTaskParam(state.demands[i], assignment)
        let endTime = startTime + duration
        
        # Add resource demand at start time
        var foundStart = false
        for tp in state.timePoints.mitems:
            if tp.time == startTime:
                tp.deltaChange += demand
                foundStart = true
                break
        if not foundStart:
            state.timePoints.add(TimePoint[T](time: startTime, deltaChange: demand))
        
        # Remove resource demand at end time
        var foundEnd = false
        for tp in state.timePoints.mitems:
            if tp.time == endTime:
                tp.deltaChange -= demand
                foundEnd = true
                break
        if not foundEnd:
            state.timePoints.add(TimePoint[T](time: endTime, deltaChange: -demand))
    
    # Sort time points by time
    state.timePoints.sort(proc(a, b: TimePoint[T]): int = cmp(a.time, b.time))
    
    # Calculate current max usage and find violations
    var currentUsage: T = T(0)
    state.currentMaxUsage = T(0)
    state.violatingTimePoint = -1
    let capacityValue = getTaskParam(state.capacity, assignment)
    
    for i, tp in state.timePoints:
        currentUsage += tp.deltaChange
        if currentUsage > state.currentMaxUsage:
            state.currentMaxUsage = currentUsage
        if state.violatingTimePoint == -1 and currentUsage > capacityValue:
            state.violatingTimePoint = i

func evaluate*[T](state: CumulativeExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    # Returns maximum resource usage across all time points
    var currentUsage: T = T(0)
    var maxUsage: T = T(0)
    
    # Rebuild time points for this assignment
    var tempTimePoints: seq[TimePoint[T]] = @[]
    
    for i in 0..<state.startTimes.len:
        let startTime = getTaskParam(state.startTimes[i], assignment)
        let duration = getTaskParam(state.durations[i], assignment)
        let demand = getTaskParam(state.demands[i], assignment)
        let endTime = startTime + duration
        
        # Add resource demand at start time
        var foundStart = false
        for tp in tempTimePoints.mitems:
            if tp.time == startTime:
                tp.deltaChange += demand
                foundStart = true
                break
        if not foundStart:
            tempTimePoints.add(TimePoint[T](time: startTime, deltaChange: demand))
        
        # Remove resource demand at end time
        var foundEnd = false
        for tp in tempTimePoints.mitems:
            if tp.time == endTime:
                tp.deltaChange -= demand
                foundEnd = true
                break
        if not foundEnd:
            tempTimePoints.add(TimePoint[T](time: endTime, deltaChange: -demand))
    
    # Sort time points by time
    tempTimePoints.sort(proc(a, b: TimePoint[T]): int = cmp(a.time, b.time))
    
    # Calculate max usage
    for tp in tempTimePoints:
        currentUsage += tp.deltaChange
        if currentUsage > maxUsage:
            maxUsage = currentUsage
    
    return maxUsage

func `$`*[T](state: CumulativeExpression[T]): string = "CumulativeExpr(maxUsage=" & $(state.currentMaxUsage) & ")"

# CumulativeExpression updates

func updatePosition*[T](state: CumulativeExpression[T], position: int, newValue: T) {.inline.} =
    # Update assignment and recalculate time points
    let oldValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue
    
    # For now, full recalculation (can be optimized later)
    state.initialize(state.currentAssignment.values.toSeq)

func moveDelta*[T](state: CumulativeExpression[T], position: int, oldValue, newValue: T): T {.inline.} =
    # Returns the change in maximum resource usage
    let oldMaxUsage = state.currentMaxUsage
    
    # Temporarily apply change
    let originalValue = state.currentAssignment[position]
    state.currentAssignment[position] = newValue
    
    # Recalculate (this is the part that can be heavily optimized)
    let newMaxUsage = state.evaluate(state.currentAssignment)
    
    # Restore original value
    state.currentAssignment[position] = originalValue
    
    return newMaxUsage - oldMaxUsage

proc deepCopy*[T](state: CumulativeExpression[T]): CumulativeExpression[T] =
    new(result)
    result.startTimes = state.startTimes  # TaskParam is a value type, safe to copy
    result.durations = state.durations
    result.demands = state.demands
    result.capacity = state.capacity
    result.timePoints = @[]
    for tp in state.timePoints:
        result.timePoints.add(tp)  # TimePoint is a value type, safe to copy
    result.currentMaxUsage = state.currentMaxUsage
    result.violatingTimePoint = state.violatingTimePoint
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy
    result.positions = state.positions  # PackedSet is a value type, safe to copy

################################################################################
# SumExpression creation helpers for constraint syntax
################################################################################

func sum*[T](expressions: seq[AlgebraicExpression[T]]): SumExpression[T] =
    # Check if all expressions are simple variable references (RefNodes)
    var allRefs = true
    var positions: seq[int] = @[]

    for exp in expressions:
        if exp.node.kind == RefNode:
            positions.add(exp.node.position)
        else:
            allRefs = false

    if allRefs:
        # Use efficient position-based approach if all expressions are simple variables
        return newSumExpression[T](positions)
    else:
        # Use general expression-based approach for complex expressions
        return newSumExpression[T](expressions)

proc deepCopy*[T](state: SumExpression[T]): SumExpression[T] =
    # Creates a deep copy of a SumExpression for thread-safe parallel processing
    new(result)
    result.value = state.value
    result.positions = state.positions  # PackedSet is a value type, safe to copy
    result.currentAssignment = state.currentAssignment  # Table is a value type, safe to copy
    result.evalMethod = state.evalMethod

    case state.evalMethod:
        of PositionBased:
            result.linearComb = state.linearComb.deepCopy()
        of ExpressionBased:
            result.expressions = state.expressions  # seq[AlgebraicExpression] should be immutable
            result.expressionsAtPosition = state.expressionsAtPosition  # Table is a value type, safe to copy
