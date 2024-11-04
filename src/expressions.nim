import std/[packedsets, sequtils, tables]

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

# Evaluation

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

# AlgebraicExpression Creation

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

# Binary (Expression, Expression) Operations

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

# Binary (Expression, Value) Operations

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

# AlgebraicExpression Evaluation

func evaluate*[T](expression: AlgebraicExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    expression.node.evaluate(assignment)

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

func sum*[T](expressions: seq[AlgebraicExpression[T]]): LinearCombination[T] =
    var positions = toPackedSet[int]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    doAssert allRefs
    return newLinearCombination[T](toSeq[int](positions))

################################################################################
# Type definitions for MinExpression
################################################################################

type
    MinExpression*[T] = ref object
        value*: T
        positions*: PackedSet[int]
        currentAssignment*: Table[int, T]

# MinExpression creation

func init*[T](state: MinExpression[T], positions: openArray[T]) =
    state.minValue = 0
    state.positions = toPackedSet[int](positions)
    state.currentAssignment = initTable[int, T]()

func newMinExpression*[T](positions: openArray[int]): MinExpression[T] =
    new(result)
    result.init(positions)

# MinExpression initialization

func initialize*[T](state: MinExpression[T], assignment: seq[T]) =
    # Initizialize the MinExpression with the given assignment, and updates the value.
    var minValue: T = high(T)
    for pos in state.positions:
        state.currentAssignment[pos] = assignment[pos]
        minValue = min(minValue, assignment[pos])
    state.value = minValue

func evaluate*[T](state: MinExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    var minValue: T = high(T)
    for pos in state.positions:
        minValue = min(minValue, assignment[pos])
    return minValue

func `$`*[T](state: MinExpression[T]): string = $(state.minValue)

# MinExpression updates

func updatePosition*[T](state: MinExpression[T], position: int, newValue: T) {.inline.} =
    # Assigns the value newValue to the variable in the given position, updating state.
    state.currentAssignment[position] = newValue
    state.value = state.currentAssignment.values.min()

func moveDelta*[T](state: MinExpression[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns the change in value obtained by reassigning position from oldValue to newValue.
    if newValue >= state.value:
        return 0
    else:
        return state.value - newValue