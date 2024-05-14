import std/[packedsets, sequtils, tables]

import expressionNode

################################################################################
# Type definitions for AlgebraicExpression
################################################################################

type
    AlgebraicExpression*[T] = ref object
        positions*: PackedSet[int]
        node*: ExpressionNode[T]
        linear*: bool

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

################################################################################
# Unary Expression Operations
################################################################################

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
# AlgebraicExpression Evaluation
################################################################################

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

################################################################################
# LinearCombinationState Creation
################################################################################

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


################################################################################
# LinearCombinationState Initialization
################################################################################

func initialize*[T](state: LinearCombination[T], assignment: seq[T]) =
    var value: T = state.constant
    state.value = 0
    for pos in state.positions:
        value = assignment[pos]
        state.value += state.coefficient[pos]*value
        state.currentAssignment[pos] = value

################################################################################
# LinearCombinationState Updates
################################################################################

func updatePosition*[T](state: LinearCombination[T], position: int, newValue: T) {.inline.} =
    let oldValue = state.currentAssignment[position]
    state.value += state.coefficient[position]*(newValue - oldValue)
    state.currentAssignment[position] = newValue


func moveDelta*[T](state: LinearCombination[T], position: int, oldValue, newValue: T): int {.inline.} =
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