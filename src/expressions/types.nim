import std/[packedsets, tables]

################################################################################
# Base type definitions shared across expression modules
################################################################################

type
    UnaryOperation* = enum
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

    StateEvalMethod* = enum
        ExpressionBased,
        PositionBased

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

func evaluate*[T](expression: AlgebraicExpression[T], assignment: seq[T]|Table[int, T]): T {.inline.} =
    expression.node.evaluate(assignment)

################################################################################
# Helper Functions for Expression Analysis
################################################################################

func isAllRefs*[T](expressions: openArray[AlgebraicExpression[T]]): (bool, seq[int]) =
    ## Check if all expressions are simple reference nodes and return positions in order (preserves duplicates)
    var positions: seq[int] = @[]
    for exp in expressions:
        if exp.node.kind != RefNode:
            # Early return if we find a non-RefNode - no need to collect positions
            return (false, positions)
        positions.add(exp.node.position)
    return (true, positions)

proc buildExpressionPositionMap*[T](expressions: openArray[AlgebraicExpression[T]]): Table[int, seq[int]] =
    ## Builds a mapping from positions to expression indices that depend on them
    result = initTable[int, seq[int]]()
    for i, exp in expressions:
        for pos in exp.positions.items:
            if pos in result:
                result[pos].add(i)
            else:
                result[pos] = @[i]

################################################################################
# Deep copy for ExpressionNode and AlgebraicExpression
################################################################################

proc deepCopy*[T](node: ExpressionNode[T]): ExpressionNode[T] =
    ## Creates a deep copy of an ExpressionNode for thread-safe parallel processing
    case node.kind:
        of LiteralNode:
            # Literals are immutable - safe to create new instance
            result = ExpressionNode[T](kind: LiteralNode, value: node.value)
        of RefNode:
            # Position references are immutable - safe to create new instance
            result = ExpressionNode[T](kind: RefNode, position: node.position)
        of UnaryOpNode:
            # Recursively copy the target node
            result = ExpressionNode[T](
                kind: UnaryOpNode,
                unaryOp: node.unaryOp,
                target: node.target.deepCopy()
            )
        of BinaryOpNode:
            # Recursively copy both left and right nodes
            result = ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: node.binaryOp,
                left: node.left.deepCopy(),
                right: node.right.deepCopy()
            )

proc deepCopy*[T](expression: AlgebraicExpression[T]): AlgebraicExpression[T] =
    ## Creates a deep copy of an AlgebraicExpression for thread-safe parallel processing
    new(result)
    result.positions = expression.positions  # PackedSet is a value type, safe to copy
    result.node = expression.node.deepCopy()  # Deep copy the node structure
    result.linear = expression.linear
