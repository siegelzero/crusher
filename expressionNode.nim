################################################################################
# Type definitions
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

################################################################################
# Evaluation
################################################################################

func evaluate*[T](tree: ExpressionNode[T], assignment: seq[T]): T {.inline.} =
    case tree.kind:
        of LiteralNode:
            return tree.value
        of RefNode:
            return assignment[tree.position]
        of UnaryOpNode:
            case tree.unaryOp:
                of AbsoluteValue:
                    return abs(evaluate[T](tree.target, assignment))
                of Negation:
                    return -evaluate[T](tree.target, assignment)
        of BinaryOpNode:
            case tree.binaryOp:
                of Addition:
                    return evaluate[T](tree.left, assignment) + evaluate[T](tree.right, assignment)
                of Subtraction:
                    return evaluate[T](tree.left, assignment) - evaluate[T](tree.right, assignment)
                of Multiplication:
                    return evaluate[T](tree.left, assignment) * evaluate[T](tree.right, assignment)
