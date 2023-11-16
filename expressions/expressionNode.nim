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
            let target = tree.target.evaluate(assignment)

            case tree.unaryOp:
                of AbsoluteValue:
                    return abs(target)
                of Negation:
                    return -target

        of BinaryOpNode:
            let
                left = tree.left.evaluate(assignment)
                right = tree.right.evaluate(assignment)

            case tree.binaryOp:
                of Addition:
                    return left + right
                of Subtraction:
                    return left - right
                of Multiplication:
                    return left * right
