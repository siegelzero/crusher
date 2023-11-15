import expressionTree

################################################################################
# Type definitions
################################################################################

type
    UnaryRelation* = enum
        Not

    BinaryRelation* = enum
        EqualTo,
        GreaterThan,
        GreaterThanEq,
        LessThan,
        LessThanEq,
        NotEqualTo
    
    NodeType* = enum
        UnaryRelNode,
        BinaryRelNode
    
    ConstraintNode*[T] = ref object
        case kind*: NodeType
            of UnaryRelNode:
                unaryRel*: UnaryRelation
                target*: ConstraintNode[T]
            of BinaryRelNode:
                binaryRel*: BinaryRelation
                left*, right*: ExpressionNode[T]

################################################################################
# Evaluation
################################################################################

func evaluate*[T](tree: ConstraintNode[T], assignment: seq[T]): bool {.inline.} =
    case tree.kind:
        of UnaryRelNode:
            case tree.unaryRel:
                of Not:
                    return not (evaluate[T](tree.target, assignment))
        of BinaryRelNode:
            case tree.binaryRel:
                of EqualTo:
                    return evaluate[T](tree.left, assignment) == evaluate[T](tree.right, assignment)
                of GreaterThan:
                    return evaluate[T](tree.left, assignment) > evaluate[T](tree.right, assignment)
                of GreaterThanEq:
                    return evaluate[T](tree.left, assignment) >= evaluate[T](tree.right, assignment)
                of LessThan:
                    return evaluate[T](tree.left, assignment) < evaluate[T](tree.right, assignment)
                of LessThanEq:
                    return evaluate[T](tree.left, assignment) <= evaluate[T](tree.right, assignment)
                of NotEqualTo:
                    return evaluate[T](tree.left, assignment) != evaluate[T](tree.right, assignment)


func penalty*[T](tree: ConstraintNode[T], assignment: seq[T]): T {.inline.} =
    case tree.kind:
        of UnaryRelNode:
            case tree.unaryRel:
                of Not:
                    return if evaluate[T](tree.target, assignment): 1 else: 0
        of BinaryRelNode:
            case tree.binaryRel:
                of EqualTo:
                    return abs(evaluate[T](tree.left, assignment) - evaluate[T](tree.right, assignment))
                of GreaterThan:
                    return if evaluate[T](tree.left, assignment) > evaluate[T](tree.right, assignment): 0 else: 1
                of GreaterThanEq:
                    return if evaluate[T](tree.left, assignment) >= evaluate[T](tree.right, assignment): 0 else: 1
                of LessThan:
                    return if evaluate[T](tree.left, assignment) < evaluate[T](tree.right, assignment): 0 else: 1
                of LessThanEq:
                    return if evaluate[T](tree.left, assignment) <= evaluate[T](tree.right, assignment): 0 else: 1
                of NotEqualTo:
                    return if evaluate[T](tree.left, assignment) != evaluate[T](tree.right, assignment): 0 else: 1