import ../expressions/expressionNode

################################################################################
# Type definitions
################################################################################

type
    UnaryRelation* = enum
        Not

    BinaryRelation* = enum
        EqualTo,
        NotEqualTo,
        GreaterThan,
        GreaterThanEq,
        LessThan,
        LessThanEq,
    
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
            let target = tree.target.evaluate(assignment)

            case tree.unaryRel:
                of Not:
                    return not target

        of BinaryRelNode:
            let left = tree.left.evaluate(assignment)
            let right = tree.right.evaluate(assignment)

            case tree.binaryRel:
                of EqualTo:
                    return left == right
                of NotEqualTo:
                    return left != right
                of GreaterThan:
                    return left > right
                of GreaterThanEq:
                    return left >= right
                of LessThan:
                    return left < right
                of LessThanEq:
                    return left <= right


func penalty*[T](tree: ConstraintNode[T], assignment: seq[T]): T {.inline.} =
    case tree.kind:
        of UnaryRelNode:
            let target = tree.target.evaluate(assignment)

            case tree.unaryRel:
                of Not:
                    return if target: 1 else: 0

        of BinaryRelNode:
            let left = tree.left.evaluate(assignment)
            let right = tree.right.evaluate(assignment)

            case tree.binaryRel:
                of EqualTo:
                    # return abs(left - right)
                    return if left == right: 0 else: 1
                of NotEqualTo:
                    return if left != right: 0 else: 1
                of GreaterThan:
                    return if left > right: 0 else: 1
                of GreaterThanEq:
                    return if left >= right: 0 else: 1
                of LessThan:
                    return if left < right: 0 else: 1
                of LessThanEq:
                    return if left <= right: 0 else: 1