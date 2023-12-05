import ../expressions/expressionNode

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

func penalty*[T](tree: ConstraintNode[T], assignment: seq[T]): T {.inline.} =
    case tree.kind:
        of UnaryRelNode:
            let target = tree.target.penalty(assignment)

            case tree.unaryRel:
                of Not:
                    return if target == 0: 1 else: 0

        of BinaryRelNode:
            let left = tree.left.evaluate(assignment)
            let right = tree.right.evaluate(assignment)

            case tree.binaryRel:
                of EqualTo:
                    return abs(left - right)
                of GreaterThan:
                    return if left > right: 0 else: 1
                of GreaterThanEq:
                    return if left >= right: 0 else: 1
                of LessThan:
                    return if left < right: 0 else: 1
                of LessThanEq:
                    return if left <= right: 0 else: 1