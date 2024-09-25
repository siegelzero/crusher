import std/tables

import ../expressions/expressionNode
import ../utils

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
        CommonFactor,

    NodeType* = enum
        UnaryRelNode,
        BinaryRelNode

    ConstraintNode*[T] {.acyclic.} = ref object
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

func evaluate*[T](node: ConstraintNode[T], assignment: seq[T] | Table[int, T]): bool {.inline.} =
    case node.kind:
        of UnaryRelNode:
            let target = node.target.evaluate(assignment)

            case node.unaryRel:
                of Not:
                    return not target

        of BinaryRelNode:
            let left = node.left.evaluate(assignment)
            let right = node.right.evaluate(assignment)

            case node.binaryRel:
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
                of CommonFactor:
                    return gcd(left, right) > 1



proc penalty*[T](node: ConstraintNode[T], assignment: seq[T] | Table[int, T]): T {.inline.} =
    # echo "node kind: ", node.kind
    case node.kind:
        of UnaryRelNode:
            let target = node.target.evaluate(assignment)

            case node.unaryRel:
                of Not:
                    return if target: 1 else: 0

        of BinaryRelNode:
            let left = node.left.evaluate(assignment)
            let right = node.right.evaluate(assignment)

            case node.binaryRel:
                of EqualTo:
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
                of CommonFactor:
                    return if gcd(left, right) > 1: 0 else: 1