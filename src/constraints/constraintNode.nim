import std/tables

import ../expressions/expressions
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
        CoPrime,

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

func evaluate*[T](relation: BinaryRelation, left, right: T): bool =
    # Evaluates the binary relation with inputs left, right
    case relation:
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
        of CoPrime:
            return gcd(left, right) == 1


func evaluate*[T](node: ConstraintNode[T], assignment: seq[T] | Table[Natural, T]): bool =
    case node.kind:
        of UnaryRelNode:
            let target = node.target.evaluate(assignment)
            case node.unaryRel:
                of Not:
                    return not target

        of BinaryRelNode:
            let left = node.left.evaluate(assignment)
            let right = node.right.evaluate(assignment)
            return node.binaryRel.evaluate(left, right)


func penalty*[T](relation: BinaryRelation, left, right: T): T =
    return if relation.evaluate(left, right): return 0 else: 1


proc penalty*[T](node: ConstraintNode[T], assignment: seq[T] | Table[Natural, T]): T =
    case node.kind:
        of UnaryRelNode:
            let target = node.target.evaluate(assignment)
            case node.unaryRel:
                of Not:
                    return if target: 1 else: 0

        of BinaryRelNode:
            let left = node.left.evaluate(assignment)
            let right = node.right.evaluate(assignment)
            return node.binaryRel.penalty(left, right)