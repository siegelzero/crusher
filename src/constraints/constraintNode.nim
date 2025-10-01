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

    BooleanOperation* = enum
        And,
        Or,
        Xor,
        Implies,
        Iff

    NodeType* = enum
        UnaryRelNode,
        BinaryRelNode,
        BooleanNode

    ConstraintNode*[T] = ref object
        case kind*: NodeType
            of UnaryRelNode:
                unaryRel*: UnaryRelation
                target*: ConstraintNode[T]
            of BinaryRelNode:
                binaryRel*: BinaryRelation
                left*, right*: ExpressionNode[T]
            of BooleanNode:
                booleanOp*: BooleanOperation
                leftConstraint*, rightConstraint*: ConstraintNode[T]

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


func evaluate*[T](node: ConstraintNode[T], assignment: seq[T] | Table[int, T]): bool =
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

        of BooleanNode:
            let left = node.leftConstraint.evaluate(assignment)
            let right = node.rightConstraint.evaluate(assignment)
            case node.booleanOp:
                of And:
                    return left and right
                of Or:
                    return left or right
                of Xor:
                    return left != right
                of Implies:
                    return (not left) or right
                of Iff:
                    return left == right


func penalty*[T](relation: BinaryRelation, left, right: T): T =
    return if relation.evaluate(left, right): return 0 else: 1


proc penalty*[T](node: ConstraintNode[T], assignment: seq[T] | Table[int, T]): T =
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

        of BooleanNode:
            let leftPenalty = node.leftConstraint.penalty(assignment)
            let rightPenalty = node.rightConstraint.penalty(assignment)
            case node.booleanOp:
                of And:
                    # Both must be satisfied
                    return leftPenalty + rightPenalty
                of Or:
                    # At least one must be satisfied
                    return min(leftPenalty, rightPenalty)
                of Xor:
                    # Exactly one must be satisfied
                    return if (leftPenalty == 0) != (rightPenalty == 0): 0 else: 1
                of Implies:
                    # If left then right
                    return if leftPenalty == 0 and rightPenalty > 0: 1 else: 0
                of Iff:
                    # Both or neither
                    return if (leftPenalty == 0) == (rightPenalty == 0): 0 else: 1