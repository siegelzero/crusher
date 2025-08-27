import std/tables

import ../expressions
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
        DivisibleBy,

    TernaryRelation* = enum
        Modulo,

    LogicalBinaryRelation* = enum
        And,
        Or

    NodeType* = enum
        UnaryRelNode,
        BinaryRelNode,
        TernaryRelNode,
        LogicalBinaryRelNode

    ConstraintNode*[T] = ref object
        case kind*: NodeType
            of UnaryRelNode:
                unaryRel*: UnaryRelation
                target*: ConstraintNode[T]
            of BinaryRelNode:
                binaryRel*: BinaryRelation
                left*, right*: ExpressionNode[T]
            of TernaryRelNode:
                ternaryRel*: TernaryRelation
                first*, second*, third*: ExpressionNode[T]
            of LogicalBinaryRelNode:
                logicalBinaryRel*: LogicalBinaryRelation
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
        of DivisibleBy:
            return right != 0 and left mod right == 0


func evaluate*[T](relation: TernaryRelation, first, second, third: T): bool =
    case relation:
        of Modulo:
            return second != 0 and (first - third) mod second == 0


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

        of TernaryRelNode:
            let first = node.first.evaluate(assignment)
            let second = node.second.evaluate(assignment)
            let third = node.third.evaluate(assignment)
            return node.ternaryRel.evaluate(first, second, third)

        of LogicalBinaryRelNode:
            let leftResult = node.leftConstraint.evaluate(assignment)
            let rightResult = node.rightConstraint.evaluate(assignment)
            case node.logicalBinaryRel:
                of And:
                    return leftResult and rightResult
                of Or:
                    return leftResult or rightResult


func penalty*[T](relation: BinaryRelation, left, right: T): T =
    return if relation.evaluate(left, right): return 0 else: 1


func penalty*[T](relation: TernaryRelation, first, second, third: T): T =
    return if relation.evaluate(first, second, third): return 0 else: 1


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

        of TernaryRelNode:
            let first = node.first.evaluate(assignment)
            let second = node.second.evaluate(assignment)
            let third = node.third.evaluate(assignment)
            return node.ternaryRel.penalty(first, second, third)

        of LogicalBinaryRelNode:
            let leftResult = node.leftConstraint.evaluate(assignment)
            let rightResult = node.rightConstraint.evaluate(assignment)
            case node.logicalBinaryRel:
                of And:
                    # AND penalty: 0 if both true, 1 if either false
                    return if leftResult and rightResult: 0 else: 1
                of Or:
                    # OR penalty: 0 if at least one true, 1 if both false
                    return if leftResult or rightResult: 0 else: 1
