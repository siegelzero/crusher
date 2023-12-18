import std/[packedsets, tables]

import constraintNode
import ../expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    ConstraintType* = enum
        AlgebraicConstraint,
        AllDifferentConstraint 

    AllDifferentState*[T] = ref object
        positions: PackedSet[T]
        count*: Table[T, int]
        currentAssignment*: Table[int, T]
        cost*: int

    Constraint*[T] = object
        positions*: PackedSet[int]

        case scope*: ConstraintType
            of AlgebraicConstraint:
                node*: ConstraintNode[T]
            of AllDifferentConstraint:
                state*: AllDifferentState[T]

################################################################################
# Unary Constraint Relations
################################################################################

func `not`*[T](cons: Constraint[T]): Constraint[T] {.inline.} =
    if cons.node.kind == BinaryRelNode and cons.node.binaryRel == EqualTo:
        return Constraint[T](
            scope: AlgebraicConstraint,
            positions: cons.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: NotEqualTo,
                left: cons.node.left,
                right: cons.node.right
            )
        )
    else:
        return Constraint[T](
            scope: AlgebraicConstraint,
            positions: cons.positions,
            node: ConstraintNode[T](
                kind: UnaryRelNode,
                unaryRel: Not,
                target: cons.node
            )
        )

################################################################################
# Binary (Expression, Expression) Relations
################################################################################

template ExpExpRel(rel, relEnum: untyped) =
    func `rel`*[T](left, right: Expression[T]): Constraint[T] {.inline.} =
        Constraint[T](
            scope: AlgebraicConstraint,
            positions: left.positions + right.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.node,
                right: right.node
            )
        )

ExpExpRel(`==`, EqualTo)
ExpExpRel(`>`, GreaterThan)
ExpExpRel(`>=`, GreaterThanEq)
ExpExpRel(`<`, LessThan)
ExpExpRel(`<=`, LessThanEq)

################################################################################
# Binary (Expression, Value) Relations
################################################################################

template ExpValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: Expression[T], right: T): Constraint[T] {.inline.} =
        Constraint[T](
            scope: AlgebraicConstraint,
            positions: left.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: left.node,
                right: ExpressionNode[T](kind: LiteralNode, value: right)
            )
        )
    func `rel`*[T](left: T, right: Expression[T]): Constraint[T] {.inline.} =
        Constraint[T](
            scope: AlgebraicConstraint,
            positions: right.positions,
            node: ConstraintNode[T](
                kind: BinaryRelNode,
                binaryRel: relEnum,
                left: ExpressionNode[T](kind: LiteralNode, value: left),
                right: right.node
            )
        )

ExpValRel(`==`, EqualTo)
ExpValRel(`>`, GreaterThan)
ExpValRel(`>=`, GreaterThanEq)
ExpValRel(`<`, LessThan)
ExpValRel(`<=`, LessThanEq)

################################################################################
# Evaluation
################################################################################

func evaluate*[T](cons: Constraint[T], assignment: seq[T]): bool {.inline.} =
    cons.node.evaluate(assignment)

func penalty*[T](cons: Constraint[T], assignment: seq[T]): T {.inline.} =
    case cons.scope:
        of AlgebraicConstraint:
            return cons.node.penalty(assignment)
        of AllDifferentConstraint:
            return cons.state.cost

################################################################################
# AllDifferentState Methods
################################################################################

func init*[T](state: AllDifferentState[T], positions: openArray[T]) =
    state.cost = 0
    state.positions = toPackedSet[T](positions)
    state.count = initTable[T, int]()
    state.currentAssignment = initTable[int, T]()

func newAllDifferentState*[T](positions: openArray[T] ): AllDifferentState[T] =
    # Allocates and initializes new AllDifferentState[T]
    new(result)
    result.init(positions)

################################################################################
# AllDifferentState Methods
################################################################################

func allDifferentConstraint*[T](positions: openArray[T]): Constraint[T] =
    return Constraint[T](
        positions: toPackedSet[T](positions),
        scope: AllDifferentConstraint,
        state: newAllDifferentState[T](positions)
    )


proc initialize*[T](state: AllDifferentState[T], assignment: seq[T]) =
    var value: T
    for pos in state.positions:
        value = assignment[pos]
        if value in state.count:
            state.count[value] += 1
        else:
            state.count[value] = 1
        state.currentAssignment[pos] = value
    for value, count in state.count.pairs:
        state.cost += count - 1


proc updatePosition*[T](state: AllDifferentState[T], position: int, newValue: T) =
    let oldValue = state.currentAssignment[position]

    if oldValue != newValue:
        state.cost -= max(0, state.count.getOrDefault(oldValue) - 1)
        state.cost -= max(0, state.count.getOrDefault(newValue) - 1)

        state.currentAssignment[position] = newValue
        state.count[oldValue] -= 1

        if not (newValue in state.count):
            state.count[newValue] = 1
        else:
            state.count[newValue] += 1

        state.cost += max(0, state.count[oldValue] - 1)
        state.cost += max(0, state.count[newValue] - 1)

proc moveDelta*[T](state: AllDifferentState[T], position: int, oldValue, newValue: T): int =
    if oldvalue == newValue:
        return 0
    else:
        var
            delta = 0
            oldC = state.count.getOrDefault(oldValue)
            newC = state.count.getOrDefault(newValue)

        delta -= max(0, oldC - 1)
        delta -= max(0, newC - 1)
        oldC -= 1

        if newValue in state.count:
            newC += 1
        else:
            newC = 1

        delta += max(0, oldC - 1)
        delta += max(0, newC - 1)
        return delta