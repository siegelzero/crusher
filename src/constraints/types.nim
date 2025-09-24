import std/[packedsets, tables]
import constraintNode, algebraic
# Import all constraint state types
import allDifferent, atleast, atmost, elementState, relationalConstraint, ordering, globalCardinality, multiknapsack, sequence

################################################################################
# Shared constraint type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentType,
        AtLeastType,
        AtMostType,
        ElementType,
        AlgebraicType,
        RelationalType,
        OrderingType,
        GlobalCardinalityType,
        MultiknapsackType,
        SequenceType,
        LogicalType

    # StatefulAlgebraicConstraint definition
    StatefulAlgebraicConstraint*[T] = ref object
        # Stateful Constraint backed by an Algebraic Constraint, where the current
        # assignment is saved, along with the cost.
        # This constraint form has state which is updated as the assignment changes.
        currentAssignment*: Table[int, T]
        cost*: int
        constraint*: AlgebraicConstraint[T]
        positions*: PackedSet[int]

    # Complete constraint type definitions
    LogicalConstraint*[T] = ref object
        cost*: int
        positions*: PackedSet[int]
        case isUnary*: bool
        of true:
            # Unary operation (like NOT)
            unaryOp*: UnaryRelation
            targetConstraint*: StatefulConstraint[T]
        of false:
            # Binary operation (like AND, OR, etc.)
            logicalOp*: LogicalOperation
            leftConstraint*: StatefulConstraint[T]
            rightConstraint*: StatefulConstraint[T]

    StatefulConstraint*[T] = ref object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of AtLeastType:
                atLeastState*: AtLeastConstraint[T]
            of AtMostType:
                atMostState*: AtMostConstraint[T]
            of ElementType:
                elementState*: ElementState[T]
            of AlgebraicType:
                algebraicState*: StatefulAlgebraicConstraint[T]
            of RelationalType:
                relationalState*: RelationalConstraint[T]
            of OrderingType:
                orderingState*: OrderingConstraint[T]
            of GlobalCardinalityType:
                globalCardinalityState*: GlobalCardinalityConstraint[T]
            of MultiknapsackType:
                multiknapsackState*: MultiknapsackConstraint[T]
            of SequenceType:
                sequenceState*: SequenceConstraint[T]
            of LogicalType:
                logicalState*: LogicalConstraint[T]