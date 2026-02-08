import std/[packedsets, tables]
import constraintNode, algebraic
# Import all constraint state types
import allDifferent, atleast, atmost, elementState, relationalConstraint, ordering, globalCardinality, multiknapsack, sequence, cumulative, geost, irdcs, circuit

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
        BooleanType,
        CumulativeType,
        GeostType,
        IrdcsType,
        CircuitType

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
    BooleanConstraint*[T] = ref object
        cost*: int
        positions*: PackedSet[int]
        case isUnary*: bool
        of true:
            # Unary operation (like NOT)
            unaryOp*: UnaryRelation
            targetConstraint*: StatefulConstraint[T]
            cachedTargetPenalty*: int  # Cache target constraint penalty
        of false:
            # Binary operation (like AND, OR, etc.)
            booleanOp*: BooleanOperation
            leftConstraint*: StatefulConstraint[T]
            rightConstraint*: StatefulConstraint[T]
            cachedLeftPenalty*: int   # Cache left constraint penalty
            cachedRightPenalty*: int  # Cache right constraint penalty

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
            of BooleanType:
                booleanState*: BooleanConstraint[T]
            of CumulativeType:
                cumulativeState*: CumulativeConstraint[T]
            of GeostType:
                geostState*: GeostConstraint[T]
            of IrdcsType:
                irdcsState*: IrdcsConstraint[T]
            of CircuitType:
                circuitState*: CircuitConstraint[T]