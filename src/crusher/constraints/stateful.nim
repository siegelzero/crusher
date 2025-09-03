import std/[packedsets, sequtils, tables, sets]

import common
import algebraic, allDifferent, elementState, linear, minConstraint, maxConstraint, sumConstraint
import globalCardinality, regular
import constraintNode
import ../expressions

################################################################################
# Reified Linear Constraint Type
################################################################################

type
    ReifiedLinearConstraint*[T] = ref object
        linearComb*: LinearCombination[T]
        relation*: BinaryRelation
        rhs*: T
        boolPosition*: int  # Position of the boolean variable
        boolValue*: T       # Current value of the boolean variable
        cost*: int

################################################################################
# Type definitions
################################################################################

type
    StatefulConstraintType* = enum
        AllDifferentType,
        ElementConstraint,
        LinearType,
        AlgebraicType,
        ReifiedLinearType,
        MinType,
        MaxType,
        SumType,
        GlobalCardinalityType,
        RegularType

    StatefulConstraint*[T] = object
        positions*: PackedSet[int]
        case stateType*: StatefulConstraintType
            of AllDifferentType:
                allDifferentState*: AllDifferentConstraint[T]
            of ElementConstraint:
                elementState*: ElementState[T]
            of LinearType:
                linearConstraintState*: LinearConstraint[T]
            of AlgebraicType:
                algebraicConstraintState*: StatefulAlgebraicConstraint[T]
            of ReifiedLinearType:
                reifiedLinearState*: ReifiedLinearConstraint[T]
            of MinType:
                minConstraintState*: MinConstraint[T]
            of MaxType:
                maxConstraintState*: MaxConstraint[T]
            of SumType:
                sumConstraintState*: SumConstraint[T]
            of GlobalCardinalityType:
                globalCardinalityState*: GlobalCardinalityConstraint[T]
            of RegularType:
                regularState*: RegularConstraint[T]


func `$`*[T](constraint: StatefulConstraint[T]): string =
    case constraint.stateType:
        of AllDifferentType:
            return "AllDifferent Constraint"
        of ElementConstraint:
            return "Element Constraint"
        of LinearType:
            return constraint.linearConstraintState.cost
        of AlgebraicType:
            return "Algebraic Constraint"
        of ReifiedLinearType:
            return "Reified Linear Constraint"
        of MinType:
            return "Min Constraint"
        of MaxType:
            return "Max Constraint"
        of SumType:
            return "Sum Constraint"
        of GlobalCardinalityType:
            return "GlobalCardinality Constraint"
        of RegularType:
            return "Regular Constraint"

proc getConstraintTypeName*[T](constraint: StatefulConstraint[T]): string {.inline.} =
    ## Returns a human-readable name for the constraint type
    case constraint.stateType:
        of AllDifferentType: "AllDifferent"
        of ElementConstraint: "Element"
        of LinearType: "Linear"
        of AlgebraicType: "Algebraic"
        of ReifiedLinearType: "ReifiedLinear"
        of MinType: "Min"
        of MaxType: "Max"
        of SumType: "Sum"
        of GlobalCardinalityType: "GlobalCardinality"
        of RegularType: "Regular"

################################################################################
# Evaluation
################################################################################

proc penalty*[T](constraint: StatefulConstraint[T]): T {.inline.} =
    case constraint.stateType:
        of AllDifferentType:
            return constraint.allDifferentState.cost
        of ElementConstraint:
            return constraint.elementState.cost
        of LinearType:
            return constraint.linearConstraintState.cost
        of AlgebraicType:
            return constraint.algebraicConstraintState.cost
        of ReifiedLinearType:
            return constraint.reifiedLinearState.cost
        of MinType:
            return constraint.minConstraintState.cost
        of MaxType:
            return constraint.maxConstraintState.cost
        of SumType:
            return constraint.sumConstraintState.cost
        of GlobalCardinalityType:
            return constraint.globalCardinalityState.cost
        of RegularType:
            return constraint.regularState.getCost()

################################################################################
# Computed Constraints
################################################################################

template LCValRel(rel, relEnum: untyped) =
    func `rel`*[T](left: LinearCombination[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: LinearType,
            linearConstraintState: newLinearConstraint[T](left, relEnum, right)
        )

LCValRel(`==`, EqualTo)
LCValRel(`!=`, NotEqualTo)
LCValRel(`>`, GreaterThan)
LCValRel(`>=`, GreaterThanEq)
LCValRel(`<`, LessThan)
LCValRel(`<=`, LessThanEq)


func allDifferent*[T](positions: openArray[int]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: AllDifferentType,
        allDifferentState: newAllDifferentConstraint[T](positions)
    )

func allDifferent*[T](expressions: seq[AlgebraicExpression[T]]): StatefulConstraint[T] =
    # Returns allDifferent constraint for the given expressions.
    var positions = toPackedSet[int]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return allDifferent[T](toSeq(positions))
    else:
        return StatefulConstraint[T](
            positions: positions,
            stateType: AllDifferentType,
            allDifferentState: newAllDifferentConstraint[T](expressions)
        )

func globalCardinality*[T](positions: openArray[int], cardinalities: Table[T, int]): StatefulConstraint[T] =
    # Returns globalCardinality constraint for the given positions.
    return StatefulConstraint[T](
        positions: toPackedSet[int](positions),
        stateType: GlobalCardinalityType,
        globalCardinalityState: newGlobalCardinalityConstraint[T](positions, cardinalities)
    )

func globalCardinality*[T](expressions: seq[AlgebraicExpression[T]], cardinalities: Table[T, int]): StatefulConstraint[T] =
    # Returns globalCardinality constraint for the given expressions.
    var positions = toPackedSet[int]([])
    var allRefs = true
    for exp in expressions:
        if exp.node.kind != RefNode:
            allRefs = false
        positions.incl(exp.positions)
    
    if allRefs:
        # Use more efficient position based constraint if all expressions are refnodes
        return globalCardinality[T](toSeq(positions), cardinalities)
    else:
        return StatefulConstraint[T](
            positions: positions,
            stateType: GlobalCardinalityType,
            globalCardinalityState: newGlobalCardinalityConstraint[T](expressions, cardinalities)
        )


################################################################################
# Reified Linear Constraint Implementation
################################################################################

func newReifiedLinearConstraint*[T](linearComb: LinearCombination[T], relation: BinaryRelation, rhs: T, boolPosition: int): ReifiedLinearConstraint[T] =
    new(result)
    result.linearComb = linearComb
    result.relation = relation
    result.rhs = rhs
    result.boolPosition = boolPosition
    result.boolValue = 0  # Will be set during initialize
    result.cost = 0

func initialize*[T](state: ReifiedLinearConstraint[T], assignment: seq[T]) =
    # Initialize the linear combination and boolean value, then compute cost
    state.linearComb.initialize(assignment)
    state.boolValue = assignment[state.boolPosition]

    let linearSatisfied = state.relation.evaluate(state.linearComb.value, state.rhs)

    # Reified constraint: boolVar ↔ linearConstraint
    # Satisfied if: (boolVar == 1 AND linearConstraint) OR (boolVar == 0 AND NOT linearConstraint)
    let reifiedSatisfied = (state.boolValue == 1 and linearSatisfied) or (state.boolValue == 0 and not linearSatisfied)
    state.cost = if reifiedSatisfied: 0 else: 1

func updatePosition*[T](state: ReifiedLinearConstraint[T], position: int, newValue: T) =
    # Update either the linear combination or the boolean variable
    if position == state.boolPosition:
        # Boolean variable changed
        state.boolValue = newValue
        let linearSatisfied = state.relation.evaluate(state.linearComb.value, state.rhs)
        let reifiedSatisfied = (state.boolValue == 1 and linearSatisfied) or (state.boolValue == 0 and not linearSatisfied)
        state.cost = if reifiedSatisfied: 0 else: 1
    elif position in state.linearComb.positions:
        # Linear combination variable changed
        state.linearComb.updatePosition(position, newValue)
        let linearSatisfied = state.relation.evaluate(state.linearComb.value, state.rhs)
        let reifiedSatisfied = (state.boolValue == 1 and linearSatisfied) or (state.boolValue == 0 and not linearSatisfied)
        state.cost = if reifiedSatisfied: 0 else: 1

func moveDelta*[T](state: ReifiedLinearConstraint[T], position: int, oldValue, newValue: T): int =
    # Compute cost delta for changing position from oldValue to newValue
    if position == state.boolPosition:
        # Boolean variable change
        let linearSatisfied = state.relation.evaluate(state.linearComb.value, state.rhs)
        let oldReifiedSatisfied = (oldValue == 1 and linearSatisfied) or (oldValue == 0 and not linearSatisfied)
        let newReifiedSatisfied = (newValue == 1 and linearSatisfied) or (newValue == 0 and not linearSatisfied)
        return (if newReifiedSatisfied: 0 else: 1) - (if oldReifiedSatisfied: 0 else: 1)
    elif position in state.linearComb.positions:
        # Linear combination variable change
        let linearDelta = state.linearComb.moveDelta(position, oldValue, newValue)
        let oldLinearValue = state.linearComb.value
        let newLinearValue = oldLinearValue + linearDelta

        let oldLinearSatisfied = state.relation.evaluate(oldLinearValue, state.rhs)
        let newLinearSatisfied = state.relation.evaluate(newLinearValue, state.rhs)

        # Use stored boolean value
        let oldReifiedSatisfied = (state.boolValue == 1 and oldLinearSatisfied) or (state.boolValue == 0 and not oldLinearSatisfied)
        let newReifiedSatisfied = (state.boolValue == 1 and newLinearSatisfied) or (state.boolValue == 0 and not newLinearSatisfied)

        return (if newReifiedSatisfied: 0 else: 1) - (if oldReifiedSatisfied: 0 else: 1)
    else:
        return 0

################################################################################
# Reified Linear Constraint Creation Functions
################################################################################

template ReifyLinCombRel(reifyFunc, rel, relEnum: untyped) =
    # Template for reified LinearCombination relations
    func `reifyFunc`*[T](boolVar: AlgebraicExpression[T], left: LinearCombination[T], right: T): StatefulConstraint[T] {.inline.} =
        # Extract boolean variable position (must be a simple reference)
        if boolVar.node.kind != RefNode:
            # For now, require boolean variable to be a simple reference
            # Could extend later to handle more complex boolean expressions
            raise newException(ValueError, "Boolean variable in reified constraint must be a simple variable reference")
        
        let boolPosition = boolVar.node.position
        let allPositions = left.positions + toPackedSet([boolPosition])
        
        return StatefulConstraint[T](
            positions: allPositions,
            stateType: ReifiedLinearType,
            reifiedLinearState: newReifiedLinearConstraint[T](left, relEnum, right, boolPosition)
        )

ReifyLinCombRel(reifyLinEq, `==`, EqualTo)
ReifyLinCombRel(reifyLinNe, `!=`, NotEqualTo)
ReifyLinCombRel(reifyLinGt, `>`, GreaterThan)
ReifyLinCombRel(reifyLinGe, `>=`, GreaterThanEq)
ReifyLinCombRel(reifyLinLt, `<`, LessThan)
ReifyLinCombRel(reifyLinLe, `<=`, LessThanEq)


################################################################################
# Computed Constraint State interface
################################################################################

func initialize*[T](constraint: StatefulConstraint[T], assignment: seq[T]) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.initialize(assignment)
        of ElementConstraint:
            constraint.elementState.initialize(assignment)
        of LinearType:
            constraint.linearConstraintState.initialize(assignment)
        of AlgebraicType:
            constraint.algebraicConstraintState.initialize(assignment)
        of ReifiedLinearType:
            constraint.reifiedLinearState.initialize(assignment)
        of MinType:
            constraint.minConstraintState.initialize(assignment)
        of MaxType:
            constraint.maxConstraintState.initialize(assignment)
        of SumType:
            constraint.sumConstraintState.initialize(assignment)
        of GlobalCardinalityType:
            constraint.globalCardinalityState.initialize(assignment)
        of RegularType:
            constraint.regularState.initialize(assignment)


func moveDelta*[T](constraint: StatefulConstraint[T], position: int, oldValue, newValue: T): int =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.moveDelta(position, oldValue, newValue)
        of ElementConstraint:
            constraint.elementState.moveDelta(position, oldValue, newValue)
        of LinearType:
            constraint.linearConstraintState.moveDelta(position, oldValue, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.moveDelta(position, oldValue, newValue)
        of ReifiedLinearType:
            constraint.reifiedLinearState.moveDelta(position, oldValue, newValue)
        of MinType:
            constraint.minConstraintState.moveDelta(position, oldValue, newValue)
        of MaxType:
            constraint.maxConstraintState.moveDelta(position, oldValue, newValue)
        of SumType:
            constraint.sumConstraintState.moveDelta(position, oldValue, newValue)
        of GlobalCardinalityType:
            constraint.globalCardinalityState.moveDelta(position, oldValue, newValue)
        of RegularType:
            constraint.regularState.moveDelta(position, oldValue, newValue)


func updatePosition*[T](constraint: StatefulConstraint[T], position: int, newValue: T) =
    case constraint.stateType:
        of AllDifferentType:
            constraint.allDifferentState.updatePosition(position, newValue)
        of ElementConstraint:
            constraint.elementState.updatePosition(position, newValue)
        of LinearType:
            constraint.linearConstraintState.updatePosition(position, newValue)
        of AlgebraicType:
            constraint.algebraicConstraintState.updatePosition(position, newValue)
        of ReifiedLinearType:
            constraint.reifiedLinearState.updatePosition(position, newValue)
        of MinType:
            constraint.minConstraintState.updatePosition(position, newValue)
        of MaxType:
            constraint.maxConstraintState.updatePosition(position, newValue)
        of SumType:
            constraint.sumConstraintState.updatePosition(position, newValue)
        of GlobalCardinalityType:
            constraint.globalCardinalityState.updatePosition(position, newValue)
        of RegularType:
            constraint.regularState.updatePosition(position, newValue)


################################################################################
# MinConstraint to StatefulConstraint conversion
################################################################################

template MinExpRel(rel, relEnum: untyped) =
    func `rel`*[T](left: MinExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: MinType,
            minConstraintState: newMinConstraint[T](left, relEnum, right)
        )
    
    proc `rel`*[T](left: MinExpression[T], right: AlgebraicExpression[T]): StatefulConstraint[T] {.inline.} =
        # MinExpression == Variable constraint
        # Check if right is a simple variable reference
        if right.node.kind == RefNode:
            let rightPos = right.node.position
            return StatefulConstraint[T](
                positions: left.positions + toPackedSet([rightPos]),
                stateType: MinType,
                minConstraintState: newMinConstraintWithVariableTarget[T](left, relEnum, rightPos)
            )
        else:
            # This operator only supports simple variable references on the right side
            raise newException(ValueError, "MinExpression == AlgebraicExpression requires right side to be a simple variable reference")

MinExpRel(`==`, EqualTo)
MinExpRel(`!=`, NotEqualTo)
MinExpRel(`>`, GreaterThan)
MinExpRel(`>=`, GreaterThanEq)
MinExpRel(`<`, LessThan)
MinExpRel(`<=`, LessThanEq)

################################################################################
# MaxExpression operators
################################################################################

template MaxExpRel(rel, relEnum: untyped) =
    func `rel`*[T](left: MaxExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: MaxType,
            maxConstraintState: newMaxConstraint[T](left, relEnum, right)
        )

MaxExpRel(`==`, EqualTo)
MaxExpRel(`!=`, NotEqualTo)
MaxExpRel(`>`, GreaterThan)
MaxExpRel(`>=`, GreaterThanEq)
MaxExpRel(`<`, LessThan)
MaxExpRel(`<=`, LessThanEq)

################################################################################
# SumExpression operators
################################################################################

template SumExpRel(rel, relEnum: untyped) =
    func `rel`*[T](left: SumExpression[T], right: T): StatefulConstraint[T] {.inline.} =
        return StatefulConstraint[T](
            positions: left.positions,
            stateType: SumType,
            sumConstraintState: newSumConstraint[T](left, relEnum, right)
        )

SumExpRel(`==`, EqualTo)
SumExpRel(`!=`, NotEqualTo)
SumExpRel(`>`, GreaterThan)
SumExpRel(`>=`, GreaterThanEq)
SumExpRel(`<`, LessThan)
SumExpRel(`<=`, LessThanEq)

################################################################################
# Deep Copy for StatefulConstraint (for parallel processing)
################################################################################

proc deepCopy*[T](constraint: StatefulConstraint[T]): StatefulConstraint[T] =
  ## Creates a deep copy of a stateful constraint for thread-safe parallel processing
  ## FIXED: Now properly copies the current constraint state instead of creating fresh state
  
  case constraint.stateType:
    of AllDifferentType:
      # FIXED: Deep copy the actual constraint state instead of creating fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: AllDifferentType,
        allDifferentState: constraint.allDifferentState.deepCopy()
      )
    of ElementConstraint:
      # Create a new ElementState with fresh state - ElementState is mostly a stub
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: ElementConstraint,
        elementState: ElementState[T](
          currentAssignment: initTable[int, T](),
          cost: 0,
          positions: constraint.positions
        )
      )  
    of LinearType:
      # Create a new LinearConstraint with same parameters but fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: LinearType,
        linearConstraintState: newLinearConstraint[T](
          constraint.linearConstraintState.lincomb.deepCopy(),
          constraint.linearConstraintState.relation, 
          constraint.linearConstraintState.target
        )
      )
    of AlgebraicType:
      # Create a new AlgebraicConstraint with same parameters but fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: AlgebraicType,
        algebraicConstraintState: newAlgebraicConstraintState[T](
          constraint.algebraicConstraintState.constraint
        )
      )
    of ReifiedLinearType:
      # Create a new ReifiedLinearConstraint with same parameters but fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: ReifiedLinearType,
        reifiedLinearState: ReifiedLinearConstraint[T](
          linearComb: constraint.reifiedLinearState.linearComb.deepCopy(),
          relation: constraint.reifiedLinearState.relation,
          rhs: constraint.reifiedLinearState.rhs,
          boolPosition: constraint.reifiedLinearState.boolPosition,
          boolValue: T(0),  # Fresh state - will be initialized by worker
          cost: 0  # Fresh state
        )
      )
    of MinType:
      # Create a new MinConstraint with same parameters but fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: MinType,
        minConstraintState: 
          case constraint.minConstraintState.constraintType:
          of ConstantTarget:
            newMinConstraint[T](
              constraint.minConstraintState.minExpr.deepCopy(),
              constraint.minConstraintState.relation,
              constraint.minConstraintState.target
            )
          of VariableTarget:
            newMinConstraintWithVariableTarget[T](
              constraint.minConstraintState.minExpr.deepCopy(),
              constraint.minConstraintState.relation,
              constraint.minConstraintState.targetPosition
            )
      )
    of MaxType:
      # Create a new MaxConstraint with same parameters but fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: MaxType,
        maxConstraintState: newMaxConstraint[T](
          constraint.maxConstraintState.maxExpr.deepCopy(),
          constraint.maxConstraintState.relation,
          constraint.maxConstraintState.target
        )
      )
    of SumType:
      # Create a new SumConstraint with same parameters but fresh state
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: SumType,
        sumConstraintState: newSumConstraint[T](
          constraint.sumConstraintState.sumExpr.deepCopy(),
          constraint.sumConstraintState.relation,
          constraint.sumConstraintState.target
        )
      )
    of GlobalCardinalityType:
      # Create a new GlobalCardinalityConstraint with same parameters but fresh state
      let origConstraint = constraint.globalCardinalityState
      case origConstraint.evalMethod:
        of PositionBased:
          result = StatefulConstraint[T](
            positions: constraint.positions,
            stateType: GlobalCardinalityType,
            globalCardinalityState: newGlobalCardinalityConstraint[T](
              toSeq(constraint.positions), 
              origConstraint.valueCardinalities
            )
          )
        of ExpressionBased:
          result = StatefulConstraint[T](
            positions: constraint.positions,
            stateType: GlobalCardinalityType,
            globalCardinalityState: newGlobalCardinalityConstraint[T](
              origConstraint.expressions,
              origConstraint.valueCardinalities
            )
          )
    of RegularType:
      # Deep copy the regular constraint
      result = StatefulConstraint[T](
        positions: constraint.positions,
        stateType: RegularType,
        regularState: constraint.regularState.deepCopy()
      )

################################################################################
# Regular constraint StatefulConstraint constructors
################################################################################

func regularConstraint*[T](
    sequence: seq[AlgebraicExpression[T]], 
    numStates: int,
    alphabetSize: int, 
    transitionMatrix: seq[seq[int]],
    initialState: int,
    acceptingStates: HashSet[int]
): StatefulConstraint[T] =
    ## Create a StatefulConstraint wrapping a RegularConstraint from expressions
    let regularConst = newRegularConstraint(sequence, numStates, alphabetSize, 
                                          transitionMatrix, initialState, acceptingStates)
    
    result = StatefulConstraint[T](
        positions: regularConst.positions,
        stateType: RegularType,
        regularState: regularConst
    )

func regularConstraint*[T](
    positions: openArray[int],
    numStates: int,
    alphabetSize: int, 
    transitionMatrix: seq[seq[int]],
    initialState: int,
    acceptingStates: HashSet[int]
): StatefulConstraint[T] =
    ## Create a StatefulConstraint wrapping a RegularConstraint from positions
    let regularConst = newRegularConstraint(positions, numStates, alphabetSize, 
                                          transitionMatrix, initialState, acceptingStates)
    
    result = StatefulConstraint[T](
        positions: regularConst.positions,
        stateType: RegularType,
        regularState: regularConst
    )

