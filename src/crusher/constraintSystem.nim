import std/[packedsets, sequtils, tables]

import constrainedArray
import constraints/[algebraic, stateful, setConstraints]
import expressions

################################################################################
# Type definitions
################################################################################

type
    VariableContainer[T] = ref object of RootObj
        system: ConstraintSystem[T]
        offset: int
        size: int

    ConstrainedSequence*[T] = ref object of VariableContainer[T]
        n*: int

    ConstrainedMatrix*[T] = ref object of VariableContainer[T]
        m*, n*: int

    ConstrainedSet*[T] = ref object of VariableContainer[T]
        setExpr*: SetExpression[T]
        universe*: PackedSet[int]

    ConstraintSystem*[T] = ref object
        size*: int
        variables*: seq[VariableContainer[T]]
        baseArray*: ConstrainedArray[T]
        assignment*: seq[T]

################################################################################
# ConstraintSystem creation
################################################################################

func initConstraintSystem*[T](): ConstraintSystem[T] =
    # Initializes empty ConstraintSystem
    return ConstraintSystem[T](
        size: 0,
        baseArray: initConstrainedArray[T](0),
        variables: newSeq[VariableContainer[T]](),
        assignment: newSeq[T]()
    )

################################################################################
# Constrained Variable creation
################################################################################

func init*[T](cvar: VariableContainer[T], system: ConstraintSystem[T]) =
    cvar.system = system
    cvar.offset = system.baseArray.len

func init*[T](cvar: ConstrainedSequence[T], system: ConstraintSystem[T], n: int) =
    cvar.init(system)
    cvar.size = n
    cvar.n = n

func init*[T](cvar: ConstrainedMatrix[T], system: ConstraintSystem[T], m, n: int) =
    cvar.init(system)
    cvar.size = m*n
    cvar.m = m
    cvar.n = n

func init*[T](cvar: ConstrainedSet[T], system: ConstraintSystem[T], universe: PackedSet[int]) =
    cvar.init(system)
    cvar.size = universe.len  # Each element in universe gets a boolean position (0/1)
    cvar.universe = universe
    cvar.setExpr = newSetExpression[T](universe)
    # Initialize positions for set membership tracking
    for i, element in pairs(toSeq(universe)):
        cvar.setExpr.dependentElements[cvar.offset + i] = @[element]

func newConstrainedSequence*[T](system: ConstraintSystem[T], n: int): ConstrainedSequence[T] =
    new(result)
    result.init(system, n)
    system.baseArray.extendArray(n)
    system.variables.add(result)

func newConstrainedMatrix*[T](system: ConstraintSystem[T], m, n: int): ConstrainedMatrix[T] =
    new(result)
    result.init(system, m, n)
    system.baseArray.extendArray(m*n)
    system.variables.add(result)

func newConstrainedSet*[T](system: ConstraintSystem[T], universe: PackedSet[int]): ConstrainedSet[T] =
    new(result)
    result.init(system, universe)
    # Sets use boolean variables (0/1) for each element in the universe
    system.baseArray.extendArray(universe.len)
    system.variables.add(result)

func newConstrainedSet*[T](system: ConstraintSystem[T], universe: seq[int]): ConstrainedSet[T] =
    newConstrainedSet[T](system, toPackedSet(universe))

################################################################################
# ConstrainedVariable access
################################################################################

func `[]`*[T](cvar: ConstrainedSequence[T], i: int): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + i]

func `[]`*[T](cvar: ConstrainedMatrix[T], i, j: int): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + cvar.m*i + j]

func currentSet*[T](cvar: ConstrainedSet[T]): PackedSet[int] {.inline.} =
    # Returns current set contents
    cvar.setExpr.currentSet

func cardinality*[T](cvar: ConstrainedSet[T]): int {.inline.} =
    # Returns current set cardinality
    cvar.setExpr.cardinality

func contains*[T](cvar: ConstrainedSet[T], element: int): bool {.inline.} =
    # Check if element is in the current set
    cvar.setExpr.contains(element)

func positions[T](cvar: VariableContainer[T]): seq[int] =
    toSeq cvar.offset..<(cvar.offset + cvar.size)

func assignment*[T](cvar: ConstrainedSequence[T]): seq[T] =
    cvar.system.assignment[cvar.offset..<(cvar.offset + cvar.size)]

func assignment*[T](cvar: ConstrainedMatrix[T]): seq[seq[T]] =
    let values = cvar.system.assignment[cvar.offset..<(cvar.offset + cvar.size)]
    for i in 0..<cvar.m:
        result.add(values[cvar.m*i..<(cvar.m*i + cvar.n)])

func assignment*[T](cvar: ConstrainedSet[T]): PackedSet[int] =
    # Returns current set assignment
    cvar.setExpr.currentSet

################################################################################
# Useful Iterators
################################################################################

iterator columns*[T](cvar: ConstrainedMatrix[T]): seq[AlgebraicExpression[T]] =
    # Yields the columns of the ConstrainedMatrix
    var col: seq[AlgebraicExpression[T]]
    for i in 0..<cvar.n:
        col = @[]
        for j in 0..<cvar.m:
            col.add(cvar[j, i])
        yield col

iterator rows*[T](cvar: ConstrainedMatrix[T]): seq[AlgebraicExpression[T]] =
    # Yields the rows of the ConstrainedMatrix
    var row: seq[AlgebraicExpression[T]]
    for i in 0..<cvar.m:
        row = @[]
        for j in 0..<cvar.n:
            row.add(cvar[i, j])
        yield row

################################################################################
# Displaying
################################################################################

func `$`*[T](cvar: ConstrainedSequence[T]): string = $(cvar.assignment)
func `$`*[T](cvar: ConstrainedMatrix[T]): string = $(cvar.assignment)
func `$`*[T](cvar: ConstrainedSet[T]): string = $(cvar.setExpr)

################################################################################
# ConstrainedVariable domains
################################################################################

func setDomain*[T](cvar: VariableContainer[T], domain: openArray[T]) =
    # sets the domain of the constrained variable for all its positions
    for i in 0..<cvar.size:
        cvar.system.baseArray.setDomain(cvar.offset + i, domain)

func setUniverse*[T](cvar: ConstrainedSet[T], universe: PackedSet[int]) =
    # Sets the universe (domain) of possible elements for the set
    cvar.universe = universe
    cvar.setExpr.universe = universe

func setUniverse*[T](cvar: ConstrainedSet[T], universe: seq[int]) =
    # Sets the universe (domain) of possible elements for the set
    setUniverse(cvar, toPackedSet(universe))

func updateSetFromAssignment*[T](cvar: ConstrainedSet[T], assignment: seq[T]) =
    # Update set contents based on boolean variable assignments
    cvar.setExpr.currentSet = initPackedSet[int]()
    cvar.setExpr.cardinality = 0
    
    let universeSeq = toSeq(cvar.universe)
    for i, element in pairs(universeSeq):
        let position = cvar.offset + i
        if position < assignment.len and int(assignment[position]) == 1:
            cvar.setExpr.currentSet.incl(element)
            cvar.setExpr.cardinality += 1

func elementPosition*[T](cvar: ConstrainedSet[T], element: int): int =
    # Returns the variable position for the given element's membership
    let universeSeq = toSeq(cvar.universe)
    for i, universeElement in pairs(universeSeq):
        if universeElement == element:
            return cvar.offset + i
    return -1  # Element not in universe

################################################################################
# ConstrainedVariable methods
################################################################################

func sum*[T](cvar: ConstrainedSequence[T]): LinearCombination[T] =
    # Returns LinearCombination object representing the sum of the
    # Constrained Sequence
    return newLinearCombination[T](cvar.positions)

template OrderingSeqRel(relName: untyped) =
    func `relName`*[T](cvar: ConstrainedSequence[T]): seq[AlgebraicConstraint[T]] {.inline.} =
        var expressions: seq[AlgebraicExpression[T]] = @[]
        for i in 0..<cvar.n:
            expressions.add(cvar[i])
        return `relName`(expressions)

OrderingSeqRel(increasing)
OrderingSeqRel(strictlyIncreasing)
OrderingSeqRel(decreasing)
OrderingSeqRel(strictlyDecreasing)

################################################################################
# ConstrainedVariable constraints
################################################################################

proc allDifferent*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # all-different constraint for the variable
    # Returns constraint requiring that all values in the container be distinct.
    allDifferent[T](cvar.positions)

proc globalCardinality*[T](cvar: VariableContainer[T], cardinalities: Table[T, int]): StatefulConstraint[T] =
    # global cardinality constraint for the variable container
    # Returns constraint requiring specific cardinalities for each value.
    globalCardinality[T](cvar.positions, cardinalities)

proc min*[T](cvar: VariableContainer[T]): MinExpression[T] =
    # min expression for the variable container
    # Returns MinExpression that tracks the minimum value across all variables.
    newMinExpression[T](cvar.positions)

proc max*[T](cvar: VariableContainer[T]): MaxExpression[T] =
    # max expression for the variable container
    # Returns MaxExpression that tracks the maximum value across all variables.
    newMaxExpression[T](cvar.positions)

proc addConstraint*[T](system: ConstraintSystem[T], constraint: StatefulConstraint[T]) =
    # adds constraint to the system
    system.baseArray.addBaseConstraint(constraint)

proc addConstraint*[T](system: ConstraintSystem[T], constraint: AlgebraicConstraint[T]) =
    # adds constraint to the system
    system.baseArray.addBaseConstraint(
        StatefulConstraint[T](
            positions: constraint.positions,
            stateType: AlgebraicType,
            algebraicConstraintState: newAlgebraicConstraintState[T](constraint))
        )

func addConstraints*[T](system: ConstraintSystem[T], constraints: openArray[StatefulConstraint[T]]) =
    # adds constraints to the system
    for constraint in constraints:
        system.baseArray.addBaseConstraint(constraint)

################################################################################
# Set Constraint Constructors
################################################################################

proc setMembership*[T](system: ConstraintSystem[T], element: AlgebraicExpression[T], setVar: ConstrainedSet[T]): StatefulConstraint[T] =
    # Creates a set membership constraint: element ∈ setVar
    let elementPositions = element.positions
    if elementPositions.len != 1:
        raise newException(ValueError, "Set membership constraint requires element to be a single variable")
    
    let elementPos = toSeq(elementPositions)[0]
    let setPositions = setVar.positions.toPackedSet
    let constraint = newSetMembershipConstraint[T](elementPos, setPositions, toSeq(setVar.universe))
    
    result = StatefulConstraint[T](
        positions: elementPositions + setPositions,
        stateType: SetMembershipType,
        setMembershipState: constraint
    )

proc setCardinality*[T](system: ConstraintSystem[T], setVar: ConstrainedSet[T], cardinality: AlgebraicExpression[T]): StatefulConstraint[T] =
    # Creates a set cardinality constraint: |setVar| = cardinality
    let cardinalityPositions = cardinality.positions
    if cardinalityPositions.len != 1:
        raise newException(ValueError, "Set cardinality constraint requires cardinality to be a single variable")
    
    let cardinalityPos = toSeq(cardinalityPositions)[0]
    let setPositions = setVar.positions.toPackedSet
    let constraint = newSetCardinalityConstraint[T](setPositions, cardinalityPos)
    
    result = StatefulConstraint[T](
        positions: setPositions + cardinalityPositions,
        stateType: SetCardinalityType,
        setCardinalityState: constraint
    )

################################################################################
# Deep Copy for ConstraintSystem (for parallel processing)
################################################################################

proc deepCopy*[T](system: ConstraintSystem[T]): ConstraintSystem[T] =
  ## Creates a deep copy of a ConstraintSystem for thread-safe parallel processing
  new(result)
  result.size = system.size
  result.assignment = system.assignment  # seq[T] - deep copy by assignment
  
  # Deep copy the base array with all its constraints
  result.baseArray = system.baseArray.deepCopy()
  
  # Deep copy the variable containers (they reference the constraint system)
  result.variables = newSeq[VariableContainer[T]](system.variables.len)
  for i, variable in system.variables:
    # Use type checking instead of case on typeof
    if variable of ConstrainedSequence[T]:
      let seq_var = ConstrainedSequence[T](variable)
      result.variables[i] = ConstrainedSequence[T](
        system: result,
        offset: seq_var.offset,
        size: seq_var.size,
        n: seq_var.n
      )
    elif variable of ConstrainedMatrix[T]:
      let matrix_var = ConstrainedMatrix[T](variable)
      result.variables[i] = ConstrainedMatrix[T](
        system: result,
        offset: matrix_var.offset,
        size: matrix_var.size,
        m: matrix_var.m,
        n: matrix_var.n
      )
    else:
      # Generic variable container
      result.variables[i] = VariableContainer[T](
        system: result,
        offset: variable.offset,
        size: variable.size
      )
