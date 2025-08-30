import std/[packedsets, sequtils, tables]

import constrainedArray
import constraints/[algebraic, stateful]
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

################################################################################
# ConstrainedVariable access
################################################################################

func `[]`*[T](cvar: ConstrainedSequence[T], i: int): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + i]

func `[]`*[T](cvar: ConstrainedMatrix[T], i, j: int): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + cvar.m*i + j]

func positions[T](cvar: VariableContainer[T]): seq[int] =
    toSeq cvar.offset..<(cvar.offset + cvar.size)

func assignment*[T](cvar: ConstrainedSequence[T]): seq[T] =
    cvar.system.assignment[cvar.offset..<(cvar.offset + cvar.size)]

func assignment*[T](cvar: ConstrainedMatrix[T]): seq[seq[T]] =
    let values = cvar.system.assignment[cvar.offset..<(cvar.offset + cvar.size)]
    for i in 0..<cvar.m:
        result.add(values[cvar.m*i..<(cvar.m*i + cvar.n)])

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

################################################################################
# ConstrainedVariable domains
################################################################################

func setDomain*[T](cvar: VariableContainer[T], domain: openArray[T]) =
    # sets the domain of the constrained variable for all its positions
    for i in 0..<cvar.size:
        cvar.system.baseArray.setDomain(cvar.offset + i, domain)

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
