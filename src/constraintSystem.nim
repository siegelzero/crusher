import std/[packedsets, sequtils]

import constrainedArray
import constraints/[algebraic, stateful, constraintNode, elementState]
export elementState.ArrayElement
import expressions/[algebraic, stateful, sumExpression, maxExpression, minExpression]

################################################################################
# Type definitions
################################################################################

type
    VariableContainer[T] = ref object of RootObj
        system: ConstraintSystem[T]
        offset: int
        size: int

    ConstrainedSequence*[T] = ref object of VariableContainer[T]
        n: int

    ConstrainedMatrix*[T] = ref object of VariableContainer[T]
        m, n: int

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
    result = newSeq[int](cvar.size)
    for i in 0..<cvar.size:
        result[i] = cvar.offset + i

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
    # sets the domain of the constrained variable
    cvar.system.baseArray.setDomain(domain)

################################################################################
# ConstrainedVariable methods
################################################################################

func sum*[T](cvar: ConstrainedSequence[T]): SumExpression[T] =
    # Returns SumExpression object representing the sum of the
    # Constrained Sequence
    return newSumExpression[T](cvar.positions)

func max*[T](cvar: ConstrainedSequence[T]): MaxExpression[T] =
    # Returns MaxExpression object representing the max of the
    # Constrained Sequence
    return newMaxExpression[T](cvar.positions)

func min*[T](cvar: ConstrainedSequence[T]): MinExpression[T] =
    # Returns MinExpression object representing the min of the
    # Constrained Sequence
    return newMinExpression[T](cvar.positions)

################################################################################
# ConstrainedVariable constraints
################################################################################

proc allDifferent*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # all-different constraint for the variable
    # Returns constraint requiring that all values in the container be distinct.
    allDifferent[T](cvar.positions)

proc increasing*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # increasing constraint for the variable
    # Returns constraint requiring that all values in the container be in non-decreasing order.
    increasing[T](cvar.positions)

proc strictlyIncreasing*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # strictly increasing constraint for the variable
    # Returns constraint requiring that all values in the container be in strictly increasing order.
    strictlyIncreasing[T](cvar.positions)

proc decreasing*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # decreasing constraint for the variable
    # Returns constraint requiring that all values in the container be in non-increasing order.
    decreasing[T](cvar.positions)

proc strictlyDecreasing*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # strictly decreasing constraint for the variable
    # Returns constraint requiring that all values in the container be in strictly decreasing order.
    strictlyDecreasing[T](cvar.positions)

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
# Element constraint functions
################################################################################

proc element*[T](indexExpr: AlgebraicExpression[T], constantArray: seq[T], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    # Creates element constraint: constantArray[indexExpr] = valueExpr
    let indexPos = indexExpr.node.position
    let valuePos = valueExpr.node.position
    let elementState = newElementState[T](indexPos, constantArray, valuePos)

    return StatefulConstraint[T](
        positions: elementState.positions,
        stateType: ElementConstraint,
        elementState: elementState
    )

proc element*[T](indexExpr: AlgebraicExpression[T], variableArray: seq[AlgebraicExpression[T]], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    # Creates element constraint: variableArray[indexExpr] = valueExpr
    let indexPos = indexExpr.node.position
    let valuePos = valueExpr.node.position

    # Convert AlgebraicExpressions to ArrayElements
    var arrayElements: seq[ArrayElement[T]] = @[]
    for expr in variableArray:
        arrayElements.add(ArrayElement[T](isConstant: false, variablePosition: expr.node.position))

    let elementState = newElementState[T](indexPos, arrayElements, valuePos)

    return StatefulConstraint[T](
        positions: elementState.positions,
        stateType: ElementConstraint,
        elementState: elementState
    )

proc element*[T](indexExpr: AlgebraicExpression[T], mixedArray: seq[ArrayElement[T]], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    # Creates element constraint: mixedArray[indexExpr] = valueExpr (mixed constant/variable array)
    let indexPos = indexExpr.node.position
    let valuePos = valueExpr.node.position
    let elementState = newElementState[T](indexPos, mixedArray, valuePos)

    return StatefulConstraint[T](
        positions: elementState.positions,
        stateType: ElementConstraint,
        elementState: elementState
    )