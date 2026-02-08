import std/packedsets

import constrainedArray
import constraints/[algebraic, stateful, elementState, types]
export elementState.ArrayElement
import expressions/[algebraic, sumExpression, maxExpression, minExpression]

################################################################################
# Type definitions
################################################################################

type
    NoSolutionFoundError* = object of CatchableError
    VariableContainer[T] = ref object of RootObj
        system: ConstraintSystem[T]
        offset: int
        size: int

    ConstrainedVariable*[T] = ref object of VariableContainer[T]

    ConstrainedSequence*[T] = ref object of VariableContainer[T]
        n: int

    ConstrainedMatrix*[T] = ref object of VariableContainer[T]
        m, n: int

    ConstraintSystem*[T] = ref object
        size*: int
        variables*: seq[VariableContainer[T]]
        baseArray*: ConstrainedArray[T]
        assignment*: seq[T]
        lastIterations*: int

################################################################################
# ConstraintSystem creation
################################################################################

func initConstraintSystem*[T](): ConstraintSystem[T] =
    # Initializes empty ConstraintSystem
    return ConstraintSystem[T](
        size: 0,
        baseArray: initConstrainedArray[T](0),
        variables: newSeq[VariableContainer[T]](),
        assignment: newSeq[T](),
        lastIterations: 0
    )

################################################################################
# Constrained Variable creation
################################################################################

func init*[T](cvar: VariableContainer[T], system: ConstraintSystem[T]) =
    cvar.system = system
    cvar.offset = system.baseArray.len

func init*[T](cvar: ConstrainedVariable[T], system: ConstraintSystem[T]) =
    VariableContainer[T](cvar).init(system)
    cvar.size = 1

func init*[T](cvar: ConstrainedSequence[T], system: ConstraintSystem[T], n: int) =
    VariableContainer[T](cvar).init(system)
    cvar.size = n
    cvar.n = n

func init*[T](cvar: ConstrainedMatrix[T], system: ConstraintSystem[T], m, n: int) =
    VariableContainer[T](cvar).init(system)
    cvar.size = m*n
    cvar.m = m
    cvar.n = n

func newConstrainedVariable*[T](system: ConstraintSystem[T]): ConstrainedVariable[T] =
    new(result)
    result.init(system)
    system.baseArray.extendArray(1)
    system.variables.add(result)

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

func value*[T](cvar: ConstrainedVariable[T]): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset]

converter toAlgebraicExpression*[T](cvar: ConstrainedVariable[T]): AlgebraicExpression[T] {.inline.} =
    cvar.value

# Template for ConstrainedVariable comparison operators
template VarVarOp(op: untyped) =
    func op*[T](left, right: ConstrainedVariable[T]): StatefulConstraint[T] {.inline.} =
        stateful.op(left.value, right.value)

template VarConstOp(op: untyped) =
    func op*[T: SomeNumber](left: ConstrainedVariable[T], right: T): StatefulConstraint[T] {.inline.} =
        stateful.op(left.value, right)

    func op*[T: SomeNumber](left: T, right: ConstrainedVariable[T]): StatefulConstraint[T] {.inline.} =
        stateful.op(left, right.value)

# Generate all comparison operators
VarVarOp(`==`)
VarVarOp(`>`)
VarVarOp(`>=`)
VarVarOp(`<`)
VarVarOp(`<=`)

VarConstOp(`==`)
VarConstOp(`>`)
VarConstOp(`>=`)
VarConstOp(`<`)
VarConstOp(`<=`)

func `[]`*[T](cvar: ConstrainedSequence[T], i: int): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + i]

func `[]`*[T](cvar: ConstrainedMatrix[T], i, j: int): AlgebraicExpression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + cvar.m*i + j]

func positions[T](cvar: VariableContainer[T]): seq[int] =
    result = newSeq[int](cvar.size)
    for i in 0..<cvar.size:
        result[i] = cvar.offset + i

func assignment*[T](cvar: ConstrainedVariable[T]): T =
    cvar.system.assignment[cvar.offset]

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

func `$`*[T](cvar: ConstrainedVariable[T]): string = $(cvar.assignment)
func `$`*[T](cvar: ConstrainedSequence[T]): string = $(cvar.assignment)
func `$`*[T](cvar: ConstrainedMatrix[T]): string = $(cvar.assignment)

################################################################################
# ConstrainedVariable domains
################################################################################

func setDomain*[T](cvar: VariableContainer[T], domain: openArray[T]) =
    # sets the domain of the constrained variable
    cvar.system.baseArray.setDomain(cvar.offset, domain)

func setDomain*[T](cvar: ConstrainedSequence[T], domain: openArray[T]) =
    # sets the domain for all positions in the constrained sequence
    for i in 0..<cvar.size:
        cvar.system.baseArray.setDomain(cvar.offset + i, domain)

func setDomain*[T](cvar: ConstrainedSequence[T], index: int, domain: openArray[T]) =
    # sets the domain for a single element of the constrained sequence
    cvar.system.baseArray.setDomain(cvar.offset + index, domain)

func setDomain*[T](cvar: ConstrainedMatrix[T], domain: openArray[T]) =
    # sets the domain for all positions in the constrained matrix
    for i in 0..<cvar.size:
        cvar.system.baseArray.setDomain(cvar.offset + i, domain)

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

proc circuit*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # circuit constraint for the variable
    # Returns constraint requiring that values form a single Hamiltonian circuit.
    circuit[T](cvar.positions)

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
            algebraicState: newAlgebraicConstraintState[T](constraint))
        )

func addConstraints*[T](system: ConstraintSystem[T], constraints: openArray[StatefulConstraint[T]]) =
    # adds constraints to the system
    for constraint in constraints:
        system.baseArray.addBaseConstraint(constraint)

proc initialize*[T](system: ConstraintSystem[T], assignment: seq[T]) =
    # Initialize the system with a complete assignment
    system.assignment = assignment
    # Initialize all constraints with this assignment
    for constraint in system.baseArray.constraints:
        constraint.initialize(assignment)

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
        stateType: ElementType,
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
        stateType: ElementType,
        elementState: elementState
    )

proc element*[T](indexExpr: AlgebraicExpression[T], mixedArray: seq[ArrayElement[T]], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    # Creates element constraint: mixedArray[indexExpr] = valueExpr (mixed constant/variable array)
    let indexPos = indexExpr.node.position
    let valuePos = valueExpr.node.position
    let elementState = newElementState[T](indexPos, mixedArray, valuePos)

    return StatefulConstraint[T](
        positions: elementState.positions,
        stateType: ElementType,
        elementState: elementState
    )

proc element*[T](indexExpr: AlgebraicExpression[T], sequence: ConstrainedSequence[T], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    # Creates element constraint: sequence[indexExpr] = valueExpr
    var variableArray: seq[AlgebraicExpression[T]] = @[]
    for i in 0..<sequence.n:
        variableArray.add(sequence[i])
    return element(indexExpr, variableArray, valueExpr)

proc element*[T](indexExpr: AlgebraicExpression[T], sequence: ConstrainedSequence[T], value: T): StatefulConstraint[T] =
    # Creates element constraint: sequence[indexExpr] = value (constant)
    # This means: the value at sequence[indexExpr] should equal the constant value

    # Create a variable constrained to the target value
    var valueVar = sequence.system.newConstrainedVariable()
    sequence.system.baseArray.setDomain(valueVar.offset, [value])

    # Create array of sequence elements
    var variableArray: seq[AlgebraicExpression[T]] = @[]
    for i in 0..<sequence.n:
        variableArray.add(sequence[i])

    # The element constraint: variableArray[indexExpr] = valueVar
    return element(indexExpr, variableArray, valueVar)

proc elementExpr*[T](indexExpr: AlgebraicExpression[T], arrayExprs: seq[AlgebraicExpression[T]], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    ## Creates expression-based element constraint: arrayExprs[indexExpr] = valueExpr
    ## This supports computed index expressions like (Y * W + X)
    ## Use this when indexExpr is not a simple variable but a computed expression
    let elementState = newElementStateExprBased[T](indexExpr, arrayExprs, valueExpr)

    return StatefulConstraint[T](
        positions: elementState.positions,
        stateType: ElementType,
        elementState: elementState
    )

proc elementExpr*[T](indexExpr: AlgebraicExpression[T], constantArray: seq[T], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    ## Creates expression-based element constraint with constant array: constantArray[indexExpr] = valueExpr
    ## This supports computed index expressions like (Y * W + X) into a constant lookup table
    ## Useful for shape lookups: Shape[Rr * 3 + Cf] where Shape is a constant array
    let elementState = newElementStateExprBasedConst[T](indexExpr, constantArray, valueExpr)

    return StatefulConstraint[T](
        positions: elementState.positions,
        stateType: ElementType,
        elementState: elementState
    )

proc elementExpr*[T](indexExpr: AlgebraicExpression[T], sequence: ConstrainedSequence[T], valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    ## Creates expression-based element constraint: sequence[indexExpr] = valueExpr
    ## This supports computed index expressions like (Y * W + X)
    var arrayExprs: seq[AlgebraicExpression[T]] = @[]
    for i in 0..<sequence.n:
        arrayExprs.add(sequence[i])
    return elementExpr(indexExpr, arrayExprs, valueExpr)

proc elementExpr*[T](indexExpr: AlgebraicExpression[T], sequence: ConstrainedSequence[T], value: T): StatefulConstraint[T] =
    ## Creates expression-based element constraint: sequence[indexExpr] = value (constant)
    ## This supports computed index expressions like (Y * W + X)

    # Create a variable constrained to the target value
    var valueVar = sequence.system.newConstrainedVariable()
    sequence.system.baseArray.setDomain(valueVar.offset, [value])

    var arrayExprs: seq[AlgebraicExpression[T]] = @[]
    for i in 0..<sequence.n:
        arrayExprs.add(sequence[i])

    return elementExpr(indexExpr, arrayExprs, valueVar)

################################################################################
# Deep copy for ConstraintSystem
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
        # Type-safe deep copy of variable containers
        if variable of ConstrainedVariable[T]:
            let var_var = ConstrainedVariable[T](variable)
            result.variables[i] = ConstrainedVariable[T](
                system: result,
                offset: var_var.offset,
                size: var_var.size
            )
        elif variable of ConstrainedSequence[T]:
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
            # This should never happen with the current type hierarchy
            raise newException(ValueError, "Unknown VariableContainer subtype encountered during deepCopy: " & $variable.type)
