import std/[packedsets, tables]

import constrainedArray
import constraints/[algebraic, constraintNode, relationalConstraint, stateful, elementState, matrixElement, types]
export elementState.ArrayElement
import expressions/[algebraic, sumExpression, maxExpression, minExpression]
import expressions/stateful as exprStateful

################################################################################
# Type definitions
################################################################################

type
    NoSolutionFoundError* = object of CatchableError
    InfeasibleError* = object of NoSolutionFoundError  ## Domain reduction proved infeasibility — retrying won't help
    TimeLimitExceededError* = object of CatchableError
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
        searchCompleted*: bool
        hasFeasibleSolution*: bool
        optimalityProven*: bool  # Domain reduction proved no better solution exists
        adaptedTabuThreshold*: int  # Persists adaptive threshold across resolve() calls

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
        lastIterations: 0,
        searchCompleted: true
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

func scalarProduct*[T](coefficients: openArray[T], cvar: ConstrainedSequence[T]): SumExpression[T] =
    ## Returns weighted sum: coefficients[0]*cvar[0] + coefficients[1]*cvar[1] + ...
    var exprs = newSeq[AlgebraicExpression[T]](cvar.n)
    for i in 0..<cvar.n:
        exprs[i] = cvar[i]
    return scalarProduct[T](coefficients, exprs)

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

proc allDifferentExcept0*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # all-different-except-0 constraint for the variable
    allDifferentExcept0[T](cvar.positions)

proc circuit*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # circuit constraint for the variable
    # Returns constraint requiring that values form a single Hamiltonian circuit.
    circuit[T](cvar.positions)

proc subcircuit*[T](cvar: VariableContainer[T]): StatefulConstraint[T] =
    # subcircuit constraint for the variable
    # Returns constraint requiring that values form at most one circuit (self-loops allowed).
    subcircuit[T](cvar.positions)

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

proc tryConvertBiconditionalToChannel[T](system: ConstraintSystem[T],
    leftChild, rightChild: StatefulConstraint[T]): bool =
    ## Tries to convert (A == constA) <-> (B == constB) to a channel binding.
    ## Returns true if conversion succeeded (constraint absorbed), false to fall through.

    # Both children must be RelationalType
    if leftChild.stateType != RelationalType or rightChild.stateType != RelationalType:
        return false

    let leftRel = leftChild.relationalState
    let rightRel = rightChild.relationalState

    # Both must have EqualTo or NotEqualTo relation
    if leftRel.relation notin {EqualTo, NotEqualTo} or
       rightRel.relation notin {EqualTo, NotEqualTo}:
        return false

    # Both must be simple: single-position PositionBased SumExpr on left, ConstantExpr on right
    # Check left child structure
    if leftRel.leftExpr.kind != SumExpr or leftRel.rightExpr.kind != ConstantExpr:
        return false
    let leftSum = leftRel.leftExpr.sumExpr
    if leftSum.evalMethod != PositionBased or leftSum.coefficient.len != 1:
        return false
    # Get position and verify coefficient is 1
    var leftPos: int
    var leftCoeff: T
    for pos in leftSum.coefficient.keys:
        leftPos = pos
        leftCoeff = leftSum.coefficient[pos]
    if leftCoeff != T(1):
        return false
    if leftSum.constant != T(0):
        return false
    let leftConst = leftRel.rightExpr.constantValue

    # Check right child structure
    if rightRel.leftExpr.kind != SumExpr or rightRel.rightExpr.kind != ConstantExpr:
        return false
    let rightSum = rightRel.leftExpr.sumExpr
    if rightSum.evalMethod != PositionBased or rightSum.coefficient.len != 1:
        return false
    var rightPos: int
    var rightCoeff: T
    for pos in rightSum.coefficient.keys:
        rightPos = pos
        rightCoeff = rightSum.coefficient[pos]
    if rightCoeff != T(1):
        return false
    if rightSum.constant != T(0):
        return false
    let rightConst = rightRel.rightExpr.constantValue

    # Exactly one side must have binary domain {0,1} with EqualTo — that's the channel variable
    let leftDomain = system.baseArray.domain[leftPos]
    let rightDomain = system.baseArray.domain[rightPos]

    let leftIsBinary = leftDomain.len == 2 and T(0) in leftDomain and T(1) in leftDomain and
                       leftRel.relation == EqualTo
    let rightIsBinary = rightDomain.len == 2 and T(0) in rightDomain and T(1) in rightDomain and
                        rightRel.relation == EqualTo

    # Exactly one side must be the binary channel variable
    if leftIsBinary == rightIsBinary:
        return false  # Both binary or neither — not a valid channeling pattern

    var channelPos, sourcePos: int
    var channelConst: T
    var sourceConst: T
    var sourceRelation: BinaryRelation
    var sourceDomain: seq[T]

    if leftIsBinary:
        channelPos = leftPos
        channelConst = leftConst
        sourcePos = rightPos
        sourceConst = rightConst
        sourceRelation = rightRel.relation
        sourceDomain = rightDomain
    else:
        channelPos = rightPos
        channelConst = rightConst
        sourcePos = leftPos
        sourceConst = leftConst
        sourceRelation = leftRel.relation
        sourceDomain = leftDomain

    # Source domain must be non-empty
    if sourceDomain.len == 0:
        return false

    # Build the array elements: for each value in source domain, determine channel value
    var arrayElems: seq[ArrayElement[T]] = @[]
    for v in sourceDomain:
        let matchesSource = (sourceRelation == EqualTo) == (v == sourceConst)
        arrayElems.add(ArrayElement[T](
            isConstant: true,
            constantValue: if matchesSource: channelConst else: T(1) - channelConst
        ))

    # Build index expression: sourcePos - lo (where lo is first element of sorted domain)
    let lo = sourceDomain[0]
    var indexExpr: AlgebraicExpression[T]
    if lo == T(0):
        indexExpr = newAlgebraicExpression[T](
            positions = toPackedSet[int]([sourcePos]),
            node = ExpressionNode[T](kind: RefNode, position: sourcePos),
            linear = true
        )
    else:
        indexExpr = newAlgebraicExpression[T](
            positions = toPackedSet[int]([sourcePos]),
            node = ExpressionNode[T](
                kind: BinaryOpNode,
                binaryOp: Subtraction,
                left: ExpressionNode[T](kind: RefNode, position: sourcePos),
                right: ExpressionNode[T](kind: LiteralNode, value: lo)
            ),
            linear = true
        )

    # Register the channel binding
    system.baseArray.addChannelBinding(channelPos, indexExpr, arrayElems)
    return true

proc addConstraint*[T](system: ConstraintSystem[T], constraint: StatefulConstraint[T]) =
    # Check for biconditional channeling pattern: (B == 1) <-> (X == val)
    if constraint.stateType == BooleanType:
        let bs = constraint.booleanState
        if not bs.isUnary and bs.booleanOp == Iff:
            if system.tryConvertBiconditionalToChannel(bs.leftConstraint, bs.rightConstraint):
                return
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

proc removeLastConstraint*[T](system: ConstraintSystem[T]) =
    # Removes the last constraint from the system
    system.baseArray.removeLastConstraint()

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
# MatrixElement constraint functions
################################################################################

proc matrixElement*[T](matrix: ConstrainedMatrix[T], row: int,
                        colExpr: AlgebraicExpression[T],
                        valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    ## Creates matrix element constraint: matrix[row, colExpr] = valueExpr
    ## Row is constant, col is a variable expression.
    var elements: seq[ArrayElement[T]] = @[]
    for i in 0..<matrix.size:
        elements.add(ArrayElement[T](isConstant: false, variablePosition: matrix.offset + i))
    let colPos = colExpr.node.position
    let valuePos = valueExpr.node.position
    return stateful.matrixElement[T](elements, matrix.m, matrix.n, row, colPos, valuePos)

proc matrixElement*[T](matrix: ConstrainedMatrix[T],
                        rowExpr: AlgebraicExpression[T], col: int,
                        valueExpr: AlgebraicExpression[T]): StatefulConstraint[T] =
    ## Creates matrix element constraint: matrix[rowExpr, col] = valueExpr
    ## Row is a variable expression, col is constant.
    var elements: seq[ArrayElement[T]] = @[]
    for i in 0..<matrix.size:
        elements.add(ArrayElement[T](isConstant: false, variablePosition: matrix.offset + i))
    let rowPos = rowExpr.node.position
    let valuePos = valueExpr.node.position
    return stateful.matrixElement[T](elements, matrix.m, matrix.n, rowPos, col, valuePos, rowIsVariable = true)

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
