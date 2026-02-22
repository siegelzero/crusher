import std/[packedsets, random, sequtils, strformat, tables]
import constraints/[stateful, algebraic, ordering, types]
import constraints/constraintNode
import constraints/relationalConstraint
import constraints/elementState
import constraints/matrixElement
import constraints/cumulative
import constraints/diffn
import expressions/expressions
import expressions/stateful as exprStateful
import expressions/sumExpression

################################################################################
# Type definitions
################################################################################

type
    ChannelBinding*[T] = object
        channelPosition*: int                # Position of the channel variable
        indexExpression*: AlgebraicExpression[T]  # Index expr (may be complex, e.g. X+1)
        arrayElements*: seq[ArrayElement[T]] # The array (constants and/or variable positions)

    ConstrainedArray*[T] = object
        len*: int
        constraints*: seq[StatefulConstraint[T]]
        domain*: seq[seq[T]]
        reducedDomain*: seq[seq[T]]
        entries*: seq[AlgebraicExpression[T]]
        channelPositions*: PackedSet[int]
        channelBindings*: seq[ChannelBinding[T]]
        channelsAtPosition*: Table[int, seq[int]]  # search_pos → [binding indices]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): AlgebraicExpression[T] {.inline.} = arr.entries[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield int(i)

iterator allSearchPositions*[T](arr: ConstrainedArray[T]): int =
    ## Iterates over all positions that are not channel variables.
    for i in 0..<arr.len:
        if i notin arr.channelPositions:
            yield int(i)

func `$`*[T](arr: ConstrainedArray[T]): string =
    return fmt"ConstrainedArray of size {arr.len}"


################################################################################
# ConstrainedArray Creation
################################################################################

func initConstrainedArray*[T](n: int): ConstrainedArray[T] =
    var entries: seq[AlgebraicExpression[T]] = @[]
    for pos in 0..<n:
        entries.add(
            newAlgebraicExpression[T](
                positions=toPackedSet[int](@[int(pos)]),
                node=ExpressionNode[T](kind: RefNode, position: pos),
                linear=true
            )
        )
    var domains = newSeq[seq[T]](n)
    # Initialize all domains with a reasonable default range
    when T is int:
        for i in 0..<n:
            domains[i] = toSeq(-100..100)  # Default integer range
    else:
        # For other types, leave empty (will need type-specific defaults)
        discard

    return ConstrainedArray[T](
        len: n,
        constraints: newSeq[StatefulConstraint[T]](),
        domain: domains,
        reducedDomain: @[],
        entries: entries
    )

func extendArray*[T](arr: var ConstrainedArray[T], m: int) =
    # Extends the array by m elements.
    let n = arr.entries.len()
    for pos in n..<(n + m):
        arr.entries.add(
            newAlgebraicExpression[T](
                positions=toPackedSet[int](@[int(pos)]),
                node=ExpressionNode[T](kind: RefNode, position: pos),
                linear=true
            )
        )
        # Add default domain for new element
        when T is int:
            arr.domain.add(toSeq(-100..100))
        else:
            arr.domain.add(newSeq[T]())
    arr.len += m

################################################################################
# ConstrainedArray domains
################################################################################

func setDomain*[T](arr: var ConstrainedArray[T], domain: openArray[T]) =
    # Sets domain of all positions to the given values.
    for position in arr.allPositions():
        arr.domain[position] = toSeq(domain)

func setDomain*[T](arr: var ConstrainedArray[T], position: int, domain: openArray[T]) =
    # Sets domain of position to the given values.
    arr.domain[position] = toSeq(domain)

func allDifferent*[T](arr: ConstrainedArray[T]): StatefulConstraint[T] {.inline.} =
    allDifferent(toSeq arr.allPositions())

proc addBaseConstraint*[T](arr: var ConstrainedArray[T], cons: StatefulConstraint[T]) {.inline.} =
    # Adds the constraint to the
    arr.constraints.add(cons)

proc removeLastConstraint*[T](arr: var ConstrainedArray[T]) {.inline.} =
    # Removes the last constraint and invalidates cached reduced domain
    arr.constraints.setLen(arr.constraints.len - 1)
    arr.reducedDomain = @[]

################################################################################
# Bounds propagation helpers
################################################################################

func ceilDivPositive[T](a, b: T): T =
    ## ceil(a / b) for b > 0
    if a >= 0: (a + b - 1) div b
    else: -((-a) div b)

func floorDivPositive[T](a, b: T): T =
    ## floor(a / b) for b > 0
    if a >= 0: a div b
    else: -((-a + b - 1) div b)

type
    LinearForm[T] = object
        coefficients: Table[int, T]
        constant: T
        relation: BinaryRelation

proc extractLinearForm[T](cons: RelationalConstraint[T]): (bool, LinearForm[T]) =
    ## Extract a normalized linear form from a RelationalConstraint.
    ## Returns (success, linearForm) where the form represents:
    ##   Σ(coeff[i] * x[i]) + constant  `relation`  0
    var leftCoeffs: Table[int, T]
    var leftConst: T
    var rightCoeffs: Table[int, T]
    var rightConst: T

    # Extract left side
    case cons.leftExpr.kind
    of SumExpr:
        let s = cons.leftExpr.sumExpr
        case s.evalMethod
        of PositionBased:
            leftCoeffs = s.coefficient
            leftConst = s.constant
        of ExpressionBased:
            return (false, LinearForm[T]())
    of ConstantExpr:
        leftConst = cons.leftExpr.constantValue
    else:
        return (false, LinearForm[T]())

    # Extract right side
    case cons.rightExpr.kind
    of SumExpr:
        let s = cons.rightExpr.sumExpr
        case s.evalMethod
        of PositionBased:
            rightCoeffs = s.coefficient
            rightConst = s.constant
        of ExpressionBased:
            return (false, LinearForm[T]())
    of ConstantExpr:
        rightConst = cons.rightExpr.constantValue
    else:
        return (false, LinearForm[T]())

    # Merge: left - right
    var merged: Table[int, T]
    for pos in leftCoeffs.keys:
        merged[pos] = leftCoeffs[pos]
    for pos in rightCoeffs.keys:
        if pos in merged:
            merged[pos] = merged[pos] - rightCoeffs[pos]
        else:
            merged[pos] = -rightCoeffs[pos]

    # Remove zero-coefficient entries
    var toRemove: seq[int]
    for pos in merged.keys:
        if merged[pos] == 0:
            toRemove.add(pos)
    for pos in toRemove:
        merged.del(pos)

    let mergedConst = leftConst - rightConst

    return (true, LinearForm[T](
        coefficients: merged,
        constant: mergedConst,
        relation: cons.relation
    ))

proc extractLinearCoeffs[T](expr: Expression[T]): (bool, Table[int, T], T) =
    ## Extract coefficients and constant from a linear Expression.
    ## Returns (success, coefficients, constant).
    case expr.kind
    of SumExpr:
        let s = expr.sumExpr
        case s.evalMethod
        of PositionBased:
            return (true, s.coefficient, s.constant)
        of ExpressionBased:
            return (false, initTable[int, T](), T(0))
    of ConstantExpr:
        return (true, initTable[int, T](), expr.constantValue)
    else:
        return (false, initTable[int, T](), T(0))

proc tryExtractAbsInner[T](expr: Expression[T]): (bool, Table[int, T], T) =
    ## If expr is abs(linear_expr), extract coefficients of the inner linear expression.
    ## Returns (success, coefficients, constant).
    if expr.kind != StatefulAlgebraicExpr:
        return (false, initTable[int, T](), T(0))
    let node = expr.algebraicExpr.algebraicExpr.node
    if node.kind != UnaryOpNode or node.unaryOp != AbsoluteValue:
        return (false, initTable[int, T](), T(0))
    # Build a temporary AlgebraicExpression from the inner node and try to linearize
    let innerExpr = AlgebraicExpression[T](
        positions: expr.positions,
        node: node.target,
        linear: true  # tentative; linearize uses evaluation which works for linear trees
    )
    # Verify linearity: linearize uses f(0) and f(e_i) to extract coefficients.
    # Verify by checking f(2*e_i) == 2*coeff_i + constant for each variable.
    let linearized = linearize(innerExpr)
    if linearized.evalMethod != PositionBased:
        return (false, initTable[int, T](), T(0))
    var testAssignment: Table[int, T]
    for pos in expr.positions.items:
        testAssignment[pos] = T(0)
    for pos in expr.positions.items:
        testAssignment[pos] = T(2)
        let actual = node.target.evaluate(testAssignment)
        let expected = T(2) * linearized.coefficient.getOrDefault(pos, T(0)) + linearized.constant
        if actual != expected:
            return (false, initTable[int, T](), T(0))
        testAssignment[pos] = T(0)
    return (true, linearized.coefficient, linearized.constant)

proc extractAbsRelaxations[T](cons: RelationalConstraint[T]): seq[LinearForm[T]] =
    ## For constraints of the form L == abs(R) where L and R are linear,
    ## extract two linear relaxation inequalities:
    ##   L - R >= 0  and  L + R >= 0
    ## Also works for L >= abs(R) and L > abs(R).
    result = @[]
    if cons.relation notin {EqualTo, GreaterThanEq, GreaterThan}:
        return

    var linCoeffs: Table[int, T]
    var linConst: T
    var absCoeffs: Table[int, T]
    var absConst: T
    var found = false

    # Case 1: L == abs(R) — left is linear, right is abs(linear)
    block:
        let (linOk, lc, lconst) = extractLinearCoeffs[T](cons.leftExpr)
        if linOk:
            let (absOk, ac, aconst) = tryExtractAbsInner[T](cons.rightExpr)
            if absOk:
                linCoeffs = lc
                linConst = lconst
                absCoeffs = ac
                absConst = aconst
                found = true

    # Case 2: abs(L) == R — left is abs(linear), right is linear
    if not found:
        let (absOk, ac, aconst) = tryExtractAbsInner[T](cons.leftExpr)
        if absOk:
            let (linOk, lc, lconst) = extractLinearCoeffs[T](cons.rightExpr)
            if linOk:
                linCoeffs = lc
                linConst = lconst
                absCoeffs = ac
                absConst = aconst
                found = true

    if not found:
        return

    # Generate: linExpr - absInner >= 0  (coeffs: lin - abs)
    var coeffs1: Table[int, T]
    for pos in linCoeffs.keys:
        coeffs1[pos] = linCoeffs[pos]
    for pos in absCoeffs.keys:
        if pos in coeffs1:
            coeffs1[pos] = coeffs1[pos] - absCoeffs[pos]
        else:
            coeffs1[pos] = -absCoeffs[pos]
    # Remove zeros
    var toRemove: seq[int]
    for pos in coeffs1.keys:
        if coeffs1[pos] == 0: toRemove.add(pos)
    for pos in toRemove: coeffs1.del(pos)

    result.add(LinearForm[T](
        coefficients: coeffs1,
        constant: linConst - absConst,
        relation: GreaterThanEq
    ))

    # Generate: linExpr + absInner >= 0  (coeffs: lin + abs)
    var coeffs2: Table[int, T]
    for pos in linCoeffs.keys:
        coeffs2[pos] = linCoeffs[pos]
    for pos in absCoeffs.keys:
        if pos in coeffs2:
            coeffs2[pos] = coeffs2[pos] + absCoeffs[pos]
        else:
            coeffs2[pos] = absCoeffs[pos]
    toRemove = @[]
    for pos in coeffs2.keys:
        if coeffs2[pos] == 0: toRemove.add(pos)
    for pos in toRemove: coeffs2.del(pos)

    result.add(LinearForm[T](
        coefficients: coeffs2,
        constant: linConst + absConst,
        relation: GreaterThanEq
    ))

proc evaluateExpression[T](expr: Expression[T], assignment: seq[T]): T =
    ## Statelessly evaluate an Expression with a raw assignment.
    case expr.kind
    of SumExpr:
        return expr.sumExpr.evaluate(assignment)
    of StatefulAlgebraicExpr:
        return expr.algebraicExpr.algebraicExpr.evaluate(assignment)
    of ConstantExpr:
        return expr.constantValue
    of MinExpr:
        return expr.minExpr.evaluate(assignment)
    of MaxExpr:
        return expr.maxExpr.evaluate(assignment)

proc evaluateConstraint[T](cons: StatefulConstraint[T], assignment: seq[T]): T =
    ## Statelessly evaluate a constraint's penalty with a raw assignment.
    ## Returns penalty (0 = satisfied). Returns -1 for unsupported types.
    case cons.stateType
    of AlgebraicType:
        return penalty(cons.algebraicState.constraint, assignment)
    of RelationalType:
        let leftVal = evaluateExpression(cons.relationalState.leftExpr, assignment)
        let rightVal = evaluateExpression(cons.relationalState.rightExpr, assignment)
        return cons.relationalState.relation.penalty(leftVal, rightVal)
    of CumulativeType:
        let cumState = cons.cumulativeState
        case cumState.evalMethod
        of PositionBased:
            # Build resource profile from scratch and count overloads
            var profile = newSeq[T](cumState.maxTime + 1)
            for i in 0..<cumState.originPositions.len:
                let origin = assignment[cumState.originPositions[i]]
                let dur = cumState.durations[i]
                let h = cumState.heights[i]
                let startT = int(origin)
                let endT = int(origin + dur)
                for t in max(0, startT) ..< min(endT, cumState.maxTime + 1):
                    profile[t] += h
            var cost: T = 0
            for t in 0..cumState.maxTime:
                if profile[t] > cumState.limit:
                    cost += profile[t] - cumState.limit
            return cost
        of ExpressionBased:
            return T(-1)
    of DiffnType:
        let dc = cons.diffnState
        var cost: T = 0
        for i in 0 ..< dc.n:
            let xi = dc.xExprs[i].evaluate(assignment)
            let yi = dc.yExprs[i].evaluate(assignment)
            let dxi = dc.dxExprs[i].evaluate(assignment)
            let dyi = dc.dyExprs[i].evaluate(assignment)
            for j in i + 1 ..< dc.n:
                let xj = dc.xExprs[j].evaluate(assignment)
                let yj = dc.yExprs[j].evaluate(assignment)
                let dxj = dc.dxExprs[j].evaluate(assignment)
                let dyj = dc.dyExprs[j].evaluate(assignment)
                if dxi > 0 and dyi > 0 and dxj > 0 and dyj > 0 and
                   xi < xj + dxj and xj < xi + dxi and
                   yi < yj + dyj and yj < yi + dyi:
                    cost += 1
        return cost
    else:
        return T(-1)  # sentinel: not supported

################################################################################
# ConstrainedArray domain reduction
################################################################################

proc reduceDomain*[T](carray: ConstrainedArray[T]): seq[seq[T]] =
    var
        reduced = newSeq[seq[T]](carray.len)
        currentDomain = newSeq[PackedSet[T]](carray.len)

    for pos in carray.allPositions():
        currentDomain[pos] = toPackedSet[T](carray.domain[pos])

    # First examine any single-variable constraints to reduce domains
    for cons in carray.constraints:
        if cons.positions.len != 1:
            continue
        let pos = toSeq(cons.positions)[0]
        # Create a temporary assignment for testing this constraint
        var tempAssignment = newSeq[T](carray.len)
        # Initialize with first values from domains (doesn't matter, we only care about position pos)
        for i in 0..<carray.len:
            if carray.domain[i].len > 0:
                tempAssignment[i] = carray.domain[i][0]

        var removed = 0
        for d in carray.domain[pos]:
            tempAssignment[pos] = d
            # Test the constraint without requiring it to be initialized
            var tempPenalty = 0
            case cons.stateType:
                of AlgebraicType:
                    tempPenalty = penalty(cons.algebraicState.constraint, tempAssignment)
                of RelationalType:
                    # RelationalConstraint needs to be evaluated differently
                    # Skip for now - these are typically multi-variable anyway
                    continue
                of AllDifferentType, AtLeastType, AtMostType, ElementType, OrderingType, GlobalCardinalityType, MultiknapsackType, SequenceType, BooleanType, CumulativeType, GeostType, IrdcsType, CircuitType, SubcircuitType, AllDifferentExcept0Type, LexOrderType, TableConstraintType, RegularType, CountEqType, DiffnType, MatrixElementType:
                    # Skip these constraint types for domain reduction
                    continue

            if tempPenalty > 0:
                currentDomain[pos].excl(d)
                removed += 1

    # Cumulative constraint domain reduction
    for cons in carray.constraints:
        if cons.stateType != CumulativeType:
            continue

        let cumState = cons.cumulativeState
        case cumState.evalMethod:
        of PositionBased:
            for taskIdx in 0..<cumState.originPositions.len:
                let pos = cumState.originPositions[taskIdx]
                let height = cumState.heights[taskIdx]

                # Skip tasks whose height exceeds capacity — no feasible placement exists
                # (the solver will fail to reach cost 0)
                if height > cumState.limit:
                    continue

                # Prune negative origins (they place the task partially outside the
                # tracked resource profile, hiding violations)
                var toExclude: seq[T] = @[]
                for v in currentDomain[pos].items:
                    if v < T(0):
                        toExclude.add(v)
                for v in toExclude:
                    currentDomain[pos].excl(v)

        of ExpressionBased:
            discard

    # Detect int_div patterns: pairs of constraints encoding z = floor(x / c)
    #   x - c*z >= 0     (i.e., c*z <= x)
    #   x - c*z <= c-1   (i.e., x < c*(z+1))
    # Applied inside the outer loop after bounds propagation.
    type
        DivHalf = object
            posX, posZ: int
            coeff: T
            isLower: bool
        DivPattern = object
            posX, posZ: int
            coeff: T

    var divPatterns: seq[DivPattern]
    block:
        var divHalves: seq[DivHalf]
        for cons in carray.constraints:
            if cons.stateType != RelationalType or cons.positions.len != 2:
                continue
            let (success, form) = extractLinearForm(cons.relationalState)
            if not success:
                continue
            let positions = toSeq(cons.positions.items)
            if positions.len != 2:
                continue
            let p0 = positions[0]
            let p1 = positions[1]
            let c0 = form.coefficients.getOrDefault(p0, T(0))
            let c1 = form.coefficients.getOrDefault(p1, T(0))

            if form.relation == GreaterThanEq and form.constant == 0:
                if c0 == 1 and c1 < 0:
                    divHalves.add(DivHalf(posX: p0, posZ: p1, coeff: -c1, isLower: true))
                elif c1 == 1 and c0 < 0:
                    divHalves.add(DivHalf(posX: p1, posZ: p0, coeff: -c0, isLower: true))
            elif form.relation == LessThanEq:
                if c0 == 1 and c1 < 0:
                    let c = -c1
                    if -form.constant == c - 1:
                        divHalves.add(DivHalf(posX: p0, posZ: p1, coeff: c, isLower: false))
                elif c1 == 1 and c0 < 0:
                    let c = -c0
                    if -form.constant == c - 1:
                        divHalves.add(DivHalf(posX: p1, posZ: p0, coeff: c, isLower: false))

        for i in 0..<divHalves.len:
            if not divHalves[i].isLower:
                continue
            for j in 0..<divHalves.len:
                if divHalves[j].isLower:
                    continue
                if divHalves[i].posX == divHalves[j].posX and
                   divHalves[i].posZ == divHalves[j].posZ and
                   divHalves[i].coeff == divHalves[j].coeff:
                    divPatterns.add(DivPattern(
                        posX: divHalves[i].posX,
                        posZ: divHalves[i].posZ,
                        coeff: divHalves[i].coeff))
                    break

        if divPatterns.len > 0:
            stderr.writeLine(&"[DomRed] Detected {divPatterns.len} int_div patterns")

    # Phase 3+4: Bounds propagation + AllDifferent, iterated to fixed point
    # Pre-extract linear forms from relational constraints
    var linearForms: seq[LinearForm[T]]
    for cons in carray.constraints:
        if cons.stateType == RelationalType:
            let (success, form) = extractLinearForm(cons.relationalState)
            if success:
                linearForms.add(form)
            else:
                # Try to extract linear relaxations from abs constraints
                # e.g., d == abs(b - a) yields d - b + a >= 0 and d + b - a >= 0
                let absForms = extractAbsRelaxations[T](cons.relationalState)
                linearForms.add(absForms)
        elif cons.stateType == OrderingType:
            # Add synthetic linear forms for ordering constraints
            # StrictlyIncreasing: x[p2] - x[p1] >= 1  →  x[p2] - x[p1] - 1 >= 0
            # Increasing:         x[p2] - x[p1] >= 0
            # StrictlyDecreasing: x[p1] - x[p2] >= 1  →  x[p1] - x[p2] - 1 >= 0
            # Decreasing:         x[p1] - x[p2] >= 0
            let ordState = cons.orderingState
            if ordState.evalMethod == PositionBased:
                for i in 0..<(ordState.sortedPositions.len - 1):
                    let p1 = ordState.sortedPositions[i]
                    let p2 = ordState.sortedPositions[i + 1]
                    var coeffs: Table[int, T]
                    var constant: T
                    case ordState.orderingType:
                    of StrictlyIncreasing:
                        coeffs = {p2: T(1), p1: T(-1)}.toTable
                        constant = T(-1)
                    of Increasing:
                        coeffs = {p2: T(1), p1: T(-1)}.toTable
                        constant = T(0)
                    of StrictlyDecreasing:
                        coeffs = {p1: T(1), p2: T(-1)}.toTable
                        constant = T(-1)
                    of Decreasing:
                        coeffs = {p1: T(1), p2: T(-1)}.toTable
                        constant = T(0)
                    linearForms.add(LinearForm[T](
                        coefficients: coeffs,
                        constant: constant,
                        relation: GreaterThanEq
                    ))

    # Normalize each linear form to >= 0
    type NormalizedForm = object
        coefficients: Table[int, T]
        constant: T

    var normalizedForms: seq[NormalizedForm]
    for form in linearForms:
        case form.relation
        of GreaterThanEq:
            normalizedForms.add(NormalizedForm(
                coefficients: form.coefficients, constant: form.constant))
        of LessThanEq:
            var negCoeffs: Table[int, T]
            for pos in form.coefficients.keys:
                negCoeffs[pos] = -form.coefficients[pos]
            normalizedForms.add(NormalizedForm(
                coefficients: negCoeffs, constant: -form.constant))
        of GreaterThan:
            normalizedForms.add(NormalizedForm(
                coefficients: form.coefficients, constant: form.constant - 1))
        of LessThan:
            var negCoeffs: Table[int, T]
            for pos in form.coefficients.keys:
                negCoeffs[pos] = -form.coefficients[pos]
            normalizedForms.add(NormalizedForm(
                coefficients: negCoeffs, constant: -form.constant - 1))
        of EqualTo:
            normalizedForms.add(NormalizedForm(
                coefficients: form.coefficients, constant: form.constant))
            var negCoeffs: Table[int, T]
            for pos in form.coefficients.keys:
                negCoeffs[pos] = -form.coefficients[pos]
            normalizedForms.add(NormalizedForm(
                coefficients: negCoeffs, constant: -form.constant))
        of NotEqualTo, CommonFactor, CoPrime:
            discard

    # Collect allDifferent constraint positions for Phase 4
    var allDiffGroups: seq[seq[int]]
    for cons in carray.constraints:
        if cons.stateType == AllDifferentType and
           cons.allDifferentState.evalMethod == PositionBased:
            allDiffGroups.add(toSeq(cons.positions.items))

    # Collect small-arity constraints for GAC
    const MAX_GAC_ARITY = 4
    const MAX_GAC_COMBOS = 1_000_000
    var gacConstraints: seq[int]  # indices into carray.constraints
    for i, cons in carray.constraints:
        if cons.stateType in {AlgebraicType, RelationalType}:
            let arity = cons.positions.len
            if arity >= 2 and arity <= MAX_GAC_ARITY:
                gacConstraints.add(i)

    # Step A: Group matrixElement constraints by shared matrix + constant index
    # for cross-constraint backward propagation (Phase 6b)
    type
        MatrixGroupEntry = object
            indexPos: int    # colPos (const-row) or rowPos (const-col)
            valPos: int
            matState: MatrixElementState[T]
        MatrixGroupKey = tuple[matrixOffset: int, constIdx: int, isConstRow: bool]

    var matrixGroups: Table[MatrixGroupKey, seq[MatrixGroupEntry]]
    for cons in carray.constraints:
        if cons.stateType != MatrixElementType:
            continue
        let ms = cons.matrixElementState
        if ms.matrixElements.len == 0:
            continue
        # Find the matrix offset from the first variable element
        var matOffset = -1
        for elem in ms.matrixElements:
            if not elem.isConstant:
                matOffset = elem.variablePosition
                break
        if matOffset < 0:
            continue  # all-constant matrix, skip

        if ms.rowKind == ConstantIndex and ms.colKind == VariableIndex:
            let key: MatrixGroupKey = (matrixOffset: matOffset, constIdx: ms.rowConstant, isConstRow: true)
            if key notin matrixGroups:
                matrixGroups[key] = @[]
            matrixGroups[key].add(MatrixGroupEntry(
                indexPos: ms.colPosition, valPos: ms.valuePosition, matState: ms))
        elif ms.rowKind == VariableIndex and ms.colKind == ConstantIndex:
            let key: MatrixGroupKey = (matrixOffset: matOffset, constIdx: ms.colConstant, isConstRow: false)
            if key notin matrixGroups:
                matrixGroups[key] = @[]
            matrixGroups[key].add(MatrixGroupEntry(
                indexPos: ms.rowPosition, valPos: ms.valuePosition, matState: ms))

    # Outer fixed-point loop: bounds propagation <-> allDifferent propagation
    for outerIter in 0..<20:
        var outerChanged = false

        # Phase 3: Bounds propagation
        if normalizedForms.len > 0:
            # Compute domainMin/domainMax from current PackedSets
            var domainMin = newSeq[T](carray.len)
            var domainMax = newSeq[T](carray.len)
            for pos in carray.allPositions():
                if currentDomain[pos].len > 0:
                    domainMin[pos] = T.high
                    domainMax[pos] = T.low
                    for v in currentDomain[pos].items:
                        if v < domainMin[pos]: domainMin[pos] = v
                        if v > domainMax[pos]: domainMax[pos] = v
                else:
                    domainMin[pos] = T(0)
                    domainMax[pos] = T(0)

            # Inner fixed-point loop for bounds propagation
            for iteration in 0..<100:
                var changed = false

                for form in normalizedForms:
                    for pos_j in form.coefficients.keys:
                        let a_j = form.coefficients[pos_j]
                        if a_j == 0: continue

                        var restMax: T = 0
                        for pos_i in form.coefficients.keys:
                            if pos_i == pos_j: continue
                            let a_i = form.coefficients[pos_i]
                            if a_i > 0:
                                restMax += a_i * domainMax[pos_i]
                            else:
                                restMax += a_i * domainMin[pos_i]

                        let bound = -form.constant - restMax

                        if a_j > 0:
                            let newMin = ceilDivPositive(bound, a_j)
                            if newMin > domainMin[pos_j]:
                                domainMin[pos_j] = newMin
                                changed = true
                        else:
                            let newMax = floorDivPositive(-bound, -a_j)
                            if newMax < domainMax[pos_j]:
                                domainMax[pos_j] = newMax
                                changed = true

                if not changed:
                    break

                var infeasible = false
                for pos in carray.allPositions():
                    if domainMin[pos] > domainMax[pos]:
                        infeasible = true
                        break
                if infeasible:
                    break

            # Apply tightened bounds to PackedSets
            for pos in carray.allPositions():
                for v in toSeq(currentDomain[pos].items):
                    if v < domainMin[pos] or v > domainMax[pos]:
                        currentDomain[pos].excl(v)
                        outerChanged = true

        # Phase IntDiv: Restrict x to ∪{[c*z, c*z+c-1] : z ∈ domain(z)}
        if divPatterns.len > 0:
            for patIdx, pat in divPatterns:
                let oldXSize = currentDomain[pat.posX].len
                let oldZSize = currentDomain[pat.posZ].len
                if oldXSize == 0 or oldZSize == 0: continue

                # Find x domain bounds
                var xMin = T.high
                var xMax = T.low
                for v in currentDomain[pat.posX].items:
                    if v < xMin: xMin = v
                    if v > xMax: xMax = v

                # Prune z values whose windows don't overlap x's domain range
                for z in toSeq(currentDomain[pat.posZ].items):
                    let lo = pat.coeff * z
                    let hi = lo + pat.coeff - 1
                    if hi < xMin or lo > xMax:
                        currentDomain[pat.posZ].excl(z)

                # Build validX as union of windows from remaining z values
                var validX = initPackedSet[T]()
                for z in currentDomain[pat.posZ].items:
                    let lo = max(xMin, pat.coeff * z)
                    let hi = min(xMax, pat.coeff * z + pat.coeff - 1)
                    for v in lo..hi:
                        if v in currentDomain[pat.posX]:
                            validX.incl(v)
                currentDomain[pat.posX] = validX

                let newXSize = currentDomain[pat.posX].len
                let newZSize = currentDomain[pat.posZ].len
                if newXSize < oldXSize or newZSize < oldZSize:
                    outerChanged = true
                    stderr.writeLine(&"[DomRed] IntDiv: x@{pat.posX} {oldXSize}->{newXSize}, z@{pat.posZ} {oldZSize}->{newZSize}")

        # Phase GAC: Generalized Arc Consistency for small-arity constraints
        # For each constraint, enumerate all value combinations and keep only
        # values that appear in at least one satisfying tuple.
        if gacConstraints.len > 0:
            var tempAssignment = newSeq[T](carray.len)
            for i in 0..<carray.len:
                if currentDomain[i].len > 0:
                    for v in currentDomain[i].items:
                        tempAssignment[i] = v
                        break

            for consIdx in gacConstraints:
                let cons = carray.constraints[consIdx]
                let positions = toSeq(cons.positions.items)

                # Get current domain values for each position
                var domains: seq[seq[T]]
                var totalCombinations = 1
                for pos in positions:
                    let vals = toSeq(currentDomain[pos].items)
                    if vals.len == 0:
                        totalCombinations = 0
                        break
                    totalCombinations *= vals.len
                    if totalCombinations > MAX_GAC_COMBOS:
                        break
                    domains.add(vals)

                if totalCombinations == 0 or totalCombinations > MAX_GAC_COMBOS:
                    continue

                # Track which values have support (appear in a satisfying tuple)
                var supported = newSeq[PackedSet[T]](positions.len)
                for i in 0..<positions.len:
                    supported[i] = initPackedSet[T]()

                # Enumerate all combinations via odometer
                var indices = newSeq[int](positions.len)
                for combo in 0..<totalCombinations:
                    # Set values in temp assignment
                    for i in 0..<positions.len:
                        tempAssignment[positions[i]] = domains[i][indices[i]]

                    # Evaluate penalty
                    let pen = evaluateConstraint(cons, tempAssignment)
                    if pen == 0:
                        for i in 0..<positions.len:
                            supported[i].incl(domains[i][indices[i]])

                    # Advance odometer
                    var carry = positions.len - 1
                    while carry >= 0:
                        indices[carry] += 1
                        if indices[carry] >= domains[carry].len:
                            indices[carry] = 0
                            carry -= 1
                        else:
                            break

                # Remove unsupported values
                var pruned = 0
                for i in 0..<positions.len:
                    let pos = positions[i]
                    for v in toSeq(currentDomain[pos].items):
                        if v notin supported[i]:
                            currentDomain[pos].excl(v)
                            outerChanged = true
                            pruned += 1

        # Phase 4: Geost pairwise arc consistency
        for cons in carray.constraints:
            if cons.stateType != GeostType:
                continue
            let gs = cons.geostState
            let np = gs.numPieces

            # Convert each placement's cells to PackedSet for fast intersection check
            var cellSets = newSeq[seq[PackedSet[int]]](np)
            for p in 0..<np:
                let pos = gs.placementPositions[p]
                cellSets[p] = newSeq[PackedSet[int]](gs.cellsByPlacement[p].len)
                for v in 0..<gs.cellsByPlacement[p].len:
                    if T(v) notin currentDomain[pos]:
                        continue
                    for cell in gs.cellsByPlacement[p][v]:
                        cellSets[p][v].incl(cell)

            # For each pair of pieces, prune placements with no compatible partner
            for a in 0..<np:
                let posA = gs.placementPositions[a]
                for b in (a+1)..<np:
                    let posB = gs.placementPositions[b]
                    # Check each placement of A against all placements of B
                    for va in toSeq(currentDomain[posA].items):
                        var hasCompat = false
                        for vb in currentDomain[posB].items:
                            if (cellSets[a][va] * cellSets[b][vb]).len == 0:
                                hasCompat = true
                                break
                        if not hasCompat:
                            currentDomain[posA].excl(va)
                            outerChanged = true
                    # Check each placement of B against all placements of A
                    for vb in toSeq(currentDomain[posB].items):
                        var hasCompat = false
                        for va in currentDomain[posA].items:
                            if (cellSets[b][vb] * cellSets[a][va]).len == 0:
                                hasCompat = true
                                break
                        if not hasCompat:
                            currentDomain[posB].excl(vb)
                            outerChanged = true

            if outerChanged:
                stderr.writeLine(&"[Init] Geost arc consistency: {np} pieces, reduced domains")
                for p in 0..<np:
                    let pos = gs.placementPositions[p]
                    stderr.writeLine(&"[Init]   Piece {p}: {gs.cellsByPlacement[p].len} -> {currentDomain[pos].len} placements")

        # Phase 5: AllDifferent domain reduction
        for adPositions in allDiffGroups:
            let k = adPositions.len

            # Cardinality check
            var domainUnion: PackedSet[T]
            for pos in adPositions:
                domainUnion = domainUnion + currentDomain[pos]
            if domainUnion.len < k:
                currentDomain[adPositions[0]] = initPackedSet[T]()

            # Singleton propagation to fixed point
            for iteration in 0..<k:
                var changed = false
                for pos in adPositions:
                    if currentDomain[pos].len == 1:
                        var singletonVal: T
                        for v in currentDomain[pos].items:
                            singletonVal = v
                        for otherPos in adPositions:
                            if otherPos != pos and singletonVal in currentDomain[otherPos]:
                                currentDomain[otherPos].excl(singletonVal)
                                changed = true
                                outerChanged = true
                if not changed:
                    break

        # Phase 5b: AtMost/AtLeast domain reduction
        for cons in carray.constraints:
            if cons.stateType == AtMostType and
               cons.atMostState.evalMethod == PositionBased:
                let maxOcc = cons.atMostState.maxOccurrences
                let target = cons.atMostState.targetValue
                # Count positions forced to targetValue (singleton domain)
                var forced = 0
                for pos in cons.positions.items:
                    if currentDomain[pos].len == 1 and T(target) in currentDomain[pos]:
                        forced += 1
                if forced >= maxOcc:
                    # Remove targetValue from all non-singleton positions
                    for pos in cons.positions.items:
                        if currentDomain[pos].len > 1 and T(target) in currentDomain[pos]:
                            currentDomain[pos].excl(T(target))
                            outerChanged = true

            elif cons.stateType == AtLeastType and
                 cons.atLeastState.evalMethod == PositionBased:
                let minOcc = cons.atLeastState.minOccurrences
                let target = cons.atLeastState.targetValue
                # Count positions that CAN take targetValue
                var possible = 0
                var possiblePositions: seq[int]
                for pos in cons.positions.items:
                    if T(target) in currentDomain[pos]:
                        possible += 1
                        possiblePositions.add(pos)
                if possible == minOcc:
                    # All positions that can take targetValue must take it
                    for pos in possiblePositions:
                        if currentDomain[pos].len > 1:
                            currentDomain[pos] = toPackedSet[T]([T(target)])
                            outerChanged = true

        # Phase 6: Element/MatrixElement arc consistency
        for cons in carray.constraints:
            if cons.stateType == ElementType:
                let elemState = cons.elementState
                if elemState.evalMethod == PositionBased:
                    let idxPos = elemState.indexPosition
                    let valPos = elemState.valuePosition
                    let arrSize = elemState.getArraySize()

                    if elemState.isConstantArray:
                        # Constant array: array[index] == value
                        # Index pruning: remove i from domain(index) if constantArray[i] not in domain(value)
                        for i in toSeq(currentDomain[idxPos].items):
                            if i >= 0 and i < arrSize:
                                if elemState.constantArray[i] notin currentDomain[valPos]:
                                    currentDomain[idxPos].excl(i)
                                    outerChanged = true
                            else:
                                # Out of bounds index — always violated
                                currentDomain[idxPos].excl(i)
                                outerChanged = true

                        # Value pruning: remove v from domain(value) if no i in domain(index) maps to v
                        var reachableValues: PackedSet[T]
                        for i in currentDomain[idxPos].items:
                            if i >= 0 and i < arrSize:
                                reachableValues.incl(elemState.constantArray[i])
                        for v in toSeq(currentDomain[valPos].items):
                            if v notin reachableValues:
                                currentDomain[valPos].excl(v)
                                outerChanged = true

                    else:
                        # Variable array: array[index] == value
                        # Index pruning: remove i from domain(index) if domain(array[i]) ∩ domain(value) = ∅
                        for i in toSeq(currentDomain[idxPos].items):
                            if i >= 0 and i < arrSize:
                                let elem = elemState.arrayElements[i]
                                if elem.isConstant:
                                    if elem.constantValue notin currentDomain[valPos]:
                                        currentDomain[idxPos].excl(i)
                                        outerChanged = true
                                else:
                                    if (currentDomain[elem.variablePosition] * currentDomain[valPos]).len == 0:
                                        currentDomain[idxPos].excl(i)
                                        outerChanged = true
                            else:
                                currentDomain[idxPos].excl(i)
                                outerChanged = true

                        # Value pruning: remove v from domain(value) if no i in domain(index) has v reachable
                        var reachableValues: PackedSet[T]
                        for i in currentDomain[idxPos].items:
                            if i >= 0 and i < arrSize:
                                let elem = elemState.arrayElements[i]
                                if elem.isConstant:
                                    reachableValues.incl(elem.constantValue)
                                else:
                                    reachableValues = reachableValues + currentDomain[elem.variablePosition]
                        for v in toSeq(currentDomain[valPos].items):
                            if v notin reachableValues:
                                currentDomain[valPos].excl(v)
                                outerChanged = true

            elif cons.stateType == MatrixElementType:
                let matState = cons.matrixElementState
                let valPos = matState.valuePosition
                let numRows = matState.numRows
                let numCols = matState.numCols

                if matState.rowKind == ConstantIndex and matState.colKind == VariableIndex:
                    # Const-row variant: matrix[constRow, col] == value
                    let constRow = matState.rowConstant
                    let colPos = matState.colPosition

                    # Col pruning: remove c from domain(col) if domain(matrix[constRow,c]) ∩ domain(value) = ∅
                    for c in toSeq(currentDomain[colPos].items):
                        if c >= 0 and c < numCols:
                            let flatIdx = constRow * numCols + c
                            let elem = matState.matrixElements[flatIdx]
                            if elem.isConstant:
                                if elem.constantValue notin currentDomain[valPos]:
                                    currentDomain[colPos].excl(c)
                                    outerChanged = true
                            else:
                                if (currentDomain[elem.variablePosition] * currentDomain[valPos]).len == 0:
                                    currentDomain[colPos].excl(c)
                                    outerChanged = true
                        else:
                            currentDomain[colPos].excl(c)
                            outerChanged = true

                    # Value pruning: remove v from domain(value) if unreachable
                    var reachableValues: PackedSet[T]
                    for c in currentDomain[colPos].items:
                        if c >= 0 and c < numCols:
                            let flatIdx = constRow * numCols + c
                            let elem = matState.matrixElements[flatIdx]
                            if elem.isConstant:
                                reachableValues.incl(elem.constantValue)
                            else:
                                reachableValues = reachableValues + currentDomain[elem.variablePosition]
                    for v in toSeq(currentDomain[valPos].items):
                        if v notin reachableValues:
                            currentDomain[valPos].excl(v)
                            outerChanged = true

                    # Backward propagation to matrix cells
                    # When col is singleton {c}: domain(Z[constRow, c]) ∩= domain(value)
                    if currentDomain[colPos].len == 1:
                        var singleCol: T
                        for v in currentDomain[colPos].items: singleCol = v
                        if singleCol >= 0 and singleCol < numCols:
                            let flatIdx = constRow * numCols + singleCol
                            let elem = matState.matrixElements[flatIdx]
                            if not elem.isConstant:
                                let mPos = elem.variablePosition
                                let intersection = currentDomain[mPos] * currentDomain[valPos]
                                if intersection.len < currentDomain[mPos].len:
                                    currentDomain[mPos] = intersection
                                    outerChanged = true

                elif matState.rowKind == VariableIndex and matState.colKind == ConstantIndex:
                    # Const-col variant: matrix[row, constCol] == value
                    let constCol = matState.colConstant
                    let rowPos = matState.rowPosition

                    # Row pruning: remove r from domain(row) if domain(matrix[r,constCol]) ∩ domain(value) = ∅
                    for r in toSeq(currentDomain[rowPos].items):
                        if r >= 0 and r < numRows:
                            let flatIdx = r * numCols + constCol
                            let elem = matState.matrixElements[flatIdx]
                            if elem.isConstant:
                                if elem.constantValue notin currentDomain[valPos]:
                                    currentDomain[rowPos].excl(r)
                                    outerChanged = true
                            else:
                                if (currentDomain[elem.variablePosition] * currentDomain[valPos]).len == 0:
                                    currentDomain[rowPos].excl(r)
                                    outerChanged = true
                        else:
                            currentDomain[rowPos].excl(r)
                            outerChanged = true

                    # Value pruning: remove v from domain(value) if unreachable
                    var reachableValues: PackedSet[T]
                    for r in currentDomain[rowPos].items:
                        if r >= 0 and r < numRows:
                            let flatIdx = r * numCols + constCol
                            let elem = matState.matrixElements[flatIdx]
                            if elem.isConstant:
                                reachableValues.incl(elem.constantValue)
                            else:
                                reachableValues = reachableValues + currentDomain[elem.variablePosition]
                    for v in toSeq(currentDomain[valPos].items):
                        if v notin reachableValues:
                            currentDomain[valPos].excl(v)
                            outerChanged = true

                    # Backward propagation to matrix cells
                    # When row is singleton {r}: domain(Z[r, constCol]) ∩= domain(value)
                    if currentDomain[rowPos].len == 1:
                        var singleRow: T
                        for v in currentDomain[rowPos].items: singleRow = v
                        if singleRow >= 0 and singleRow < numRows:
                            let flatIdx = singleRow * numCols + constCol
                            let elem = matState.matrixElements[flatIdx]
                            if not elem.isConstant:
                                let mPos = elem.variablePosition
                                let intersection = currentDomain[mPos] * currentDomain[valPos]
                                if intersection.len < currentDomain[mPos].len:
                                    currentDomain[mPos] = intersection
                                    outerChanged = true

                elif matState.rowKind == VariableIndex and matState.colKind == VariableIndex:
                    # Var-var variant: matrix[row, col] == value
                    let rowPos = matState.rowPosition
                    let colPos = matState.colPosition

                    # Row pruning: remove r if no col c has domain(matrix[r,c]) ∩ domain(value) ≠ ∅
                    for r in toSeq(currentDomain[rowPos].items):
                        if r >= 0 and r < numRows:
                            var hasSupport = false
                            for c in currentDomain[colPos].items:
                                if c >= 0 and c < numCols:
                                    let flatIdx = r * numCols + c
                                    let elem = matState.matrixElements[flatIdx]
                                    if elem.isConstant:
                                        if elem.constantValue in currentDomain[valPos]:
                                            hasSupport = true
                                            break
                                    else:
                                        if (currentDomain[elem.variablePosition] * currentDomain[valPos]).len > 0:
                                            hasSupport = true
                                            break
                            if not hasSupport:
                                currentDomain[rowPos].excl(r)
                                outerChanged = true
                        else:
                            currentDomain[rowPos].excl(r)
                            outerChanged = true

                    # Col pruning: remove c if no row r has domain(matrix[r,c]) ∩ domain(value) ≠ ∅
                    for c in toSeq(currentDomain[colPos].items):
                        if c >= 0 and c < numCols:
                            var hasSupport = false
                            for r in currentDomain[rowPos].items:
                                if r >= 0 and r < numRows:
                                    let flatIdx = r * numCols + c
                                    let elem = matState.matrixElements[flatIdx]
                                    if elem.isConstant:
                                        if elem.constantValue in currentDomain[valPos]:
                                            hasSupport = true
                                            break
                                    else:
                                        if (currentDomain[elem.variablePosition] * currentDomain[valPos]).len > 0:
                                            hasSupport = true
                                            break
                            if not hasSupport:
                                currentDomain[colPos].excl(c)
                                outerChanged = true
                        else:
                            currentDomain[colPos].excl(c)
                            outerChanged = true

                    # Value pruning: remove v from domain(value) if unreachable
                    var reachableValues: PackedSet[T]
                    for r in currentDomain[rowPos].items:
                        if r >= 0 and r < numRows:
                            for c in currentDomain[colPos].items:
                                if c >= 0 and c < numCols:
                                    let flatIdx = r * numCols + c
                                    let elem = matState.matrixElements[flatIdx]
                                    if elem.isConstant:
                                        reachableValues.incl(elem.constantValue)
                                    else:
                                        reachableValues = reachableValues + currentDomain[elem.variablePosition]
                    for v in toSeq(currentDomain[valPos].items):
                        if v notin reachableValues:
                            currentDomain[valPos].excl(v)
                            outerChanged = true

        # Phase 6b: Cross-constraint backward propagation to matrix cells
        # For each group of matrixElement constraints sharing the same matrix row/col,
        # restrict each matrix cell to the union of value domains that could reach it.
        for key in matrixGroups.keys:
            let group = matrixGroups[key]
            if group.len == 0:
                continue
            let ms0 = group[0].matState
            let numCols = ms0.numCols
            let numRows = ms0.numRows

            if key.isConstRow:
                let constRow = key.constIdx
                # For each column c in the matrix row:
                # allowedValues = union of domain(valPos) for all constraints where c ∈ domain(colPos)
                for c in 0..<numCols:
                    let flatIdx = constRow * numCols + c
                    let elem = ms0.matrixElements[flatIdx]
                    if elem.isConstant:
                        continue
                    let mPos = elem.variablePosition

                    var allowedValues = initPackedSet[T]()
                    for entry in group:
                        if T(c) in currentDomain[entry.indexPos]:
                            allowedValues = allowedValues + currentDomain[entry.valPos]

                    if allowedValues.len > 0:
                        let intersection = currentDomain[mPos] * allowedValues
                        if intersection.len < currentDomain[mPos].len:
                            currentDomain[mPos] = intersection
                            outerChanged = true
            else:
                let constCol = key.constIdx
                # For each row r in the matrix column:
                # allowedValues = union of domain(valPos) for all constraints where r ∈ domain(rowPos)
                for r in 0..<numRows:
                    let flatIdx = r * numCols + constCol
                    let elem = ms0.matrixElements[flatIdx]
                    if elem.isConstant:
                        continue
                    let mPos = elem.variablePosition

                    var allowedValues = initPackedSet[T]()
                    for entry in group:
                        if T(r) in currentDomain[entry.indexPos]:
                            allowedValues = allowedValues + currentDomain[entry.valPos]

                    if allowedValues.len > 0:
                        let intersection = currentDomain[mPos] * allowedValues
                        if intersection.len < currentDomain[mPos].len:
                            currentDomain[mPos] = intersection
                            outerChanged = true

        if not outerChanged:
            break

    # Convert PackedSets to output sequences
    for pos in carray.allPositions():
        reduced[pos] = toSeq(currentDomain[pos])

    return reduced

################################################################################
# Deep copy for ConstrainedArray
################################################################################

proc deepCopy*[T](arr: ConstrainedArray[T]): ConstrainedArray[T] =
    ## Creates a deep copy of a ConstrainedArray for thread-safe parallel processing
    result.len = arr.len

    # Deep copy the domain (seq[seq[T]] requires copying both outer and inner sequences)
    result.domain = newSeq[seq[T]](arr.domain.len)
    for i, innerSeq in arr.domain:
        result.domain[i] = innerSeq  # This creates a deep copy of the inner seq[T]

    # Deep copy the reducedDomain if it exists
    if arr.reducedDomain.len > 0:
        result.reducedDomain = newSeq[seq[T]](arr.reducedDomain.len)
        for i, innerSeq in arr.reducedDomain:
            result.reducedDomain[i] = innerSeq  # This creates a deep copy of the inner seq[T]
    else:
        result.reducedDomain = @[]

    # Deep copy entries - AlgebraicExpression[T] are ref objects, must deep copy for ARC thread safety
    result.entries = newSeq[AlgebraicExpression[T]](arr.entries.len)
    for i, expr in arr.entries:
        result.entries[i] = expr.deepCopy()

    # Deep copy all stateful constraints
    result.constraints = newSeq[StatefulConstraint[T]](arr.constraints.len)
    for i, constraint in arr.constraints:
        result.constraints[i] = constraint.deepCopy()

    # Deep copy channel data - channelBindings contains AlgebraicExpression refs
    result.channelPositions = arr.channelPositions
    result.channelBindings = newSeq[ChannelBinding[T]](arr.channelBindings.len)
    for i, binding in arr.channelBindings:
        result.channelBindings[i] = ChannelBinding[T](
            channelPosition: binding.channelPosition,
            indexExpression: binding.indexExpression.deepCopy(),
            arrayElements: binding.arrayElements
        )
    result.channelsAtPosition = arr.channelsAtPosition

