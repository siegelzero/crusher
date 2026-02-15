import std/[packedsets, sequtils, strformat, tables]

import constraints/[stateful, algebraic, ordering, types]
import constraints/constraintNode
import constraints/relationalConstraint
import expressions/expressions
import expressions/stateful as exprStateful
import expressions/sumExpression

################################################################################
# Type definitions
################################################################################

type
    ConstrainedArray*[T] = object
        len*: int
        constraints*: seq[StatefulConstraint[T]]
        domain*: seq[seq[T]]
        reducedDomain*: seq[seq[T]]
        entries*: seq[AlgebraicExpression[T]]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): AlgebraicExpression[T] {.inline.} = arr.entries[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield int(i)

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
    ## Returns penalty (0 = satisfied). Only supports types usable for GAC.
    case cons.stateType
    of AlgebraicType:
        return penalty(cons.algebraicState.constraint, assignment)
    of RelationalType:
        let leftVal = evaluateExpression(cons.relationalState.leftExpr, assignment)
        let rightVal = evaluateExpression(cons.relationalState.rightExpr, assignment)
        return cons.relationalState.relation.penalty(leftVal, rightVal)
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
                of AllDifferentType, AtLeastType, AtMostType, ElementType, OrderingType, GlobalCardinalityType, MultiknapsackType, SequenceType, BooleanType, CumulativeType, GeostType, IrdcsType, CircuitType, AllDifferentExcept0Type, LexOrderType, TableConstraintType, RegularType, CountEqType:
                    # Skip these constraint types for domain reduction
                    continue

            if tempPenalty > 0:
                # echo "Excluding ", d, " from ", pos
                currentDomain[pos].excl(d)

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
    var gacConstraints: seq[int]  # indices into carray.constraints
    for i, cons in carray.constraints:
        if cons.stateType in {AlgebraicType, RelationalType}:
            let arity = cons.positions.len
            if arity >= 2 and arity <= MAX_GAC_ARITY:
                gacConstraints.add(i)

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
                    domains.add(vals)

                if totalCombinations == 0:
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

        # Phase 4: AllDifferent domain reduction
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

        if not outerChanged:
            break

    # Phase 5: Convert PackedSets to output sequences
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

    # Deep copy entries - AlgebraicExpression[T] are functionally immutable but we copy the seq
    result.entries = arr.entries  # seq itself is copied by assignment

    # Deep copy all stateful constraints
    result.constraints = newSeq[StatefulConstraint[T]](arr.constraints.len)
    for i, constraint in arr.constraints:
        result.constraints[i] = constraint.deepCopy()

