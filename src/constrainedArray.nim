import std/[packedsets, sequtils, strformat, tables]

import constraints/[stateful, algebraic, types]
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
                of AllDifferentType, AtLeastType, AtMostType, ElementType, OrderingType, GlobalCardinalityType, MultiknapsackType, SequenceType, BooleanType, CumulativeType, GeostType, IrdcsType, CircuitType, AllDifferentExcept0Type, LexOrderType, TableConstraintType, RegularType:
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

    # Phase 3: Bounds propagation for linear relational constraints
    # Pre-extract linear forms from relational constraints
    var linearForms: seq[LinearForm[T]]
    for cons in carray.constraints:
        if cons.stateType != RelationalType:
            continue
        let (success, form) = extractLinearForm(cons.relationalState)
        if success:
            linearForms.add(form)

    if linearForms.len > 0:
        discard

        # Compute initial domainMin/domainMax from current PackedSets
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

        # Normalize each linear form to >= 0 and propagate bounds
        type NormalizedForm = object
            coefficients: Table[int, T]
            constant: T

        var normalizedForms: seq[NormalizedForm]
        for form in linearForms:
            case form.relation
            of GreaterThanEq:
                # Σ(a_i * x_i) + C >= 0
                normalizedForms.add(NormalizedForm(
                    coefficients: form.coefficients, constant: form.constant))
            of LessThanEq:
                # negate: Σ(-a_i * x_i) - C >= 0
                var negCoeffs: Table[int, T]
                for pos in form.coefficients.keys:
                    negCoeffs[pos] = -form.coefficients[pos]
                normalizedForms.add(NormalizedForm(
                    coefficients: negCoeffs, constant: -form.constant))
            of GreaterThan:
                # Σ(a_i * x_i) + (C - 1) >= 0
                normalizedForms.add(NormalizedForm(
                    coefficients: form.coefficients, constant: form.constant - 1))
            of LessThan:
                # negate + adjust: Σ(-a_i * x_i) + (-C - 1) >= 0
                var negCoeffs: Table[int, T]
                for pos in form.coefficients.keys:
                    negCoeffs[pos] = -form.coefficients[pos]
                normalizedForms.add(NormalizedForm(
                    coefficients: negCoeffs, constant: -form.constant - 1))
            of EqualTo:
                # Both >= 0 and <= 0 (negate for >= 0)
                normalizedForms.add(NormalizedForm(
                    coefficients: form.coefficients, constant: form.constant))
                var negCoeffs: Table[int, T]
                for pos in form.coefficients.keys:
                    negCoeffs[pos] = -form.coefficients[pos]
                normalizedForms.add(NormalizedForm(
                    coefficients: negCoeffs, constant: -form.constant))
            of NotEqualTo, CommonFactor, CoPrime:
                discard

        # Fixed-point loop
        for iteration in 0..<100:
            var changed = false

            for form in normalizedForms:
                # For each variable x_j with coefficient a_j:
                # We have: a_j * x_j + rest + C >= 0
                # rest = Σ_{i≠j}(a_i * x_i)
                for pos_j in form.coefficients.keys:
                    let a_j = form.coefficients[pos_j]
                    if a_j == 0: continue

                    # Compute restMax: max possible value of rest = Σ_{i≠j}(a_i * x_i)
                    var restMax: T = 0
                    for pos_i in form.coefficients.keys:
                        if pos_i == pos_j: continue
                        let a_i = form.coefficients[pos_i]
                        if a_i > 0:
                            restMax += a_i * domainMax[pos_i]
                        else:
                            restMax += a_i * domainMin[pos_i]

                    # a_j * x_j >= -C - restMax  (i.e., bound = -C - restMax)
                    let bound = -form.constant - restMax

                    if a_j > 0:
                        # x_j >= ceil(bound / a_j)
                        let newMin = ceilDivPositive(bound, a_j)
                        if newMin > domainMin[pos_j]:
                            domainMin[pos_j] = newMin
                            changed = true
                    else:  # a_j < 0
                        # x_j <= floor(-bound / (-a_j))
                        let newMax = floorDivPositive(-bound, -a_j)
                        if newMax < domainMax[pos_j]:
                            domainMax[pos_j] = newMax
                            changed = true

            if not changed:
                break

            # Check for infeasibility: if any domainMin > domainMax, the system
            # is infeasible and further propagation would diverge
            var infeasible = false
            for pos in carray.allPositions():
                if domainMin[pos] > domainMax[pos]:
                    infeasible = true
                    break
            if infeasible:
                break

        # Apply tightened bounds to PackedSets
        for pos in carray.allPositions():
            var toExclude: seq[T]
            for v in currentDomain[pos].items:
                if v < domainMin[pos] or v > domainMax[pos]:
                    toExclude.add(v)
            for v in toExclude:
                currentDomain[pos].excl(v)

    # Phase 4: Convert PackedSets to output sequences
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

