import std/[tables, sets, packedsets]
import ../expressions/expressions
import ../expressions/stateful
import ../expressions/piecewiseLinear
import constraintNode

################################################################################
# RelationalConstraint - Unified constraint for expression relations
################################################################################

type
    ExprTerm*[T] = object
        node*: ExpressionNode[T]
        positions*: PackedSet[int]

    CachedTermPL*[T] = object
        pl*: PiecewiseLinear
        compiled*: bool          # true if compilePL succeeded for this term
        populated*: bool         # true after first compilation attempt
        depValues*: seq[(int, T)]  # (position, savedAssignmentValue) for invalidation

    RelationalConstraint*[T] = ref object
        leftExpr*: Expression[T]               # Any expression type
        rightExpr*: Expression[T]              # Any expression type
        relation*: BinaryRelation              # Reuse existing ==, !=, <, <=, >, >=
        cost*: int                             # Cache current penalty
        positions*: PackedSet[int]         # Union of left + right positions
        # Cache for expression values
        leftValue*: T
        rightValue*: T
        # Track which positions were affected by last updatePosition
        lastAffectedPositions*: PackedSet[int]
        lastOldLeftValue*: T
        lastOldRightValue*: T
        # Max |leftDelta - rightDelta| from any single position change.
        # Used for slack-based optimization: if both old and new slack >= maxNetDelta,
        # penalty map entries are unchanged and updates can be skipped.
        # Defaults to high(int) (optimization disabled). Set via setMaxNetDelta()
        # when domain ranges are known.
        maxNetDelta*: int
        # Additive term decomposition for fast partial evaluation (non-linear only)
        leftTerms*: seq[ExprTerm[T]]
        rightTerms*: seq[ExprTerm[T]]
        # Precomputed per-position: which term indices vary vs are constant
        leftVaryingIdx*: Table[int, seq[int]]
        leftConstantIdx*: Table[int, seq[int]]
        rightVaryingIdx*: Table[int, seq[int]]
        rightConstantIdx*: Table[int, seq[int]]
        graduated*: bool  # When true, EqualTo uses abs(left-right) instead of binary 0/1
        # Cached piecewise-linear compilations per (varyingPos, termIdx)
        leftTermPLCache*: Table[int, seq[CachedTermPL[T]]]
        rightTermPLCache*: Table[int, seq[CachedTermPL[T]]]

func computeCost*[T](c: RelationalConstraint[T], left, right: T): int {.inline.} =
    ## Compute penalty, using graduated abs(left-right) for EqualTo when enabled.
    if c.graduated and c.relation == EqualTo:
        return int(abs(left - right))
    else:
        return int(c.relation.penalty(left, right))

# Create a new RelationalConstraint with Expression wrappers
func newRelationalConstraint*[T](leftExpr, rightExpr: Expression[T],
                                  relation: BinaryRelation): RelationalConstraint[T] =
    result = RelationalConstraint[T](
        leftExpr: leftExpr,
        rightExpr: rightExpr,
        relation: relation,
        cost: 0,
        maxNetDelta: high(int),
        positions: leftExpr.positions + rightExpr.positions
    )
    # Extract additive terms for partial evaluation optimization (non-linear only)
    if leftExpr.kind == StatefulAlgebraicExpr:
        let terms = extractAdditiveTerms(leftExpr.algebraicExpr.algebraicExpr.node)
        if terms.len > 1:
            for t in terms:
                result.leftTerms.add(ExprTerm[T](node: t, positions: collectPositions(t)))
            # Precompute per-position varying/constant term indices
            result.leftVaryingIdx = initTable[int, seq[int]]()
            result.leftConstantIdx = initTable[int, seq[int]]()
            for pos in leftExpr.positions.items:
                var varying, constant: seq[int]
                for ti, term in result.leftTerms:
                    if pos in term.positions:
                        varying.add(ti)
                    else:
                        constant.add(ti)
                result.leftVaryingIdx[pos] = varying
                result.leftConstantIdx[pos] = constant
    if rightExpr.kind == StatefulAlgebraicExpr:
        let terms = extractAdditiveTerms(rightExpr.algebraicExpr.algebraicExpr.node)
        if terms.len > 1:
            for t in terms:
                result.rightTerms.add(ExprTerm[T](node: t, positions: collectPositions(t)))
            result.rightVaryingIdx = initTable[int, seq[int]]()
            result.rightConstantIdx = initTable[int, seq[int]]()
            for pos in rightExpr.positions.items:
                var varying, constant: seq[int]
                for ti, term in result.rightTerms:
                    if pos in term.positions:
                        varying.add(ti)
                    else:
                        constant.add(ti)
                result.rightVaryingIdx[pos] = varying
                result.rightConstantIdx[pos] = constant

# Template-based constructor that accepts any expression types
template newRelationalConstraint*[T](leftExpr, rightExpr: typed,
                                     relation: BinaryRelation): RelationalConstraint[T] =
    newRelationalConstraint(newExpression[T](leftExpr), newExpression[T](rightExpr), relation)

# Initialize the constraint with an assignment
func initialize*[T](constraint: RelationalConstraint[T], assignment: seq[T]) =
    # Initialize both expressions
    constraint.leftExpr.initialize(assignment)
    constraint.rightExpr.initialize(assignment)

    # Cache values
    constraint.leftValue = constraint.leftExpr.getValue()
    constraint.rightValue = constraint.rightExpr.getValue()

    # Calculate initial cost
    constraint.cost = constraint.computeCost(constraint.leftValue, constraint.rightValue)

# Calculate the change in penalty for a position change
func moveDelta*[T](constraint: RelationalConstraint[T],
                   position: int, oldValue, newValue: T): int =
    # Early exit if position doesn't affect this constraint
    if position notin constraint.positions:
        return 0

    # Calculate deltas incrementally for affected expressions only
    var newLeftValue = constraint.leftValue
    var newRightValue = constraint.rightValue

    if position in constraint.leftExpr.positions:
        let leftDelta = constraint.leftExpr.moveDelta(position, oldValue, newValue)
        newLeftValue = constraint.leftValue + leftDelta

    if position in constraint.rightExpr.positions:
        let rightDelta = constraint.rightExpr.moveDelta(position, oldValue, newValue)
        newRightValue = constraint.rightValue + rightDelta

    # Return the change in penalty
    let newCost = constraint.computeCost(newLeftValue, newRightValue)
    return newCost - constraint.cost

# Update a position with a new value
func updatePosition*[T](constraint: RelationalConstraint[T],
                        position: int, newValue: T) =
    # Save old values for getAffectedPositions/getAffectedDomainValues
    constraint.lastOldLeftValue = constraint.leftValue
    constraint.lastOldRightValue = constraint.rightValue

    # Update expressions incrementally and get their new values directly
    # The expressions maintain their own values, so we don't need getValue()

    if position in constraint.leftExpr.positions:
        constraint.leftExpr.updatePosition(position, newValue)
        # Expression already updated its internal value during updatePosition
        constraint.leftValue = constraint.leftExpr.getValue()

    if position in constraint.rightExpr.positions:
        constraint.rightExpr.updatePosition(position, newValue)
        # Expression already updated its internal value during updatePosition
        constraint.rightValue = constraint.rightExpr.getValue()

    # Update cost based on new cached values
    constraint.cost = constraint.computeCost(constraint.leftValue, constraint.rightValue)

    # Track affected positions: only positions in expressions whose values changed
    constraint.lastAffectedPositions = initPackedSet[int]()
    let leftChanged = constraint.leftValue != constraint.lastOldLeftValue
    let rightChanged = constraint.rightValue != constraint.lastOldRightValue

    if leftChanged or rightChanged:
        # For inequality constraints (≤/≥) that remain satisfied with sufficient slack,
        # no penalty map entries change. For the cached moveDelta values at all other
        # positions to remain correct, both old and new slack must be >= maxNetDelta,
        # where maxNetDelta is the maximum |leftDelta - rightDelta| from any single
        # position change across the entire domain.
        var canSkip = false
        if constraint.cost == 0 and constraint.maxNetDelta < high(int):
            let threshold = constraint.maxNetDelta
            case constraint.relation
            of LessThanEq:
                let oldSlack = constraint.lastOldRightValue - constraint.lastOldLeftValue
                let newSlack = constraint.rightValue - constraint.leftValue
                canSkip = oldSlack >= threshold and newSlack >= threshold
            of GreaterThanEq:
                let oldSlack = constraint.lastOldLeftValue - constraint.lastOldRightValue
                let newSlack = constraint.leftValue - constraint.rightValue
                canSkip = oldSlack >= threshold and newSlack >= threshold
            of LessThan:
                let oldSlack = constraint.lastOldRightValue - constraint.lastOldLeftValue
                let newSlack = constraint.rightValue - constraint.leftValue
                canSkip = oldSlack >= threshold + 1 and newSlack >= threshold + 1
            of GreaterThan:
                let oldSlack = constraint.lastOldLeftValue - constraint.lastOldRightValue
                let newSlack = constraint.leftValue - constraint.rightValue
                canSkip = oldSlack >= threshold + 1 and newSlack >= threshold + 1
            else:
                discard

        if not canSkip:
            if leftChanged or rightChanged:
                # When either expression value changes, penalty at ALL positions is affected
                # because movePenalty(P) = f(leftValue, rightValue, P) depends on both values
                constraint.lastAffectedPositions = constraint.positions

# Get the current penalty
func penalty*[T](constraint: RelationalConstraint[T]): int =
    return constraint.cost

func getAffectedPositions*[T](constraint: RelationalConstraint[T]): PackedSet[int] =
    ## Returns positions affected by the last updatePosition call.
    ## Only includes positions of expressions whose values actually changed.
    return constraint.lastAffectedPositions

func getAffectedDomainValues*[T](constraint: RelationalConstraint[T], position: int): seq[T] =
    ## Returns empty (all values need recalculation) since expression-based
    ## constraints can have complex dependencies.
    return @[]

proc batchMovePenalty*[T](constraint: RelationalConstraint[T], position: int,
                          currentValue: T, domain: seq[T],
                          assignment: var seq[T]): seq[int] =
    ## Compute penalty for ALL domain values at a position in a tight loop.
    ## For linear expressions (SumExpr/ConstantExpr), avoids per-value function call overhead.
    ## For non-linear expressions, evaluates directly against the assignment seq
    ## (O(1) array access per RefNode) instead of through Table-based moveDelta.
    result = newSeq[int](domain.len)

    # Extract left coefficient for this position
    var leftCoeff: T = 0
    var leftOk = true
    case constraint.leftExpr.kind
    of SumExpr:
        let s = constraint.leftExpr.sumExpr
        if s.evalMethod == PositionBased:
            leftCoeff = s.coefficient.getOrDefault(position, T(0))
        else:
            leftOk = false
    of ConstantExpr:
        leftCoeff = 0
    else:
        leftOk = false

    # Extract right coefficient for this position
    var rightCoeff: T = 0
    var rightOk = true
    case constraint.rightExpr.kind
    of SumExpr:
        let s = constraint.rightExpr.sumExpr
        if s.evalMethod == PositionBased:
            rightCoeff = s.coefficient.getOrDefault(position, T(0))
        else:
            rightOk = false
    of ConstantExpr:
        rightCoeff = 0
    else:
        rightOk = false

    if leftOk and rightOk:
        # Batch evaluation: compute base values (with position contribution removed)
        let leftBase = constraint.leftValue - leftCoeff * currentValue
        let rightBase = constraint.rightValue - rightCoeff * currentValue
        let currentCost = constraint.cost

        for i in 0..<domain.len:
            let v = domain[i]
            let left = leftBase + leftCoeff * v
            let right = rightBase + rightCoeff * v
            result[i] = constraint.computeCost(left, right) - currentCost
    else:
        # Non-linear fallback: use term-based partial evaluation when available.
        # Splits expression into additive terms, precomputes constant terms once,
        # and only re-evaluates terms that depend on the varying position.
        # For varying terms, uses cached piecewise-linear (PL) representations
        # for O(1) per-candidate evaluation instead of O(tree_depth).
        # Each term's PL is cached and invalidated only when a non-varying
        # dependency's assignment changes.
        let currentCost = constraint.cost
        let leftInPos = position in constraint.leftExpr.positions
        let rightInPos = position in constraint.rightExpr.positions

        let hasLeftTerms = leftInPos and constraint.leftTerms.len > 0
        let hasRightTerms = rightInPos and constraint.rightTerms.len > 0

        # Cache varying term references
        let leftVarying = if hasLeftTerms: constraint.leftVaryingIdx[position] else: @[]
        let rightVarying = if hasRightTerms: constraint.rightVaryingIdx[position] else: @[]

        # Get or create cached PLs for left varying terms
        var leftTermPLs: seq[CachedTermPL[T]]
        var leftAllPL = true
        if hasLeftTerms:
            if position notin constraint.leftTermPLCache:
                constraint.leftTermPLCache[position] = newSeq[CachedTermPL[T]](constraint.leftTerms.len)
            leftTermPLs = constraint.leftTermPLCache[position]
            for ti in leftVarying:
                var cache = leftTermPLs[ti]
                # Check if cached PL is still valid
                var valid = cache.populated
                if valid:
                    for (pos, savedVal) in cache.depValues:
                        if assignment[pos] != savedVal:
                            valid = false
                            break
                if not valid:
                    # Recompile PL and store dependency values
                    let (ok, pl) = compilePL(constraint.leftTerms[ti].node, position, assignment)
                    var deps: seq[(int, T)] = @[]
                    for depPos in constraint.leftTerms[ti].positions.items:
                        if depPos != position:
                            deps.add((depPos, assignment[depPos]))
                    cache = CachedTermPL[T](pl: pl, compiled: ok, populated: true, depValues: deps)
                    constraint.leftTermPLCache[position][ti] = cache
                if not cache.compiled:
                    leftAllPL = false
            # Re-read local copy to pick up any recompiled entries
            leftTermPLs = constraint.leftTermPLCache[position]

        # Get or create cached PLs for right varying terms
        var rightTermPLs: seq[CachedTermPL[T]]
        var rightAllPL = true
        if hasRightTerms:
            if position notin constraint.rightTermPLCache:
                constraint.rightTermPLCache[position] = newSeq[CachedTermPL[T]](constraint.rightTerms.len)
            rightTermPLs = constraint.rightTermPLCache[position]
            for ti in rightVarying:
                var cache = rightTermPLs[ti]
                var valid = cache.populated
                if valid:
                    for (pos, savedVal) in cache.depValues:
                        if assignment[pos] != savedVal:
                            valid = false
                            break
                if not valid:
                    let (ok, pl) = compilePL(constraint.rightTerms[ti].node, position, assignment)
                    var deps: seq[(int, T)] = @[]
                    for depPos in constraint.rightTerms[ti].positions.items:
                        if depPos != position:
                            deps.add((depPos, assignment[depPos]))
                    cache = CachedTermPL[T](pl: pl, compiled: ok, populated: true, depValues: deps)
                    constraint.rightTermPLCache[position][ti] = cache
                if not cache.compiled:
                    rightAllPL = false
            # Re-read local copy to pick up any recompiled entries
            rightTermPLs = constraint.rightTermPLCache[position]

        # Compute constant part using cached PLs to avoid tree evaluation.
        # constPart = cachedValue - sum(plEval(termPL, currentValue)) for varying terms.
        var leftConstPart: T = 0
        if hasLeftTerms:
            var varyingPart: T = 0
            for ti in leftVarying:
                if leftTermPLs[ti].compiled:
                    varyingPart += T(plEval(leftTermPLs[ti].pl, int(currentValue)))
                else:
                    varyingPart += constraint.leftTerms[ti].node.evaluate(assignment)
            leftConstPart = constraint.leftValue - varyingPart

        var rightConstPart: T = 0
        if hasRightTerms:
            var varyingPart: T = 0
            for ti in rightVarying:
                if rightTermPLs[ti].compiled:
                    varyingPart += T(plEval(rightTermPLs[ti].pl, int(currentValue)))
                else:
                    varyingPart += constraint.rightTerms[ti].node.evaluate(assignment)
            rightConstPart = constraint.rightValue - varyingPart

        # Fast path: all varying terms compiled to PL — no assignment mutation needed.
        # Try to combine term PLs via plAdd for single-eval inner loop.
        # Fall back to per-term eval if plAdd overflows MaxPLSegs.
        if (hasLeftTerms or not leftInPos) and
           (hasRightTerms or not rightInPos) and
           leftAllPL and rightAllPL:
            # Combine left term PLs
            var leftCombinedPL = plConst(0)
            var leftCombineOk = true
            if hasLeftTerms:
                for ti in leftVarying:
                    let combined = plAdd(leftCombinedPL, leftTermPLs[ti].pl)
                    if combined.n >= MaxPLSegs:
                        leftCombineOk = false
                        break
                    leftCombinedPL = combined

            # Combine right term PLs
            var rightCombinedPL = plConst(0)
            var rightCombineOk = true
            if hasRightTerms:
                for ti in rightVarying:
                    let combined = plAdd(rightCombinedPL, rightTermPLs[ti].pl)
                    if combined.n >= MaxPLSegs:
                        rightCombineOk = false
                        break
                    rightCombinedPL = combined

            if leftCombineOk and rightCombineOk:
                # Single combined PL per side — fastest inner loop
                for i in 0..<domain.len:
                    let v = domain[i]
                    let newLeft = if hasLeftTerms: leftConstPart + T(plEval(leftCombinedPL, int(v)))
                                  else: constraint.leftValue
                    let newRight = if hasRightTerms: rightConstPart + T(plEval(rightCombinedPL, int(v)))
                                   else: constraint.rightValue
                    result[i] = constraint.computeCost(newLeft, newRight) - currentCost
            else:
                # Per-term eval fallback when combined PL overflows
                for i in 0..<domain.len:
                    let v = domain[i]
                    let newLeft = if hasLeftTerms:
                        var total = leftConstPart
                        for ti in leftVarying:
                            total += T(plEval(leftTermPLs[ti].pl, int(v)))
                        total
                    else: constraint.leftValue
                    let newRight = if hasRightTerms:
                        var total = rightConstPart
                        for ti in rightVarying:
                            total += T(plEval(rightTermPLs[ti].pl, int(v)))
                        total
                    else: constraint.rightValue
                    result[i] = constraint.computeCost(newLeft, newRight) - currentCost
        else:
            # Mixed path: PL for compiled terms, tree eval for the rest
            let savedValue = assignment[position]

            # Pre-compute old term sums for ExpressionBased SumExpr (evaluated once, not per value)
            let leftIsSumEB = not hasLeftTerms and leftInPos and
                constraint.leftExpr.kind == SumExpr and
                constraint.leftExpr.sumExpr.evalMethod == ExpressionBased
            var leftOldTermSum: T = 0
            if leftIsSumEB:
                let s = constraint.leftExpr.sumExpr
                for idx in s.expressionsAtPosition.getOrDefault(position, @[]):
                    leftOldTermSum += s.expressions[idx].evaluate(assignment)

            let rightIsSumEB = not hasRightTerms and rightInPos and
                constraint.rightExpr.kind == SumExpr and
                constraint.rightExpr.sumExpr.evalMethod == ExpressionBased
            var rightOldTermSum: T = 0
            if rightIsSumEB:
                let s = constraint.rightExpr.sumExpr
                for idx in s.expressionsAtPosition.getOrDefault(position, @[]):
                    rightOldTermSum += s.expressions[idx].evaluate(assignment)

            for i in 0..<domain.len:
                let v = domain[i]
                assignment[position] = v

                let newLeft = if hasLeftTerms:
                    var total = leftConstPart
                    for ti in leftVarying:
                        if leftTermPLs[ti].compiled:
                            total += T(plEval(leftTermPLs[ti].pl, int(v)))
                        else:
                            total += constraint.leftTerms[ti].node.evaluate(assignment)
                    total
                elif leftIsSumEB:
                    # Fast: only evaluate terms at this position using seq-based assignment
                    let s = constraint.leftExpr.sumExpr
                    var newTermSum: T = 0
                    for idx in s.expressionsAtPosition.getOrDefault(position, @[]):
                        newTermSum += s.expressions[idx].evaluate(assignment)
                    constraint.leftValue + newTermSum - leftOldTermSum
                elif leftInPos and constraint.leftExpr.kind == StatefulAlgebraicExpr:
                    constraint.leftExpr.algebraicExpr.algebraicExpr.node.evaluate(assignment)
                elif leftInPos:
                    constraint.leftValue + constraint.leftExpr.moveDelta(position, currentValue, v)
                else:
                    constraint.leftValue

                let newRight = if hasRightTerms:
                    var total = rightConstPart
                    for ti in rightVarying:
                        if rightTermPLs[ti].compiled:
                            total += T(plEval(rightTermPLs[ti].pl, int(v)))
                        else:
                            total += constraint.rightTerms[ti].node.evaluate(assignment)
                    total
                elif rightIsSumEB:
                    let s = constraint.rightExpr.sumExpr
                    var newTermSum: T = 0
                    for idx in s.expressionsAtPosition.getOrDefault(position, @[]):
                        newTermSum += s.expressions[idx].evaluate(assignment)
                    constraint.rightValue + newTermSum - rightOldTermSum
                elif rightInPos and constraint.rightExpr.kind == StatefulAlgebraicExpr:
                    constraint.rightExpr.algebraicExpr.algebraicExpr.node.evaluate(assignment)
                elif rightInPos:
                    constraint.rightValue + constraint.rightExpr.moveDelta(position, currentValue, v)
                else:
                    constraint.rightValue

                result[i] = constraint.computeCost(newLeft, newRight) - currentCost

            assignment[position] = savedValue
