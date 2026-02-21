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
        # Additive term decomposition for fast partial evaluation (non-linear only)
        leftTerms*: seq[ExprTerm[T]]
        rightTerms*: seq[ExprTerm[T]]
        # Precomputed per-position: which term indices vary vs are constant
        leftVaryingIdx*: Table[int, seq[int]]
        leftConstantIdx*: Table[int, seq[int]]
        rightVaryingIdx*: Table[int, seq[int]]
        rightConstantIdx*: Table[int, seq[int]]

# Create a new RelationalConstraint with Expression wrappers
func newRelationalConstraint*[T](leftExpr, rightExpr: Expression[T],
                                  relation: BinaryRelation): RelationalConstraint[T] =
    result = RelationalConstraint[T](
        leftExpr: leftExpr,
        rightExpr: rightExpr,
        relation: relation,
        cost: 0,
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
    constraint.cost = constraint.relation.penalty(constraint.leftValue, constraint.rightValue)

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
    let newCost = constraint.relation.penalty(newLeftValue, newRightValue)
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
    constraint.cost = constraint.relation.penalty(constraint.leftValue, constraint.rightValue)

    # Track affected positions: only positions in expressions whose values changed
    constraint.lastAffectedPositions = initPackedSet[int]()
    if constraint.leftValue != constraint.lastOldLeftValue:
        constraint.lastAffectedPositions.incl(constraint.leftExpr.positions)
    if constraint.rightValue != constraint.lastOldRightValue:
        constraint.lastAffectedPositions.incl(constraint.rightExpr.positions)

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
        let rel = constraint.relation
        let currentCost = constraint.cost

        for i in 0..<domain.len:
            let v = domain[i]
            let left = leftBase + leftCoeff * v
            let right = rightBase + rightCoeff * v
            result[i] = int(rel.penalty(left, right)) - currentCost
    else:
        # Non-linear fallback: use term-based partial evaluation when available.
        # Splits expression into additive terms, precomputes constant terms once,
        # and only re-evaluates terms that depend on the varying position.
        # For varying terms, tries to compile piecewise-linear (PL) representations
        # for O(1) per-candidate evaluation instead of O(tree_depth).
        let rel = constraint.relation
        let currentCost = constraint.cost
        let leftInPos = position in constraint.leftExpr.positions
        let rightInPos = position in constraint.rightExpr.positions

        let hasLeftTerms = leftInPos and constraint.leftTerms.len > 0
        let hasRightTerms = rightInPos and constraint.rightTerms.len > 0

        # Precompute constant parts using prebuilt index arrays
        var leftConstPart: T = 0
        if hasLeftTerms:
            for ti in constraint.leftConstantIdx[position]:
                leftConstPart += constraint.leftTerms[ti].node.evaluate(assignment)

        var rightConstPart: T = 0
        if hasRightTerms:
            for ti in constraint.rightConstantIdx[position]:
                rightConstPart += constraint.rightTerms[ti].node.evaluate(assignment)

        # Cache varying term references
        let leftVarying = if hasLeftTerms: constraint.leftVaryingIdx[position] else: @[]
        let rightVarying = if hasRightTerms: constraint.rightVaryingIdx[position] else: @[]

        # Try to compile varying terms into piecewise-linear functions.
        # Sum all successfully compiled terms into one combined PL per side.
        # Track which terms need tree-eval fallback.
        var leftPL = plConst(0)
        var leftTreeTerms: seq[int] = @[]
        var leftAllPL = true
        for ti in leftVarying:
            let (ok, pl) = compilePL(constraint.leftTerms[ti].node, position, assignment)
            if ok:
                leftPL = plAdd(leftPL, pl)
            else:
                leftTreeTerms.add(ti)
                leftAllPL = false

        var rightPL = plConst(0)
        var rightTreeTerms: seq[int] = @[]
        var rightAllPL = true
        for ti in rightVarying:
            let (ok, pl) = compilePL(constraint.rightTerms[ti].node, position, assignment)
            if ok:
                rightPL = plAdd(rightPL, pl)
            else:
                rightTreeTerms.add(ti)
                rightAllPL = false

        # Fast path: all varying terms compiled to PL — no assignment mutation needed
        if (hasLeftTerms or not leftInPos) and
           (hasRightTerms or not rightInPos) and
           leftAllPL and rightAllPL:
            for i in 0..<domain.len:
                let v = domain[i]
                let newLeft = if hasLeftTerms: leftConstPart + plEval(leftPL, v)
                              else: constraint.leftValue
                let newRight = if hasRightTerms: rightConstPart + plEval(rightPL, v)
                               else: constraint.rightValue
                result[i] = int(rel.penalty(newLeft, newRight)) - currentCost
        else:
            # Mixed path: PL for compiled terms, tree eval for the rest
            let savedValue = assignment[position]
            for i in 0..<domain.len:
                let v = domain[i]
                assignment[position] = v

                let newLeft = if hasLeftTerms:
                    var total = leftConstPart + plEval(leftPL, v)
                    for ti in leftTreeTerms:
                        total += constraint.leftTerms[ti].node.evaluate(assignment)
                    total
                elif leftInPos and constraint.leftExpr.kind == StatefulAlgebraicExpr:
                    constraint.leftExpr.algebraicExpr.algebraicExpr.node.evaluate(assignment)
                elif leftInPos:
                    constraint.leftValue + constraint.leftExpr.moveDelta(position, currentValue, v)
                else:
                    constraint.leftValue

                let newRight = if hasRightTerms:
                    var total = rightConstPart + plEval(rightPL, v)
                    for ti in rightTreeTerms:
                        total += constraint.rightTerms[ti].node.evaluate(assignment)
                    total
                elif rightInPos and constraint.rightExpr.kind == StatefulAlgebraicExpr:
                    constraint.rightExpr.algebraicExpr.algebraicExpr.node.evaluate(assignment)
                elif rightInPos:
                    constraint.rightValue + constraint.rightExpr.moveDelta(position, currentValue, v)
                else:
                    constraint.rightValue

                result[i] = int(rel.penalty(newLeft, newRight)) - currentCost

            assignment[position] = savedValue
