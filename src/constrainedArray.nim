import std/[packedsets, sequtils, strformat, tables, times]
import constraints/[stateful, algebraic, ordering, types, tableConstraint, regular]
from constraints/globalCardinality import ExactCounts, BoundedCounts
import constraints/constraintNode
import constraints/relationalConstraint
import constraints/elementState
import constraints/matrixElement
import constraints/cumulative
import constraints/diffn
import expressions/expressions
import expressions/stateful as exprStateful
import expressions/sumExpression
import utils

################################################################################
# Type definitions
################################################################################

type
    ChannelBinding*[T] = object
        channelPosition*: int                # Position of the channel variable
        indexExpression*: AlgebraicExpression[T]  # Index expr (may be complex, e.g. X+1)
        arrayElements*: seq[ArrayElement[T]] # The array (constants and/or variable positions)
        hasOffset*: bool                     # true if any element has non-zero offset

    MinMaxChannelBinding*[T] = object
        channelPosition*: int                # Position of the min/max channel variable
        isMin*: bool                         # true = min, false = max
        inputExprs*: seq[AlgebraicExpression[T]]  # Input expressions to take min/max of
        inputPositions*: PackedSet[int]      # Union of all input expression positions

    CountEqChannelBinding*[T] = object
        channelPosition*: int                # Position of the count output variable
        targetValue*: T                      # Value being counted
        inputPositions*: seq[int]            # Positions to scan
        constantOffset*: T                   # Fixed count from constant elements in the array

    ConditionalCountEqChannelBinding*[T] = object
        channelPosition*: int       # Output position (e.g., uses[p])
        targetValue*: T             # Value counted on primary positions
        primaryPositions*: seq[int] # Paired positions checked == targetValue
        filterPositions*: seq[int]  # Paired positions checked == filterValue
        filterValue*: T             # Required value at filter positions
        primaryOnlyPositions*: seq[int]  # Positions checked only against targetValue (no filter)
        constantOffset*: T          # Count from constant matches

    ArgmaxChannelBinding*[T] = object
        channelPosition*: int       # Position of the argmax result variable
        inputExprs*: seq[AlgebraicExpression[T]]  # Signal expressions (ordered by index)
        inputPositions*: PackedSet[int]  # Union of all input expression positions
        valueOffset*: int           # result = argmax_index + valueOffset (e.g., 1 for 1-based)

    InverseGroup*[T] = object
        ## A group of positions forming an involution (self-inverse permutation).
        ## position[i] holds the opponent for team (i + valueOffset).
        ## The involution invariant is: assignment[positions[assignment[positions[i]] + valueOffset]] == i - valueOffset
        positions*: seq[int]   # System positions [index 0 = team 0+offset, etc.]
        valueOffset*: int      # group_index = value + valueOffset (e.g., -1 for 1-based teams)

    PartitionGroup*[T] = object
        ## A group of search positions forming a partition constraint:
        ## exactly one member must be "active" (non-null value).
        ## Used for compound swap moves that simultaneously deactivate one
        ## member and activate another within the group.
        searchPositions*: seq[int]  # place variable positions in this group
        nullValue*: T               # value meaning "not selected"

    InverseChannelGroup*[T] = object
        ## A group encoding an inverse relationship: inverse[forward[i]] = i.
        ## Forward positions are searched; inverse positions are channels.
        ## When forwardValues is non-empty, inverse[forward[i]] = forwardValues[i]
        ## instead of i + forwardBase (supports duplicate values).
        forwardPositions*: seq[int]  # searched positions (e.g., person vars)
        inversePositions*: seq[int]  # channel positions (e.g., seat vars)
        forwardBase*: int            # value representing forwardPositions[0] (e.g., 1)
        inverseBase*: int            # value representing inversePositions[0] (e.g., 1)
        defaultValue*: T             # value for unmapped inverse slots (e.g., 0)
        forwardValues*: seq[T]       # explicit values per forward position (empty = use i + forwardBase)

    ConstrainedArray*[T] = object
        len*: int
        constraints*: seq[StatefulConstraint[T]]
        domain*: seq[seq[T]]
        reducedDomain*: seq[seq[T]]
        sharedDomainPtr*: ptr seq[seq[T]]  # Points to shared (non-copied) reducedDomain for parallel states
        entries*: seq[AlgebraicExpression[T]]
        channelPositions*: PackedSet[int]
        channelBindings*: seq[ChannelBinding[T]]
        channelsAtPosition*: Table[int, seq[int]]  # search_pos → [binding indices]
        minMaxChannelBindings*: seq[MinMaxChannelBinding[T]]
        minMaxChannelsAtPosition*: Table[int, seq[int]]  # source_pos → [minMax binding indices]
        implicitMinMaxPositions*: PackedSet[int]  # channel positions from implicit detection (cascade-exempt)
        countEqChannelBindings*: seq[CountEqChannelBinding[T]]
        countEqChannelsAtPosition*: Table[int, seq[int]]  # source_pos → [countEq binding indices]
        conditionalCountEqChannelBindings*: seq[ConditionalCountEqChannelBinding[T]]
        conditionalCountEqChannelsAtPosition*: Table[int, seq[int]]  # source_pos → [condCountEq binding indices]
        argmaxChannelBindings*: seq[ArgmaxChannelBinding[T]]
        argmaxChannelsAtPosition*: Table[int, seq[int]]  # source_pos → [argmax binding indices]
        disjunctivePairs*: seq[tuple[
            coeffs1: seq[T], positions1: seq[int], rhs1: T,
            coeffs2: seq[T], positions2: seq[int], rhs2: T]]
        inverseGroups*: seq[InverseGroup[T]]
        inverseChannelGroups*: seq[InverseChannelGroup[T]]
        inverseChannelsAtPosition*: Table[int, seq[int]]  # forward_pos → [group indices]
        fixedPositions*: PackedSet[int]  # Singleton-domain positions after reduction (excluded from search)
        elementInverseDetected*: bool  # guard: detectElementInverseChannels already ran
        dormancyBindings*: seq[tuple[dormantPos: int, selectorPos: int, activeValue: T]]
        dormancyAtSelector*: Table[int, seq[int]]  # selector_pos → [binding indices]
        partitionGroups*: seq[PartitionGroup[T]]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): AlgebraicExpression[T] {.inline.} = arr.entries[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield int(i)

iterator allSearchPositions*[T](arr: ConstrainedArray[T]): int =
    ## Iterates over all positions that are not channel or fixed variables.
    for i in 0..<arr.len:
        if i notin arr.channelPositions and i notin arr.fixedPositions:
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
    # Adds the constraint and invalidates cached reduced domain
    arr.constraints.add(cons)
    arr.reducedDomain = @[]

proc removeLastConstraint*[T](arr: var ConstrainedArray[T]) {.inline.} =
    # Removes the last constraint and invalidates cached reduced domain
    arr.constraints.setLen(arr.constraints.len - 1)
    arr.reducedDomain = @[]

proc addChannelBinding*[T](arr: var ConstrainedArray[T],
                           channelPos: int,
                           indexExpr: AlgebraicExpression[T],
                           arrayElems: seq[ArrayElement[T]]) =
    var hasOff = false
    for elem in arrayElems:
        if not elem.isConstant and elem.offset != 0:
            hasOff = true
            break
    let bindingIdx = arr.channelBindings.len
    arr.channelBindings.add(ChannelBinding[T](
        channelPosition: channelPos,
        indexExpression: indexExpr,
        arrayElements: arrayElems,
        hasOffset: hasOff
    ))
    arr.channelPositions.incl(channelPos)
    # Register at index expression positions (index change → re-evaluate)
    for pos in indexExpr.positions.items:
        if pos notin arr.channelsAtPosition:
            arr.channelsAtPosition[pos] = @[bindingIdx]
        else:
            arr.channelsAtPosition[pos].add(bindingIdx)
    # Register at array element positions (value change → re-evaluate).
    # Needed when array elements are themselves channels (e.g. min/max channels
    # from set comprehensions feeding into element selections in deeper layers).
    for elem in arrayElems:
        if not elem.isConstant:
            let pos = elem.variablePosition
            if pos notin arr.channelsAtPosition:
                arr.channelsAtPosition[pos] = @[bindingIdx]
            elif bindingIdx notin arr.channelsAtPosition[pos]:
                arr.channelsAtPosition[pos].add(bindingIdx)

proc addMinMaxChannelBinding*[T](arr: var ConstrainedArray[T],
                                  channelPos: int,
                                  isMin: bool,
                                  inputExprs: seq[AlgebraicExpression[T]],
                                  isImplicit: bool = false) =
    ## Register a min/max channel: channelPos = min/max(inputExprs).
    ## The channel position is added to channelPositions (not searched).
    ## Source positions are mapped in minMaxChannelsAtPosition.
    ## isImplicit=true marks channels detected without defines_var as cascade-exempt
    ## (still computed after each move but not included in channel-dep cascade topology).
    var allPositions: PackedSet[int]
    for expr in inputExprs:
        for pos in expr.positions.items:
            allPositions.incl(pos)
    let bindingIdx = arr.minMaxChannelBindings.len
    arr.minMaxChannelBindings.add(MinMaxChannelBinding[T](
        channelPosition: channelPos,
        isMin: isMin,
        inputExprs: inputExprs,
        inputPositions: allPositions
    ))
    arr.channelPositions.incl(channelPos)
    if isImplicit:
        arr.implicitMinMaxPositions.incl(channelPos)
    for pos in allPositions.items:
        if pos notin arr.minMaxChannelsAtPosition:
            arr.minMaxChannelsAtPosition[pos] = @[bindingIdx]
        else:
            arr.minMaxChannelsAtPosition[pos].add(bindingIdx)

proc addCountEqChannelBinding*[T](arr: var ConstrainedArray[T],
                                   channelPos: int,
                                   targetValue: T,
                                   inputPositions: seq[int],
                                   constantOffset: T = T(0)) =
    ## Register a count-equals channel: channelPos = constantOffset + #{p in inputPositions : assignment[p] == targetValue}.
    ## constantOffset accounts for fixed elements in the source array that always match targetValue.
    ## The channel position is added to channelPositions (not searched).
    let bindingIdx = arr.countEqChannelBindings.len
    arr.countEqChannelBindings.add(CountEqChannelBinding[T](
        channelPosition: channelPos,
        targetValue: targetValue,
        inputPositions: inputPositions,
        constantOffset: constantOffset
    ))
    arr.channelPositions.incl(channelPos)
    for pos in inputPositions:
        if pos notin arr.countEqChannelsAtPosition:
            arr.countEqChannelsAtPosition[pos] = @[bindingIdx]
        else:
            arr.countEqChannelsAtPosition[pos].add(bindingIdx)

proc addConditionalCountEqChannelBinding*[T](arr: var ConstrainedArray[T],
                                               channelPos: int,
                                               targetValue: T,
                                               primaryPositions: seq[int],
                                               filterPositions: seq[int],
                                               filterValue: T,
                                               primaryOnlyPositions: seq[int] = @[],
                                               constantOffset: T = T(0)) =
    ## Register a conditional count-equals channel:
    ## channelPos = constantOffset +
    ##   #{i : assignment[primaryPositions[i]] == targetValue AND assignment[filterPositions[i]] == filterValue} +
    ##   #{p in primaryOnlyPositions : assignment[p] == targetValue}.
    ## primaryOnlyPositions are checked only against targetValue (filter is trivially true).
    assert primaryPositions.len == filterPositions.len
    let bindingIdx = arr.conditionalCountEqChannelBindings.len
    arr.conditionalCountEqChannelBindings.add(ConditionalCountEqChannelBinding[T](
        channelPosition: channelPos,
        targetValue: targetValue,
        primaryPositions: primaryPositions,
        filterPositions: filterPositions,
        filterValue: filterValue,
        primaryOnlyPositions: primaryOnlyPositions,
        constantOffset: constantOffset
    ))
    arr.channelPositions.incl(channelPos)
    # Register at primary, filter, and primary-only positions
    for pos in primaryPositions:
        if pos notin arr.conditionalCountEqChannelsAtPosition:
            arr.conditionalCountEqChannelsAtPosition[pos] = @[bindingIdx]
        elif bindingIdx notin arr.conditionalCountEqChannelsAtPosition[pos]:
            arr.conditionalCountEqChannelsAtPosition[pos].add(bindingIdx)
    for pos in filterPositions:
        if pos notin arr.conditionalCountEqChannelsAtPosition:
            arr.conditionalCountEqChannelsAtPosition[pos] = @[bindingIdx]
        elif bindingIdx notin arr.conditionalCountEqChannelsAtPosition[pos]:
            arr.conditionalCountEqChannelsAtPosition[pos].add(bindingIdx)
    for pos in primaryOnlyPositions:
        if pos notin arr.conditionalCountEqChannelsAtPosition:
            arr.conditionalCountEqChannelsAtPosition[pos] = @[bindingIdx]
        elif bindingIdx notin arr.conditionalCountEqChannelsAtPosition[pos]:
            arr.conditionalCountEqChannelsAtPosition[pos].add(bindingIdx)

proc addArgmaxChannelBinding*[T](arr: var ConstrainedArray[T],
                                   channelPos: int,
                                   inputExprs: seq[AlgebraicExpression[T]],
                                   valueOffset: int) =
    ## Register an argmax channel: channelPos = valueOffset + index of first maximum in inputExprs.
    var allPositions: PackedSet[int]
    for expr in inputExprs:
        for p in expr.positions.items:
            allPositions.incl(p)
    let bindingIdx = arr.argmaxChannelBindings.len
    arr.argmaxChannelBindings.add(ArgmaxChannelBinding[T](
        channelPosition: channelPos,
        inputExprs: inputExprs,
        inputPositions: allPositions,
        valueOffset: valueOffset
    ))
    arr.channelPositions.incl(channelPos)
    for pos in allPositions.items:
        if pos notin arr.argmaxChannelsAtPosition:
            arr.argmaxChannelsAtPosition[pos] = @[bindingIdx]
        elif bindingIdx notin arr.argmaxChannelsAtPosition[pos]:
            arr.argmaxChannelsAtPosition[pos].add(bindingIdx)

proc addInverseGroup*[T](arr: var ConstrainedArray[T],
                          positions: seq[int],
                          valueOffset: int) =
    ## Register an inverse group: positions form an involution where
    ## assignment[positions[assignment[positions[i]] + valueOffset]] == i - valueOffset.
    arr.inverseGroups.add(InverseGroup[T](
        positions: positions,
        valueOffset: valueOffset
    ))

proc addInverseChannelGroup*[T](arr: var ConstrainedArray[T],
                                 forwardPositions, inversePositions: seq[int],
                                 forwardBase, inverseBase: int,
                                 defaultValue: T,
                                 forwardValues: seq[T] = @[]) =
    ## Register an inverse channel group: inverse[forward[i]] = i + forwardBase.
    ## When forwardValues is non-empty, inverse[forward[i]] = forwardValues[i] instead.
    ## Inverse positions become channel variables.
    let gi = arr.inverseChannelGroups.len
    arr.inverseChannelGroups.add(InverseChannelGroup[T](
        forwardPositions: forwardPositions,
        inversePositions: inversePositions,
        forwardBase: forwardBase,
        inverseBase: inverseBase,
        defaultValue: defaultValue,
        forwardValues: forwardValues
    ))
    # Mark inverse positions as channels
    for pos in inversePositions:
        arr.channelPositions.incl(pos)
    # Build reverse lookup: forward position → group indices
    for pos in forwardPositions:
        if pos notin arr.inverseChannelsAtPosition:
            arr.inverseChannelsAtPosition[pos] = @[gi]
        else:
            arr.inverseChannelsAtPosition[pos].add(gi)

proc recomputeInverse*[T](group: InverseChannelGroup[T], assignment: seq[T]): seq[T] =
    ## Compute the inverse channel values from the current forward assignments.
    ## Returns a seq aligned with group.inversePositions.
    result = newSeq[T](group.inversePositions.len)
    for j in 0..<result.len:
        result[j] = group.defaultValue
    for i, fpos in group.forwardPositions:
        let v = assignment[fpos]
        let idx = v - group.inverseBase
        if idx >= 0 and idx < group.inversePositions.len:
            if group.forwardValues.len > 0:
                result[idx] = group.forwardValues[i]
            else:
                result[idx] = T(i + group.forwardBase)

################################################################################
# Element-to-inverse-channel detection
################################################################################

proc detectElementInverseChannels*[T](arr: var ConstrainedArray[T]) =
    ## Detects element constraints of the form array[index] = constant_value
    ## (where the value position has a singleton domain) sharing the same array,
    ## and converts the array positions into inverse channel variables.
    ## This handles patterns like Langford sequences where element(position[i], solution, i)
    ## makes solution fully determined by position.

    if arr.elementInverseDetected: return
    arr.elementInverseDetected = true

    # Step 1: Find element constraints with singleton-domain value positions
    type ElementInfo = object
        constraintIdx: int
        indexPosition: int
        valuePosition: int
        constantValue: T
        arrayKey: seq[int]  # positions of array elements, used as group key

    var candidates: seq[ElementInfo]
    for ci in 0..<arr.constraints.len:
        let c = arr.constraints[ci]
        if c.stateType != ElementType: continue
        if c.elementState.evalMethod != PositionBased: continue
        if c.elementState.isConstantArray: continue

        let vpos = c.elementState.valuePosition
        if arr.domain[vpos].len != 1: continue

        # Build the array key from element positions
        var key: seq[int]
        for elem in c.elementState.arrayElements:
            if elem.isConstant: continue  # mixed arrays with constants — skip for now
            key.add(elem.variablePosition)
        if key.len != c.elementState.arrayElements.len:
            continue  # had some constants, skip

        candidates.add(ElementInfo(
            constraintIdx: ci,
            indexPosition: c.elementState.indexPosition,
            valuePosition: vpos,
            constantValue: arr.domain[vpos][0],
            arrayKey: key
        ))

    if candidates.len == 0: return

    # Step 2: Group by array identity
    var groups: Table[seq[int], seq[int]]  # arrayKey -> indices into candidates
    for i, info in candidates:
        if info.arrayKey notin groups:
            groups[info.arrayKey] = @[]
        groups[info.arrayKey].add(i)

    # Step 3: For each group with >= 2 constraints, create inverse channel group
    var consumedConstraints: PackedSet[int]
    for arrayKey, memberIdxs in groups.pairs:
        if memberIdxs.len < 2: continue

        var forwardPositions: seq[int]
        var forwardValues: seq[T]
        let inversePositions = arrayKey  # the shared array positions

        # Check that all index positions are NOT in the inverse array
        # (they must be independent search variables)
        let inverseSet = toPackedSet[int](inversePositions)
        var valid = true
        for mi in memberIdxs:
            let info = candidates[mi]
            if info.indexPosition in inverseSet:
                valid = false
                break
            # Also skip if index position is already a channel
            if info.indexPosition in arr.channelPositions:
                valid = false
                break
        if not valid: continue

        for mi in memberIdxs:
            let info = candidates[mi]
            forwardPositions.add(info.indexPosition)
            forwardValues.add(info.constantValue)

        # Determine inverse base: the minimum domain value of forward positions
        # (these are indices into the array, so inverseBase is typically 0)
        var inverseBase = high(int)
        for fpos in forwardPositions:
            for v in arr.domain[fpos]:
                if v < inverseBase:
                    inverseBase = v

        # Default value: pick first value from inverse position domain that's not in forwardValues
        var defaultValue: T = arr.domain[inversePositions[0]][0]
        let fvSet = toPackedSet[int](forwardValues.mapIt(int(it)))
        for v in arr.domain[inversePositions[0]]:
            if int(v) notin fvSet:
                defaultValue = v
                break

        # forwardBase is not used when forwardValues is set, but set it to 0
        arr.addInverseChannelGroup(forwardPositions, inversePositions,
                                    0, inverseBase, defaultValue, forwardValues)

        # Mark consumed constraints
        for mi in memberIdxs:
            consumedConstraints.incl(candidates[mi].constraintIdx)

    if consumedConstraints.len == 0: return

    # Remove consumed constraints
    var newConstraints: seq[StatefulConstraint[T]]
    for ci in 0..<arr.constraints.len:
        if ci notin consumedConstraints:
            newConstraints.add(arr.constraints[ci])
    arr.constraints = newConstraints

    # Invalidate cached reduced domain
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

proc tightenFromLe[T](domainMin, domainMax: var seq[T],
                       coeffs: seq[T], positions: seq[int], rhs: T) =
    ## For constraint coeffs · vars <= rhs, tighten domainMin/domainMax bounds.
    for j in 0..<positions.len:
        let pos_j = positions[j]
        let a_j = coeffs[j]
        if a_j == 0: continue

        # Compute restMin: minimum possible sum of all other terms
        var restMin: T = 0
        for i in 0..<positions.len:
            if i == j: continue
            let a_i = coeffs[i]
            let pos_i = positions[i]
            if a_i > 0:
                restMin += a_i * domainMin[pos_i]
            else:
                restMin += a_i * domainMax[pos_i]

        # From a_j * x_j + restMin <= rhs  =>  a_j * x_j <= rhs - restMin
        let slack = rhs - restMin
        if a_j > 0:
            # x_j <= floor(slack / a_j)
            let newMax = floorDivPositive(slack, a_j)
            if newMax < domainMax[pos_j]:
                domainMax[pos_j] = newMax
        else:
            # a_j < 0, divide flips: x_j >= ceil(slack / a_j)
            # ceil(slack / a_j) = -floor(-slack / |a_j|) = -floorDivPositive(-slack, -a_j)
            let newMin = -floorDivPositive(-slack, -a_j)
            if newMin > domainMin[pos_j]:
                domainMin[pos_j] = newMin

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

proc tightenReducedDomain*[T](carray: var ConstrainedArray[T]) =
    ## Lightweight bounds propagation on the existing reducedDomain using
    ## linear forms extracted from constraints. Does NOT modify constraints
    ## or fixed positions — safe to call repeatedly during optimization.
    if carray.reducedDomain.len == 0: return

    let n = carray.len
    var domainMin = newSeq[T](n)
    var domainMax = newSeq[T](n)
    for pos in carray.allPositions():
        let rd = carray.reducedDomain[pos]
        if rd.len == 0:
            domainMin[pos] = T(0)
            domainMax[pos] = T(0)
        elif pos in carray.channelPositions and rd.len <= 1 and carray.domain[pos].len > 1:
            # Channel with placeholder reducedDomain — use original domain bounds
            # so bounds propagation can tighten through channels correctly
            domainMin[pos] = carray.domain[pos][0]
            domainMax[pos] = carray.domain[pos][^1]
        else:
            # Find actual min/max (reducedDomain may not be sorted)
            domainMin[pos] = rd[0]
            domainMax[pos] = rd[0]
            for v in rd:
                if v < domainMin[pos]: domainMin[pos] = v
                if v > domainMax[pos]: domainMax[pos] = v

    # Extract linear forms from relational constraints, reusing extractLinearForm
    type NormForm = object
        coefficients: Table[int, T]
        constant: T  # form: Σ(coeff[i]*x[i]) + constant >= 0

    proc normalizeToGe(form: LinearForm[T]): seq[NormForm] =
        ## Normalize a LinearForm to one or two >= 0 forms
        case form.relation
        of LessThanEq:
            var neg: Table[int, T]
            for pos, c in form.coefficients.pairs: neg[pos] = -c
            result.add(NormForm(coefficients: neg, constant: -form.constant))
        of GreaterThanEq:
            result.add(NormForm(coefficients: form.coefficients, constant: form.constant))
        of EqualTo:
            result.add(NormForm(coefficients: form.coefficients, constant: form.constant))
            var neg: Table[int, T]
            for pos, c in form.coefficients.pairs: neg[pos] = -c
            result.add(NormForm(coefficients: neg, constant: -form.constant))
        of LessThan:
            var neg: Table[int, T]
            for pos, c in form.coefficients.pairs: neg[pos] = -c
            result.add(NormForm(coefficients: neg, constant: -form.constant - T(1)))
        of GreaterThan:
            result.add(NormForm(coefficients: form.coefficients, constant: form.constant - T(1)))
        else: discard

    var forms: seq[NormForm]
    for cons in carray.constraints:
        if cons.stateType != RelationalType: continue
        let (ok, linearForm) = extractLinearForm[T](cons.relationalState)
        if not ok: continue
        forms.add(normalizeToGe(linearForm))

    # Add min/max channel linear forms for bounds propagation through channels
    # For max channel ch = max(e1, ..., en): ch >= e_i for all i
    # For min channel ch = min(e1, ..., en): ch <= e_i for all i
    for binding in carray.minMaxChannelBindings:
        let chPos = binding.channelPosition
        for inputExpr in binding.inputExprs:
            if inputExpr.linear:
                let linearized = linearize(inputExpr)
                if linearized.evalMethod != PositionBased: continue
                var coeffs: Table[int, T]
                if not binding.isMin:
                    # Max: ch >= input → ch - input >= 0
                    coeffs[chPos] = T(1)
                    for pos in linearized.coefficient.keys:
                        if pos in coeffs:
                            coeffs[pos] = coeffs[pos] - linearized.coefficient[pos]
                        else:
                            coeffs[pos] = -linearized.coefficient[pos]
                    forms.add(NormForm(coefficients: coeffs, constant: -linearized.constant))
                else:
                    # Min: ch <= input → input - ch >= 0
                    coeffs[chPos] = T(-1)
                    for pos in linearized.coefficient.keys:
                        if pos in coeffs:
                            coeffs[pos] = coeffs[pos] + linearized.coefficient[pos]
                        else:
                            coeffs[pos] = linearized.coefficient[pos]
                    forms.add(NormForm(coefficients: coeffs, constant: linearized.constant))

    if forms.len == 0: return

    # Fixed-point bounds propagation (same as reduceDomain Phase 3)
    # Guard against overflow — skip any form where arithmetic would overflow
    const SafeLimit = high(T) div 4  # conservative bound to prevent overflow
    var changed = true
    for iteration in 0..<50:
        if not changed: break
        changed = false
        for form in forms:
            for pos_j in form.coefficients.keys:
                let a_j = form.coefficients[pos_j]
                if a_j == 0: continue
                var restMax: T = 0
                var overflow = false
                for pos_i in form.coefficients.keys:
                    if pos_i == pos_j: continue
                    let a_i = form.coefficients[pos_i]
                    if a_i == 0: continue
                    let dVal = if a_i > 0: domainMax[pos_i] else: domainMin[pos_i]
                    if abs(dVal) > SafeLimit or abs(a_i) > SafeLimit:
                        overflow = true; break
                    let product = a_i * dVal
                    if abs(restMax) > SafeLimit:
                        overflow = true; break
                    restMax += product
                if overflow: continue
                if abs(form.constant) > SafeLimit or abs(restMax) > SafeLimit:
                    continue
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

    # Apply tightened bounds to reducedDomain.
    # Never produce empty or singleton domains — empty causes crashes,
    # singletons cause removeFixedConstraints to remove constraints that
    # are still needed during optimization.
    for pos in carray.allPositions():
        let rd = carray.reducedDomain[pos]
        if rd.len <= 2: continue  # keep at least 2 values
        if domainMin[pos] > domainMax[pos]: continue
        var newDomain: seq[T]
        for v in rd:
            if v >= domainMin[pos] and v <= domainMax[pos]:
                newDomain.add(v)
        if newDomain.len < 2: continue  # never tighten to singleton or empty
        if newDomain.len < rd.len:
            carray.reducedDomain[pos] = newDomain

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
    of WeightedSameValueExpr:
        return expr.weightedSameValueExpr.evaluate(assignment)

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
    of BooleanType:
        let bc = cons.booleanState
        case bc.isUnary
        of true:
            let targetPen = evaluateConstraint(bc.targetConstraint, assignment)
            if targetPen < 0: return T(-1)
            return calculateUnaryPenalty(bc.unaryOp, targetPen)
        of false:
            let leftPen = evaluateConstraint(bc.leftConstraint, assignment)
            if leftPen < 0: return T(-1)
            let rightPen = evaluateConstraint(bc.rightConstraint, assignment)
            if rightPen < 0: return T(-1)
            return calculateBooleanPenalty(bc.booleanOp, leftPen, rightPen)
    else:
        return T(-1)  # sentinel: not supported

################################################################################
# Sum-of-abs decomposition helpers
################################################################################

proc tryExtractAbsLinearNode[T](node: ExpressionNode[T]): (bool, Table[int, T], T) =
    ## If node is abs(linear) or constant*abs(linear), extract the inner linear form.
    ## Returns (success, innerCoeffs, innerConstant).
    ## The outer scaling constant is NOT folded in — use getAbsOuterScale() separately.

    var absTarget: ExpressionNode[T]

    # Check for: abs(...)
    if node.kind == UnaryOpNode and node.unaryOp == AbsoluteValue:
        absTarget = node.target
    # Check for: constant * abs(...) or abs(...) * constant
    elif node.kind == BinaryOpNode and node.binaryOp == Multiplication:
        if node.left.kind == LiteralNode and
           node.right.kind == UnaryOpNode and node.right.unaryOp == AbsoluteValue:
            absTarget = node.right.target
        elif node.right.kind == LiteralNode and
             node.left.kind == UnaryOpNode and node.left.unaryOp == AbsoluteValue:
            absTarget = node.left.target
        else:
            return (false, initTable[int, T](), T(0))
    else:
        return (false, initTable[int, T](), T(0))

    # Try to linearize the inner expression
    let positions = collectPositions(absTarget)
    if positions.len == 0:
        return (false, initTable[int, T](), T(0))
    let innerAlg = AlgebraicExpression[T](
        positions: positions,
        node: absTarget,
        linear: true
    )
    let linearized = linearize(innerAlg)
    if linearized.evalMethod != PositionBased:
        return (false, initTable[int, T](), T(0))

    # Verify linearity: check f(2*e_i) == 2*coeff_i + constant
    var testAssignment: Table[int, T]
    for pos in positions.items:
        testAssignment[pos] = T(0)
    for pos in positions.items:
        testAssignment[pos] = T(2)
        let actual = absTarget.evaluate(testAssignment)
        let expected = T(2) * linearized.coefficient.getOrDefault(pos, T(0)) + linearized.constant
        if actual != expected:
            return (false, initTable[int, T](), T(0))
        testAssignment[pos] = T(0)

    return (true, linearized.coefficient, linearized.constant)

proc getAbsOuterScale[T](node: ExpressionNode[T]): T =
    ## For constant*abs(...) returns the constant; for bare abs(...) returns 1.
    if node.kind == BinaryOpNode and node.binaryOp == Multiplication:
        if node.left.kind == LiteralNode:
            return node.left.value
        elif node.right.kind == LiteralNode:
            return node.right.value
    return T(1)

################################################################################
# ConstrainedArray domain reduction
################################################################################

proc reduceDomain*[T](carray: ConstrainedArray[T]): seq[seq[T]] =
    var
        reduced = newSeq[seq[T]](carray.len)
        currentDomain = newSeq[PackedSet[T]](carray.len)

    # Channel positions with large domains skip expensive PackedSet creation.
    # They're never searched, so domain reduction is pointless. We just need
    # their min/max for bounds propagation (computed from sorted domain endpoints).
    const LargeDomainThreshold = 1000
    var skippedPositions: PackedSet[int]
    var nSkipped, nNormal, maxDomainSize: int
    for pos in carray.allPositions():
        if pos in carray.channelPositions and carray.domain[pos].len > LargeDomainThreshold:
            # Don't copy the million-element domain; channel propagation will set the
            # correct value anyway. Store a 1-element placeholder for random init.
            reduced[pos] = @[carray.domain[pos][0]]
            skippedPositions.incl(pos)
            inc nSkipped
        else:
            if carray.domain[pos].len > maxDomainSize:
                maxDomainSize = carray.domain[pos].len
            currentDomain[pos] = toPackedSet[T](carray.domain[pos])
            inc nNormal
    discard (nSkipped, nNormal, maxDomainSize)  # used only for debug logging

    # First examine any single-variable constraints to reduce domains
    var totalRemoved: int
    for cons in carray.constraints:
        if cons.positions.len != 1:
            continue
        let pos = toSeq(cons.positions)[0]
        if pos in skippedPositions:
            continue
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
                    let rc = cons.relationalState
                    rc.leftExpr.initialize(tempAssignment)
                    rc.rightExpr.initialize(tempAssignment)
                    let lv = rc.leftExpr.getValue()
                    let rv = rc.rightExpr.getValue()
                    tempPenalty = rc.computeCost(lv, rv)
                of AllDifferentType, AtLeastType, AtMostType, ElementType, OrderingType, GlobalCardinalityType, MultiknapsackType, SequenceType, BooleanType, CumulativeType, GeostType, IrdcsType, CircuitType, SubcircuitType, ConnectedType, AllDifferentExcept0Type, LexOrderType, TableConstraintType, RegularType, CountEqType, DiffnType, DiffnKType, MatrixElementType, NoOverlapFixedBoxType, ConditionalCumulativeType, ConditionalNoOverlapPairType, ConditionalDayCapacityType, DisjunctiveClauseType, ValueSupportType, MultiResourceNoOverlapType, CircuitTimePropType:
                    # Skip these constraint types for domain reduction
                    continue

            if tempPenalty > 0:
                currentDomain[pos].excl(d)
                removed += 1
        totalRemoved += removed
    if totalRemoved > 0:
        stderr.writeLine(&"[Solve] Single-var constraint reduction: {totalRemoved} values removed")

    # Phase 1b: Element constraint backward propagation (constant arrays)
    # For element(idx, const_array, result): restrict idx based on result domain
    # and restrict result based on idx domain. Runs in a local fixed-point loop.
    # Handles both PositionBased and ExpressionBased (single-position index/value) elements.
    block:
        var elementTotalRemoved = 0
        var elementChanged = true
        var elementIter = 0
        while elementChanged and elementIter < 10:
            elementChanged = false
            inc elementIter
            for cons in carray.constraints:
                if cons.stateType != ElementType: continue
                let es = cons.elementState

                if es.evalMethod == PositionBased and es.isConstantArray:
                    let idxPos = es.indexPosition
                    let resPos = es.valuePosition
                    if idxPos in skippedPositions or resPos in skippedPositions: continue

                    # Forward: restrict result to values reachable from current idx domain
                    var reachableResults = initPackedSet[T]()
                    for idx in currentDomain[idxPos].items:
                        if idx >= 0 and idx < es.constantArray.len:
                            reachableResults.incl(es.constantArray[idx])
                    let newResDom = currentDomain[resPos] * reachableResults
                    if newResDom.len < currentDomain[resPos].len:
                        elementTotalRemoved += currentDomain[resPos].len - newResDom.len
                        currentDomain[resPos] = newResDom
                        elementChanged = true

                    # Backward: restrict idx to values that map to valid result values
                    var validIndices = initPackedSet[T]()
                    for idx in currentDomain[idxPos].items:
                        if idx >= 0 and idx < es.constantArray.len:
                            if es.constantArray[idx] in currentDomain[resPos]:
                                validIndices.incl(idx)
                    if validIndices.len < currentDomain[idxPos].len:
                        elementTotalRemoved += currentDomain[idxPos].len - validIndices.len
                        currentDomain[idxPos] = validIndices
                        elementChanged = true

                elif es.evalMethod == ExpressionBased and es.isConstantArrayEB:
                    # Expression-based with constant array: common FlatZinc pattern (idx-1 offset)
                    # Only handle single-position index and value expressions to keep it tractable
                    let idxPositions = toSeq(es.indexExpression.positions.items)
                    let valPositions = toSeq(es.valueExpression.positions.items)
                    if idxPositions.len != 1 or valPositions.len != 1: continue
                    let idxPos = idxPositions[0]
                    let resPos = valPositions[0]
                    if idxPos in skippedPositions or resPos in skippedPositions: continue

                    let arrLen = es.constantArrayEB.len
                    var tempAssign = initTable[int, T]()

                    # Forward/backward pruning of result domain is only sound when the
                    # value expression is a simple RefNode (identity mapping between
                    # resPos domain values and constraint values). For non-trivial
                    # expressions (e.g. resPos*2+1), raw domain values != expression
                    # output, so domain intersection would be incorrect.
                    let simpleValueExpr = es.valueExpression.node.kind == RefNode

                    # Forward: restrict result to values reachable from current idx domain
                    if simpleValueExpr:
                        var reachableResults = initPackedSet[T]()
                        for v in currentDomain[idxPos].items:
                            tempAssign[idxPos] = v
                            let idx = es.indexExpression.evaluate(tempAssign)
                            if idx >= 0 and idx < arrLen:
                                reachableResults.incl(es.constantArrayEB[idx])
                        let newResDom = currentDomain[resPos] * reachableResults
                        if newResDom.len < currentDomain[resPos].len:
                            elementTotalRemoved += currentDomain[resPos].len - newResDom.len
                            currentDomain[resPos] = newResDom
                            elementChanged = true

                    # Backward: restrict idx position to values that map to valid results
                    for v in toSeq(currentDomain[idxPos].items):
                        tempAssign[idxPos] = v
                        let idx = es.indexExpression.evaluate(tempAssign)
                        if idx < 0 or idx >= arrLen:
                            currentDomain[idxPos].excl(v)
                            elementTotalRemoved += 1
                            elementChanged = true
                        elif simpleValueExpr:
                            # Only prune when value expression is identity — otherwise
                            # arrVal may not directly correspond to resPos domain values
                            let arrVal = es.constantArrayEB[idx]
                            if arrVal notin currentDomain[resPos]:
                                currentDomain[idxPos].excl(v)
                                elementTotalRemoved += 1
                                elementChanged = true

        if elementTotalRemoved > 0:
            stderr.writeLine(&"[DomRed] Element backward propagation: {elementTotalRemoved} values removed in {elementIter} iterations")

    # Phase 1c: Channel binding domain propagation
    # For element channel bindings with constant arrays: restrict channel domain to
    # reachable values, and restrict index domain to values that produce valid results.
    # For variable-array bindings: restrict channel domain to union of source domains.
    # Runs as fixpoint since tightening one channel may tighten downstream channels.
    block:
        var channelTotalRemoved = 0
        var channelChanged = true
        var channelIter = 0
        while channelChanged and channelIter < 20:
            channelChanged = false
            inc channelIter
            for binding in carray.channelBindings:
                let chanPos = binding.channelPosition
                if chanPos in skippedPositions: continue

                # Collect index positions
                let idxPositions = toSeq(binding.indexExpression.positions.items)
                if idxPositions.len != 1: continue  # only single-position index
                let idxPos = idxPositions[0]
                if idxPos in skippedPositions: continue

                # Check if constant array
                var isConstArray = true
                for elem in binding.arrayElements:
                    if not elem.isConstant:
                        isConstArray = false
                        break

                if isConstArray:
                    # Forward: channel domain ⊆ {arr[idx] : idx ∈ idxDomain}
                    var reachable = initPackedSet[T]()
                    var tempAssign = initTable[int, T]()
                    for v in currentDomain[idxPos].items:
                        tempAssign[idxPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx >= 0 and idx < binding.arrayElements.len:
                            reachable.incl(binding.arrayElements[idx].constantValue)
                    let newChanDom = currentDomain[chanPos] * reachable
                    if newChanDom.len < currentDomain[chanPos].len:
                        channelTotalRemoved += currentDomain[chanPos].len - newChanDom.len
                        currentDomain[chanPos] = newChanDom
                        channelChanged = true

                    # Backward: index domain restricted to values mapping to valid channel values
                    for v in toSeq(currentDomain[idxPos].items):
                        tempAssign[idxPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx < 0 or idx >= binding.arrayElements.len:
                            currentDomain[idxPos].excl(v)
                            channelTotalRemoved += 1
                            channelChanged = true
                        elif binding.arrayElements[idx].constantValue notin currentDomain[chanPos]:
                            currentDomain[idxPos].excl(v)
                            channelTotalRemoved += 1
                            channelChanged = true
                else:
                    # Variable array: channel domain ⊆ union of element domains at reachable indices
                    var reachable = initPackedSet[T]()
                    var tempAssign = initTable[int, T]()
                    for v in currentDomain[idxPos].items:
                        tempAssign[idxPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx >= 0 and idx < binding.arrayElements.len:
                            let elem = binding.arrayElements[idx]
                            if elem.isConstant:
                                reachable.incl(elem.constantValue)
                            else:
                                # Include all domain values of the source position
                                for sv in currentDomain[elem.variablePosition].items:
                                    reachable.incl(sv)
                    if reachable.len > 0:
                        let newChanDom = currentDomain[chanPos] * reachable
                        if newChanDom.len < currentDomain[chanPos].len:
                            channelTotalRemoved += currentDomain[chanPos].len - newChanDom.len
                            currentDomain[chanPos] = newChanDom
                            channelChanged = true

        if channelTotalRemoved > 0:
            stderr.writeLine(&"[DomRed] Channel binding propagation: {channelTotalRemoved} values removed in {channelIter} iterations")

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

                # Prune negative origins only when the task has constant positive height.
                # Variable-height tasks may have height=0 at negative origins (e.g., -1
                # sentinel meaning "not scheduled"), so pruning would be unsound.
                let hasConstHeight = cumState.heightPositions.len == 0 or
                    (taskIdx < cumState.heightPositions.len and cumState.heightPositions[taskIdx] < 0)
                if hasConstHeight and height > 0:
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

    # Phase: Sum-of-abs bound decomposition
    # Detect constraints of the form sum(scale_i * abs(linear_i)) <= bound
    # and decompose into per-term linear bounds: -bound/scale_i <= linear_i <= bound/scale_i
    type AbsTermInfo = tuple[coeffs: Table[int, T], constant: T, scale: T]
    var sumAbsDecomposed = 0
    for cons in carray.constraints:
        if cons.stateType != RelationalType:
            continue
        let rel = cons.relationalState
        if rel.relation notin {LessThanEq, LessThan}:
            continue
        if rel.rightExpr.kind != ConstantExpr:
            continue
        var bound = rel.rightExpr.constantValue
        if rel.relation == LessThan:
            bound -= T(1)
        if bound < T(0):
            continue

        # Case A: leftExpr is StatefulAlgebraicExpr — decompose via extractAdditiveTerms
        if rel.leftExpr.kind == StatefulAlgebraicExpr:
            let terms = extractAdditiveTerms(rel.leftExpr.algebraicExpr.algebraicExpr.node)
            var allAbsLinear = true
            var termInfos: seq[AbsTermInfo]
            for term in terms:
                if term.kind == LiteralNode:
                    # Constant term — subtract from bound
                    bound -= term.value
                    continue
                let (ok, coeffs, innerConst) = tryExtractAbsLinearNode[T](term)
                if ok:
                    let scale = getAbsOuterScale[T](term)
                    if scale > T(0):
                        termInfos.add((coeffs: coeffs, constant: innerConst, scale: scale))
                    else:
                        allAbsLinear = false
                        break
                else:
                    allAbsLinear = false
                    break

            if allAbsLinear and termInfos.len > 0 and bound >= T(0):
                for info in termInfos:
                    let perBound = bound div info.scale
                    # inner + perBound >= 0
                    linearForms.add(LinearForm[T](
                        coefficients: info.coeffs,
                        constant: info.constant + perBound,
                        relation: GreaterThanEq
                    ))
                    # -inner + perBound >= 0
                    var negCoeffs: Table[int, T]
                    for pos in info.coeffs.keys:
                        negCoeffs[pos] = -info.coeffs[pos]
                    linearForms.add(LinearForm[T](
                        coefficients: negCoeffs,
                        constant: -info.constant + perBound,
                        relation: GreaterThanEq
                    ))
                sumAbsDecomposed += termInfos.len

        # Case B: leftExpr is SumExpr with ExpressionBased evaluation
        elif rel.leftExpr.kind == SumExpr:
            let sumExpr = rel.leftExpr.sumExpr
            if sumExpr.evalMethod == ExpressionBased:
                var adjustedBound = bound - sumExpr.constant
                var allAbsLinear = true
                var termInfos: seq[AbsTermInfo]
                for expr in sumExpr.expressions:
                    let (ok, coeffs, innerConst) = tryExtractAbsLinearNode[T](expr.node)
                    if ok:
                        let scale = getAbsOuterScale[T](expr.node)
                        if scale > T(0):
                            termInfos.add((coeffs: coeffs, constant: innerConst, scale: scale))
                        else:
                            allAbsLinear = false
                            break
                    else:
                        allAbsLinear = false
                        break

                if allAbsLinear and termInfos.len > 0 and adjustedBound >= T(0):
                    for info in termInfos:
                        let perBound = adjustedBound div info.scale
                        linearForms.add(LinearForm[T](
                            coefficients: info.coeffs,
                            constant: info.constant + perBound,
                            relation: GreaterThanEq
                        ))
                        var negCoeffs: Table[int, T]
                        for pos in info.coeffs.keys:
                            negCoeffs[pos] = -info.coeffs[pos]
                        linearForms.add(LinearForm[T](
                            coefficients: negCoeffs,
                            constant: -info.constant + perBound,
                            relation: GreaterThanEq
                        ))
                    sumAbsDecomposed += termInfos.len

    if sumAbsDecomposed > 0:
        stderr.writeLine(&"[DomRed] Sum-of-abs decomposition: {sumAbsDecomposed} terms, {sumAbsDecomposed * 2} linear forms")

    # Phase: Min/max channel to linear forms
    # For max channel ch = max(e1, ..., en): ch >= e_i for all i
    # For min channel ch = min(e1, ..., en): ch <= e_i for all i
    # These structural constraints enable bounds propagation through channels
    var channelLinearForms = 0
    for binding in carray.minMaxChannelBindings:
        let chPos = binding.channelPosition
        for inputExpr in binding.inputExprs:
            if inputExpr.linear:
                # Direct linear input
                let linearized = linearize(inputExpr)
                if linearized.evalMethod != PositionBased:
                    continue

                if not binding.isMin:
                    # Max: ch >= input → ch - input >= 0
                    var coeffs: Table[int, T]
                    coeffs[chPos] = T(1)
                    for pos in linearized.coefficient.keys:
                        if pos in coeffs:
                            coeffs[pos] = coeffs[pos] - linearized.coefficient[pos]
                        else:
                            coeffs[pos] = -linearized.coefficient[pos]
                    linearForms.add(LinearForm[T](
                        coefficients: coeffs,
                        constant: -linearized.constant,
                        relation: GreaterThanEq
                    ))
                else:
                    # Min: ch <= input → input - ch >= 0
                    var coeffs: Table[int, T]
                    coeffs[chPos] = T(-1)
                    for pos in linearized.coefficient.keys:
                        if pos in coeffs:
                            coeffs[pos] = coeffs[pos] + linearized.coefficient[pos]
                        else:
                            coeffs[pos] = linearized.coefficient[pos]
                    linearForms.add(LinearForm[T](
                        coefficients: coeffs,
                        constant: linearized.constant,
                        relation: GreaterThanEq
                    ))
                channelLinearForms += 1
            else:
                # Try abs(linear) pattern: common for int_abs defined variables
                let (ok, innerCoeffs, innerConst) = tryExtractAbsLinearNode[T](inputExpr.node)
                if ok:
                    if not binding.isMin:
                        # Max: ch >= abs(inner) → ch >= inner AND ch >= -inner
                        # Form 1: ch - inner >= 0
                        var coeffs1: Table[int, T]
                        coeffs1[chPos] = T(1)
                        for pos in innerCoeffs.keys:
                            if pos in coeffs1:
                                coeffs1[pos] = coeffs1[pos] - innerCoeffs[pos]
                            else:
                                coeffs1[pos] = -innerCoeffs[pos]
                        linearForms.add(LinearForm[T](
                            coefficients: coeffs1,
                            constant: -innerConst,
                            relation: GreaterThanEq
                        ))
                        # Form 2: ch + inner >= 0
                        var coeffs2: Table[int, T]
                        coeffs2[chPos] = T(1)
                        for pos in innerCoeffs.keys:
                            if pos in coeffs2:
                                coeffs2[pos] = coeffs2[pos] + innerCoeffs[pos]
                            else:
                                coeffs2[pos] = innerCoeffs[pos]
                        linearForms.add(LinearForm[T](
                            coefficients: coeffs2,
                            constant: innerConst,
                            relation: GreaterThanEq
                        ))
                        channelLinearForms += 2
                    else:
                        # Min: ch <= abs(inner) is always true for ch >= 0, not useful
                        # But we can add: ch >= 0 (min of abs values is non-negative)
                        var coeffs: Table[int, T]
                        coeffs[chPos] = T(1)
                        linearForms.add(LinearForm[T](
                            coefficients: coeffs,
                            constant: T(0),
                            relation: GreaterThanEq
                        ))
                        channelLinearForms += 1

    # Count-equals channel linear forms
    # For each countEq binding: count[v] >= 0 and count[v] <= n
    # For groups sharing the same inputPositions: sum(count[v]) == n (closed GCC)
    var countEqLinearForms = 0
    for binding in carray.countEqChannelBindings:
        let chPos = binding.channelPosition
        let n = T(binding.inputPositions.len)
        # count >= 0
        var geCoeffs: Table[int, T]
        geCoeffs[chPos] = T(1)
        linearForms.add(LinearForm[T](
            coefficients: geCoeffs,
            constant: T(0),
            relation: GreaterThanEq
        ))
        # count <= n  →  n - count >= 0
        var leCoeffs: Table[int, T]
        leCoeffs[chPos] = T(-1)
        linearForms.add(LinearForm[T](
            coefficients: leCoeffs,
            constant: n,
            relation: GreaterThanEq
        ))
        countEqLinearForms += 2

    # Detect closed-GCC groups: bindings sharing the same inputPositions
    # For closed groups: sum(all counts) == n
    var groupsByInputs: Table[seq[int], seq[int]]  # inputPositions → [binding indices]
    for i, binding in carray.countEqChannelBindings:
        if binding.inputPositions notin groupsByInputs:
            groupsByInputs[binding.inputPositions] = @[i]
        else:
            groupsByInputs[binding.inputPositions].add(i)
    for inputPositions, bindingIndices in groupsByInputs.pairs:
        if bindingIndices.len < 2: continue
        # Check if closed: all input position domains ⊆ cover set
        var coverValues: PackedSet[int]
        for bi in bindingIndices:
            coverValues.incl(int(carray.countEqChannelBindings[bi].targetValue))
        var isClosed = true
        for p in inputPositions:
            for v in carray.domain[p]:
                if v notin coverValues:
                    isClosed = false
                    break
            if not isClosed: break
        if isClosed:
            # sum(count[v] for v in cover) == n
            var sumCoeffs: Table[int, T]
            for bi in bindingIndices:
                let chPos = carray.countEqChannelBindings[bi].channelPosition
                sumCoeffs[chPos] = T(1)
            linearForms.add(LinearForm[T](
                coefficients: sumCoeffs,
                constant: -T(inputPositions.len),
                relation: EqualTo
            ))
            countEqLinearForms += 1

    channelLinearForms += countEqLinearForms

    if channelLinearForms > 0:
        stderr.writeLine(&"[DomRed] Channel-to-linear forms: {channelLinearForms}")

    # Phase: Cumulative energy bounds
    # For cumulative(starts, durations, heights, limit):
    #   energy = sum(d_i * h_i) <= limit * makespan
    #   => limit >= ceil(energy / makespan_max)
    # When limit is a variable, this gives a lower bound on the limit variable.
    # When limit is constant, this gives a lower bound on makespan which propagates
    # through other constraints.
    # Also: for each task i, start_i + duration_i <= max_end
    #   => start_i <= max_end - duration_i (linear bound on start position)
    var cumulativeEnergyForms = 0
    for cons in carray.constraints:
        if cons.stateType != CumulativeType: continue
        let cumState = cons.cumulativeState

        var durations, heights: seq[T]
        var nTasks: int
        case cumState.evalMethod:
        of PositionBased:
            durations = cumState.durations
            heights = cumState.heights
            nTasks = cumState.originPositions.len
        of ExpressionBased:
            durations = cumState.durationsExpr
            heights = cumState.heightsExpr
            nTasks = cumState.originExpressions.len

        if nTasks == 0: continue

        # Compute total energy
        var energy: T = T(0)
        for i in 0..<nTasks:
            energy += durations[i] * heights[i]

        if energy <= T(0): continue

        # Compute makespan upper bound from domains
        var minStart = T.high
        var maxEnd = T.low
        case cumState.evalMethod:
        of PositionBased:
            for i in 0..<nTasks:
                let pos = cumState.originPositions[i]
                let dom = carray.domain[pos]
                if dom.len == 0: continue
                if dom[0] < minStart: minStart = dom[0]
                let endMax = dom[^1] + durations[i]
                if endMax > maxEnd: maxEnd = endMax
        of ExpressionBased:
            for i in 0..<nTasks:
                let expr = cumState.originExpressions[i]
                for pos in expr.positions.items:
                    let dom = carray.domain[pos]
                    if dom.len == 0: continue
                    if dom[0] < minStart: minStart = dom[0]
                    if dom[^1] > maxEnd: maxEnd = dom[^1]
                # ExpressionBased: maxEnd is approximate (from position domains, not expr evaluation)
                # Add maximum possible duration shift
                maxEnd += durations[i]

        let makespanMax = maxEnd - minStart
        if makespanMax <= T(0): continue

        # Variable limit: limit >= ceil(energy / makespanMax)
        if cumState.limitPosition >= 0:
            let lowerBound = (energy + makespanMax - T(1)) div makespanMax  # ceil division
            # limitVar >= lowerBound => limitVar - lowerBound >= 0
            var coeffs: Table[int, T]
            coeffs[cumState.limitPosition] = T(1)
            linearForms.add(LinearForm[T](
                coefficients: coeffs,
                constant: -lowerBound,
                relation: GreaterThanEq
            ))
            cumulativeEnergyForms += 1

        # Per-task start bounds: for PositionBased with constant limit,
        # start_i + duration_i <= limit (resource time horizon not directly, but
        # we know start_i >= 0 from domains; the useful bound is from the start+dur<=W
        # constraints which are already generated by MiniZinc as int_lin_le).

    if cumulativeEnergyForms > 0:
        stderr.writeLine(&"[DomRed] Cumulative energy bounds: {cumulativeEnergyForms} linear forms")

    # Phase: Diffn area/strip bounds
    # For diffn(x, y, dx, dy):
    #   1. Area bound: sum(dx_i * dy_i) <= W * H where W/H are bounding box dimensions
    #      If a cumulative constraint shares the same starts/dimensions and has a variable limit,
    #      the area bound tightens the limit (e.g., objective).
    #   2. Per-rect strip bounds: x_i + dx_i <= W, y_i + dy_i <= H
    #      These are linear forms when expressions are linear.
    var diffnBoundForms = 0
    for cons in carray.constraints:
        if cons.stateType != DiffnType: continue
        let ds = cons.diffnState
        let n = ds.n

        # Compute minimum total area using domain bounds on dimensions
        # For each rect, compute min(dx_i) * min(dy_i) as a conservative area lower bound
        var totalMinArea: T = T(0)
        for i in 0..<n:
            var minDX, minDY: T

            if ds.dxExprs[i].positions.len == 0:
                # Constant expression — evaluate directly
                minDX = ds.dxExprs[i].node.evaluate(initTable[int, T]())
            else:
                # Variable — use minimum domain values for each position
                # For a linear expression, min occurs at min/max of domain depending on coefficient sign
                if ds.dxExprs[i].linear:
                    let lin = linearize(ds.dxExprs[i])
                    var minVal: T = lin.constant
                    for pos in lin.coefficient.keys:
                        let c = lin.coefficient[pos]
                        let dom = carray.domain[pos]
                        if dom.len == 0: continue
                        if c > 0:
                            minVal += c * dom[0]
                        else:
                            minVal += c * dom[^1]
                    minDX = max(minVal, T(0))
                else:
                    minDX = T(0)  # Can't bound non-linear — conservative

            if ds.dyExprs[i].positions.len == 0:
                minDY = ds.dyExprs[i].node.evaluate(initTable[int, T]())
            else:
                if ds.dyExprs[i].linear:
                    let lin = linearize(ds.dyExprs[i])
                    var minVal: T = lin.constant
                    for pos in lin.coefficient.keys:
                        let c = lin.coefficient[pos]
                        let dom = carray.domain[pos]
                        if dom.len == 0: continue
                        if c > 0:
                            minVal += c * dom[0]
                        else:
                            minVal += c * dom[^1]
                    minDY = max(minVal, T(0))
                else:
                    minDY = T(0)

            totalMinArea += minDX * minDY

        if totalMinArea <= T(0): continue

        # Find companion cumulative constraints sharing the same variable limit
        # Pattern: cumulative(x, dx, dy, Limit) or cumulative(y, dy, dx, Limit)
        # where Limit is a variable (e.g., objective)
        for cons2 in carray.constraints:
            if cons2.stateType != CumulativeType: continue
            let cumState = cons2.cumulativeState
            if cumState.limitPosition < 0: continue  # constant limit, skip

            # Get the cumulative's fixed capacity (the non-variable dimension)
            # Look for a companion cumulative with a constant limit
            # that represents the other dimension of the bounding box
            discard  # Handled below

        # Approach: for each cumulative with variable limit sharing positions with this diffn,
        # the area bound gives: limitVar >= ceil(totalMinArea / fixedDimLimit)
        # But we need to find the fixed dimension. In carpet-cutting:
        #   cumulative(y, dy, dx, objective) => objective >= ceil(area / H)
        #   cumulative(x, dx, dy, 1000)     => H=1000 is the fixed dimension
        # General approach: for any cumulative with variable limit, we know
        # limit * makespan_ub >= energy. The area bound is:
        # limit >= ceil(totalMinArea / other_dimension_limit)
        #
        # Find constant-limit cumulatives sharing positions with this diffn
        for cons2 in carray.constraints:
            if cons2.stateType != CumulativeType: continue
            let cumState = cons2.cumulativeState
            if cumState.limitPosition >= 0: continue  # variable limit, skip
            let fixedLimit = cumState.limit
            if fixedLimit <= T(0): continue

            # Check if this cumulative shares positions with the diffn
            var shared = false
            for pos in cons2.positions.items:
                if pos in cons.positions:
                    shared = true
                    break
            if not shared: continue

            # Now find variable-limit cumulatives also sharing positions with diffn
            for cons3 in carray.constraints:
                if cons3.stateType != CumulativeType: continue
                let cumState3 = cons3.cumulativeState
                if cumState3.limitPosition < 0: continue  # constant limit, skip

                var shared3 = false
                for pos in cons3.positions.items:
                    if pos in cons.positions:
                        shared3 = true
                        break
                if not shared3: continue

                # Area bound: varLimit >= ceil(totalMinArea / fixedLimit)
                let lowerBound = (totalMinArea + fixedLimit - T(1)) div fixedLimit
                var coeffs: Table[int, T]
                coeffs[cumState3.limitPosition] = T(1)
                linearForms.add(LinearForm[T](
                    coefficients: coeffs,
                    constant: -lowerBound,
                    relation: GreaterThanEq
                ))
                diffnBoundForms += 1

        # Per-rect linear bounds: if x_i + dx_i is a linear expression,
        # generate synthetic linear forms for bounds propagation.
        # For each rect i where xExpr[i] + dxExpr[i] is linear:
        #   xExpr[i] + dxExpr[i] <= domainMax(objective or bounding variable)
        #   This is already handled by int_lin_le constraints from MiniZinc.
        # More useful: pairwise separation bounds.
        # For rects i,j: if min_y_i + min_dy_i > max_y_j or min_y_j + min_dy_j > max_y_i,
        # they can't overlap in y -> no x constraint needed.
        # Otherwise they MIGHT overlap in y, so they must separate in x:
        #   x_i + dx_i <= x_j OR x_j + dx_j <= x_i
        # This is a disjunction, not a linear form. But if we have 3+ rects that all
        # must separate in x, we get: sum(dx_i) <= W (strip bound).
        # Compute a "must-separate-in-x" clique and add sum(dx_i) <= varLimit.

        # Strip bound using compulsory parts.
        # A rect's compulsory y-interval is [lst_y, est_y + minDy) where:
        #   est_y = earliest start (min possible y)
        #   lst_y = latest start (max possible y)
        #   minDy = minimum height
        # A rect only has a compulsory part if lst_y < est_y + minDy.
        # At any y-cut, sum of minWidths of rects whose compulsory part covers that y <= limit.
        type CompulsoryPart = tuple[cpStart, cpEnd, minWidth: T, valid: bool]
        var compParts = newSeq[CompulsoryPart](n)
        for i in 0..<n:
            var estY, lstY, minDY: T

            # Compute est_y (earliest start) and lst_y (latest start)
            if ds.yExprs[i].positions.len == 0:
                let yConst = ds.yExprs[i].node.evaluate(initTable[int, T]())
                estY = yConst
                lstY = yConst
            elif ds.yExprs[i].linear:
                let lin = linearize(ds.yExprs[i])
                var minVal: T = lin.constant
                var maxVal: T = lin.constant
                for pos in lin.coefficient.keys:
                    let c = lin.coefficient[pos]
                    let dom = carray.domain[pos]
                    if dom.len == 0: continue
                    if c > 0:
                        minVal += c * dom[0]
                        maxVal += c * dom[^1]
                    else:
                        minVal += c * dom[^1]
                        maxVal += c * dom[0]
                estY = minVal
                lstY = maxVal
            else:
                # Non-linear — can't compute tight bounds, skip
                compParts[i].valid = false
                continue

            # Compute minDy
            if ds.dyExprs[i].positions.len == 0:
                minDY = ds.dyExprs[i].node.evaluate(initTable[int, T]())
            elif ds.dyExprs[i].linear:
                let lin = linearize(ds.dyExprs[i])
                var minVal: T = lin.constant
                for pos in lin.coefficient.keys:
                    let c = lin.coefficient[pos]
                    let dom = carray.domain[pos]
                    if dom.len == 0: continue
                    if c > 0: minVal += c * dom[0]
                    else: minVal += c * dom[^1]
                minDY = max(minVal, T(0))
            else:
                minDY = T(0)

            # Compute minimum width (dx)
            var minDX: T
            if ds.dxExprs[i].positions.len == 0:
                minDX = ds.dxExprs[i].node.evaluate(initTable[int, T]())
            elif ds.dxExprs[i].linear:
                let lin = linearize(ds.dxExprs[i])
                var minVal: T = lin.constant
                for pos in lin.coefficient.keys:
                    let c = lin.coefficient[pos]
                    let dom = carray.domain[pos]
                    if dom.len == 0: continue
                    if c > 0: minVal += c * dom[0]
                    else: minVal += c * dom[^1]
                minDX = max(minVal, T(0))
            else:
                minDX = T(0)

            # Compulsory part exists only if lst_y < est_y + minDy
            if lstY < estY + minDY:
                compParts[i] = (cpStart: lstY, cpEnd: estY + minDY, minWidth: minDX, valid: true)
            else:
                compParts[i].valid = false

        # For each variable-limit cumulative sharing positions with diffn,
        # sweep over compulsory parts to find the y-cut with maximum total width.
        for cons3 in carray.constraints:
            if cons3.stateType != CumulativeType: continue
            let cumState3 = cons3.cumulativeState
            if cumState3.limitPosition < 0: continue

            var shared3 = false
            for pos in cons3.positions.items:
                if pos in cons.positions:
                    shared3 = true
                    break
            if not shared3: continue

            # Find best strip bound by sweeping compulsory part start points
            var bestStripSum: T = T(0)
            for i in 0..<n:
                if not compParts[i].valid: continue
                let cutY = compParts[i].cpStart
                var stripSum: T = T(0)
                for j in 0..<n:
                    if not compParts[j].valid: continue
                    if compParts[j].cpStart <= cutY and cutY < compParts[j].cpEnd:
                        stripSum += compParts[j].minWidth
                if stripSum > bestStripSum:
                    bestStripSum = stripSum

            if bestStripSum > T(0):
                # limitVar >= bestStripSum
                var coeffs: Table[int, T]
                coeffs[cumState3.limitPosition] = T(1)
                linearForms.add(LinearForm[T](
                    coefficients: coeffs,
                    constant: -bestStripSum,
                    relation: GreaterThanEq
                ))
                diffnBoundForms += 1

        # Time profile bound for all-constant x/dx/dy diffn:
        # When all x, dx, and dy are constants, compute exact max load via sweep-line.
        # This gives limitVar >= maxLoad for any variable-limit cumulative sharing positions.
        block timeProfile:
            var allConst = true
            for i in 0..<n:
                if ds.xExprs[i].positions.len > 0 or
                   ds.dxExprs[i].positions.len > 0 or
                   ds.dyExprs[i].positions.len > 0:
                    allConst = false
                    break
            if allConst:
                # Compute time profile via sweep-line
                # Use int arrays to avoid generic closure issues
                var eventTimes: seq[int]
                var eventDeltas: seq[int]
                let emptyAssign = initTable[int, T]()
                for i in 0..<n:
                    let x = int(ds.xExprs[i].node.evaluate(emptyAssign))
                    let dx = int(ds.dxExprs[i].node.evaluate(emptyAssign))
                    let dy = int(ds.dyExprs[i].node.evaluate(emptyAssign))
                    eventTimes.add(x)
                    eventDeltas.add(dy)
                    eventTimes.add(x + dx)
                    eventDeltas.add(-dy)
                # Insertion sort by time, then by delta (end events before start events
                # at the same time to avoid inflating max load)
                for i in 1..<eventTimes.len:
                    var j = i
                    while j > 0 and (eventTimes[j] < eventTimes[j-1] or
                                     (eventTimes[j] == eventTimes[j-1] and eventDeltas[j] < eventDeltas[j-1])):
                        swap(eventTimes[j], eventTimes[j-1])
                        swap(eventDeltas[j], eventDeltas[j-1])
                        dec j
                var maxLoad: T = T(0)
                var currentLoad: T = T(0)
                for i in 0..<eventTimes.len:
                    currentLoad += T(eventDeltas[i])
                    if currentLoad > maxLoad:
                        maxLoad = currentLoad
                if maxLoad > T(0):
                    for cons3 in carray.constraints:
                        if cons3.stateType != CumulativeType: continue
                        let cumState3 = cons3.cumulativeState
                        if cumState3.limitPosition < 0: continue
                        var shared3 = false
                        for pos in cons3.positions.items:
                            if pos in cons.positions:
                                shared3 = true; break
                        if not shared3: continue
                        var coeffs: Table[int, T]
                        coeffs[cumState3.limitPosition] = T(1)
                        linearForms.add(LinearForm[T](
                            coefficients: coeffs,
                            constant: -maxLoad,
                            relation: GreaterThanEq
                        ))
                        diffnBoundForms += 1
                    stderr.writeLine(&"[DomRed] Diffn time profile: max_load = {maxLoad} ({n} all-const rects)")

    if diffnBoundForms > 0:
        stderr.writeLine(&"[DomRed] Diffn area/strip bounds: {diffnBoundForms} linear forms")

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

    # Fourier-Motzkin resolution: derive new constraints by pairwise elimination.
    # Only keep resolvents that have strictly fewer positions than both parents.
    # Single-var resolvents (direct bounds) are always valuable. Multi-var resolvents
    # are added too but limited to avoid bloating bounds propagation.
    block fmResolution:
        var positiveAt: Table[int, seq[int]]
        var negativeAt: Table[int, seq[int]]
        for fi, form in normalizedForms:
            for pos, coeff in form.coefficients.pairs:
                if coeff > 0:
                    positiveAt.mgetOrPut(pos, @[]).add(fi)
                elif coeff < 0:
                    negativeAt.mgetOrPut(pos, @[]).add(fi)

        var totalResolvents = 0
        const MaxResolventsPerPos = 50
        const MaxTotalResolvents = 500
        const MaxPairProduct = 100

        for pos in positiveAt.keys:
            if pos notin negativeAt:
                continue
            let posIdxs = positiveAt[pos]
            let negIdxs = negativeAt[pos]
            if posIdxs.len * negIdxs.len > MaxPairProduct:
                continue
            var posResolvents = 0
            for pIdx in posIdxs:
                if posResolvents >= MaxResolventsPerPos or totalResolvents >= MaxTotalResolvents:
                    break
                let fp = normalizedForms[pIdx]
                let ap = fp.coefficients[pos]
                for nIdx in negIdxs:
                    if posResolvents >= MaxResolventsPerPos or totalResolvents >= MaxTotalResolvents:
                        break
                    let fn = normalizedForms[nIdx]
                    let an = fn.coefficients[pos]
                    let absAn = -an
                    var resolvent: Table[int, T]
                    var resolventConst: T = absAn * fp.constant + ap * fn.constant
                    for p, c in fp.coefficients.pairs:
                        if p == pos: continue
                        resolvent[p] = absAn * c
                    for p, c in fn.coefficients.pairs:
                        if p == pos: continue
                        if p in resolvent:
                            resolvent[p] = resolvent[p] + ap * c
                        else:
                            resolvent[p] = ap * c
                    var toRemove: seq[int]
                    for p, c in resolvent.pairs:
                        if c == T(0):
                            toRemove.add(p)
                    for p in toRemove:
                        resolvent.del(p)
                    if resolvent.len >= fp.coefficients.len or resolvent.len >= fn.coefficients.len:
                        continue
                    if resolvent.len == 0:
                        continue
                    # gcd(0, x) == x, so starting from resolventConst==0 is safe
                    var g = abs(resolventConst)
                    for p, c in resolvent.pairs:
                        g = gcd(g, abs(c))
                    if g > 1:
                        for p in resolvent.keys:
                            resolvent[p] = resolvent[p] div g
                        resolventConst = resolventConst div g
                    normalizedForms.add(NormalizedForm(
                        coefficients: resolvent, constant: resolventConst))
                    posResolvents += 1
                    totalResolvents += 1

        if totalResolvents > 0:
            stderr.writeLine(&"[DomRed] FM resolution: {totalResolvents} resolvents added")

    # Collect allDifferent constraint positions for Phase 4
    var allDiffGroups: seq[seq[int]]
    for cons in carray.constraints:
        if cons.stateType == AllDifferentType and
           cons.allDifferentState.evalMethod == PositionBased:
            allDiffGroups.add(toSeq(cons.positions.items))

    # Collect ne pairs for singleton propagation (Phase 5c)
    type NePair = object
        posA, posB: int
        coeffA, coeffB: T
        constant: T
    var nePairs: seq[NePair]
    var neAtPos: Table[int, seq[int]]  # position -> indices into nePairs
    for form in linearForms:
        if form.relation == NotEqualTo and form.coefficients.len == 2:
            let positions = toSeq(form.coefficients.keys)
            let pair = NePair(
                posA: positions[0], posB: positions[1],
                coeffA: form.coefficients[positions[0]],
                coeffB: form.coefficients[positions[1]],
                constant: form.constant)
            let idx = nePairs.len
            nePairs.add(pair)
            neAtPos.mgetOrPut(positions[0], @[]).add(idx)
            neAtPos.mgetOrPut(positions[1], @[]).add(idx)
    # Also handle 1-position ne constraints: coeff * x + constant != 0  →  x != -constant/coeff
    for form in linearForms:
        if form.relation == NotEqualTo and form.coefficients.len == 1:
            let pos = toSeq(form.coefficients.keys)[0]
            let coeff = form.coefficients[pos]
            let numerator = -form.constant
            if coeff != T(0) and numerator mod coeff == T(0):
                let forbiddenVal = numerator div coeff
                if forbiddenVal in currentDomain[pos]:
                    currentDomain[pos].excl(forbiddenVal)
    if nePairs.len > 0:
        stderr.writeLine(&"[DomRed] Collected {nePairs.len} binary ne pairs for singleton propagation")

    # Collect small-arity constraints for GAC
    const MAX_GAC_ARITY = 12
    const MAX_GAC_COMBOS = 50_000
    const GAC_TIME_BUDGET = 1.0  # seconds per outer iteration
    var gacConstraints: seq[int]  # indices into carray.constraints
    for i, cons in carray.constraints:
        if cons.stateType in {AlgebraicType, RelationalType, BooleanType}:
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

    # Precompute reverse map: position -> element constraints where it's a variable array element
    # Used for backward propagation (Phase 6b-elem)
    var elemArrayParticipation: Table[int, seq[int]]  # pos -> constraint indices
    for ci, cons in carray.constraints:
        if cons.stateType == ElementType:
            let es = cons.elementState
            if es.evalMethod == PositionBased and not es.isConstantArray:
                var seen = initPackedSet[int]()  # deduplicate positions within this constraint
                for elem in es.arrayElements:
                    if not elem.isConstant and elem.variablePosition notin seen:
                        seen.incl(elem.variablePosition)
                        elemArrayParticipation.mgetOrPut(elem.variablePosition, @[]).add(ci)

    # Precompute reverse map: position -> channel binding indices where it's a variable array element
    # Used for backward propagation (Phase CB-var)
    var channelArrayParticipation: Table[int, seq[int]]  # pos -> binding indices
    for bi, binding in carray.channelBindings:
        var hasVariable = false
        for elem in binding.arrayElements:
            if not elem.isConstant:
                hasVariable = true
                break
        if hasVariable:
            for elem in binding.arrayElements:
                if not elem.isConstant:
                    channelArrayParticipation.mgetOrPut(elem.variablePosition, @[]).add(bi)

    # Precompute reverse map: single-position index -> variable-array channel binding indices
    # Used for Phase CB-idx (multi-constraint index domain filtering)
    var idxToVarArrayBindings: Table[int, seq[int]]  # idxPos -> binding indices
    for bi, binding in carray.channelBindings:
        var hasVariable = false
        for elem in binding.arrayElements:
            if not elem.isConstant:
                hasVariable = true
                break
        if not hasVariable: continue
        let idxPositions = toSeq(binding.indexExpression.positions.items)
        if idxPositions.len == 1:
            let idxPos = idxPositions[0]
            idxToVarArrayBindings.mgetOrPut(idxPos, @[]).add(bi)

    # Also map: index position -> element constraint indices (for Phase CB-idx)
    var idxToElementConstraints: Table[int, seq[int]]  # idxPos -> constraint indices
    for ci, cons in carray.constraints:
        if cons.stateType == ElementType:
            let es = cons.elementState
            if es.evalMethod != PositionBased: continue
            if es.isConstantArray: continue  # constant arrays handled by Phase 6 already
            var hasVariable = false
            for elem in es.arrayElements:
                if not elem.isConstant:
                    hasVariable = true
                    break
            if not hasVariable: continue
            let idxPos = es.indexPosition
            idxToElementConstraints.mgetOrPut(idxPos, @[]).add(ci)

    # Outer fixed-point loop: bounds propagation <-> allDifferent propagation
    var domainMin = newSeq[T](carray.len)
    var domainMax = newSeq[T](carray.len)

    # Precompute positions involved in bounds propagation (for targeted application)
    var boundsPositions: PackedSet[int]
    for form in normalizedForms:
        for pos in form.coefficients.keys:
            boundsPositions.incl(pos)
    for dp in carray.disjunctivePairs:
        for pos in dp.positions1: boundsPositions.incl(pos)
        for pos in dp.positions2: boundsPositions.incl(pos)

    # Initialize domainMin/domainMax for skipped positions once (before outer loop)
    # so their bounds can be tightened by bounds propagation without resetting.
    for pos in carray.allPositions():
        if pos in skippedPositions:
            domainMin[pos] = carray.domain[pos][0]
            domainMax[pos] = carray.domain[pos][^1]

    # Precompute Phase CB constant-array binding metadata (avoids repeated allConstant checks)
    type CbBindingInfo = tuple[bi: int, chPos: int, idxPositions: seq[int]]
    var cbConstBindings: seq[CbBindingInfo]
    var cbParticipantPositions = initPackedSet[int]()
    for bi, binding in carray.channelBindings:
        var allConstant = true
        for elem in binding.arrayElements:
            if not elem.isConstant:
                allConstant = false
                break
        if not allConstant: continue
        let idxPos = toSeq(binding.indexExpression.positions.items)
        if idxPos.len == 0 or idxPos.len > 6: continue
        cbConstBindings.add((bi: bi, chPos: binding.channelPosition, idxPositions: idxPos))
        cbParticipantPositions.incl(binding.channelPosition)
        for p in idxPos:
            cbParticipantPositions.incl(p)

    # Snapshot of domain sizes for Phase CB dirty detection
    var cbDomSnapshot = newSeq[int](carray.len)
    for pos in cbParticipantPositions.items:
        cbDomSnapshot[pos] = if pos in skippedPositions: -1
                             else: currentDomain[pos].len

    let domRedStartTime = epochTime()
    const DomRedTimeBudget = 5.0  # seconds

    for outerIter in 0..<100:
        var outerChanged = false

        if outerIter > 0 and epochTime() - domRedStartTime > DomRedTimeBudget:
            stderr.writeLine(&"[DomRed] Time budget ({DomRedTimeBudget:.1f}s) reached after {outerIter} iterations")
            break

        # Phase 3: Bounds propagation
        if normalizedForms.len > 0 or carray.disjunctivePairs.len > 0:
            # Compute domainMin/domainMax from current PackedSets
            for pos in carray.allPositions():
                if pos in skippedPositions:
                    # Preserve tightened bounds from previous iterations (don't reset)
                    discard
                elif currentDomain[pos].len > 0:
                    # For channel positions not in any bounds constraint, use domain endpoints
                    if pos in carray.channelPositions and pos notin boundsPositions:
                        domainMin[pos] = carray.domain[pos][0]
                        domainMax[pos] = carray.domain[pos][^1]
                    else:
                        domainMin[pos] = T.high
                        domainMax[pos] = T.low
                        for v in currentDomain[pos].items:
                            if v < domainMin[pos]: domainMin[pos] = v
                            if v > domainMax[pos]: domainMax[pos] = v
                else:
                    domainMin[pos] = T(0)
                    domainMax[pos] = T(0)

            if normalizedForms.len > 0:
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
                    for pos in boundsPositions.items:
                        if domainMin[pos] > domainMax[pos]:
                            infeasible = true
                            break
                    if infeasible:
                        break

            # Apply tightened bounds to PackedSets (only positions in bounds constraints)
            # Skip skipped positions: their PackedSets are 1-element placeholders, not real domains
            for pos in boundsPositions.items:
                if pos in skippedPositions: continue
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

        let gacStartTime = epochTime()
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
                # Time budget check
                if epochTime() - gacStartTime > GAC_TIME_BUDGET:
                    break

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
                    if pen < 0:
                        # Constraint type not supported by evaluateConstraint — skip entirely
                        for i in 0..<positions.len:
                            for v in currentDomain[positions[i]].items:
                                supported[i].incl(v)
                        break
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

                # Remove unsupported values (skip channel positions — their domains
                # are defined by channel bindings, not by constraints. GAC treats them
                # as independent but they're functionally determined, leading to over-pruning.)
                var pruned = 0
                for i in 0..<positions.len:
                    let pos = positions[i]
                    if pos in carray.channelPositions:
                        continue  # Don't prune channel position domains via GAC
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

        # Phase 5c: NotEqual singleton propagation
        # When a variable in a binary != constraint becomes singleton,
        # remove the forbidden value from the other variable's domain.
        if nePairs.len > 0:
            for iteration in 0..<nePairs.len:
                var changed = false
                for pos, pairIndices in neAtPos.pairs:
                    if currentDomain[pos].len != 1:
                        continue
                    var singletonVal: T
                    for v in currentDomain[pos].items:
                        singletonVal = v
                    for idx in pairIndices:
                        let pair = nePairs[idx]
                        let (myCoeff, otherPos, otherCoeff) =
                            if pair.posA == pos:
                                (pair.coeffA, pair.posB, pair.coeffB)
                            else:
                                (pair.coeffB, pair.posA, pair.coeffA)
                        # myCoeff * singletonVal + otherCoeff * y + constant != 0
                        # → y != -(myCoeff * singletonVal + constant) / otherCoeff
                        let numerator = -(myCoeff * singletonVal + pair.constant)
                        if otherCoeff != T(0) and numerator mod otherCoeff == T(0):
                            let forbiddenVal = numerator div otherCoeff
                            if forbiddenVal in currentDomain[otherPos]:
                                currentDomain[otherPos].excl(forbiddenVal)
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

        # Phase 5d: GCC (Global Cardinality) domain reduction
        var gccPruned = 0
        for cons in carray.constraints:
            if cons.stateType != GlobalCardinalityType: continue
            let gcc = cons.globalCardinalityState
            if gcc.evalMethod != PositionBased: continue

            # Collect non-skipped positions
            var gccPositions: seq[int]
            for pos in gcc.positions.items:
                if pos notin skippedPositions:
                    gccPositions.add(pos)
            let nPositions = gccPositions.len
            if nPositions == 0: continue

            case gcc.constraintType
            of ExactCounts:
                var totalTarget = 0
                for coverVal in gcc.cover:
                    let target = gcc.targetCounts[coverVal]
                    totalTarget += target
                    var forced = 0
                    var possiblePositions: seq[int]
                    for pos in gccPositions:
                        if currentDomain[pos].len == 1 and coverVal in currentDomain[pos]:
                            forced += 1
                        if coverVal in currentDomain[pos]:
                            possiblePositions.add(pos)

                    if forced >= target:
                        # Value fully assigned — remove from non-singleton positions
                        for pos in possiblePositions:
                            if currentDomain[pos].len > 1:
                                currentDomain[pos].excl(coverVal)
                                outerChanged = true
                                inc gccPruned

                    elif possiblePositions.len == target:
                        # All positions that can take coverVal must take it
                        for pos in possiblePositions:
                            if currentDomain[pos].len > 1:
                                currentDomain[pos] = toPackedSet[T]([coverVal])
                                outerChanged = true

                # Closed-world: if sum of targets == nPositions, remove non-cover values
                if totalTarget == nPositions:
                    let coverSet = toPackedSet[T](gcc.cover)
                    for pos in gccPositions:
                        if currentDomain[pos].len > 1:
                            var pruned = false
                            for v in toSeq(currentDomain[pos].items):
                                if v notin coverSet:
                                    currentDomain[pos].excl(v)
                                    pruned = true
                            if pruned:
                                outerChanged = true

            of BoundedCounts:
                var totalLB = 0
                for coverVal in gcc.cover:
                    let ub = gcc.upperBounds[coverVal]
                    let lb = gcc.lowerBounds[coverVal]
                    totalLB += lb
                    var forced = 0
                    var possiblePositions: seq[int]
                    for pos in gccPositions:
                        if currentDomain[pos].len == 1 and coverVal in currentDomain[pos]:
                            forced += 1
                        if coverVal in currentDomain[pos]:
                            possiblePositions.add(pos)

                    if forced >= ub:
                        # Upper bound reached — remove from non-singleton positions
                        for pos in possiblePositions:
                            if currentDomain[pos].len > 1:
                                currentDomain[pos].excl(coverVal)
                                outerChanged = true

                    elif possiblePositions.len <= lb:
                        # All positions that can take coverVal must take it
                        for pos in possiblePositions:
                            if currentDomain[pos].len > 1:
                                currentDomain[pos] = toPackedSet[T]([coverVal])
                                outerChanged = true

                # Closed-world: if sum of lower bounds >= nPositions, remove non-cover values
                if totalLB >= nPositions:
                    let coverSet = toPackedSet[T](gcc.cover)
                    for pos in gccPositions:
                        if currentDomain[pos].len > 1:
                            var pruned = false
                            for v in toSeq(currentDomain[pos].items):
                                if v notin coverSet:
                                    currentDomain[pos].excl(v)
                                    pruned = true
                            if pruned:
                                outerChanged = true

        # Phase Regular: DFA reachability domain reduction
        var regPruned, regSkipped = 0
        for cons in carray.constraints:
            if cons.stateType != RegularType: continue
            let reg = cons.regularState
            let n = reg.n
            if n == 0: continue

            # Skip if any position is in skippedPositions
            var hasSkipped = false
            var maxDomSize = 0
            for pos in reg.positions.items:
                if pos in skippedPositions:
                    hasSkipped = true
                    break
                if currentDomain[pos].len > maxDomSize:
                    maxDomSize = currentDomain[pos].len
            if hasSkipped:
                inc regSkipped
                continue

            # Guard against pathological cases
            if n * maxDomSize * reg.nStates > 1_000_000:
                inc regSkipped
                continue

            # Forward pass: compute reachable states at each position
            var forwardStates = newSeq[PackedSet[int]](n + 1)
            forwardStates[0].incl(reg.initialState)
            for i in 0..<n:
                let pos = reg.sortedPositions[i]
                for s in forwardStates[i].items:
                    for v in currentDomain[pos].items:
                        let ns = reg.getNextState(s, v)
                        if ns != 0:
                            forwardStates[i + 1].incl(ns)
                if forwardStates[i + 1].len == 0:
                    break  # Dead end — no reachable states

            # Backward pass: compute states that can reach final states
            var backwardStates = newSeq[PackedSet[int]](n + 1)
            backwardStates[n] = reg.finalStates
            for i in countdown(n - 1, 0):
                let pos = reg.sortedPositions[i]
                for s in forwardStates[i].items:
                    for v in currentDomain[pos].items:
                        let ns = reg.getNextState(s, v)
                        if ns != 0 and ns in backwardStates[i + 1]:
                            backwardStates[i].incl(s)

            # Filter: remove unsupported values
            for i in 0..<n:
                let pos = reg.sortedPositions[i]
                if currentDomain[pos].len <= 1: continue
                var supported: PackedSet[T]
                for v in currentDomain[pos].items:
                    var hasSupport = false
                    for s in forwardStates[i].items:
                        let ns = reg.getNextState(s, v)
                        if ns != 0 and ns in backwardStates[i + 1]:
                            hasSupport = true
                            break
                    if hasSupport:
                        supported.incl(v)
                if supported.len < currentDomain[pos].len:
                    regPruned += currentDomain[pos].len - supported.len
                    currentDomain[pos] = supported
                    outerChanged = true

        discard (gccPruned, regPruned, regSkipped)

        # Phase: Time-table domain reduction for disjunctive cumulative (limit=1)
        # For each cumulative constraint with limit=1 and all heights=1:
        # 1. Compute compulsory parts: [LST_i, EST_i + dur_i) when LST_i < EST_i + dur_i
        # 2. Build compulsory profile with prefix sums
        # 3. Prune start values where foreign compulsory usage overlaps
        for cons in carray.constraints:
            if cons.stateType != CumulativeType: continue
            let cumState = cons.cumulativeState
            if cumState.limit != 1: continue
            if cumState.evalMethod != PositionBased: continue
            # Verify all heights are constant 1 (skip if any height is variable)
            var allUnit = true
            for i, h in cumState.heights:
                if h != T(1):
                    allUnit = false
                    break
                if cumState.heightPositions.len > 0 and i < cumState.heightPositions.len and cumState.heightPositions[i] >= 0:
                    allUnit = false
                    break
            if not allUnit: continue

            let nTasks = cumState.originPositions.len
            if nTasks < 2: continue

            # Compute EST (earliest start time) and LST (latest start time) from current domains
            var est = newSeq[int](nTasks)
            var lst = newSeq[int](nTasks)
            var hasCompulsory = false
            var globalMin = high(int)
            var globalMax = low(int)

            for i in 0..<nTasks:
                let pos = cumState.originPositions[i]
                let dur = int(cumState.durations[i])
                if dur <= 0: continue
                if currentDomain[pos].len == 0: continue
                # Get min and max from current domain
                var dmin = high(int)
                var dmax = low(int)
                for v in currentDomain[pos].items:
                    if int(v) < dmin: dmin = int(v)
                    if int(v) > dmax: dmax = int(v)
                est[i] = dmin
                lst[i] = dmax
                if lst[i] < est[i] + dur:
                    hasCompulsory = true
                if dmin < globalMin: globalMin = dmin
                let ect = dmax + dur
                if ect > globalMax: globalMax = ect

            if not hasCompulsory: continue
            if globalMax - globalMin > 100000: continue  # Guard against enormous profiles

            let profileSize = globalMax - globalMin + 1
            var profile = newSeq[int](profileSize)

            # Build compulsory profile
            for i in 0..<nTasks:
                let pos = cumState.originPositions[i]
                let dur = int(cumState.durations[i])
                if dur <= 0 or currentDomain[pos].len == 0: continue
                let compStart = lst[i]
                let compEnd = est[i] + dur
                if compStart < compEnd:
                    # Task i has a compulsory part [compStart, compEnd)
                    for t in compStart..<compEnd:
                        profile[t - globalMin] += 1

            # Build prefix sums for O(1) range queries
            var prefix = newSeq[int](profileSize + 1)
            for t in 0..<profileSize:
                prefix[t + 1] = prefix[t] + profile[t]

            # Prune infeasible start values for each task
            for i in 0..<nTasks:
                let pos = cumState.originPositions[i]
                let dur = int(cumState.durations[i])
                if dur <= 0 or currentDomain[pos].len == 0: continue
                let compStart = lst[i]
                let compEnd = est[i] + dur
                let hasOwnCompulsory = compStart < compEnd

                var toExclude: seq[T]
                for v in currentDomain[pos].items:
                    let s = int(v)
                    let sEnd = s + dur
                    # Clamp to profile range
                    let lo = max(s, globalMin) - globalMin
                    let hi = min(sEnd, globalMax) - globalMin
                    if lo >= hi: continue
                    # Total compulsory usage in [s, s+dur)
                    var totalUsage = prefix[hi] - prefix[lo]
                    # Subtract own contribution if this task has a compulsory part
                    if hasOwnCompulsory:
                        let ownLo = max(s, compStart) - globalMin
                        let ownHi = min(sEnd, compEnd) - globalMin
                        if ownLo < ownHi:
                            totalUsage -= (ownHi - ownLo)  # Own contribution is 1 per time unit
                    # For limit=1 resource: any foreign usage > 0 means conflict
                    if totalUsage > 0:
                        toExclude.add(v)

                for v in toExclude:
                    currentDomain[pos].excl(v)
                    outerChanged = true

        # Phase: Disjunctive pair propagation
        if carray.disjunctivePairs.len > 0:
            # Recompute domainMin/domainMax from current PackedSets
            for pos in carray.allPositions():
                if currentDomain[pos].len > 0:
                    domainMin[pos] = T.high
                    domainMax[pos] = T.low
                    for v in currentDomain[pos].items:
                        if v < domainMin[pos]: domainMin[pos] = v
                        if v > domainMax[pos]: domainMax[pos] = v

            for dp in carray.disjunctivePairs:
                # Compute min/max of each linear expression: coeffs · vars - rhs
                # Disjunct is satisfied when coeffs · vars - rhs <= 0, i.e. coeffs · vars <= rhs
                var minE1, maxE1, minE2, maxE2: T = 0
                for i, pos in dp.positions1:
                    if dp.coeffs1[i] > 0:
                        minE1 += dp.coeffs1[i] * domainMin[pos]
                        maxE1 += dp.coeffs1[i] * domainMax[pos]
                    else:
                        minE1 += dp.coeffs1[i] * domainMax[pos]
                        maxE1 += dp.coeffs1[i] * domainMin[pos]
                minE1 -= dp.rhs1
                maxE1 -= dp.rhs1
                for i, pos in dp.positions2:
                    if dp.coeffs2[i] > 0:
                        minE2 += dp.coeffs2[i] * domainMin[pos]
                        maxE2 += dp.coeffs2[i] * domainMax[pos]
                    else:
                        minE2 += dp.coeffs2[i] * domainMax[pos]
                        maxE2 += dp.coeffs2[i] * domainMin[pos]
                minE2 -= dp.rhs2
                maxE2 -= dp.rhs2

                # If max of expression <= 0, disjunct is always satisfiable — skip
                if maxE1 <= 0 or maxE2 <= 0:
                    continue

                if minE1 > 0:
                    # Disjunct 1 cannot be satisfied → force disjunct 2: coeffs2 · vars <= rhs2
                    tightenFromLe(domainMin, domainMax, dp.coeffs2, dp.positions2, dp.rhs2)
                elif minE2 > 0:
                    # Disjunct 2 cannot be satisfied → force disjunct 1: coeffs1 · vars <= rhs1
                    tightenFromLe(domainMin, domainMax, dp.coeffs1, dp.positions1, dp.rhs1)

            # Apply tightened bounds to PackedSets (only positions in bounds constraints)
            # Skip skipped positions: their PackedSets are 1-element placeholders, not real domains
            for pos in boundsPositions.items:
                if pos in skippedPositions: continue
                for v in toSeq(currentDomain[pos].items):
                    if v < domainMin[pos] or v > domainMax[pos]:
                        currentDomain[pos].excl(v)
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

                elif elemState.evalMethod == ExpressionBased and elemState.isConstantArrayEB:
                    # Expression-based with constant array: constantArrayEB[indexExpr] == valueExpr
                    let idxExprPositions = toSeq(elemState.indexExpression.positions.items)
                    let valExprPositions = toSeq(elemState.valueExpression.positions.items)
                    let arrSize = elemState.getArraySize()

                    # Check no positions are skipped
                    var anySkipped = false
                    for p in idxExprPositions:
                        if p in skippedPositions: anySkipped = true; break
                    if not anySkipped:
                        for p in valExprPositions:
                            if p in skippedPositions: anySkipped = true; break

                    if not anySkipped and idxExprPositions.len == 1 and valExprPositions.len == 1:
                        let idxPos = idxExprPositions[0]
                        let valPos = valExprPositions[0]

                        if idxPos != valPos:
                            var tempAssign = initTable[int, T]()

                            # Precompute reachable value expression results for backward pruning
                            var reachableExprValues: PackedSet[T]
                            for w in currentDomain[valPos].items:
                                tempAssign[valPos] = w
                                reachableExprValues.incl(elemState.valueExpression.evaluate(tempAssign))

                            # Backward: prune index domain
                            # Remove v if constantArrayEB[indexExpr(v)] not achievable by any w in domain(valPos)
                            for v in toSeq(currentDomain[idxPos].items):
                                tempAssign[idxPos] = v
                                let idx = elemState.indexExpression.evaluate(tempAssign)
                                if idx >= 0 and idx < arrSize:
                                    if elemState.constantArrayEB[idx] notin reachableExprValues:
                                        currentDomain[idxPos].excl(v)
                                        outerChanged = true
                                else:
                                    # Out of bounds — always violated
                                    currentDomain[idxPos].excl(v)
                                    outerChanged = true

                            # Forward: prune value domain
                            # Compute set of array values reachable from remaining index domain
                            var reachableArrayValues: PackedSet[T]
                            for v in currentDomain[idxPos].items:
                                tempAssign[idxPos] = v
                                let idx = elemState.indexExpression.evaluate(tempAssign)
                                if idx >= 0 and idx < arrSize:
                                    reachableArrayValues.incl(elemState.constantArrayEB[idx])
                            # Remove w if valueExpr(w) not in reachable set
                            for w in toSeq(currentDomain[valPos].items):
                                tempAssign[valPos] = w
                                let exprVal = elemState.valueExpression.evaluate(tempAssign)
                                if exprVal notin reachableArrayValues:
                                    currentDomain[valPos].excl(w)
                                    outerChanged = true

                    elif not anySkipped and idxExprPositions.len >= 1:
                        # Multi-position index expression with constant array.
                        # Enumerate Cartesian product of index position domains to find
                        # reachable array values. Guard with product size threshold.
                        let allIdxPositions = idxExprPositions
                        let allValPositions = valExprPositions

                        # Compute product sizes and check threshold
                        const MaxProduct = 100_000
                        var idxProduct = 1
                        var idxOverflow = false
                        for p in allIdxPositions:
                            let sz = currentDomain[p].len
                            if sz == 0:
                                idxProduct = 0
                                break
                            if idxProduct > MaxProduct div sz:
                                idxOverflow = true
                                break
                            idxProduct *= sz

                        var valProduct = 1
                        var valOverflow = false
                        for p in allValPositions:
                            let sz = currentDomain[p].len
                            if sz == 0:
                                valProduct = 0
                                break
                            if valProduct > MaxProduct div sz:
                                valOverflow = true
                                break
                            valProduct *= sz

                        if not idxOverflow and not valOverflow and idxProduct > 0 and valProduct > 0:
                            var tempAssign = initTable[int, T]()

                            # Forward pass: enumerate all index-expression combinations,
                            # collect reachable array values
                            var reachableArrayValues: PackedSet[T]

                            proc enumerateIdx(depth: int) =
                                if depth == allIdxPositions.len:
                                    let idx = elemState.indexExpression.evaluate(tempAssign)
                                    if idx >= 0 and idx < arrSize:
                                        reachableArrayValues.incl(elemState.constantArrayEB[idx])
                                    return
                                let pos = allIdxPositions[depth]
                                for v in currentDomain[pos].items:
                                    tempAssign[pos] = v
                                    enumerateIdx(depth + 1)

                            enumerateIdx(0)

                            # Compute reachable value-expression results
                            var reachableExprValues: PackedSet[T]

                            proc enumerateVal(depth: int) =
                                if depth == allValPositions.len:
                                    reachableExprValues.incl(elemState.valueExpression.evaluate(tempAssign))
                                    return
                                let pos = allValPositions[depth]
                                for v in currentDomain[pos].items:
                                    tempAssign[pos] = v
                                    enumerateVal(depth + 1)

                            enumerateVal(0)

                            # Value pruning: remove value-expression results not reachable from index side
                            # For each value position, check if removing a value eliminates all
                            # value-expression results that are in reachableArrayValues
                            if allValPositions.len == 1:
                                let valPos = allValPositions[0]
                                for w in toSeq(currentDomain[valPos].items):
                                    tempAssign[valPos] = w
                                    let exprVal = elemState.valueExpression.evaluate(tempAssign)
                                    if exprVal notin reachableArrayValues:
                                        currentDomain[valPos].excl(w)
                                        outerChanged = true

                            # Backward pass: prune each index position
                            for ki in 0..<allIdxPositions.len:
                                let pk = allIdxPositions[ki]
                                # For each value in domain(pk), check if some assignment
                                # to other index positions produces a valid index whose
                                # array value is in reachableExprValues
                                for vk in toSeq(currentDomain[pk].items):
                                    tempAssign[pk] = vk
                                    var reachable = false

                                    proc enumerateOther(depth: int) =
                                        if reachable:
                                            return
                                        if depth == allIdxPositions.len:
                                            let idx = elemState.indexExpression.evaluate(tempAssign)
                                            if idx >= 0 and idx < arrSize:
                                                if elemState.constantArrayEB[idx] in reachableExprValues:
                                                    reachable = true
                                            return
                                        if depth == ki:
                                            enumerateOther(depth + 1)
                                            return
                                        let pos = allIdxPositions[depth]
                                        for v in currentDomain[pos].items:
                                            if reachable: return
                                            tempAssign[pos] = v
                                            enumerateOther(depth + 1)

                                    enumerateOther(0)
                                    if not reachable:
                                        currentDomain[pk].excl(vk)
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

        # Phase 6b-elem: Variable-array element backward propagation
        # For each position that appears as a variable array element in element constraints,
        # restrict its domain to the union of value-position domains from constraints
        # where the index is FORCED to select this position (all reachable index values
        # map to this position). If some index values map elsewhere, the solver can
        # avoid selecting this position, so the constraint doesn't constrain it.
        var elemBackPruned = 0
        for pos, constraintIndices in elemArrayParticipation.pairs:
            if currentDomain[pos].len <= 1: continue
            if pos in skippedPositions: continue
            var allowedValues = initPackedSet[T]()
            for ci in constraintIndices:
                let cons = carray.constraints[ci]
                let es = cons.elementState
                let valPos = es.valuePosition
                let idxPos = es.indexPosition
                let arrSize = es.getArraySize()
                # Check if ALL reachable index values map to this position
                var allMapToPos = true
                var anyMapsToPos = false
                for i in currentDomain[idxPos].items:
                    if i >= 0 and i < arrSize:
                        let elem = es.arrayElements[i]
                        if not elem.isConstant and elem.variablePosition == pos:
                            anyMapsToPos = true
                        else:
                            allMapToPos = false
                    else:
                        allMapToPos = false
                if allMapToPos and anyMapsToPos:
                    allowedValues = allowedValues + currentDomain[valPos]
            if allowedValues.len > 0:
                for v in toSeq(currentDomain[pos].items):
                    if v notin allowedValues:
                        currentDomain[pos].excl(v)
                        outerChanged = true
                        elemBackPruned += 1
        if elemBackPruned > 0:
            stderr.writeLine(&"[DomRed] Element backward propagation: {elemBackPruned} values removed in {outerIter+1} iterations")

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

        # Phase CB: Channel Binding arc consistency
        # For each channel binding with all-constant array elements, propagate domain
        # restrictions bidirectionally between key positions and channel position.
        var cbProcessed, cbPruned = 0

        # Check if any participant position domain changed since last Phase CB
        var cbHasChanges = (outerIter == 0)
        if not cbHasChanges:
            for pos in cbParticipantPositions.items:
                let curSize = if pos in skippedPositions: -1
                              else: currentDomain[pos].len
                if curSize != cbDomSnapshot[pos]:
                    cbHasChanges = true
                    break

        if cbHasChanges:
         for cbInfo in cbConstBindings:
            let binding = carray.channelBindings[cbInfo.bi]
            let chPos = cbInfo.chPos
            let arrElems = binding.arrayElements
            let arrLen = arrElems.len
            let idxPositions = cbInfo.idxPositions

            let chSkipped = chPos in skippedPositions
            inc cbProcessed

            if idxPositions.len == 1:
                # Single-position index: ch = lookup[keyPos - offset]
                let keyPos = idxPositions[0]
                let keySkipped = keyPos in skippedPositions
                var tempAssign = initTable[int, T]()

                if not chSkipped and not keySkipped:
                    # Forward: domain(ch) ∩= {lookup[eval(v)] : v ∈ domain(keyPos), eval(v) ∈ bounds}
                    if currentDomain[keyPos].len == 0 or currentDomain[chPos].len == 0:
                        continue
                    var reachableValues = initPackedSet[T]()
                    for v in currentDomain[keyPos].items:
                        tempAssign[keyPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx >= 0 and idx < arrLen:
                            reachableValues.incl(arrElems[idx].constantValue)
                    let newChDom = currentDomain[chPos] * reachableValues
                    if newChDom.len < currentDomain[chPos].len:
                        currentDomain[chPos] = newChDom
                        outerChanged = true

                    # Backward: domain(keyPos) ∩= {v : eval(v) ∈ bounds AND lookup[eval(v)] ∈ domain(ch)}
                    for v in toSeq(currentDomain[keyPos].items):
                        tempAssign[keyPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx < 0 or idx >= arrLen:
                            currentDomain[keyPos].excl(v)
                            outerChanged = true
                        elif arrElems[idx].constantValue notin currentDomain[chPos]:
                            currentDomain[keyPos].excl(v)
                            outerChanged = true

                elif chSkipped and not keySkipped:
                    # Channel position skipped: use domainMin/domainMax bounds for feasibility
                    if currentDomain[keyPos].len == 0:
                        continue
                    for v in toSeq(currentDomain[keyPos].items):
                        tempAssign[keyPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx < 0 or idx >= arrLen:
                            currentDomain[keyPos].excl(v)
                            outerChanged = true
                        else:
                            let val = arrElems[idx].constantValue
                            if val < domainMin[chPos] or val > domainMax[chPos]:
                                currentDomain[keyPos].excl(v)
                                outerChanged = true

                elif not chSkipped and keySkipped:
                    # Key position skipped: use original domain with min/max bounds
                    var reachableValues = initPackedSet[T]()
                    for v in carray.domain[keyPos]:
                        if v < domainMin[keyPos] or v > domainMax[keyPos]:
                            continue
                        tempAssign[keyPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx >= 0 and idx < arrLen:
                            reachableValues.incl(arrElems[idx].constantValue)
                    if reachableValues.len > 0:
                        let newChDom = currentDomain[chPos] * reachableValues
                        if newChDom.len < currentDomain[chPos].len:
                            currentDomain[chPos] = newChDom
                            outerChanged = true

            elif idxPositions.len == 2:
                # Two-position index: ch = lookup[(p0-a)*range + (p1-b)]
                let p0 = idxPositions[0]
                let p1 = idxPositions[1]
                let p0Skipped = p0 in skippedPositions
                let p1Skipped = p1 in skippedPositions

                # Determine domain sizes for guard
                let p0Size = if p0Skipped:
                    (domainMax[p0] - domainMin[p0] + 1)
                else:
                    T(currentDomain[p0].len)
                let p1Size = if p1Skipped:
                    (domainMax[p1] - domainMin[p1] + 1)
                else:
                    T(currentDomain[p1].len)

                if p0Size * p1Size > 500_000:
                    continue

                if not p0Skipped and not p1Skipped and not chSkipped:
                    # Skip if any participating domain is already empty (infeasibility cascading)
                    if currentDomain[p0].len == 0 or currentDomain[p1].len == 0 or currentDomain[chPos].len == 0:
                        continue

                    var tempAssign = initTable[int, T]()
                    let oldP0 = currentDomain[p0].len
                    let oldP1 = currentDomain[p1].len
                    let oldCh = currentDomain[chPos].len

                    # Forward: domain(ch) ∩= {lookup[eval(v0,v1)] : (v0,v1) ∈ dom(p0)×dom(p1)}
                    var reachableValues = initPackedSet[T]()
                    for v0 in currentDomain[p0].items:
                        tempAssign[p0] = v0
                        for v1 in currentDomain[p1].items:
                            tempAssign[p1] = v1
                            let idx = binding.indexExpression.evaluate(tempAssign)
                            if idx >= 0 and idx < arrLen:
                                reachableValues.incl(arrElems[idx].constantValue)
                    let newChDom = currentDomain[chPos] * reachableValues
                    if newChDom.len < currentDomain[chPos].len:
                        currentDomain[chPos] = newChDom
                        outerChanged = true

                    # Backward for p0: keep v0 if ∃ v1 s.t. lookup[eval(v0,v1)] ∈ domain(ch)
                    for v0 in toSeq(currentDomain[p0].items):
                        tempAssign[p0] = v0
                        var hasSupport = false
                        for v1 in currentDomain[p1].items:
                            tempAssign[p1] = v1
                            let idx = binding.indexExpression.evaluate(tempAssign)
                            if idx >= 0 and idx < arrLen:
                                if arrElems[idx].constantValue in currentDomain[chPos]:
                                    hasSupport = true
                                    break
                        if not hasSupport:
                            currentDomain[p0].excl(v0)
                            outerChanged = true

                    # Backward for p1: symmetric
                    for v1 in toSeq(currentDomain[p1].items):
                        tempAssign[p1] = v1
                        var hasSupport = false
                        for v0 in currentDomain[p0].items:
                            tempAssign[p0] = v0
                            let idx = binding.indexExpression.evaluate(tempAssign)
                            if idx >= 0 and idx < arrLen:
                                if arrElems[idx].constantValue in currentDomain[chPos]:
                                    hasSupport = true
                                    break
                        if not hasSupport:
                            currentDomain[p1].excl(v1)
                            outerChanged = true

                    let prunedP0 = oldP0 - currentDomain[p0].len
                    let prunedP1 = oldP1 - currentDomain[p1].len
                    let prunedCh = oldCh - currentDomain[chPos].len
                    cbPruned += prunedP0 + prunedP1 + prunedCh

                elif chSkipped and not p0Skipped and not p1Skipped:
                    # Skip if any participating domain is already empty
                    if currentDomain[p0].len == 0 or currentDomain[p1].len == 0:
                        continue

                    # Channel skipped: use domainMin/domainMax for feasibility
                    var tempAssign = initTable[int, T]()

                    for v0 in toSeq(currentDomain[p0].items):
                        tempAssign[p0] = v0
                        var hasSupport = false
                        for v1 in currentDomain[p1].items:
                            tempAssign[p1] = v1
                            let idx = binding.indexExpression.evaluate(tempAssign)
                            if idx >= 0 and idx < arrLen:
                                let val = arrElems[idx].constantValue
                                if val >= domainMin[chPos] and val <= domainMax[chPos]:
                                    hasSupport = true
                                    break
                        if not hasSupport:
                            currentDomain[p0].excl(v0)
                            outerChanged = true

                    for v1 in toSeq(currentDomain[p1].items):
                        tempAssign[p1] = v1
                        var hasSupport = false
                        for v0 in currentDomain[p0].items:
                            tempAssign[p0] = v0
                            let idx = binding.indexExpression.evaluate(tempAssign)
                            if idx >= 0 and idx < arrLen:
                                let val = arrElems[idx].constantValue
                                if val >= domainMin[chPos] and val <= domainMax[chPos]:
                                    hasSupport = true
                                    break
                        if not hasSupport:
                            currentDomain[p1].excl(v1)
                            outerChanged = true

            elif idxPositions.len >= 3:
                # N-position index (3-6 positions): general enumeration with product guard
                const MAX_CB_MULTI_PRODUCT = 500_000

                # Compute product of domain sizes and check guard
                var anySkipped = false
                var product = 1
                var posDomains: seq[seq[T]]
                for p in idxPositions:
                    if p in skippedPositions:
                        anySkipped = true
                        break
                    let vals = toSeq(currentDomain[p].items)
                    if vals.len == 0:
                        product = 0
                        break
                    product *= vals.len
                    if product > MAX_CB_MULTI_PRODUCT:
                        break
                    posDomains.add(vals)

                if anySkipped or product == 0 or product > MAX_CB_MULTI_PRODUCT:
                    discard  # skip this binding
                elif chPos in skippedPositions or currentDomain[chPos].len == 0:
                    discard
                else:
                    var tempAssign = initTable[int, T]()
                    let nPos = idxPositions.len

                    # Forward: compute reachable channel values
                    var reachableValues = initPackedSet[T]()
                    var indices = newSeq[int](nPos)
                    for combo in 0..<product:
                        for i in 0..<nPos:
                            tempAssign[idxPositions[i]] = posDomains[i][indices[i]]
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx >= 0 and idx < arrLen:
                            reachableValues.incl(arrElems[idx].constantValue)
                        # Advance odometer
                        var carry = nPos - 1
                        while carry >= 0:
                            indices[carry] += 1
                            if indices[carry] >= posDomains[carry].len:
                                indices[carry] = 0
                                carry -= 1
                            else:
                                break

                    let newChDom = currentDomain[chPos] * reachableValues
                    if newChDom.len < currentDomain[chPos].len:
                        cbPruned += currentDomain[chPos].len - newChDom.len
                        currentDomain[chPos] = newChDom
                        outerChanged = true

                    # Backward: for each key position, check if value has support
                    for ki in 0..<nPos:
                        let kPos = idxPositions[ki]
                        # Precompute other positions and domains (invariant per ki)
                        var otherDomains: seq[seq[T]]
                        var otherPositions: seq[int]
                        var otherProduct = 1
                        for oi in 0..<nPos:
                            if oi == ki: continue
                            otherPositions.add(idxPositions[oi])
                            otherDomains.add(posDomains[oi])
                            otherProduct *= posDomains[oi].len
                        var oIndices = newSeq[int](otherPositions.len)
                        for v in toSeq(currentDomain[kPos].items):
                            tempAssign[kPos] = v
                            var hasSupport = false
                            # Reset odometer indices
                            for i in 0..<oIndices.len: oIndices[i] = 0
                            for combo in 0..<otherProduct:
                                for i in 0..<otherPositions.len:
                                    tempAssign[otherPositions[i]] = otherDomains[i][oIndices[i]]
                                let idx = binding.indexExpression.evaluate(tempAssign)
                                if idx >= 0 and idx < arrLen:
                                    if arrElems[idx].constantValue in currentDomain[chPos]:
                                        hasSupport = true
                                        break
                                var carry = otherPositions.len - 1
                                while carry >= 0:
                                    oIndices[carry] += 1
                                    if oIndices[carry] >= otherDomains[carry].len:
                                        oIndices[carry] = 0
                                        carry -= 1
                                    else:
                                        break
                            if not hasSupport:
                                currentDomain[kPos].excl(v)
                                cbPruned += 1
                                outerChanged = true

         # end if cbHasChanges
         # Update snapshot for next iteration's dirty detection
         for pos in cbParticipantPositions.items:
            cbDomSnapshot[pos] = if pos in skippedPositions: -1
                                 else: currentDomain[pos].len

        if cbPruned > 0:
            stderr.writeLine(&"[DomRed] Channel AC: {cbPruned} values pruned ({cbProcessed} bindings)")

        # Phase CB-var: Variable-array channel binding backward propagation
        # For each position that appears as a variable array element in channel bindings,
        # restrict its domain to the union of channel-position domains from bindings
        # where the index is FORCED to select this position (all reachable index values
        # map to this position). If some index values map elsewhere, the solver can
        # avoid selecting this position, so the binding doesn't constrain it.
        var cbVarPruned = 0
        var tempAssign = initTable[int, T]()
        for pos, bindingIndices in channelArrayParticipation.pairs:
            if currentDomain[pos].len <= 1: continue
            if pos in skippedPositions: continue
            var allowedValues = initPackedSet[T]()
            for bi in bindingIndices:
                let binding = carray.channelBindings[bi]
                let chPos = binding.channelPosition
                let arrElems = binding.arrayElements
                let arrLen = arrElems.len
                let idxPositions = toSeq(binding.indexExpression.positions.items)
                # Check if ALL reachable index values map to this position
                # (meaning the binding is forced to select this position)
                if idxPositions.len == 1:
                    let keyPos = idxPositions[0]
                    var allMapToPos = true
                    var anyMapsToPos = false
                    for v in currentDomain[keyPos].items:
                        tempAssign[keyPos] = v
                        let idx = binding.indexExpression.evaluate(tempAssign)
                        if idx >= 0 and idx < arrLen:
                            let elem = arrElems[idx]
                            if not elem.isConstant and elem.variablePosition == pos:
                                anyMapsToPos = true
                            else:
                                allMapToPos = false
                        else:
                            allMapToPos = false  # out of bounds doesn't map to pos
                    if allMapToPos and anyMapsToPos:
                        # All index values forced to select pos — add channel domain
                        if chPos in skippedPositions:
                            for bv in domainMin[chPos]..domainMax[chPos]:
                                allowedValues.incl(bv)
                        else:
                            allowedValues = allowedValues + currentDomain[chPos]
            if allowedValues.len > 0:
                for v in toSeq(currentDomain[pos].items):
                    if v notin allowedValues:
                        currentDomain[pos].excl(v)
                        outerChanged = true
                        cbVarPruned += 1
        if cbVarPruned > 0:
            stderr.writeLine(&"[DomRed] Channel var-array backward: {cbVarPruned} values removed in {outerIter+1} iterations")

        # Phase CB-idx: Multi-constraint index filtering for shared-index variable-array bindings
        # For each index position with 2+ constraints (channel bindings + element constraints),
        # check each candidate index value against ALL constraints. Remove values that fail any.
        var cbIdxPruned = 0
        # Collect all index positions that have at least 2 constraints total
        var cbIdxPositions: PackedSet[int]
        for idxPos in idxToVarArrayBindings.keys:
            let nBindings = idxToVarArrayBindings[idxPos].len
            let nElems = if idxPos in idxToElementConstraints: idxToElementConstraints[idxPos].len else: 0
            if nBindings + nElems >= 2:
                cbIdxPositions.incl(idxPos)
        for idxPos in idxToElementConstraints.keys:
            if idxPos notin cbIdxPositions:
                let nBindings = if idxPos in idxToVarArrayBindings: idxToVarArrayBindings[idxPos].len else: 0
                let nElems = idxToElementConstraints[idxPos].len
                if nBindings + nElems >= 2:
                    cbIdxPositions.incl(idxPos)

        for idxPos in cbIdxPositions.items:
            if currentDomain[idxPos].len <= 1: continue
            if idxPos in skippedPositions: continue
            let cbBindings = if idxPos in idxToVarArrayBindings: idxToVarArrayBindings[idxPos] else: @[]
            let elemCons = if idxPos in idxToElementConstraints: idxToElementConstraints[idxPos] else: @[]
            var tempAssign = initTable[int, T]()
            for v in toSeq(currentDomain[idxPos].items):
                tempAssign[idxPos] = v
                var supported = true
                # Check channel bindings (e.g., distance, pad_xy)
                for bi in cbBindings:
                    let binding = carray.channelBindings[bi]
                    let idx = binding.indexExpression.evaluate(tempAssign)
                    let arrLen = binding.arrayElements.len
                    if idx < 0 or idx >= arrLen:
                        supported = false
                        break
                    let elem = binding.arrayElements[idx]
                    let chPos = binding.channelPosition
                    if elem.isConstant:
                        if chPos in skippedPositions:
                            if elem.constantValue < domainMin[chPos] or elem.constantValue > domainMax[chPos]:
                                supported = false
                                break
                        else:
                            if elem.constantValue notin currentDomain[chPos]:
                                supported = false
                                break
                    else:
                        let elemPos = elem.variablePosition
                        if elemPos in skippedPositions and chPos in skippedPositions:
                            # Both skipped: use bounds overlap check
                            if domainMin[elemPos] > domainMax[chPos] or domainMax[elemPos] < domainMin[chPos]:
                                supported = false
                                break
                        elif elemPos in skippedPositions:
                            # elemPos skipped, chPos has domain: check bounds vs domain overlap
                            let chDom = currentDomain[chPos]
                            if chDom.len > 0:
                                var chMin = T.high
                                var chMax = T.low
                                for cv in chDom.items:
                                    if cv < chMin: chMin = cv
                                    if cv > chMax: chMax = cv
                                if domainMin[elemPos] > chMax or domainMax[elemPos] < chMin:
                                    supported = false
                                    break
                        elif chPos in skippedPositions:
                            # chPos skipped, elemPos has domain: check domain vs bounds overlap
                            let epDom = currentDomain[elemPos]
                            if epDom.len > 0:
                                var epMin = T.high
                                var epMax = T.low
                                for ev in epDom.items:
                                    if ev < epMin: epMin = ev
                                    if ev > epMax: epMax = ev
                                if epMin > domainMax[chPos] or epMax < domainMin[chPos]:
                                    supported = false
                                    break
                        else:
                            # Both have domains: intersection check
                            let epDom = currentDomain[elemPos]
                            let chDom = currentDomain[chPos]
                            if epDom.len > 0 and chDom.len > 0:
                                if (epDom * chDom).len == 0:
                                    supported = false
                                    break
                # Check element constraints (e.g., connection, pad_y)
                if supported:
                    for ci in elemCons:
                        let es = carray.constraints[ci].elementState
                        let arrSize = es.getArraySize()
                        # Element constraint: arr[idxPos] = valuePos
                        # v is already the index value (0-based in the constraint)
                        if v < 0 or v >= arrSize:
                            supported = false
                            break
                        let elem = es.arrayElements[v]
                        let valPos = es.valuePosition
                        if elem.isConstant:
                            if valPos in skippedPositions:
                                if elem.constantValue < domainMin[valPos] or elem.constantValue > domainMax[valPos]:
                                    supported = false
                                    break
                            else:
                                if elem.constantValue notin currentDomain[valPos]:
                                    supported = false
                                    break
                        else:
                            let elemPos = elem.variablePosition
                            if elemPos in skippedPositions and valPos in skippedPositions:
                                # Both skipped: use bounds overlap check
                                if domainMin[elemPos] > domainMax[valPos] or domainMax[elemPos] < domainMin[valPos]:
                                    supported = false
                                    break
                            elif elemPos in skippedPositions:
                                # elemPos skipped, valPos has domain: check bounds vs domain overlap
                                let valDom = currentDomain[valPos]
                                if valDom.len > 0:
                                    var valMin = T.high
                                    var valMax = T.low
                                    for vv in valDom.items:
                                        if vv < valMin: valMin = vv
                                        if vv > valMax: valMax = vv
                                    if domainMin[elemPos] > valMax or domainMax[elemPos] < valMin:
                                        supported = false
                                        break
                            elif valPos in skippedPositions:
                                # valPos skipped, elemPos has domain: check domain vs bounds overlap
                                let epDom = currentDomain[elemPos]
                                if epDom.len > 0:
                                    var epMin = T.high
                                    var epMax = T.low
                                    for ev in epDom.items:
                                        if ev < epMin: epMin = ev
                                        if ev > epMax: epMax = ev
                                    if epMin > domainMax[valPos] or epMax < domainMin[valPos]:
                                        supported = false
                                        break
                            else:
                                # Both have domains: intersection check
                                if (currentDomain[elemPos] * currentDomain[valPos]).len == 0:
                                    supported = false
                                    break
                if not supported:
                    currentDomain[idxPos].excl(v)
                    outerChanged = true
                    cbIdxPruned += 1
        if cbIdxPruned > 0:
            stderr.writeLine(&"[DomRed] Channel idx intersection: {cbIdxPruned} values removed in {outerIter+1} iterations")

        # Phase 7: Table constraint arc consistency
        # For each TableIn constraint, remove domain values that have no support
        # (no tuple where all other columns' values are in their domains).
        # Tables may be partial (from implications): values not appearing in any
        # tuple are unconstrained by this table and are skipped. Only values that
        # DO appear but have no supported tuple are pruned.
        for cons in carray.constraints:
            if cons.stateType != TableConstraintType:
                continue
            let tbl = cons.tableConstraintState
            if tbl.mode != TableIn:
                continue
            # Only apply AC to large tables (e.g., transition tables with full graph
            # adjacency). Small tables from implications may be partial — they encode
            # one-directional constraints where not all valid combinations are listed.
            if tbl.tuples.len < MinTransitionTableSize and not tbl.gacSafe:
                continue
            let nCols = tbl.sortedPositions.len
            for col in 0..<nCols:
                let pos = tbl.sortedPositions[col]
                # Skip pruning channel positions — their values are determined by
                # channel propagation, not search. Also skip positions that were
                # excluded from currentDomain (large-domain channels).
                if pos in skippedPositions:
                    continue
                for v in toSeq(currentDomain[pos].items):
                    if v notin tbl.tuplesByColumnValue[col]:
                        continue  # Not mentioned in table — unconstrained
                    # Check if any tuple with this value has support in all other columns
                    var hasSupport = false
                    for t in tbl.tuplesByColumnValue[col][v]:
                        var supported = true
                        for otherCol in 0..<nCols:
                            if otherCol == col:
                                continue
                            let otherPos = tbl.sortedPositions[otherCol]
                            # Skipped positions (large-domain channels) have empty
                            # currentDomain — treat them as having universal support.
                            if otherPos in skippedPositions:
                                continue
                            if tbl.tuples[t][otherCol] notin currentDomain[otherPos]:
                                supported = false
                                break
                        if supported:
                            hasSupport = true
                            break
                    if not hasSupport:
                        currentDomain[pos].excl(v)
                        outerChanged = true
        if not outerChanged:
            break

    # Convert PackedSets to output sequences
    for pos in carray.allPositions():
        if pos in skippedPositions:
            continue  # already set above
        reduced[pos] = toSeq(currentDomain[pos])

    return reduced

################################################################################
# Fixed-position constraint removal
################################################################################

proc removeFixedConstraints*[T](carray: var ConstrainedArray[T]) =
    ## Identifies singleton-domain positions and removes constraints where all
    ## positions are fixed (singleton domain). Constraints with any channel
    ## position are kept — channel values depend on search variables and
    ## aren't guaranteed satisfied by domain reduction alone.

    # 1. Identify singleton positions from reducedDomain
    for pos in carray.allPositions():
        if carray.reducedDomain[pos].len == 1 and pos notin carray.channelPositions:
            carray.fixedPositions.incl(pos)

    if carray.fixedPositions.len == 0:
        return

    # 2. Remove constraints where ALL positions are fixed (singleton domain).
    #    Constraints with any channel position are kept — channel values depend
    #    on search variables and aren't guaranteed satisfied by domain reduction.
    var newConstraints: seq[StatefulConstraint[T]]
    var removedCount = 0
    for c in carray.constraints:
        var allFixed = true
        for pos in c.positions.items:
            if pos notin carray.fixedPositions:
                allFixed = false
                break
        if allFixed and c.positions.card > 0:
            inc removedCount
        else:
            newConstraints.add(c)
    if removedCount > 0:
        carray.constraints = newConstraints

################################################################################
# Deep copy for ConstrainedArray
################################################################################

proc deepCopy*[T](arr: ConstrainedArray[T]): ConstrainedArray[T] =
    ## Creates a deep copy of a ConstrainedArray for thread-safe parallel processing
    result.len = arr.len

    if arr.sharedDomainPtr != nil:
        # Parallel search state: domain not needed (reduceDomain already ran),
        # reducedDomain shared via pointer. Saves ~25 GB for large-domain models.
        result.domain = @[]
        result.reducedDomain = @[]
        result.sharedDomainPtr = arr.sharedDomainPtr
    else:
        # General deepCopy: preserve domain for future reduceDomain calls
        result.domain = newSeq[seq[T]](arr.domain.len)
        for i, innerSeq in arr.domain:
            if i in arr.channelPositions and innerSeq.len > 1000:
                result.domain[i] = @[innerSeq[0], innerSeq[^1]]
            else:
                result.domain[i] = innerSeq
        if arr.reducedDomain.len > 0:
            result.reducedDomain = newSeq[seq[T]](arr.reducedDomain.len)
            for i, innerSeq in arr.reducedDomain:
                result.reducedDomain[i] = innerSeq
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
            arrayElements: binding.arrayElements,
            hasOffset: binding.hasOffset
        )
    result.channelsAtPosition = arr.channelsAtPosition

    # Deep copy min/max channel bindings - AlgebraicExpression refs need deep copy
    result.minMaxChannelBindings = newSeq[MinMaxChannelBinding[T]](arr.minMaxChannelBindings.len)
    for i, binding in arr.minMaxChannelBindings:
        var exprs = newSeq[AlgebraicExpression[T]](binding.inputExprs.len)
        for j, expr in binding.inputExprs:
            exprs[j] = expr.deepCopy()
        result.minMaxChannelBindings[i] = MinMaxChannelBinding[T](
            channelPosition: binding.channelPosition,
            isMin: binding.isMin,
            inputExprs: exprs,
            inputPositions: binding.inputPositions
        )
    result.minMaxChannelsAtPosition = arr.minMaxChannelsAtPosition

    # Count-equals channel bindings are all value types — shallow copy is fine
    result.countEqChannelBindings = arr.countEqChannelBindings
    result.countEqChannelsAtPosition = arr.countEqChannelsAtPosition

    # Conditional count-equals channel bindings are all value types — shallow copy is fine
    result.conditionalCountEqChannelBindings = arr.conditionalCountEqChannelBindings
    result.conditionalCountEqChannelsAtPosition = arr.conditionalCountEqChannelsAtPosition

    # Deep copy argmax channel bindings — AlgebraicExpression refs need deep copy
    result.argmaxChannelBindings = newSeq[ArgmaxChannelBinding[T]](arr.argmaxChannelBindings.len)
    for i, binding in arr.argmaxChannelBindings:
        var exprs = newSeq[AlgebraicExpression[T]](binding.inputExprs.len)
        for j, expr in binding.inputExprs:
            exprs[j] = expr.deepCopy()
        result.argmaxChannelBindings[i] = ArgmaxChannelBinding[T](
            channelPosition: binding.channelPosition,
            inputExprs: exprs,
            inputPositions: binding.inputPositions,
            valueOffset: binding.valueOffset
        )
    result.argmaxChannelsAtPosition = arr.argmaxChannelsAtPosition

    # Inverse groups are all value types — shallow copy is fine
    result.inverseGroups = arr.inverseGroups

    # Inverse channel groups are all value types — shallow copy is fine
    result.inverseChannelGroups = arr.inverseChannelGroups
    result.inverseChannelsAtPosition = arr.inverseChannelsAtPosition
    result.fixedPositions = arr.fixedPositions
    result.elementInverseDetected = arr.elementInverseDetected

    # Dormancy bindings are all value types — shallow copy is fine
    result.dormancyBindings = arr.dormancyBindings
    result.dormancyAtSelector = arr.dormancyAtSelector

    # Partition groups are all value types — shallow copy is fine
    result.partitionGroups = arr.partitionGroups

