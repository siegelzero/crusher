import std/[algorithm, packedsets, sequtils, strformat, strutils, tables]

import constraints/stateful
import constraints/algebraic  
import constraints/allDifferent
import constraints/common
import constraints/constraintNode
import constraints/minConstraint
import constraints/globalCardinality
import constraints/regularDomainFiltering
import expressions

################################################################################
# Type definitions
################################################################################

type
    ConstrainedArray*[T] = object
        len*: int
        constraints*: seq[StatefulConstraint[T]]
        domain*: seq[seq[T]]
        entries*: seq[AlgebraicExpression[T]]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): AlgebraicExpression[T] {.inline.} = arr.entries[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield i

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
                positions=toPackedSet[int](@[pos]),
                node=ExpressionNode[T](kind: RefNode, position: pos),
                linear=true
            )
        )
    return ConstrainedArray[T](
        len: n,
        constraints: newSeq[StatefulConstraint[T]](),
        domain: newSeq[seq[T]](n),
        entries: entries
    )

func extendArray*[T](arr: var ConstrainedArray[T], m: int) =
    # Extends the array by m elements.
    let n = arr.entries.len()
    for pos in n..<(n + m):
        arr.entries.add(
            newAlgebraicExpression[T](
                positions=toPackedSet[int]([pos]),
                node=ExpressionNode[T](kind: RefNode, position: pos),
                linear=true
            )
        )
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
    arr.domain[position] = @domain

func allDifferent*[T](arr: ConstrainedArray[T]): StatefulConstraint[T] {.inline.} =
    allDifferent(toSeq arr.allPositions())

template OrderingArrayRel(relName: untyped) =
    func `relName`*[T](arr: ConstrainedArray[T]): seq[AlgebraicConstraint[T]] {.inline.} =
        var expressions: seq[AlgebraicExpression[T]] = @[]
        for pos in arr.allPositions():
            expressions.add(newAlgebraicExpression[T](
                toPackedSet[int]([pos]),
                ExpressionNode[T](kind: RefNode, position: pos),
                true
            ))
        return `relName`(expressions)

OrderingArrayRel(increasing)
OrderingArrayRel(strictlyIncreasing)
OrderingArrayRel(decreasing)
OrderingArrayRel(strictlyDecreasing)

proc addBaseConstraint*[T](arr: var ConstrainedArray[T], cons: StatefulConstraint[T]) {.inline.} =
    # Adds the constraint to the 
    arr.constraints.add(cons)

################################################################################
# Helper functions for bounds propagation
################################################################################

func divCeil[T](numerator, denominator: T): T {.inline.} =
    ## Integer ceiling division: ⌈numerator / denominator⌉
    let quotient = numerator div denominator
    let remainder = numerator mod denominator
    if remainder == 0:
        return quotient
    elif (numerator > 0) == (denominator > 0):  # Same sign
        return quotient + 1
    else:
        return quotient

func divFloor[T](numerator, denominator: T): T {.inline.} =
    ## Integer floor division: ⌊numerator / denominator⌋
    let quotient = numerator div denominator
    let remainder = numerator mod denominator
    if remainder == 0:
        return quotient
    elif (numerator > 0) == (denominator > 0):  # Same sign
        return quotient
    else:
        return quotient - 1

################################################################################
# ConstrainedArray domain reduction
################################################################################

proc reduceAllDifferentDomains*[T](carray: ConstrainedArray[T], currentDomain: var seq[PackedSet[T]], constraint: StatefulConstraint[T]): bool =
    ## Reduces domains for AllDifferent constraints using arc consistency
    ## Returns true if any domain was reduced
    if constraint.stateType != AllDifferentType:
        return false
    
    var changed = false
    let allDiffState = constraint.allDifferentState
    
    case allDiffState.evalMethod:
        of PositionBased:
            # Handle position-based AllDifferent (simple variables)
            let positions = toSeq(constraint.positions)
            
            # Step 1: Singleton propagation - if any variable has domain size 1, 
            # remove that value from all other variables in the constraint
            for pos in positions:
                if currentDomain[pos].card == 1:
                    let singletonValue = toSeq(currentDomain[pos])[0]
                    for otherPos in positions:
                        if otherPos != pos and singletonValue in currentDomain[otherPos]:
                            currentDomain[otherPos].excl(singletonValue)
                            changed = true
            
            # Step 2: Hall's Marriage Theorem - if k variables have exactly k values
            # between them, those values are reserved for those variables
            # Smart heuristic approach: focus on promising subsets instead of exhaustive search
            
            # First, identify variables with small domains (most likely to form Hall sets)
            var smallDomainPositions: seq[(int, int)] = @[]  # (position, domain_size)
            for pos in positions:
                smallDomainPositions.add((pos, currentDomain[pos].card))
            smallDomainPositions.sort(proc(a, b: (int, int)): int = a[1] - b[1])  # Sort by domain size
            
            # Smart Hall's theorem checking with early termination
            let maxChecks = min(10000, positions.len * positions.len)  # Reasonable computational budget
            var checksPerformed = 0
            var reductionsMade = 0
            
            # Check pairs first (size 2) - most common and efficient
            for i in 0..<min(20, smallDomainPositions.len):
                for j in i+1..<min(20, smallDomainPositions.len):
                    if checksPerformed >= maxChecks: break
                    checksPerformed += 1
                    
                    let pos1 = smallDomainPositions[i][0]
                    let pos2 = smallDomainPositions[j][0]
                    
                    # Compute union of domains
                    var unionValues: PackedSet[T]
                    for value in currentDomain[pos1]:
                        unionValues.incl(value)
                    for value in currentDomain[pos2]:
                        unionValues.incl(value)
                    
                    # Hall condition: exactly 2 values for 2 variables
                    if unionValues.card == 2:
                        # Remove these values from all other positions
                        for value in unionValues:
                            for pos in positions:
                                if pos != pos1 and pos != pos2 and value in currentDomain[pos]:
                                    currentDomain[pos].excl(value)
                                    changed = true
                                    reductionsMade += 1
            
            # Check triples (size 3) only if we're making good progress and have small domains
            if reductionsMade > 0 and positions.len <= 100:
                for i in 0..<min(10, smallDomainPositions.len):
                    for j in i+1..<min(10, smallDomainPositions.len):
                        for k in j+1..<min(10, smallDomainPositions.len):
                            if checksPerformed >= maxChecks: break
                            checksPerformed += 1
                            
                            let pos1 = smallDomainPositions[i][0]
                            let pos2 = smallDomainPositions[j][0]
                            let pos3 = smallDomainPositions[k][0]
                            
                            # Quick pruning: if any domain is too large, skip
                            if currentDomain[pos1].card > 5 or currentDomain[pos2].card > 5 or currentDomain[pos3].card > 5:
                                continue
                            
                            # Compute union of domains
                            var unionValues: PackedSet[T]
                            for value in currentDomain[pos1]:
                                unionValues.incl(value)
                            for value in currentDomain[pos2]:
                                unionValues.incl(value)
                            for value in currentDomain[pos3]:
                                unionValues.incl(value)
                            
                            # Hall condition: exactly 3 values for 3 variables
                            if unionValues.card == 3:
                                # Remove these values from all other positions
                                for value in unionValues:
                                    for pos in positions:
                                        if pos != pos1 and pos != pos2 and pos != pos3 and value in currentDomain[pos]:
                                            currentDomain[pos].excl(value)
                                            changed = true
                                            reductionsMade += 1
        
        of ExpressionBased:
            # Handle expression-based AllDifferent (e.g., x[i] + i, x[i] - i in N-Queens)
            let expressions = allDiffState.expressions
            
            # Step 1: Compute possible expression values for each expression
            var expressionValues: seq[PackedSet[T]] = @[]
            for exp in expressions:
                var possibleValues: PackedSet[T]
                let expPositions = toSeq(exp.positions)
                
                # For simple expressions with single variable, evaluate all possibilities
                if expPositions.len == 1:
                    let pos = expPositions[0]
                    for domainValue in currentDomain[pos]:
                        # Create temporary assignment to evaluate expression
                        var tempAssignment = newSeq[T](carray.len)
                        tempAssignment[pos] = domainValue
                        let expValue = exp.evaluate(tempAssignment)
                        possibleValues.incl(expValue)
                else:
                    # For more complex expressions with multiple variables
                    # This is less common but we handle it for completeness
                    for pos in expPositions:
                        if pos < currentDomain.len:
                            for domainValue in currentDomain[pos]:
                                var tempAssignment = newSeq[T](carray.len)
                                tempAssignment[pos] = domainValue
                                let expValue = exp.evaluate(tempAssignment)
                                possibleValues.incl(expValue)
                
                expressionValues.add(possibleValues)
            
            # Step 2: Apply singleton propagation for expression values
            for i, expValues in expressionValues:
                if expValues.card == 1:
                    let singletonValue = toSeq(expValues)[0]
                    # This expression can only evaluate to one value
                    # Remove this value from all other expressions
                    for j in 0..<expressions.len:
                        if i != j and singletonValue in expressionValues[j]:
                            # Need to remove domain values that would make expression j equal singletonValue
                            let exp = expressions[j]
                            let expPositions = toSeq(exp.positions)
                            
                            if expPositions.len == 1:
                                let pos = expPositions[0]
                                var toRemove: seq[T] = @[]
                                
                                for domainValue in currentDomain[pos]:
                                    var tempAssignment = newSeq[T](carray.len)
                                    tempAssignment[pos] = domainValue
                                    if exp.evaluate(tempAssignment) == singletonValue:
                                        toRemove.add(domainValue)
                                
                                for value in toRemove:
                                    currentDomain[pos].excl(value)
                                    changed = true
            
            # Step 3: Hall's Marriage Theorem for expression values
            # Smart heuristic approach: focus on expressions with small value sets
            
            # Sort expressions by their value set size (smallest first)
            var sortedExpressions: seq[(int, int)] = @[]  # (expr_index, value_count)
            for i, expValues in expressionValues:
                sortedExpressions.add((i, expValues.card))
            sortedExpressions.sort(proc(a, b: (int, int)): int = a[1] - b[1])
            
            # Smart Hall's checking with computational budget
            let maxExpChecks = min(5000, expressions.len * expressions.len)
            var expChecksPerformed = 0
            var expReductionsMade = 0
            
            # Check pairs of expressions (size 2)
            for i in 0..<min(15, sortedExpressions.len):
                for j in i+1..<min(15, sortedExpressions.len):
                    if expChecksPerformed >= maxExpChecks: break
                    expChecksPerformed += 1
                    
                    let expr1Idx = sortedExpressions[i][0]
                    let expr2Idx = sortedExpressions[j][0]
                    
                    # Compute union of expression values
                    var unionExpValues: PackedSet[T]
                    for value in expressionValues[expr1Idx]:
                        unionExpValues.incl(value)
                    for value in expressionValues[expr2Idx]:
                        unionExpValues.incl(value)
                    
                    # Hall condition: exactly 2 values for 2 expressions
                    if unionExpValues.card == 2:
                        # These values are reserved for these expressions
                        for value in unionExpValues:
                            for k in 0..<expressions.len:
                                if k != expr1Idx and k != expr2Idx and value in expressionValues[k]:
                                    # Remove domain values that would make expression k equal this value
                                    let exp = expressions[k]
                                    let expPositions = toSeq(exp.positions)
                                    
                                    if expPositions.len == 1:
                                        let pos = expPositions[0]
                                        var toRemove: seq[T] = @[]
                                        
                                        for domainValue in currentDomain[pos]:
                                            var tempAssignment = newSeq[T](carray.len)
                                            tempAssignment[pos] = domainValue
                                            if exp.evaluate(tempAssignment) == value:
                                                toRemove.add(domainValue)
                                        
                                        for removeValue in toRemove:
                                            currentDomain[pos].excl(removeValue)
                                            changed = true
                                            expReductionsMade += 1
            
            # Check triples (size 3) only if making progress and small problem
            if expReductionsMade > 0 and expressions.len <= 50:
                for i in 0..<min(8, sortedExpressions.len):
                    for j in i+1..<min(8, sortedExpressions.len):
                        for k in j+1..<min(8, sortedExpressions.len):
                            if expChecksPerformed >= maxExpChecks: break
                            expChecksPerformed += 1
                            
                            let expr1Idx = sortedExpressions[i][0]
                            let expr2Idx = sortedExpressions[j][0]
                            let expr3Idx = sortedExpressions[k][0]
                            
                            # Quick pruning: skip if any expression has too many values
                            if expressionValues[expr1Idx].card > 4 or expressionValues[expr2Idx].card > 4 or expressionValues[expr3Idx].card > 4:
                                continue
                            
                            # Compute union of expression values
                            var unionExpValues: PackedSet[T]
                            for value in expressionValues[expr1Idx]:
                                unionExpValues.incl(value)
                            for value in expressionValues[expr2Idx]:
                                unionExpValues.incl(value)
                            for value in expressionValues[expr3Idx]:
                                unionExpValues.incl(value)
                            
                            # Hall condition: exactly 3 values for 3 expressions
                            if unionExpValues.card == 3:
                                # These values are reserved for these expressions
                                for value in unionExpValues:
                                    for l in 0..<expressions.len:
                                        if l != expr1Idx and l != expr2Idx and l != expr3Idx and value in expressionValues[l]:
                                            # Remove domain values that would make expression l equal this value
                                            let exp = expressions[l]
                                            let expPositions = toSeq(exp.positions)
                                            
                                            if expPositions.len == 1:
                                                let pos = expPositions[0]
                                                var toRemove: seq[T] = @[]
                                                
                                                for domainValue in currentDomain[pos]:
                                                    var tempAssignment = newSeq[T](carray.len)
                                                    tempAssignment[pos] = domainValue
                                                    if exp.evaluate(tempAssignment) == value:
                                                        toRemove.add(domainValue)
                                                
                                                for removeValue in toRemove:
                                                    currentDomain[pos].excl(removeValue)
                                                    changed = true
                                                    expReductionsMade += 1
    
    return changed

proc reduceLinearDomains*[T](carray: ConstrainedArray[T], currentDomain: var seq[PackedSet[T]], constraint: StatefulConstraint[T]): bool =
    ## Reduces domains for Linear constraints using bounds propagation
    ## For constraint: Σ(aᵢ·xᵢ) ≤ b, compute bounds for each variable
    ## Properly handles both positive and negative coefficients
    ## Returns true if any domain was reduced
    if constraint.stateType != LinearType:
        return false
    
    var changed = false
    let linState = constraint.linearConstraintState
    let positions = toSeq(constraint.positions)
    
    # Handle different constraint types
    if linState.relation notin [LessThan, LessThanEq, GreaterThan, GreaterThanEq, EqualTo, NotEqualTo]:
        return false
    
    # Skip single-variable constraints as they don't benefit from bounds propagation
    if positions.len <= 1:
        return false
    
    # For each variable in the constraint, compute tighter bounds
    for targetPos in positions:
        let coeff = linState.lincomb.coefficient[targetPos]
        if coeff == 0:
            continue  # Skip variables with zero coefficient
        
        # Skip if any other variable has empty domain (can't compute meaningful bounds)
        var skipThisVariable = false
        for pos in positions:
            if pos != targetPos and currentDomain[pos].card == 0:
                skipThisVariable = true
                break
        
        if skipThisVariable:
            continue
        
        # Compute bounds for other variables
        var minOthers: T = linState.lincomb.constant
        var maxOthers: T = linState.lincomb.constant
        
        for pos in positions:
            if pos == targetPos:
                continue
            let c = linState.lincomb.coefficient[pos]
            if currentDomain[pos].card == 0:
                continue  # Skip empty domains (shouldn't happen due to check above)
            
            let domainVals = toSeq(currentDomain[pos])
            let minVal = min(domainVals)
            let maxVal = max(domainVals)
            
            if c > 0:
                minOthers += c * minVal
                maxOthers += c * maxVal
            else:
                minOthers += c * maxVal
                maxOthers += c * minVal
        
        # Now compute bounds for targetPos based on constraint type
        
        case linState.relation:
            of LessThanEq, LessThan:
                # Σ(aᵢ·xᵢ) ≤ b  =>  aⱼ·xⱼ ≤ b - Σᵢ≠ⱼ(aᵢ·xᵢ)
                let targetValue = linState.target - minOthers
                
                if coeff > 0:
                    # xⱼ ≤ (b - minOthers) / aⱼ
                    let newMax = if linState.relation == LessThan:
                        divFloor(targetValue - 1, coeff)  # Strict: x < (target/coeff)
                    else:
                        divFloor(targetValue, coeff)  # Non-strict: x ≤ (target/coeff)
                    
                    for val in toSeq(currentDomain[targetPos]):
                        if val > newMax:
                            currentDomain[targetPos].excl(val)
                            changed = true
                            
                else:  # coeff < 0
                    # When coefficient is negative, inequality flips: xⱼ ≥ (b - minOthers) / aⱼ
                    let newMin = if linState.relation == LessThan:
                        divCeil(targetValue - 1, coeff)  # Strict: x > (target/coeff)
                    else:
                        divCeil(targetValue, coeff)  # Non-strict: x ≥ (target/coeff)
                    
                    for val in toSeq(currentDomain[targetPos]):
                        if val < newMin:
                            currentDomain[targetPos].excl(val)
                            changed = true
            
            of GreaterThanEq, GreaterThan:
                # Σ(aᵢ·xᵢ) ≥ b  =>  aⱼ·xⱼ ≥ b - Σᵢ≠ⱼ(aᵢ·xᵢ)
                let targetValue = linState.target - maxOthers
                
                if coeff > 0:
                    # xⱼ ≥ (b - maxOthers) / aⱼ
                    let newMin = if linState.relation == GreaterThan:
                        divCeil(targetValue + 1, coeff)  # Strict: x > (target/coeff)
                    else:
                        divCeil(targetValue, coeff)  # Non-strict: x ≥ (target/coeff)
                    
                    for val in toSeq(currentDomain[targetPos]):
                        if val < newMin:
                            currentDomain[targetPos].excl(val)
                            changed = true
                            
                else:  # coeff < 0
                    # When coefficient is negative, inequality flips: xⱼ ≤ (b - maxOthers) / aⱼ
                    let newMax = if linState.relation == GreaterThan:
                        divFloor(targetValue + 1, coeff)  # Strict: x < (target/coeff)
                    else:
                        divFloor(targetValue, coeff)  # Non-strict: x ≤ (target/coeff)
                    
                    for val in toSeq(currentDomain[targetPos]):
                        if val > newMax:
                            currentDomain[targetPos].excl(val)
                            changed = true
            
            of EqualTo:
                # For equality: aⱼ·xⱼ = b - Σᵢ≠ⱼ(aᵢ·xᵢ)
                # The range of Σᵢ≠ⱼ(aᵢ·xᵢ) is [minOthers, maxOthers]
                # So xⱼ must satisfy: (b - maxOthers) / aⱼ ≤ xⱼ ≤ (b - minOthers) / aⱼ (if aⱼ > 0)
                # Or: (b - minOthers) / aⱼ ≤ xⱼ ≤ (b - maxOthers) / aⱼ (if aⱼ < 0)
                let targetMin = linState.target - maxOthers
                let targetMax = linState.target - minOthers
                
                if coeff > 0:
                    # For positive coefficient: xⱼ ∈ [⌈targetMin/coeff⌉, ⌊targetMax/coeff⌋]
                    let computedMin = divCeil(targetMin, coeff)
                    let computedMax = divFloor(targetMax, coeff)
                    
                    for val in toSeq(currentDomain[targetPos]):
                        if val < computedMin or val > computedMax:
                            currentDomain[targetPos].excl(val)
                            changed = true
                            
                else:  # coeff < 0
                    # For negative coefficient: division flips the inequality
                    # xⱼ ∈ [⌈targetMax/coeff⌉, ⌊targetMin/coeff⌋]
                    let computedMin = divCeil(targetMax, coeff)
                    let computedMax = divFloor(targetMin, coeff)
                    
                    for val in toSeq(currentDomain[targetPos]):
                        if val < computedMin or val > computedMax:
                            currentDomain[targetPos].excl(val)
                            changed = true
            
            of NotEqualTo:
                # For Σ(aᵢ·xᵢ) ≠ b, we can only remove values when all but one variable have singleton domains
                # Skip this variable in the outer loop - we'll handle it separately after
                discard
            
            else:
                discard  # Other relations not handled yet
    
    # Special handling for NotEqualTo constraints
    if linState.relation == NotEqualTo:
        # Count variables with non-singleton domains
        var multiValueVars: seq[int] = @[]
        for pos in positions:
            if currentDomain[pos].card > 1:
                multiValueVars.add(pos)
        
        # If exactly one variable has multiple values, we can remove the forbidden value
        if multiValueVars.len == 1:
            let targetPos = multiValueVars[0]
            let coeff = linState.lincomb.coefficient[targetPos]
            
            if coeff != 0:  # Ensure non-zero coefficient
                # Compute the sum of all other (singleton) variables
                var fixedSum: T = linState.lincomb.constant
                for pos in positions:
                    if pos != targetPos:
                        if currentDomain[pos].card == 1:
                            let fixedValue = toSeq(currentDomain[pos])[0]
                            fixedSum += linState.lincomb.coefficient[pos] * fixedValue
                        else:
                            # Should not happen if multiValueVars.len == 1
                            break
                
                # The forbidden value for targetPos is: (target - fixedSum) / coeff
                let remainder = linState.target - fixedSum
                if remainder mod coeff == 0:  # Check if division is exact
                    let forbiddenValue = remainder div coeff
                    
                    # Remove the forbidden value if it's in the domain
                    if forbiddenValue in currentDomain[targetPos]:
                        currentDomain[targetPos].excl(forbiddenValue)
                        changed = true
    
    return changed

proc reduceMinDomains*[T](carray: ConstrainedArray[T], currentDomain: var seq[PackedSet[T]], constraint: StatefulConstraint[T]): bool =
    ## Reduces domains for Min constraints using bounds propagation
    ## Returns true if any domain was reduced
    if constraint.stateType != MinType:
        return false
    
    var changed = false
    let minState = constraint.minConstraintState
    let positions = toSeq(constraint.positions)
    
    # Get target value based on constraint type
    var target: T
    case minState.constraintType:
    of ConstantTarget:
        target = minState.target
    of VariableTarget:
        # Variable targets require bidirectional domain propagation which is complex
        # For now, skip domain reduction for variable targets to avoid over-pruning
        return false
    
    case minState.relation:
        of EqualTo:
            # min(variables) = target
            # 1. At least one variable must contain target
            # 2. All variables can have values > target removed
            # 3. If no variable can achieve target, constraint is unsatisfiable
            
            var canAchieveTarget = false
            for pos in positions:
                if minState.constraintType == VariableTarget and pos == minState.targetPosition:
                    continue  # Skip target variable itself
                if target in currentDomain[pos]:
                    canAchieveTarget = true
            
            if not canAchieveTarget:
                # Constraint unsatisfiable - make all domains empty (signals failure)
                for pos in positions:
                    if minState.constraintType == VariableTarget and pos == minState.targetPosition:
                        continue
                    currentDomain[pos] = initPackedSet[T]()
                    changed = true
            else:
                # Remove values > target from all variables
                for pos in positions:
                    if minState.constraintType == VariableTarget and pos == minState.targetPosition:
                        continue  # Skip target variable
                    for val in toSeq(currentDomain[pos]):
                        if val > target:
                            currentDomain[pos].excl(val)
                            changed = true
        
        of LessThanEq, LessThan:
            # min(variables) ≤ target (or <)
            # All variables can have upper bound set to target (or target-1)
            let upperBound = if minState.relation == LessThan: target - 1 else: target
            
            for pos in positions:
                if minState.constraintType == VariableTarget and pos == minState.targetPosition:
                    continue  # Skip target variable
                for val in toSeq(currentDomain[pos]):
                    if val > upperBound:
                        currentDomain[pos].excl(val)
                        changed = true
        
        of GreaterThanEq, GreaterThan:
            # min(variables) ≥ target (or >)
            # At least one variable must have a value ≥ target (or > target)
            let lowerBound = if minState.relation == GreaterThan: target + 1 else: target
            
            var canSatisfy = false
            for pos in positions:
                if minState.constraintType == VariableTarget and pos == minState.targetPosition:
                    continue  # Skip target variable
                let domainVals = toSeq(currentDomain[pos])
                if domainVals.len > 0 and max(domainVals) >= lowerBound:
                    canSatisfy = true
                    break
            
            if not canSatisfy:
                # Constraint unsatisfiable - make all domains empty
                for pos in positions:
                    if minState.constraintType == VariableTarget and pos == minState.targetPosition:
                        continue
                    currentDomain[pos] = initPackedSet[T]()
                    changed = true
        
        else:
            discard  # Other relations not handled
    
    return changed

proc reduceMaxDomains*[T](carray: ConstrainedArray[T], currentDomain: var seq[PackedSet[T]], constraint: StatefulConstraint[T]): bool =
    ## Reduces domains for Max constraints using bounds propagation  
    ## Returns true if any domain was reduced
    if constraint.stateType != MaxType:
        return false
    
    var changed = false
    let maxState = constraint.maxConstraintState
    let positions = toSeq(constraint.positions)
    let target = maxState.target
    
    case maxState.relation:
        of EqualTo:
            # max(variables) = target
            # 1. At least one variable must contain target
            # 2. All variables can have values < target removed
            # 3. If no variable can achieve target, constraint is unsatisfiable
            
            var canAchieveTarget = false
            for pos in positions:
                if target in currentDomain[pos]:
                    canAchieveTarget = true
            
            if not canAchieveTarget:
                # Constraint unsatisfiable - make all domains empty
                for pos in positions:
                    currentDomain[pos] = initPackedSet[T]()
                    changed = true
            else:
                # Remove values < target from all variables
                for pos in positions:
                    for val in toSeq(currentDomain[pos]):
                        if val < target:
                            currentDomain[pos].excl(val)
                            changed = true
        
        of GreaterThanEq, GreaterThan:
            # max(variables) ≥ target (or >)
            # All variables can have lower bound set to target (or target+1)
            let lowerBound = if maxState.relation == GreaterThan: target + 1 else: target
            
            for pos in positions:
                for val in toSeq(currentDomain[pos]):
                    if val < lowerBound:
                        currentDomain[pos].excl(val)
                        changed = true
        
        of LessThanEq, LessThan:
            # max(variables) ≤ target (or <)
            # At least one variable must have a value ≤ target (or < target)
            let upperBound = if maxState.relation == LessThan: target - 1 else: target
            
            var canSatisfy = false
            for pos in positions:
                let domainVals = toSeq(currentDomain[pos])
                if domainVals.len > 0 and min(domainVals) <= upperBound:
                    canSatisfy = true
                    break
            
            if not canSatisfy:
                # Constraint unsatisfiable - make all domains empty
                for pos in positions:
                    currentDomain[pos] = initPackedSet[T]()
                    changed = true
        
        else:
            discard  # Other relations not handled
    
    return changed

proc reduceGlobalCardinalityDomains*[T](carray: ConstrainedArray[T], currentDomain: var seq[PackedSet[T]], constraint: StatefulConstraint[T]): bool =
    ## Reduces domains for GlobalCardinality constraints
    ## Returns true if any domain was reduced
    if constraint.stateType != GlobalCardinalityType:
        return false
    
    var changed = false
    let gcState = constraint.globalCardinalityState
    let positions = toSeq(constraint.positions)
    let cardinalities = gcState.valueCardinalities
    
    # Only handle position-based constraints for now (not expression-based)
    if gcState.evalMethod != PositionBased:
        return false
    
    # Step 1: Remove values with cardinality 0
    for value, requiredCount in cardinalities.pairs:
        if requiredCount == 0:
            # This value should not appear at all
            for pos in positions:
                if value in currentDomain[pos]:
                    currentDomain[pos].excl(value)
                    changed = true
    
    # Step 2: Count current assignments and possibilities for each value
    var minCount = initTable[T, int]()  # Minimum occurrences (singleton domains)
    var maxCount = initTable[T, int]()  # Maximum possible occurrences
    var forcedPositions = initTable[T, seq[int]]()  # Positions forced to a value
    var possiblePositions = initTable[T, seq[int]]()  # Positions that could take a value
    
    # Analyze current domains
    for pos in positions:
        let domainVals = toSeq(currentDomain[pos])
        if domainVals.len == 0:
            continue  # Skip empty domains
        
        if domainVals.len == 1:
            # Singleton domain - this position is forced
            let value = domainVals[0]
            minCount[value] = minCount.getOrDefault(value, 0) + 1
            maxCount[value] = maxCount.getOrDefault(value, 0) + 1
            if value notin forcedPositions:
                forcedPositions[value] = @[]
            forcedPositions[value].add(pos)
        else:
            # Multiple values possible
            for value in domainVals:
                maxCount[value] = maxCount.getOrDefault(value, 0) + 1
                if value notin possiblePositions:
                    possiblePositions[value] = @[]
                possiblePositions[value].add(pos)
    
    # Step 3: Check feasibility and remove values
    for value, requiredCount in cardinalities.pairs:
        let currentMin = minCount.getOrDefault(value, 0)
        let currentMax = maxCount.getOrDefault(value, 0)
        
        # Check if constraint is satisfiable
        if currentMax < requiredCount:
            # Not enough positions can take this value - constraint unsatisfiable
            # Make all domains empty to signal failure
            for pos in positions:
                currentDomain[pos] = initPackedSet[T]()
                changed = true
            return changed
        
        if currentMin > requiredCount:
            # Too many positions forced to this value - constraint unsatisfiable
            for pos in positions:
                currentDomain[pos] = initPackedSet[T]()
                changed = true
            return changed
        
        # If we've reached the required count, remove this value from other positions
        if currentMin == requiredCount:
            # We have exactly the required number of forced positions
            # Remove this value from all other positions
            if value in possiblePositions:
                for pos in possiblePositions[value]:
                    if value in currentDomain[pos]:
                        currentDomain[pos].excl(value)
                        changed = true
        
        # If exactly requiredCount positions can take this value, force them all
        if currentMax == requiredCount and requiredCount > 0:
            # These positions must take this value
            let allPositions = forcedPositions.getOrDefault(value, @[]) & possiblePositions.getOrDefault(value, @[])
            for pos in allPositions:
                if currentDomain[pos].card > 1:
                    # Force to singleton domain
                    currentDomain[pos] = toPackedSet[T]([value])
                    changed = true
    
    # Step 4: Hall's theorem-like reasoning for sets of values
    # For simplicity, we'll check pairs of values
    if positions.len <= 20:  # Only for small problems to avoid exponential blowup
        var valuesToCheck = newSeq[T]()
        for value, _ in cardinalities.pairs:
            valuesToCheck.add(value)
        
        # Check pairs of values
        for i in 0..<valuesToCheck.len:
            for j in i+1..<valuesToCheck.len:
                let v1 = valuesToCheck[i]
                let v2 = valuesToCheck[j]
                let totalRequired = cardinalities[v1] + cardinalities[v2]
                
                # Find positions that can only take v1 or v2
                var restrictedPositions = newSeq[int]()
                for pos in positions:
                    let domainVals = toSeq(currentDomain[pos])
                    var canTakeOther = false
                    for val in domainVals:
                        if val != v1 and val != v2 and val in cardinalities:
                            canTakeOther = true
                            break
                    if not canTakeOther and domainVals.len > 0:
                        # This position can only take v1 or v2 (or values not in cardinalities)
                        var hasV1orV2 = false
                        for val in domainVals:
                            if val == v1 or val == v2:
                                hasV1orV2 = true
                                break
                        if hasV1orV2:
                            restrictedPositions.add(pos)
                
                # If exactly totalRequired positions can only take v1 or v2
                if restrictedPositions.len == totalRequired:
                    # Remove all other values from these positions
                    for pos in restrictedPositions:
                        for val in toSeq(currentDomain[pos]):
                            if val != v1 and val != v2:
                                currentDomain[pos].excl(val)
                                changed = true
    
    return changed

proc reduceDomain*[T](carray: ConstrainedArray[T], verbose: bool = true): seq[seq[T]] =
    var
        reduced = newSeq[seq[T]](carray.len)
        currentDomain = newSeq[PackedSet[T]](carray.len)

    for pos in carray.allPositions():
        currentDomain[pos] = toPackedSet[T](carray.domain[pos])

    # Log initial domain sizes
    var totalDomainSize = 0
    for pos in carray.allPositions():
        totalDomainSize += currentDomain[pos].card
    
    if verbose:
        echo "Domain Reduction Starting:"
        echo "  Initial total domain size: ", totalDomainSize

    # Iterative domain reduction until fixpoint
    var changed = true
    var iterations = 0
    const maxIterations = 10  # Prevent infinite loops
    
    
    while changed and iterations < maxIterations:
        changed = false
        iterations += 1
        
        if verbose: echo "\n--- Iteration ", iterations, " ---"
        
        # Process AllDifferent constraints first (most impactful)
        var allDifferentChanged = false
        var allDifferentCount = 0
        for cons in carray.constraints:
            if cons.stateType == AllDifferentType:
                allDifferentCount += 1
                if carray.reduceAllDifferentDomains(currentDomain, cons):
                    allDifferentChanged = true
                    changed = true
        
        if verbose and allDifferentCount > 0:
            var totalAfterAllDiff = 0
            for pos in carray.allPositions():
                totalAfterAllDiff += currentDomain[pos].card
            echo "  After ", allDifferentCount, " AllDifferent constraint(s):"
            echo "    Total domain size: ", totalAfterAllDiff
            if not allDifferentChanged:
                echo "    No changes made"
        
        # Process Linear constraints with bounds propagation
        var linearChanged = false
        var linearCount = 0
        for cons in carray.constraints:
            if cons.stateType == LinearType:
                linearCount += 1
                if carray.reduceLinearDomains(currentDomain, cons):
                    linearChanged = true
                    changed = true
        
        if verbose and linearCount > 0:
            var totalAfterLinear = 0
            for pos in carray.allPositions():
                totalAfterLinear += currentDomain[pos].card
            echo "  After ", linearCount, " Linear constraint(s):"
            echo "    Total domain size: ", totalAfterLinear
            if not linearChanged:
                echo "    No changes made"
        
        # Process Min constraints with bounds propagation
        var minChanged = false
        var minCount = 0
        for cons in carray.constraints:
            if cons.stateType == MinType:
                minCount += 1
                if carray.reduceMinDomains(currentDomain, cons):
                    minChanged = true
                    changed = true
        
        if verbose and minCount > 0:
            var totalAfterMin = 0
            for pos in carray.allPositions():
                totalAfterMin += currentDomain[pos].card
            echo "  After ", minCount, " Min constraint(s):"
            echo "    Total domain size: ", totalAfterMin
            if not minChanged:
                echo "    No changes made"
        
        # Process Max constraints with bounds propagation
        var maxChanged = false
        var maxCount = 0
        for cons in carray.constraints:
            if cons.stateType == MaxType:
                maxCount += 1
                if carray.reduceMaxDomains(currentDomain, cons):
                    maxChanged = true
                    changed = true
        
        if verbose and maxCount > 0:
            var totalAfterMax = 0
            for pos in carray.allPositions():
                totalAfterMax += currentDomain[pos].card
            echo "  After ", maxCount, " Max constraint(s):"
            echo "    Total domain size: ", totalAfterMax
            if not maxChanged:
                echo "    No changes made"
        
        # Process GlobalCardinality constraints
        var globalCardChanged = false
        var globalCardCount = 0
        for cons in carray.constraints:
            if cons.stateType == GlobalCardinalityType:
                globalCardCount += 1
                if carray.reduceGlobalCardinalityDomains(currentDomain, cons):
                    globalCardChanged = true
                    changed = true
        
        if verbose and globalCardCount > 0:
            var totalAfterGlobalCard = 0
            for pos in carray.allPositions():
                totalAfterGlobalCard += currentDomain[pos].card
            echo "  After ", globalCardCount, " GlobalCardinality constraint(s):"
            echo "    Total domain size: ", totalAfterGlobalCard
            if not globalCardChanged:
                echo "    No changes made"
        
        # Process Regular constraints with arc consistency
        var regularChanged = false
        var regularCount = 0
        for cons in carray.constraints:
            if cons.stateType == RegularType:
                regularCount += 1
                if carray.reduceRegularDomains(currentDomain, cons):
                    regularChanged = true
                    changed = true
        
        if verbose and regularCount > 0:
            var totalAfterRegular = 0
            for pos in carray.allPositions():
                totalAfterRegular += currentDomain[pos].card
            echo "  After ", regularCount, " Regular constraint(s):"
            echo "    Total domain size: ", totalAfterRegular
            if not regularChanged:
                echo "    No changes made"
        
        # Then examine single-variable constraints to reduce domains
        var singleVarChanged = false
        var singleVarCount = 0
        for cons in carray.constraints:
            if cons.positions.len != 1:
                continue
            singleVarCount += 1
            var pos = toSeq(cons.positions)[0]
            
            # Initialize constraint with a dummy assignment using CURRENT reduced domains
            var dummyAssignment = newSeq[T](carray.len)
            for i in 0..<carray.len:
                if currentDomain[i].card > 0:
                    dummyAssignment[i] = toSeq(currentDomain[i])[0]
                else:
                    # If current domain is empty, use default value
                    dummyAssignment[i] = T.default
            
            # Only initialize and test single-position constraints to avoid interference
            cons.initialize(dummyAssignment)
            
            var originalSize = currentDomain[pos].card
            for d in toSeq(currentDomain[pos]):  # Need to convert to seq to avoid modification during iteration
                cons.updatePosition(pos, d)
                if cons.penalty() > 0:
                    currentDomain[pos].excl(d)
            
            if currentDomain[pos].card < originalSize:
                singleVarChanged = true
                changed = true
        
        if verbose and singleVarCount > 0:
            var totalAfterSingleVar = 0
            for pos in carray.allPositions():
                totalAfterSingleVar += currentDomain[pos].card
            echo "  After ", singleVarCount, " single-variable constraint(s):"
            echo "    Total domain size: ", totalAfterSingleVar
            if not singleVarChanged:
                echo "    No changes made"
    
    # Final logging
    var finalTotalDomainSize = 0
    for pos in carray.allPositions():
        finalTotalDomainSize += currentDomain[pos].card
        reduced[pos] = toSeq(currentDomain[pos])
    
    if verbose:
        echo "\nDomain Reduction Complete:"
        echo "  Total iterations: ", iterations
        echo "  Final total domain size: ", finalTotalDomainSize
        echo "  Domain size reduction: ", (totalDomainSize - finalTotalDomainSize), " (", 
             if totalDomainSize > 0: (100 * (totalDomainSize - finalTotalDomainSize) div totalDomainSize) else: 0, "%)"
    
    return reduced

################################################################################
# Regular constraint domain reduction integration
################################################################################

proc reduceRegularDomains*[T](carray: ConstrainedArray[T], 
                             currentDomains: var seq[PackedSet[T]], 
                             constraint: StatefulConstraint[T]): bool =
    ## Integration function for regular constraint domain reduction
    ## Returns true if any domain was reduced
    when T is int:
        if constraint.stateType == RegularType:
            # Create domain filterer for this regular constraint
            var filterer = newRegularDomainFilterer(constraint.regularState)
            
            # Apply arc consistency filtering
            return filterer.filterDomainsArcConsistent(currentDomains)
    
    return false

################################################################################
# Deep Copy for ConstrainedArray (for parallel processing)
################################################################################

proc deepCopy*[T](arr: ConstrainedArray[T]): ConstrainedArray[T] =
  ## Creates a deep copy of a ConstrainedArray for thread-safe parallel processing
  result.len = arr.len
  result.domain = arr.domain  # seq[seq[T]] - deep copy by assignment
  result.entries = arr.entries  # seq[AlgebraicExpression[T]] - should be immutable
  
  # Deep copy all stateful constraints
  result.constraints = newSeq[StatefulConstraint[T]](arr.constraints.len)
  for i, constraint in arr.constraints:
    result.constraints[i] = constraint.deepCopy()

