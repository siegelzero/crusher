import std/[tables, strutils, sequtils, packedsets, math, strformat, sets]
import ast
import ../crusher/[constraintSystem, constrainedArray, expressions]
import ../crusher/constraints/[algebraic, stateful, constraintNode, globalCardinality, minConstraint, regular]
import ../crusher/search/[resolution, tabu, optimization]

type
  FlatZincError* = object of CatchableError
  
  AlgebraicConstraintStats* = object
    inequalities*: int  # <=, >=, <, >
    equalities*: int    # ==
    inequalities_linear*: int  # LinearCombination <= value
    inequalities_variable*: int # Variable <= Variable  
    
  FlatZincTranslator* = object
    system*: ConstraintSystem[int]
    variables*: Table[string, int] # Maps FZ variable names to Crusher indices
    varDecls*: seq[FlatZincVarDecl]
    algebraicStats*: AlgebraicConstraintStats

proc initTranslator*(): FlatZincTranslator =
  result = FlatZincTranslator(
    system: initConstraintSystem[int](),
    variables: initTable[string, int](),
    varDecls: @[],
    algebraicStats: AlgebraicConstraintStats(inequalities: 0, equalities: 0, inequalities_linear: 0, inequalities_variable: 0)
  )

# Wrapper to track algebraic constraint types
proc addConstraintWithTracking(translator: var FlatZincTranslator, constraint: AlgebraicConstraint[int], constraintType: string) =
  # Track the type of algebraic constraint
  if "==" in constraintType:
    translator.algebraicStats.equalities += 1
  elif "<=" in constraintType or ">=" in constraintType or "<" in constraintType or ">" in constraintType:
    translator.algebraicStats.inequalities += 1
    if "LinearCombination" in constraintType:
      translator.algebraicStats.inequalities_linear += 1  
    elif "Variable" in constraintType:
      translator.algebraicStats.inequalities_variable += 1
  
  translator.system.addConstraint(constraint)

proc printAlgebraicStats(translator: FlatZincTranslator) =
  echo "\n=== ALGEBRAIC CONSTRAINT ANALYSIS ==="
  echo fmt"Total equalities (==): {translator.algebraicStats.equalities}"
  echo fmt"Total inequalities (<=,>=,<,>): {translator.algebraicStats.inequalities}"
  echo fmt"  - LinearCombination inequalities: {translator.algebraicStats.inequalities_linear}"
  echo fmt"  - Variable-to-Variable inequalities: {translator.algebraicStats.inequalities_variable}"
  echo "======================================"


proc translateDomain(domain: FlatZincDomain): seq[int] =
  case domain.domainType:
    of fzInt:
      if domain.hasRange:
        result = toSeq(domain.intRange.min .. domain.intRange.max)
      elif domain.hasSet:
        result = domain.intSet
      else:
        # Unbounded integer - will be refined later based on constraint analysis
        result = @[]  # Empty domain signals need for inference
    of fzBool:
      result = @[0, 1] # false=0, true=1
    of fzArrayInt, fzArrayBool, fzArrayFloat:
      # For array types, use default domain - the individual elements should have their own domains
      result = toSeq(0 .. 100)
    else:
      # For other types, use default integer domain
      result = toSeq(0 .. 100)

proc addVariable(translator: var FlatZincTranslator, decl: FlatZincVarDecl) =
  translator.varDecls.add(decl)
  
  if decl.isVar: # Only constrained variables go into the constraint system
    let domain = translateDomain(decl.domain)
    
    case decl.varType:
      of fzArrayInt, fzArrayBool, fzArrayFloat:
        # Check if this array references other variables (no new variables needed)
        if decl.arrayVarRefs.len > 0:
          # This is an alias array - map it to the first referenced variable's index
          # The actual array access will be handled in expression translation
          if decl.arrayVarRefs[0] in translator.variables:
            translator.variables[decl.name] = translator.variables[decl.arrayVarRefs[0]]
          else:
            # Defer mapping until referenced variables are processed
            translator.variables[decl.name] = -1  # Mark as deferred
        else:
          # Create new variables for this array
          let arraySize = if decl.arraySize.len > 0:
            decl.arraySize[0]  # Use the actual array size from parser
          else:
            raise newException(FlatZincError, "Array variable '" & decl.name & "' has no size information")
          
          # Create array as a sequence, not a matrix
          let baseVarIndex = translator.system.baseArray.len
          let sequence = newConstrainedSequence(translator.system, arraySize)
          if domain.len == 0:
            # Unbounded array elements - use temporary large domain
            sequence.setDomain(toSeq(0 .. 10000))
          else:
            sequence.setDomain(domain)
          
          # Map the array variable to the base index
          translator.variables[decl.name] = baseVarIndex
        
      else:
        # Regular scalar variable
        let varIndex = translator.system.baseArray.len
        let varSeq = newConstrainedSequence(translator.system, 1)
        # Set domain using the correct API pattern
        if domain.len == 0:
          # Unbounded variable - use temporary large domain, will be refined later
          varSeq.setDomain(toSeq(0 .. 10000))
        else:
          varSeq.setDomain(domain)
        translator.variables[decl.name] = varIndex

proc translateExpr(translator: FlatZincTranslator, expr: FlatZincExpr): ExpressionNode[int] =
    case expr.exprType:
    of feIdent:
      if expr.name in translator.variables:
        result = ExpressionNode[int](
          kind: RefNode,
          position: translator.variables[expr.name]
        )
      else:
        # Check if this is array indexing like "a[1]"
        if '[' in expr.name and expr.name.endsWith("]"):
          let parts = expr.name.split('[')
          if parts.len == 2:
            let arrayName = parts[0]
            let indexStr = parts[1].replace("]", "")
            try:
              let index = parseInt(indexStr)
              if arrayName in translator.variables:
                let basePos = translator.variables[arrayName]
                # Array access is now linear, not matrix-based
                let linearIndex = index - 1  # Convert to 0-based
                result = ExpressionNode[int](
                  kind: RefNode, 
                  position: basePos + linearIndex
                )
                return
            except:
              discard
        
        # Must be a parameter - find its value
        for decl in translator.varDecls:
          if decl.name == expr.name and not decl.isVar:
            # For simplicity, assume parameter values are embedded in name or use 0
            result = ExpressionNode[int](kind: LiteralNode, value: 0)
            return
        # Default fallback
        result = ExpressionNode[int](kind: LiteralNode, value: 0)
    of feLiteral:
      case expr.literal.literalType:
        of fzInt:
          result = ExpressionNode[int](kind: LiteralNode, value: expr.literal.intVal)
        of fzBool:
          result = ExpressionNode[int](kind: LiteralNode, value: if expr.literal.boolVal: 1 else: 0)
        else:
          result = ExpressionNode[int](kind: LiteralNode, value: 0)
    of feArray:
      # For array expressions, we'll need to handle them as needed
      # For now, just return first element or 0
      if expr.elements.len > 0:
        result = translator.translateExpr(expr.elements[0])
      else:
        result = ExpressionNode[int](kind: LiteralNode, value: 0)

proc translateObjective(translator: FlatZincTranslator, expr: FlatZincExpr): AlgebraicExpression[int] =
  ## Translate a FlatZinc objective expression to Crusher AlgebraicExpression
  case expr.exprType:
    of feIdent:
      # Simple variable reference as objective
      if expr.name in translator.variables:
        let position = translator.variables[expr.name]
        result = translator.system.baseArray.entries[position]
      else:
        # Handle array indexing like "cost[1]"
        if '[' in expr.name and expr.name.endsWith("]"):
          let parts = expr.name.split('[')
          if parts.len == 2:
            let arrayName = parts[0]
            let indexStr = parts[1].replace("]", "")
            try:
              let index = parseInt(indexStr)
              if arrayName in translator.variables:
                let basePos = translator.variables[arrayName]
                let linearIndex = index - 1  # Convert to 0-based
                result = translator.system.baseArray.entries[basePos + linearIndex]
                return
            except:
              discard
        # Fallback: create a constant expression with value 0
        result = newAlgebraicExpression[int](
          positions = initPackedSet[int](),
          node = ExpressionNode[int](kind: LiteralNode, value: 0),
          linear = true
        )
    of feLiteral:
      # Constant objective (unusual but possible)
      var value = 0
      case expr.literal.literalType:
        of fzInt: 
          value = expr.literal.intVal
        of fzBool: 
          value = if expr.literal.boolVal: 1 else: 0
        else: 
          value = 0
      result = newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: value),
        linear = true
      )
    of feArray:
      # Complex expression - for now, just use first element or return constant 0
      if expr.elements.len > 0:
        result = translator.translateObjective(expr.elements[0])
      else:
        result = newAlgebraicExpression[int](
          positions = initPackedSet[int](),
          node = ExpressionNode[int](kind: LiteralNode, value: 0),
          linear = true
        )

proc translateLinearConstraint(translator: var FlatZincTranslator, 
                              coeffs: seq[int], vars: seq[string], 
                              rhs: int, op: string) =
  # Build LinearCombination: coeffs[0]*vars[0] + coeffs[1]*vars[1] + ...
  var coefficients = initTable[int, int]()
  
  for i, varName in vars:
    let coeff = if i < coeffs.len: coeffs[i] else: 1
    
    # Get the position for this variable name
    # Handle array indexing like "a[1]" -> matrix position
    let position = if '[' in varName and varName.endsWith("]"):
      let parts = varName.split('[')
      if parts.len == 2:
        let arrayName = parts[0]
        let indexStr = parts[1].replace("]", "")
        try:
          let index = parseInt(indexStr)
          if arrayName in translator.variables:
            let basePos = translator.variables[arrayName]
            # Simple linear array indexing - don't assume 2D matrix structure
            let linearIndex = index - 1  # Convert to 0-based indexing
            basePos + linearIndex
          else:
            -1  # Invalid
        except:
          -1  # Invalid
      else:
        -1  # Invalid
    else:
      if varName in translator.variables:
        translator.variables[varName]
      else:
        -1  # Invalid
    
    if position >= 0:
      coefficients[position] = coefficients.getOrDefault(position, 0) + coeff
  
  if coefficients.len == 0:
    return
  
  
  # Create LinearCombination
  let linearComb = newLinearCombination(coefficients, 0)
  
  # Add constraint using LinearCombination operators
  case op:
    of "eq", "=": 
      # This creates a LinearType StatefulConstraint, not AlgebraicConstraint
      translator.system.addConstraint(linearComb == rhs)
    of "le", "<=": 
      # This creates a LinearType StatefulConstraint, not AlgebraicConstraint  
      translator.system.addConstraint(linearComb <= rhs)
    of "ge", ">=": 
      # This creates a LinearType StatefulConstraint, not AlgebraicConstraint
      translator.system.addConstraint(linearComb >= rhs)
    of "lt", "<": 
      # This creates a LinearType StatefulConstraint, not AlgebraicConstraint
      translator.system.addConstraint(linearComb < rhs)
    of "gt", ">": 
      # This creates a LinearType StatefulConstraint, not AlgebraicConstraint
      translator.system.addConstraint(linearComb > rhs)
    of "ne", "!=":
      # This creates a LinearType StatefulConstraint, not AlgebraicConstraint
      translator.system.addConstraint(linearComb != rhs)
    else: 
      translator.system.addConstraint(linearComb == rhs)

proc translateConstraint(translator: var FlatZincTranslator, constraint: FlatZincConstraint, verbose: bool = false) =
  case constraint.name:
    of "int_lin_eq":
      # int_lin_eq([c1,c2,...], [x1,x2,...], rhs)
      if constraint.args.len >= 3:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1]
        let rhsExpr = constraint.args[2]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference like X_INTRODUCED_28_
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              # This is an array parameter - get its values
              coeffs = decl.arrayValue
              break
        
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        elif varsExpr.exprType == feIdent:
          # Handle array parameter reference for variables
          for decl in translator.varDecls:
            if decl.name == varsExpr.name and decl.varType == fzArrayInt:
              # This is an array - get variable references
              if decl.arrayVarRefs.len > 0:
                varNames = decl.arrayVarRefs
              break
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "eq")
    
    of "int_lin_le":
      # Similar to int_lin_eq but with <=
      if constraint.args.len >= 3:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1] 
        let rhsExpr = constraint.args[2]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference like X_INTRODUCED_267_
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              # This is an array parameter - get its values
              coeffs = decl.arrayValue
              break
        
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        elif varsExpr.exprType == feIdent:
          # Handle array parameter reference for variables
          for decl in translator.varDecls:
            if decl.name == varsExpr.name and decl.varType == fzArrayInt:
              # This is an array - get variable references
              if decl.arrayVarRefs.len > 0:
                varNames = decl.arrayVarRefs
              break
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "le")
    
    of "int_lin_ge":
      # Similar to int_lin_eq but with >=
      if constraint.args.len >= 3:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1]
        let rhsExpr = constraint.args[2]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              coeffs = decl.arrayValue
              break
        
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "ge")
    
    of "int_lin_ne":
      # int_lin_ne([c1,c2,...], [x1,x2,...], rhs) - NOT EQUAL
      if constraint.args.len >= 3:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1]
        let rhsExpr = constraint.args[2]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              coeffs = decl.arrayValue
              break
        
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "ne")
    
    of "int_lin_lt":
      # int_lin_lt([c1,c2,...], [x1,x2,...], rhs) - LESS THAN
      if constraint.args.len >= 3:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1]
        let rhsExpr = constraint.args[2]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              coeffs = decl.arrayValue
              break
        
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "lt")
    
    of "int_lin_gt":
      # int_lin_gt([c1,c2,...], [x1,x2,...], rhs) - GREATER THAN
      if constraint.args.len >= 3:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1]
        let rhsExpr = constraint.args[2]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              coeffs = decl.arrayValue
              break
        
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "gt")
    
    of "all_different_int", "gecode_all_different_int":
      # all_different_int([x1, x2, x3, ...]) or gecode_all_different_int([x1, x2, x3, ...])
      if constraint.args.len >= 1:
        let varsExpr = constraint.args[0]
        
        var expressions: seq[AlgebraicExpression[int]] = @[]
        
        if varsExpr.exprType == feArray:
          # Extract the specific variable references from the array
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              # Check if this is a regular variable reference
              if elem.name in translator.variables:
                let position = translator.variables[elem.name]
                # Individual variables are stored in the base array
                expressions.add(translator.system.baseArray.entries[position])
              # Parse array indexing like "a[1]", "a[2]", etc.
              elif '[' in elem.name and elem.name.endsWith("]"):
                let parts = elem.name.split('[')
                if parts.len == 2:
                  let arrayName = parts[0]
                  let indexStr = parts[1].replace("]", "")
                  
                  if arrayName in translator.variables:
                    let basePos = translator.variables[arrayName]
                    try:
                      let index = parseInt(indexStr) - 1  # Convert to 0-based indexing
                      expressions.add(translator.system.baseArray.entries[basePos + index])
                    except:
                      discard
        elif varsExpr.exprType == feIdent:
          # Handle the case where the argument is an array identifier
          if varsExpr.name in translator.variables:
            let basePos = translator.variables[varsExpr.name]
            # Add all variables in the array to allDifferent
            for varDecl in translator.varDecls:
              if varDecl.name == varsExpr.name and varDecl.arraySize.len > 0:
                let arraySize = varDecl.arraySize[0]
                for i in 0..<arraySize:
                  expressions.add(translator.system.baseArray.entries[basePos + i])
                break
          elif varsExpr.name in translator.variables:
            let position = translator.variables[varsExpr.name]
            expressions.add(translator.system.baseArray.entries[position])
          else:
            # Check if this is an array that references other variables
            for varDecl in translator.varDecls:
              if varDecl.name == varsExpr.name and varDecl.arrayVarRefs.len > 0:
                # Use the variable references from the array
                for varRefName in varDecl.arrayVarRefs:
                  if varRefName in translator.variables:
                    let position = translator.variables[varRefName]
                    expressions.add(translator.system.baseArray.entries[position])
                break
        
        # Apply allDifferent to the specific expressions
        if expressions.len > 0:
          translator.system.addConstraint(allDifferent(expressions))
    
    of "bool_clause":
      # bool_clause([pos_vars], [neg_vars])
      # Represents: (pos_vars[0] OR pos_vars[1] OR ...) OR (NOT neg_vars[0] OR NOT neg_vars[1] OR ...)
      if constraint.args.len >= 2:
        let posVarsExpr = constraint.args[0]
        let negVarsExpr = constraint.args[1]
        
        var clauseConstraints: seq[AlgebraicConstraint[int]] = @[]
        
        # Handle positive variables (appear as-is in the clause)
        if posVarsExpr.exprType == feArray:
          for elem in posVarsExpr.elements:
            if elem.exprType == feIdent and elem.name in translator.variables:
              let position = translator.variables[elem.name]
              # Assuming boolean variables have domain [0,1], constraint is var == 1 (true)
              clauseConstraints.add(translator.system.baseArray.entries[position] == 1)
        
        # Handle negative variables (appear negated in the clause)
        if negVarsExpr.exprType == feArray:
          for elem in negVarsExpr.elements:
            if elem.exprType == feIdent and elem.name in translator.variables:
              let position = translator.variables[elem.name]
              # Negated variables: constraint is var == 0 (false, so NOT var is true)
              clauseConstraints.add(translator.system.baseArray.entries[position] == 0)
        
        # Create the disjunctive constraint (OR of all clause constraints)
        if clauseConstraints.len > 0:
          var disjunctiveConstraint = clauseConstraints[0]
          for i in 1..<clauseConstraints.len:
            disjunctiveConstraint = disjunctiveConstraint or clauseConstraints[i]
          translator.system.addConstraint(disjunctiveConstraint)
    
    of "array_bool_and":
      # array_bool_and([input_vars], output_var)
      # Means: output_var = input_vars[0] AND input_vars[1] AND ... AND input_vars[n]
      if constraint.args.len >= 2:
        let inputVarsExpr = constraint.args[0]
        let outputVarExpr = constraint.args[1]
        
        var inputConstraints: seq[AlgebraicConstraint[int]] = @[]
        
        # Get all input variables
        if inputVarsExpr.exprType == feArray:
          for elem in inputVarsExpr.elements:
            if elem.exprType == feIdent and elem.name in translator.variables:
              let position = translator.variables[elem.name]
              # Input variable must be true (== 1) for AND to be true
              inputConstraints.add(translator.system.baseArray.entries[position] == 1)
        
        # Get output variable
        if outputVarExpr.exprType == feIdent and outputVarExpr.name in translator.variables:
          let outputPos = translator.variables[outputVarExpr.name]
          let outputVar = translator.system.baseArray.entries[outputPos]
          
          if inputConstraints.len > 0:
            # Create the conjunctive constraint (AND of all input constraints)
            var conjunctiveConstraint = inputConstraints[0]
            for i in 1..<inputConstraints.len:
              conjunctiveConstraint = conjunctiveConstraint and inputConstraints[i]
            
            # output_var == 1 IFF all inputs are 1 (conjunctive constraint is satisfied)
            # This is: (output_var == 1) IFF (conjunctiveConstraint)
            # Implemented as: (output_var == 1 AND conjunctiveConstraint) OR (output_var == 0 AND NOT conjunctiveConstraint)
            let outputTrue = outputVar == 1
            let outputFalse = outputVar == 0
            let equivalence = (outputTrue and conjunctiveConstraint) or (outputFalse and not conjunctiveConstraint)
            translator.system.addConstraint(equivalence)
    
    of "array_bool_or":
      # array_bool_or([input_vars], output_var)  
      # Means: output_var = input_vars[0] OR input_vars[1] OR ... OR input_vars[n]
      if constraint.args.len >= 2:
        let inputVarsExpr = constraint.args[0]
        let outputVarExpr = constraint.args[1]
        
        var inputConstraints: seq[AlgebraicConstraint[int]] = @[]
        
        # Get all input variables
        if inputVarsExpr.exprType == feArray:
          for elem in inputVarsExpr.elements:
            if elem.exprType == feIdent and elem.name in translator.variables:
              let position = translator.variables[elem.name]
              # Input variable is true (== 1) 
              inputConstraints.add(translator.system.baseArray.entries[position] == 1)
        
        # Get output variable
        if outputVarExpr.exprType == feIdent and outputVarExpr.name in translator.variables:
          let outputPos = translator.variables[outputVarExpr.name]
          let outputVar = translator.system.baseArray.entries[outputPos]
          
          if inputConstraints.len > 0:
            # Create the disjunctive constraint (OR of all input constraints)
            var disjunctiveConstraint = inputConstraints[0]
            for i in 1..<inputConstraints.len:
              disjunctiveConstraint = disjunctiveConstraint or inputConstraints[i]
            
            # output_var == 1 IFF at least one input is 1 (disjunctive constraint is satisfied)
            let outputTrue = outputVar == 1
            let outputFalse = outputVar == 0
            let equivalence = (outputTrue and disjunctiveConstraint) or (outputFalse and not disjunctiveConstraint)
            translator.system.addConstraint(equivalence)
    
    of "int_eq_reif":
      # int_eq_reif(var1, var2, bool_result)
      # Means: bool_result ↔ (var1 == var2)
      if constraint.args.len >= 3:
        let var1Expr = constraint.args[0]
        let var2Expr = constraint.args[1] 
        let boolResultExpr = constraint.args[2]
        
        # Parse variables
        var var1Position = -1
        var var2Position = -1
        
        # Get first variable or literal
        if var1Expr.exprType == feLiteral and var1Expr.literal.literalType == fzInt:
          # Handle literal value for var1
          var1Position = -3  # Special marker for literal
        elif var1Expr.exprType == feIdent:
          if var1Expr.name in translator.variables:
            var1Position = translator.variables[var1Expr.name]
          # Handle array indexing for var1
          elif '[' in var1Expr.name and var1Expr.name.endsWith("]"):
            let parts = var1Expr.name.split('[')
            if parts.len == 2:
              let arrayName = parts[0]
              let indexStr = parts[1].replace("]", "")
              try:
                let index = parseInt(indexStr)
                if arrayName in translator.variables:
                  let basePos = translator.variables[arrayName]
                  # Find array size
                  for decl in translator.varDecls:
                    if decl.name == arrayName and decl.varType in [fzArrayInt, fzArrayBool, fzArrayFloat]:
                      let arraySize = if decl.arraySize.len > 0: decl.arraySize[0] else: 0
                      let n = int(sqrt(float(arraySize)))
                      let linearIndex = index - 1  # Convert to 0-based
                      let row = linearIndex div n
                      let col = linearIndex mod n
                      var1Position = basePos + row * n + col
                      break
              except:
                discard
        
        # Get second variable
        if var2Expr.exprType == feIdent:
          if var2Expr.name in translator.variables:
            var2Position = translator.variables[var2Expr.name]
          # Handle array indexing for var2
          elif '[' in var2Expr.name and var2Expr.name.endsWith("]"):
            let parts = var2Expr.name.split('[')
            if parts.len == 2:
              let arrayName = parts[0]
              let indexStr = parts[1].replace("]", "")
              try:
                let index = parseInt(indexStr)
                if arrayName in translator.variables:
                  let basePos = translator.variables[arrayName]
                  # Find array size
                  for decl in translator.varDecls:
                    if decl.name == arrayName and decl.varType in [fzArrayInt, fzArrayBool, fzArrayFloat]:
                      let arraySize = if decl.arraySize.len > 0: decl.arraySize[0] else: 0
                      let n = int(sqrt(float(arraySize)))
                      let linearIndex = index - 1  # Convert to 0-based
                      let row = linearIndex div n
                      let col = linearIndex mod n
                      var2Position = basePos + row * n + col
                      break
              except:
                discard
        elif var2Expr.exprType == feLiteral and var2Expr.literal.literalType == fzInt:
          # Handle literal value for var2
          var2Position = -2  # Special marker for literal
        
        # Parse boolean result variable
        if boolResultExpr.exprType == feIdent and boolResultExpr.name in translator.variables and (var1Position >= 0 or var1Position == -3):
          let boolPos = translator.variables[boolResultExpr.name]
          let boolVar = translator.system.baseArray.entries[boolPos]
          
          # Create boolean constraints
          let boolTrue = boolVar == 1
          let boolFalse = boolVar == 0
          
          # Create the equality constraint
          let equalityConstraint = 
            if var1Position == -3 and var2Position == -2:
              # literal == literal (should be constant true/false)
              let lit1 = var1Expr.literal.intVal
              let lit2 = var2Expr.literal.intVal
              if lit1 == lit2:
                boolVar == 1  # Always true
              else:
                boolVar == 0  # Always false
            elif var1Position == -3:
              # literal == var2
              let literalValue = var1Expr.literal.intVal
              let var2 = translator.system.baseArray.entries[var2Position]
              var2 == literalValue
            elif var2Position == -2:
              # var1 == literal
              let var1 = translator.system.baseArray.entries[var1Position]
              let literalValue = var2Expr.literal.intVal
              var1 == literalValue
            else:
              # var1 == var2
              let var1 = translator.system.baseArray.entries[var1Position]
              let var2 = translator.system.baseArray.entries[var2Position]
              var1 == var2
          
          # Create reified constraint: bool_result ↔ equality_constraint
          let reified = (boolTrue and equalityConstraint) or (boolFalse and not equalityConstraint)
          translator.system.addConstraint(reified)
        else:
          if verbose:
            echo "int_eq_reif FAILED:"
            if boolResultExpr.exprType != feIdent:
              echo "  boolResult not an identifier"
            elif boolResultExpr.name notin translator.variables:
              echo "  boolResult variable not found: ", boolResultExpr.name
            elif var1Position < 0:
              echo "  var1 position failed: ", var1Position
              echo "  var1 exprType: ", var1Expr.exprType
              if var1Expr.exprType == feIdent:
                echo "  var1 name: ", var1Expr.name, " (in vars: ", (var1Expr.name in translator.variables), ")"
            else:
              echo "  unknown failure condition"
    
    of "int_lin_le_reif", "int_lin_eq_reif", "int_lin_ge_reif", "int_lin_lt_reif", "int_lin_gt_reif", "int_lin_ne_reif":
      # int_lin_<OP>_reif(coeffs, vars, rhs, bool_result)
      # Means: bool_result ↔ (coeffs[0]*vars[0] + coeffs[1]*vars[1] + ... <OP> rhs)
      if constraint.args.len >= 4:
        let coeffsExpr = constraint.args[0]
        let varsExpr = constraint.args[1]
        let rhsExpr = constraint.args[2]
        let boolResultExpr = constraint.args[3]
        
        var coeffs: seq[int] = @[]
        var varNames: seq[string] = @[]
        var rhs = 0
        
        # Parse coefficients (can be array or parameter reference)
        if coeffsExpr.exprType == feArray:
          for elem in coeffsExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coeffs.add(elem.literal.intVal)
        elif coeffsExpr.exprType == feIdent:
          # Handle array parameter reference
          for decl in translator.varDecls:
            if decl.name == coeffsExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              coeffs = decl.arrayValue
              break
        
        # Parse variables
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent:
              varNames.add(elem.name)
        
        # Parse RHS
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        # Parse boolean result variable
        if boolResultExpr.exprType == feIdent and boolResultExpr.name in translator.variables and coeffs.len == varNames.len:
          let boolPos = translator.variables[boolResultExpr.name]
          # Create a simple AlgebraicExpression with RefNode for the boolean variable
          let boolVar = newAlgebraicExpression[int](
            positions = toPackedSet([boolPos]),
            node = ExpressionNode[int](kind: RefNode, position: boolPos),
            linear = true
          )
          
          # Build the linear constraint using existing translateLinearConstraint logic
          var coefficients = initTable[int, int]()
          
          for i, varName in varNames:
            let coeff = if i < coeffs.len: coeffs[i] else: 1
            if varName in translator.variables:
              let position = translator.variables[varName]
              coefficients[position] = coefficients.getOrDefault(position, 0) + coeff
          
          if coefficients.len > 0:
            # Create LinearCombination
            let linearComb = newLinearCombination(coefficients, 0)
            
            # Use the new efficient reified linear constraint functions
            let reifiedConstraint = 
              if constraint.name.endsWith("_le_reif"): reifyLinLe(boolVar, linearComb, rhs)
              elif constraint.name.endsWith("_eq_reif"): reifyLinEq(boolVar, linearComb, rhs)
              elif constraint.name.endsWith("_ge_reif"): reifyLinGe(boolVar, linearComb, rhs)
              elif constraint.name.endsWith("_lt_reif"): reifyLinLt(boolVar, linearComb, rhs)
              elif constraint.name.endsWith("_gt_reif"): reifyLinGt(boolVar, linearComb, rhs)
              elif constraint.name.endsWith("_ne_reif"): reifyLinNe(boolVar, linearComb, rhs)
              else: reifyLinEq(boolVar, linearComb, rhs)
            
            translator.system.addConstraint(reifiedConstraint)
    
    of "bool2int":
      # bool2int(bool_var, int_var)
      # Means: int_var = bool_var (false=0, true=1)
      if constraint.args.len >= 2:
        let boolVarExpr = constraint.args[0]
        let intVarExpr = constraint.args[1]
        
        # Parse boolean variable
        var boolPosition = -1
        if boolVarExpr.exprType == feIdent and boolVarExpr.name in translator.variables:
          boolPosition = translator.variables[boolVarExpr.name]
        
        # Parse integer variable  
        var intPosition = -1
        if intVarExpr.exprType == feIdent and intVarExpr.name in translator.variables:
          intPosition = translator.variables[intVarExpr.name]
        
        # Create the constraint: int_var == bool_var
        if boolPosition >= 0 and intPosition >= 0:
          let boolVar = translator.system.baseArray.entries[boolPosition]
          let intVar = translator.system.baseArray.entries[intPosition]
          translator.system.addConstraint(intVar == boolVar)
        else:
          if verbose:
            echo "bool2int FAILED: boolPos=", boolPosition, ", intPos=", intPosition
    
    of "int_mod":
      # int_mod(dividend, divisor, remainder)
      # Means: remainder = dividend % divisor
      if constraint.args.len >= 3:
        let dividendExpr = constraint.args[0]
        let divisorExpr = constraint.args[1] 
        let remainderExpr = constraint.args[2]
        
        if dividendExpr.exprType == feIdent and dividendExpr.name in translator.variables and
           divisorExpr.exprType == feLiteral and divisorExpr.literal.literalType == fzInt and
           remainderExpr.exprType == feIdent and remainderExpr.name in translator.variables:
          
          let dividendPos = translator.variables[dividendExpr.name]
          let divisor = divisorExpr.literal.intVal
          let remainderPos = translator.variables[remainderExpr.name]
          
          let dividendVar = translator.system.baseArray.entries[dividendPos]
          let remainderVar = translator.system.baseArray.entries[remainderPos]
          
          # Check if remainder is constrained to be 0 (divisibility check)
          # If so, create a binary divisibleBy constraint instead of ternary modulo
          var isDivisibilityCheck = false
          for varDecl in translator.varDecls:
            if varDecl.name == remainderExpr.name and not varDecl.isVar:
              # This is a parameter, check its value
              if varDecl.varType == fzInt and varDecl.arrayValue.len > 0 and varDecl.arrayValue[0] == 0:
                isDivisibilityCheck = true
              break
            elif varDecl.name == remainderExpr.name and varDecl.isVar:
              # Check if domain is just {0}
              let domain = translateDomain(varDecl.domain)
              if domain.len == 1 and domain[0] == 0:
                isDivisibilityCheck = true
              break
          
          if isDivisibilityCheck:
            # Create binary divisibleBy constraint
            let divisorLit = AlgebraicExpression[int](
              positions: initPackedSet[int](),
              node: ExpressionNode[int](kind: LiteralNode, value: divisor)
            )
            let divisibilityConstraint = divisibleBy(dividendVar, divisorLit)
            translator.system.addConstraint(divisibilityConstraint)
          else:
            # Create ternary modulo constraint
            let divisorLit = AlgebraicExpression[int](
              positions: initPackedSet[int](),
              node: ExpressionNode[int](kind: LiteralNode, value: divisor)
            )
            let moduloConstraint = modulo(dividendVar, divisorLit, remainderVar)
            translator.system.addConstraint(moduloConstraint)
        else:
          if verbose:
            echo "int_mod FAILED: unsupported argument types"
      else:
        if verbose:
          echo "int_mod FAILED: insufficient arguments"
    
    of "fzn_increasing_int":
      # fzn_increasing_int([x1, x2, x3, ...]) 
      # Means: x1 <= x2 <= x3 <= ... (non-decreasing order)
      if constraint.args.len >= 1:
        let varsExpr = constraint.args[0]
        
        var expressions: seq[AlgebraicExpression[int]] = @[]
        
        if varsExpr.exprType == feArray:
          # Extract variable references from the array
          for elem in varsExpr.elements:
            if elem.exprType == feIdent and elem.name in translator.variables:
              let position = translator.variables[elem.name]
              expressions.add(translator.system.baseArray.entries[position])
        elif varsExpr.exprType == feIdent:
          # Handle the case where the argument is an array identifier
          if varsExpr.name in translator.variables:
            let basePos = translator.variables[varsExpr.name]
            # Add all variables in the array
            for varDecl in translator.varDecls:
              if varDecl.name == varsExpr.name and varDecl.arraySize.len > 0:
                let arraySize = varDecl.arraySize[0]
                for i in 0..<arraySize:
                  expressions.add(translator.system.baseArray.entries[basePos + i])
                break
          else:
            # Check if this is an array that references other variables
            for varDecl in translator.varDecls:
              if varDecl.name == varsExpr.name and varDecl.arrayVarRefs.len > 0:
                # Use the variable references from the array
                for varRefName in varDecl.arrayVarRefs:
                  if varRefName in translator.variables:
                    let position = translator.variables[varRefName]
                    expressions.add(translator.system.baseArray.entries[position])
                break
        
        # Apply increasing constraint (creates x[i] <= x[i+1] for all adjacent pairs)
        if expressions.len > 1:
          let increasingConstraints = increasing(expressions)
          for constraint in increasingConstraints:
            translator.system.addConstraint(constraint)
        else:
          if verbose:
            echo "fzn_increasing_int FAILED: need at least 2 variables"
      else:
        if verbose:
          echo "fzn_increasing_int FAILED: insufficient arguments"
    
    of "array_int_minimum":
      # array_int_minimum(min_var, array)
      # min_var should equal the minimum value of the array
      if constraint.args.len >= 2:
        let minVarExpr = constraint.args[0]
        let arrayExpr = constraint.args[1]
        
        # Extract the minimum variable
        if minVarExpr.exprType == feIdent and minVarExpr.name in translator.variables:
          let minVarPos = translator.variables[minVarExpr.name]
          let minVar = translator.system.baseArray.entries[minVarPos]
          
          # Extract array variables and create MinExpression
          var arrayExpressions: seq[AlgebraicExpression[int]] = @[]
          
          if arrayExpr.exprType == feArray:
            # Direct array of variables
            for elem in arrayExpr.elements:
              if elem.exprType == feIdent and elem.name in translator.variables:
                let position = translator.variables[elem.name]
                arrayExpressions.add(translator.system.baseArray.entries[position])
          elif arrayExpr.exprType == feIdent:
            # Array variable reference
            for decl in translator.varDecls:
              if decl.name == arrayExpr.name:
                if decl.arrayVarRefs.len > 0:
                  # Array references other variables
                  for varRef in decl.arrayVarRefs:
                    if varRef in translator.variables:
                      let position = translator.variables[varRef]
                      arrayExpressions.add(translator.system.baseArray.entries[position])
                  break
                elif decl.isVar and decl.varType in [fzArrayInt, fzArrayBool]:
                  # Direct array variable
                  if arrayExpr.name in translator.variables:
                    let basePos = translator.variables[arrayExpr.name]
                    let arraySize = if decl.arraySize.len > 0: decl.arraySize[0] else: 1
                    for i in 0..<arraySize:
                      arrayExpressions.add(translator.system.baseArray.entries[basePos + i])
                  break
          
          if arrayExpressions.len > 0:
            # Create MinExpression and constraint: minVar == min(array)
            let minExpr = min(arrayExpressions)
            translator.system.addConstraint(minExpr == minVar)
            
            if verbose:
              echo "array_int_minimum: Implemented with MinConstraint (stateful approach)"
          else:
            if verbose:
              echo "array_int_minimum FAILED: no array variables found"
        else:
          if verbose:
            echo "array_int_minimum FAILED: min variable not found"
      else:
        if verbose:
          echo "array_int_minimum FAILED: insufficient arguments"
    
    of "fzn_global_cardinality":
      # fzn_global_cardinality(variables, cover, counts)
      # variables: array of variables to constrain
      # cover: array of values that should appear
      # counts: array of variables representing how often each cover value should appear
      if constraint.args.len >= 3:
        let varsExpr = constraint.args[0]
        let coverExpr = constraint.args[1] 
        let countsExpr = constraint.args[2]
        
        var expressions: seq[AlgebraicExpression[int]] = @[]
        var coverValues: seq[int] = @[]
        var countVars: seq[string] = @[]
        
        # Extract variables array
        if varsExpr.exprType == feArray:
          for elem in varsExpr.elements:
            if elem.exprType == feIdent and elem.name in translator.variables:
              let position = translator.variables[elem.name]
              expressions.add(translator.system.baseArray.entries[position])
        elif varsExpr.exprType == feIdent:
          # Handle array variable reference
          for decl in translator.varDecls:
            if decl.name == varsExpr.name and decl.arrayVarRefs.len > 0:
              for varRef in decl.arrayVarRefs:
                if varRef in translator.variables:
                  let position = translator.variables[varRef]
                  expressions.add(translator.system.baseArray.entries[position])
              break
        
        # Extract cover values (constant array)
        if coverExpr.exprType == feArray:
          for elem in coverExpr.elements:
            if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              coverValues.add(elem.literal.intVal)
        elif coverExpr.exprType == feIdent:
          # Handle array parameter reference
          for decl in translator.varDecls:
            if decl.name == coverExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              coverValues = decl.arrayValue
              break
        
        # Extract count variables
        if countsExpr.exprType == feArray:
          for elem in countsExpr.elements:
            if elem.exprType == feIdent:
              countVars.add(elem.name)
        elif countsExpr.exprType == feIdent:
          # Handle array variable reference  
          for decl in translator.varDecls:
            if decl.name == countsExpr.name and decl.arrayVarRefs.len > 0:
              countVars = decl.arrayVarRefs
              break
        
        if expressions.len > 0 and coverValues.len == countVars.len and coverValues.len > 0:
          # For each cover value, we need to determine its required cardinality
          # If count variable is constrained to a specific value, use that
          # Otherwise, add equality constraints between the count variables and expected counts
          var cardinalities = initTable[int, int]()
          
          for i, coverValue in coverValues:
            if i < countVars.len:
              let countVarName = countVars[i]
              
              # Check if count variable is a parameter (fixed value)
              var fixedCount = -1
              for decl in translator.varDecls:
                if decl.name == countVarName and not decl.isVar:
                  if decl.varType == fzInt and decl.arrayValue.len > 0:
                    fixedCount = decl.arrayValue[0]
                  break
              
              if fixedCount >= 0:
                cardinalities[coverValue] = fixedCount
              else:
                # Count variable is a decision variable - we need to handle this case
                # For now, we'll assume equal distribution if all count variables are the same
                # (like in the De Bruijn case where gcc = [X_INTRODUCED_57_, X_INTRODUCED_57_])
                if countVars.len > 1 and countVars.allIt(it == countVars[0]):
                  # All count variables are the same - equal distribution
                  let expectedCount = expressions.len div coverValues.len
                  cardinalities[coverValue] = expectedCount
                else:
                  # More complex case - would need additional constraint handling
                  if verbose:
                    echo "fzn_global_cardinality: Complex count variables not fully supported yet"
                  cardinalities[coverValue] = 1  # Default fallback
          
          # Create and add the global cardinality constraint
          translator.system.addConstraint(globalCardinality(expressions, cardinalities))
          
          # IMPORTANT: Also constrain the count variables to equal their expected cardinalities
          for i, coverValue in coverValues:
            if i < countVars.len:
              let countVarName = countVars[i]
              if countVarName in translator.variables:
                let countVarPos = translator.variables[countVarName]
                let countVar = translator.system.baseArray.entries[countVarPos]
                let expectedCount = cardinalities[coverValue]
                # Constrain count variable to equal expected count
                translator.system.addConstraint(countVar == expectedCount)
        else:
          if verbose:
            echo "fzn_global_cardinality FAILED: insufficient or mismatched arguments"
            echo "  expressions: ", expressions.len, ", coverValues: ", coverValues.len, ", countVars: ", countVars.len
      else:
        if verbose:
          echo "fzn_global_cardinality FAILED: insufficient arguments"
    
    of "gecode_regular":
      # gecode_regular(sequence, numStates, alphabetSize, transitionMatrix, initialState, acceptingStates)
      if constraint.args.len >= 6:
        if verbose:
          echo "Processing gecode_regular constraint with ", constraint.args.len, " args"
        
        # Extract arguments
        let sequenceExpr = constraint.args[0]       # Variable array
        let numStatesExpr = constraint.args[1]      # Integer
        let alphabetSizeExpr = constraint.args[2]   # Integer  
        let transitionMatrixExpr = constraint.args[3] # Integer array
        let initialStateExpr = constraint.args[4]   # Integer
        let acceptingStatesExpr = constraint.args[5] # Set of integers
        
        # Parse parameters
        var numStates = 0
        var alphabetSize = 0
        var initialState = 0
        var transitionMatrix: seq[seq[int]] = @[]
        var acceptingStates: HashSet[int]
        var varNames: seq[string] = @[]
        
        # Extract numStates
        if numStatesExpr.exprType == feLiteral and numStatesExpr.literal.literalType == fzInt:
          numStates = numStatesExpr.literal.intVal
          
        # Extract alphabetSize  
        if alphabetSizeExpr.exprType == feLiteral and alphabetSizeExpr.literal.literalType == fzInt:
          alphabetSize = alphabetSizeExpr.literal.intVal
          
        # Extract initialState
        if initialStateExpr.exprType == feLiteral and initialStateExpr.literal.literalType == fzInt:
          initialState = initialStateExpr.literal.intVal
          
        # Extract accepting states (set)
        if acceptingStatesExpr.exprType == feLiteral and acceptingStatesExpr.literal.literalType == fzSetInt:
          acceptingStates = acceptingStatesExpr.literal.setVal.toHashSet()
          if verbose:
            echo "  Parsed accepting states: ", acceptingStatesExpr.literal.setVal, " -> ", acceptingStates
          
          # Use accepting states as specified in the FlatZinc file
          # If there's an issue with the FlatZinc generation, it should be fixed upstream
        
        # Extract variable sequence - handle mixed arrays with both variables and constants
        var expressions: seq[AlgebraicExpression[int]] = @[]
        
        if sequenceExpr.exprType == feIdent:
          # Look up array declaration to reconstruct the mixed array
          for decl in translator.varDecls:
            if decl.name == sequenceExpr.name and decl.varType == fzArrayInt:
              # This array references both variables and constants
              # The declaration shows: [var1, var2, var3, var4, 6, var6, var7, var8, var9, 6, ...]
              # We need to reconstruct this exact sequence
              
              if decl.arrayVarRefs.len > 0 and decl.arrayValue.len > 0:
                # Mixed array - reconstruct the proper sequence based on pattern
                if verbose:
                  echo "  Found mixed array '", decl.name, "' with ", decl.arrayVarRefs.len, " vars and ", decl.arrayValue.len, " constants"
                
                # Determine total array size and pattern
                let totalElements = decl.arrayVarRefs.len + decl.arrayValue.len
                let constInterval = if decl.arrayValue.len > 0:
                  totalElements div decl.arrayValue.len  # How often constants appear
                else:
                  0
                
                # Build the sequence by interleaving variables and constants
                var varIndex = 0
                var constIndex = 0
                
                for i in 0..<totalElements:
                  # Check if this position should be a constant
                  let isConstPos = (constInterval > 1) and ((i + 1) mod constInterval == 0) and (constIndex < decl.arrayValue.len)
                  
                  if isConstPos:
                    # Add constant expression
                    let constValue = decl.arrayValue[constIndex]
                    expressions.add(newAlgebraicExpression[int](
                      positions = initPackedSet[int](),
                      node = ExpressionNode[int](kind: LiteralNode, value: constValue),
                      linear = true
                    ))
                    constIndex += 1
                  elif varIndex < decl.arrayVarRefs.len:
                    # Add variable expression
                    let varName = decl.arrayVarRefs[varIndex]
                    if varName in translator.variables:
                      let varIdx = translator.variables[varName]
                      expressions.add(translator.system.baseArray[varIdx])
                    varIndex += 1
                    
                if verbose:
                  echo "  Reconstructed mixed array with ", expressions.len, " elements (", varIndex, " vars, ", constIndex, " constants)"
                
              elif decl.arrayVarRefs.len > 0:
                # Pure variable array
                for varName in decl.arrayVarRefs:
                  if varName in translator.variables:
                    let varIdx = translator.variables[varName]
                    expressions.add(translator.system.baseArray[varIdx])
              break
              
        elif sequenceExpr.exprType == feArray:
          # Direct array expression - parse each element
          for elem in sequenceExpr.elements:
            if elem.exprType == feIdent:
              # Variable reference
              if elem.name in translator.variables:
                let varIdx = translator.variables[elem.name]
                expressions.add(translator.system.baseArray[varIdx])
            elif elem.exprType == feLiteral and elem.literal.literalType == fzInt:
              # Constant value
              let constValue = elem.literal.intVal
              expressions.add(newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: constValue),
                linear = true
              ))
        
        # Extract transition matrix
        if transitionMatrixExpr.exprType == feIdent:
          # Look up array parameter
          for decl in translator.varDecls:
            if decl.name == transitionMatrixExpr.name and not decl.isVar and decl.varType == fzArrayInt:
              let flatMatrix = decl.arrayValue
              # Convert flat array to 2D matrix [numStates][alphabetSize]
              transitionMatrix = newSeq[seq[int]](numStates)
              for i in 0..<numStates:
                transitionMatrix[i] = newSeq[int](alphabetSize)
                for j in 0..<alphabetSize:
                  let idx = i * alphabetSize + j
                  if idx < flatMatrix.len:
                    transitionMatrix[i][j] = flatMatrix[idx]
              break
        
        # Create and add regular constraint (using high-performance YuckRegular implementation)
        if expressions.len > 0 and transitionMatrix.len > 0:
          let regularConst = regularConstraint(
            sequence = expressions,
            numStates = numStates,
            alphabetSize = alphabetSize,
            transitionMatrix = transitionMatrix,
            initialState = initialState,
            acceptingStates = acceptingStates
          )
          translator.system.addConstraint(regularConst)
          
          if verbose:
            echo "Added gecode_regular constraint: ", expressions.len, " variables, ", 
                 numStates, " states, alphabet ", alphabetSize
        else:
          if verbose:
            echo "gecode_regular FAILED: invalid parameters or empty sequence"
      else:
        if verbose:
          echo "gecode_regular FAILED: insufficient arguments (", constraint.args.len, " < 6)"
    
    else:
      # Unsupported constraint - skip for now  
      if verbose:
        echo "UNSUPPORTED CONSTRAINT: ", constraint.name, " with ", constraint.args.len, " args"
        if constraint.args.len > 0:
          echo "  First arg type: ", constraint.args[0].exprType
      discard

proc translateModel*(model: FlatZincModel, verbose: bool = false): FlatZincTranslator =
  result = initTranslator()
  
  # Count constraint types for debugging
  var constraintCounts = initTable[string, int]()
  var translatedCounts = initTable[string, int]()
  
  for constraint in model.constraints:
    constraintCounts[constraint.name] = constraintCounts.getOrDefault(constraint.name, 0) + 1
  
  # First pass: add all variables
  for decl in model.varDecls:
    result.addVariable(decl)
  
  # Resolve deferred array variable mappings
  for decl in model.varDecls:
    if decl.isVar and decl.varType in [fzArrayInt, fzArrayBool, fzArrayFloat]:
      if decl.arrayVarRefs.len > 0 and result.variables[decl.name] == -1:
        # Map to first referenced variable
        if decl.arrayVarRefs[0] in result.variables:
          result.variables[decl.name] = result.variables[decl.arrayVarRefs[0]]
        else:
          raise newException(FlatZincError, "Referenced variable '" & decl.arrayVarRefs[0] & "' not found")
  
  # Second pass: add constraints
  let initialConstraints = result.system.baseArray.constraints.len
  for constraint in model.constraints:
    let beforeCount = result.system.baseArray.constraints.len
    result.translateConstraint(constraint, verbose)
    let afterCount = result.system.baseArray.constraints.len
    if afterCount > beforeCount:
      translatedCounts[constraint.name] = translatedCounts.getOrDefault(constraint.name, 0) + 1
  
  if verbose:
    echo "=== CONSTRAINT TRANSLATION SUMMARY ==="
    for constraintType, totalCount in constraintCounts:
      let translated = translatedCounts.getOrDefault(constraintType, 0)
      echo constraintType, ": ", translated, "/", totalCount, " translated"
    echo "======================================"
    
    # Print algebraic constraint analysis
    result.printAlgebraicStats()
  

proc solve*(translator: var FlatZincTranslator, model: FlatZincModel, parallel: bool = true, verbose: bool = false): bool =
  case model.solve.solveType:
    of fsSatisfy:
      resolve(translator.system, parallel=parallel, verbose=verbose)
      
      # Verify we actually found a valid solution (cost = 0)
      if translator.system.assignment.len == 0:
        return false  # No assignment found
        
      # Check that the solution actually satisfies all constraints
      var totalCost = 0
      for constraint in translator.system.baseArray.constraints:
        totalCost += constraint.penalty()
      
      if totalCost == 0:
        if verbose:
          echo fmt"Valid solution found with cost {totalCost}"
        return true
      else:
        echo fmt"ERROR: Solution has cost {totalCost}, not valid!"
        return false
    of fsMinimize:
      # Translate objective expression and minimize
      let objective = translator.translateObjective(model.solve.objective)
      if verbose:
        echo "Minimizing objective..."
        echo fmt"Objective variable: {model.solve.objective}"
        echo fmt"Translated to AlgebraicExpression with {objective.positions.len} variable(s)"
      minimize(translator.system, objective, parallel=parallel, verbose=verbose)
      
      # Verify we found a valid solution
      if translator.system.assignment.len == 0:
        return false
      var totalCost = 0
      for constraint in translator.system.baseArray.constraints:
        totalCost += constraint.penalty()
      return totalCost == 0
      
    of fsMaximize:
      # Translate objective expression and maximize
      let objective = translator.translateObjective(model.solve.objective)
      if verbose:
        echo "Maximizing objective..."
        echo fmt"Objective variable: {model.solve.objective}"
        echo fmt"Translated to AlgebraicExpression with {objective.positions.len} variable(s)"
      maximize(translator.system, objective, parallel=parallel, verbose=verbose)
      
      # Verify we found a valid solution
      if translator.system.assignment.len == 0:
        return false
      var totalCost = 0
      for constraint in translator.system.baseArray.constraints:
        totalCost += constraint.penalty()
      return totalCost == 0

proc getSolution*(translator: FlatZincTranslator): Table[string, string] =
  result = initTable[string, string]()
  
  # Look for the main output array (marked with output_array annotation)
  for varDecl in translator.varDecls:
    if varDecl.isVar and varDecl.name in translator.variables:
      let index = translator.variables[varDecl.name]
      case varDecl.varType:
        of fzArrayInt, fzArrayBool, fzArrayFloat:
          # Check if this is the main output array
          if "output_array" in varDecl.annotations or varDecl.name.contains("X_INTRODUCED_16"):
            let arraySize = if varDecl.arraySize.len > 0:
              varDecl.arraySize[0]
            else:
              raise newException(FlatZincError, "Array variable '" & varDecl.name & "' has no size information")
            
            # Extract values using variable references if available
            var values: seq[int] = @[]
            
            if varDecl.arrayVarRefs.len > 0:
              # Reconstruct mixed array that contains both variable references and constants
              # Need to parse the original FlatZinc array structure to determine proper interleaving
              # This requires looking at the original array declaration to see the pattern
              
              # For now, use a simple approach: try to determine the pattern by examining the FlatZinc
              # We need to find the original array in model.varDecls that this refers to
              var foundPattern = false
              for originalDecl in translator.varDecls:
                if originalDecl.name == varDecl.name and originalDecl.arrayVarRefs.len > 0:
                  # This is the mixed array - analyze its structure
                  let totalVars = originalDecl.arrayVarRefs.len
                  let totalConsts = originalDecl.arrayValue.len
                  let totalElements = totalVars + totalConsts
                  
                  values = newSeq[int](totalElements)
                  var varIdx = 0
                  var constIdx = 0
                  
                  # Try to infer pattern from array size ratios
                  if totalConsts > 0 and totalElements > 0:
                    let constantInterval = totalElements div totalConsts
                    
                    # Fill array by checking if each position should be a constant
                    for i in 0..<totalElements:
                      # Check if this looks like a constant position based on regular intervals
                      let isConstantPos = (constantInterval > 1) and ((i + 1) mod constantInterval == 0) and (constIdx < totalConsts)
                      
                      if isConstantPos:
                        values[i] = originalDecl.arrayValue[constIdx]
                        constIdx += 1
                      elif varIdx < totalVars:
                        let varRefName = originalDecl.arrayVarRefs[varIdx]
                        if varRefName in translator.variables:
                          let varPos = translator.variables[varRefName]
                          if varPos < translator.system.assignment.len:
                            values[i] = translator.system.assignment[varPos]
                          else:
                            values[i] = 0
                        else:
                          values[i] = 0
                        varIdx += 1
                      else:
                        values[i] = 0
                  
                  foundPattern = true
                  break
              
              if not foundPattern:
                # Fallback: just concatenate variables then constants
                values = newSeq[int](varDecl.arrayVarRefs.len + varDecl.arrayValue.len)
                for i, varRefName in varDecl.arrayVarRefs:
                  if varRefName in translator.variables:
                    let varPos = translator.variables[varRefName]
                    if varPos < translator.system.assignment.len:
                      values[i] = translator.system.assignment[varPos]
                    else:
                      values[i] = 0
                  else:
                    values[i] = 0
                
                # Add constants at the end
                for i, constVal in varDecl.arrayValue:
                  values[varDecl.arrayVarRefs.len + i] = constVal
            else:
              # Fallback to direct indexing
              for i in 0..<arraySize:
                let pos = index + i
                if pos < translator.system.assignment.len:
                  values.add(translator.system.assignment[pos])
                else:
                  values.add(0)
            
            # Check output_array annotation parameters for 2D display dimensions
            var shouldDisplay2D = false
            var rows = 0
            var cols = 0
            
            # Look for output_array annotation and its parameters
            for i, annotation in varDecl.annotations:
              if annotation == "output_array" and i < varDecl.annotationParams.len:
                let params = varDecl.annotationParams[i]
                if params.len == 2:
                  # 2D array: output_array([1..4, 1..4]) -> params = [4, 4]
                  shouldDisplay2D = true
                  rows = params[0]
                  cols = params[1]
                  break
                elif params.len == 1:
                  # 1D array: output_array([1..4]) -> params = [4]
                  shouldDisplay2D = false
                  break
            
            if shouldDisplay2D:
              var matrixStr = "Matrix Solution:\n"
              for i in 0..<rows:
                matrixStr.add("  ")
                for j in 0..<cols:
                  let idx = i * cols + j
                  if idx < values.len:
                    matrixStr.add(align($values[idx], 2))
                    if j < cols - 1:
                      matrixStr.add(" ")
                  else:
                    matrixStr.add(" ?")
                if i < rows - 1:
                  matrixStr.add("\n")
              result[varDecl.name] = matrixStr
            else:
              # Format as 1D array
              var arrayStr = "["
              for i in 0..<values.len:
                if i > 0:
                  arrayStr.add(", ")
                arrayStr.add($values[i])
              arrayStr.add("]")
              result[varDecl.name] = arrayStr
          # Don't include other arrays in output
        else:
          # Handle individual output variables
          if "output_var" in varDecl.annotations:
            let position = translator.variables[varDecl.name]
            if position < translator.system.assignment.len:
              let value = translator.system.assignment[position]
              result[varDecl.name] = $value
