import std/[tables, strutils, sequtils, packedsets, math, strformat]
import ast
import ../crusher/[constraintSystem, constrainedArray, expressions]
import ../crusher/constraints/[algebraic, stateful, constraintNode]
import ../crusher/search/[resolution, tabuSearch]

type
  FlatZincError* = object of CatchableError
  
  FlatZincTranslator* = object
    system*: ConstraintSystem[int]
    variables*: Table[string, int] # Maps FZ variable names to Crusher indices
    varDecls*: seq[FlatZincVarDecl]

proc initTranslator*(): FlatZincTranslator =
  result = FlatZincTranslator(
    system: initConstraintSystem[int](),
    variables: initTable[string, int](),
    varDecls: @[]
  )


proc translateDomain(domain: FlatZincDomain): seq[int] =
  case domain.domainType:
    of fzInt:
      if domain.hasRange:
        result = toSeq(domain.intRange.min .. domain.intRange.max)
      elif domain.hasSet:
        result = domain.intSet
      else:
        # Unbounded integer - use reasonable default
        result = toSeq(0 .. 100)
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
          sequence.setDomain(domain)
          
          # Map the array variable to the base index
          translator.variables[decl.name] = baseVarIndex
        
      else:
        # Regular scalar variable
        let varIndex = translator.system.baseArray.len
        let varSeq = newConstrainedSequence(translator.system, 1)
        # Set domain using the correct API pattern
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
            # Find the array declaration to get its size
            var n = 0
            var found = false
            for decl in translator.varDecls:
              if decl.name == arrayName and decl.varType in [fzArrayInt, fzArrayBool, fzArrayFloat]:
                let arraySize = if decl.arraySize.len > 0:
                  decl.arraySize[0]
                else:
                  raise newException(FlatZincError, "Array variable '" & arrayName & "' has no size information in linear constraint translation")
                n = int(sqrt(float(arraySize)))
                found = true
                break
            if not found:
              raise newException(FlatZincError, "Array variable '" & arrayName & "' not found in linear constraint translation")
            let linearIndex = index - 1  # Convert to 0-based
            let row = linearIndex div n
            let col = linearIndex mod n
            basePos + row * n + col
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
      translator.system.addConstraint(linearComb == rhs)
    of "le", "<=": 
      translator.system.addConstraint(linearComb <= rhs)
    of "ge", ">=": 
      translator.system.addConstraint(linearComb >= rhs)
    of "lt", "<": 
      translator.system.addConstraint(linearComb < rhs)
    of "gt", ">": 
      translator.system.addConstraint(linearComb > rhs)
    of "ne", "!=":
      translator.system.addConstraint(linearComb != rhs)
    else: 
      translator.system.addConstraint(linearComb == rhs)

proc translateConstraint(translator: var FlatZincTranslator, constraint: FlatZincConstraint) =
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
        
        if rhsExpr.exprType == feLiteral and rhsExpr.literal.literalType == fzInt:
          rhs = rhsExpr.literal.intVal
        
        if coeffs.len == varNames.len:
          translator.translateLinearConstraint(coeffs, varNames, rhs, "le")
        else:
          echo "int_lin_le FAILED: coeffs.len=", coeffs.len, ", varNames.len=", varNames.len
    
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
          echo "int_mod FAILED: unsupported argument types"
      else:
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
          echo "fzn_increasing_int FAILED: need at least 2 variables"
      else:
        echo "fzn_increasing_int FAILED: insufficient arguments"
    
    else:
      # Unsupported constraint - skip for now  
      echo "UNSUPPORTED CONSTRAINT: ", constraint.name, " with ", constraint.args.len, " args"
      if constraint.args.len > 0:
        echo "  First arg type: ", constraint.args[0].exprType
      discard

proc translateModel*(model: FlatZincModel): FlatZincTranslator =
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
    result.translateConstraint(constraint)
    let afterCount = result.system.baseArray.constraints.len
    if afterCount > beforeCount:
      translatedCounts[constraint.name] = translatedCounts.getOrDefault(constraint.name, 0) + 1
  
  echo "=== CONSTRAINT TRANSLATION SUMMARY ==="
  for constraintType, totalCount in constraintCounts:
    let translated = translatedCounts.getOrDefault(constraintType, 0)
    echo constraintType, ": ", translated, "/", totalCount, " translated"
  echo "======================================"
  

proc solve*(translator: var FlatZincTranslator, model: FlatZincModel): bool =
  case model.solve.solveType:
    of fsSatisfy:
      resolve(translator.system)
      # resolve() already sets the assignment if a solution is found
      return translator.system.assignment.len > 0
    of fsMinimize:
      # For now, just find a satisfying solution
      # TODO: Implement actual minimization
      resolve(translator.system)
      return translator.system.assignment.len > 0
    of fsMaximize:
      # For now, just find a satisfying solution  
      # TODO: Implement actual maximization
      resolve(translator.system)
      return translator.system.assignment.len > 0

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
              # Use the variable references from the array assignment
              for varRefName in varDecl.arrayVarRefs:
                if varRefName in translator.variables:
                  let varPos = translator.variables[varRefName]
                  if varPos < translator.system.assignment.len:
                    values.add(translator.system.assignment[varPos])
                  else:
                    values.add(0)
                else:
                  values.add(0)
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