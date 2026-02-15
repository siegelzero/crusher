## FlatZinc translator - maps FznModel to ConstraintSystem[int].

import std/[tables, sequtils, strutils, strformat, packedsets, sets]

import parser
import ../constraintSystem
import ../constrainedArray
import ../constraints/[stateful, countEq]
import ../expressions/[expressions, algebraic, sumExpression, minExpression, maxExpression]

type
  CountEqPattern* = object
    ## A detected count_eq pattern from int_lin_eq → bool2int → int_eq_reif chains
    linEqIdx*: int           # index of the int_lin_eq constraint
    countValue*: int         # the constant value being counted
    targetVarName*: string   # name of the target variable (the count)
    arrayVarNames*: seq[string]  # names of the array variables being counted over

  FznTranslator* = object
    sys*: ConstraintSystem[int]
    # Maps FZN variable name -> position in the ConstrainedArray
    varPositions*: Table[string, int]
    # Maps FZN parameter name -> constant int value
    paramValues*: Table[string, int]
    # Maps FZN array name -> list of positions (for variable arrays) or sentinel
    arrayPositions*: Table[string, seq[int]]
    # Maps FZN array name -> constant int values (for parameter arrays)
    arrayValues*: Table[string, seq[int]]
    # Tracks which variables have output_var annotation
    outputVars*: seq[string]
    # Tracks which arrays have output_array annotation, with their index ranges
    outputArrays*: seq[tuple[name: string, lo, hi: int]]
    # The model
    model*: FznModel
    # Objective expression position (for minimize/maximize)
    objectivePos*: int
    # Set of variable names that will be replaced by defining expressions
    definedVarNames*: HashSet[string]
    # Maps defined variable name -> defining AlgebraicExpression (for defines_var elimination)
    definedVarExprs*: Table[string, AlgebraicExpression[int]]
    # Set of constraint indices that are defining constraints (to skip during translation)
    definingConstraints*: PackedSet[int]
    # Maps array name -> element variable names (for resolving defined vars in arrays)
    arrayElementNames*: Table[string, seq[string]]
    # Detected count_eq patterns (mapped by int_lin_eq constraint index)
    countEqPatterns*: Table[int, CountEqPattern]

proc getExpr*(tr: FznTranslator, pos: int): AlgebraicExpression[int] {.inline.} =
  tr.sys.baseArray[pos]

proc resolveExprArg*(tr: FznTranslator, arg: FznExpr): AlgebraicExpression[int] =
  ## Resolves a FznExpr to an AlgebraicExpression.
  ## For identifiers: looks up variable position, or returns defining expression for defined vars.
  ## For int literals: creates a literal expression with no positions.
  ## For bool literals: true=1, false=0.
  case arg.kind
  of FznIdent:
    if arg.ident in tr.definedVarExprs:
      return tr.definedVarExprs[arg.ident]
    elif arg.ident in tr.varPositions:
      return tr.getExpr(tr.varPositions[arg.ident])
    elif arg.ident in tr.paramValues:
      let val = tr.paramValues[arg.ident]
      return newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: val),
        linear = true
      )
    else:
      raise newException(KeyError, &"Unknown identifier '{arg.ident}' in expression")
  of FznIntLit:
    return newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: arg.intVal),
      linear = true
    )
  of FznBoolLit:
    let val = if arg.boolVal: 1 else: 0
    return newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: val),
      linear = true
    )
  else:
    raise newException(ValueError, &"Cannot resolve {arg.kind} as expression")

proc resolveIntArg*(tr: FznTranslator, arg: FznExpr): int =
  ## Resolves a FznExpr that must be a constant integer.
  case arg.kind
  of FznIntLit:
    return arg.intVal
  of FznBoolLit:
    return if arg.boolVal: 1 else: 0
  of FznIdent:
    if arg.ident in tr.paramValues:
      return tr.paramValues[arg.ident]
    else:
      raise newException(KeyError, &"Expected constant, got variable '{arg.ident}'")
  else:
    raise newException(ValueError, &"Expected int constant, got {arg.kind}")

proc resolveIntArray*(tr: FznTranslator, arg: FznExpr): seq[int] =
  ## Resolves a FznExpr to a constant int array.
  case arg.kind
  of FznArrayLit:
    result = newSeq[int](arg.elems.len)
    for i, e in arg.elems:
      result[i] = tr.resolveIntArg(e)
  of FznIdent:
    if arg.ident in tr.arrayValues:
      return tr.arrayValues[arg.ident]
    else:
      raise newException(KeyError, &"Unknown constant array '{arg.ident}'")
  else:
    raise newException(ValueError, &"Expected array, got {arg.kind}")

proc resolveExprArray*(tr: FznTranslator, arg: FznExpr): seq[AlgebraicExpression[int]] =
  ## Resolves a FznExpr to an array of AlgebraicExpressions (for variable arrays).
  case arg.kind
  of FznArrayLit:
    result = newSeq[AlgebraicExpression[int]](arg.elems.len)
    for i, e in arg.elems:
      result[i] = tr.resolveExprArg(e)
  of FznIdent:
    if arg.ident in tr.arrayPositions:
      let positions = tr.arrayPositions[arg.ident]
      result = newSeq[AlgebraicExpression[int]](positions.len)
      for i, pos in positions:
        if pos == -1:
          # Defined variable - use defining expression
          if arg.ident in tr.arrayElementNames:
            let elemName = tr.arrayElementNames[arg.ident][i]
            if elemName in tr.definedVarExprs:
              result[i] = tr.definedVarExprs[elemName]
              continue
          raise newException(ValueError, &"Array '{arg.ident}' element {i} has no position or defining expression")
        result[i] = tr.getExpr(pos)
    elif arg.ident in tr.arrayValues:
      # Constant array - create literal expressions
      let vals = tr.arrayValues[arg.ident]
      result = newSeq[AlgebraicExpression[int]](vals.len)
      for i, v in vals:
        result[i] = newAlgebraicExpression[int](
          positions = initPackedSet[int](),
          node = ExpressionNode[int](kind: LiteralNode, value: v),
          linear = true
        )
    else:
      raise newException(KeyError, &"Unknown array '{arg.ident}'")
  else:
    raise newException(ValueError, &"Expected array, got {arg.kind}")

proc resolvePositionArray*(tr: FznTranslator, arg: FznExpr): seq[int] =
  ## Resolves a FznExpr to positions (for constraints that take position arrays).
  case arg.kind
  of FznArrayLit:
    result = newSeq[int](arg.elems.len)
    for i, e in arg.elems:
      case e.kind
      of FznIdent:
        if e.ident in tr.varPositions:
          result[i] = tr.varPositions[e.ident]
        else:
          raise newException(KeyError, &"Unknown variable '{e.ident}'")
      else:
        raise newException(ValueError, &"Expected variable identifier, got {e.kind}")
  of FznIdent:
    if arg.ident in tr.arrayPositions:
      return tr.arrayPositions[arg.ident]
    else:
      raise newException(KeyError, &"Unknown variable array '{arg.ident}'")
  else:
    raise newException(ValueError, &"Expected array of variables, got {arg.kind}")

proc resolveMixedArray*(tr: FznTranslator, arg: FznExpr): seq[ArrayElement[int]] =
  ## Resolves a FznExpr to a mixed constant/variable array (for element constraints).
  case arg.kind
  of FznArrayLit:
    result = newSeq[ArrayElement[int]](arg.elems.len)
    for i, e in arg.elems:
      case e.kind
      of FznIdent:
        if e.ident in tr.varPositions:
          result[i] = ArrayElement[int](isConstant: false, variablePosition: tr.varPositions[e.ident])
        elif e.ident in tr.paramValues:
          result[i] = ArrayElement[int](isConstant: true, constantValue: tr.paramValues[e.ident])
        else:
          raise newException(KeyError, &"Unknown identifier '{e.ident}'")
      of FznIntLit:
        result[i] = ArrayElement[int](isConstant: true, constantValue: e.intVal)
      of FznBoolLit:
        result[i] = ArrayElement[int](isConstant: true, constantValue: if e.boolVal: 1 else: 0)
      else:
        raise newException(ValueError, &"Expected variable or constant, got {e.kind}")
  else:
    raise newException(ValueError, &"Expected array literal, got {arg.kind}")

proc stripSolverPrefix(name: string): string =
  ## Strips solver-specific prefixes like gecode_, chuffed_ and maps to fzn_ equivalents.
  for prefix in ["gecode_", "chuffed_", "sicstus_"]:
    if name.startsWith(prefix):
      let stripped = name[prefix.len..^1]
      # Some gecode names need remapping
      if stripped == "all_different_int":
        return "fzn_all_different_int"
      elif stripped == "cumulatives":
        return "fzn_cumulative"
      return "fzn_" & stripped
  return name

proc translateParameters(tr: var FznTranslator) =
  ## Process parameter declarations (constant values and arrays).
  ## Must be called before collectDefinedVars since it needs resolveIntArray.
  for decl in tr.model.parameters:
    if decl.isArray:
      if decl.value != nil and decl.value.kind == FznArrayLit:
        var vals = newSeq[int](decl.value.elems.len)
        for i, e in decl.value.elems:
          case e.kind
          of FznIntLit:
            vals[i] = e.intVal
          of FznBoolLit:
            vals[i] = if e.boolVal: 1 else: 0
          of FznIdent:
            if e.ident in tr.paramValues:
              vals[i] = tr.paramValues[e.ident]
            else:
              vals[i] = 0  # fallback
          else:
            vals[i] = 0
        tr.arrayValues[decl.name] = vals
    else:
      # Single parameter
      if decl.value != nil:
        case decl.value.kind
        of FznIntLit:
          tr.paramValues[decl.name] = decl.value.intVal
        of FznBoolLit:
          tr.paramValues[decl.name] = if decl.value.boolVal: 1 else: 0
        else:
          discard

proc translateVariables(tr: var FznTranslator) =
  ## Creates ConstrainedVariables for all FZN variable declarations and sets domains.

  # First pass: create all variables (non-array), skipping defined variables
  for decl in tr.model.variables:
    if decl.isArray:
      continue
    # Skip variables that will be replaced by defining expressions
    if decl.name in tr.definedVarNames:
      continue
    let pos = tr.sys.baseArray.len
    let v = tr.sys.newConstrainedVariable()
    tr.varPositions[decl.name] = pos

    # Set domain based on type
    case decl.varType.kind
    of FznIntRange:
      v.setDomain(toSeq(decl.varType.lo..decl.varType.hi))
    of FznIntSet:
      v.setDomain(decl.varType.values)
    of FznBool:
      v.setDomain(@[0, 1])
    of FznInt:
      # Unbounded int - use a reasonable range
      v.setDomain(toSeq(-1000..1000))
    else:
      v.setDomain(toSeq(-100..100))

    # Check for output annotations
    if decl.hasAnnotation("output_var"):
      tr.outputVars.add(decl.name)

  # Second pass: process variable arrays (they reference already-created variables)
  for decl in tr.model.variables:
    if not decl.isArray:
      continue
    if decl.value != nil and decl.value.kind == FznArrayLit:
      var positions = newSeq[int](decl.value.elems.len)
      var allConstants = true
      var constantVals = newSeq[int](decl.value.elems.len)

      var elemNames = newSeq[string](decl.value.elems.len)
      for i, e in decl.value.elems:
        case e.kind
        of FznIdent:
          elemNames[i] = e.ident
          if e.ident in tr.definedVarNames:
            # Defined variable - use sentinel position, expression will be used later
            positions[i] = -1
            allConstants = false
          elif e.ident in tr.varPositions:
            positions[i] = tr.varPositions[e.ident]
            allConstants = false
          elif e.ident in tr.paramValues:
            # Constant in a "var" array - create a variable with singleton domain
            let cpos = tr.sys.baseArray.len
            let v = tr.sys.newConstrainedVariable()
            let val = tr.paramValues[e.ident]
            v.setDomain(@[val])
            tr.varPositions[e.ident & "_const_" & $i] = cpos
            positions[i] = cpos
            constantVals[i] = val
          else:
            raise newException(KeyError, &"Unknown identifier '{e.ident}' in array '{decl.name}'")
        of FznIntLit:
          # Constant in a variable array - create a variable with singleton domain
          let cpos = tr.sys.baseArray.len
          let v = tr.sys.newConstrainedVariable()
          v.setDomain(@[e.intVal])
          positions[i] = cpos
          constantVals[i] = e.intVal
        of FznBoolLit:
          let val = if e.boolVal: 1 else: 0
          let cpos = tr.sys.baseArray.len
          let v = tr.sys.newConstrainedVariable()
          v.setDomain(@[val])
          positions[i] = cpos
          constantVals[i] = val
        else:
          discard

      tr.arrayPositions[decl.name] = positions
      tr.arrayElementNames[decl.name] = elemNames
      if allConstants:
        tr.arrayValues[decl.name] = constantVals

    # Check for output_array annotation
    if decl.hasAnnotation("output_array"):
      let ann = decl.getAnnotation("output_array")
      var lo = 1
      var hi = decl.arraySize
      if ann.args.len > 0 and ann.args[0].kind == FznArrayLit:
        let indexRanges = ann.args[0]
        if indexRanges.elems.len > 0 and indexRanges.elems[0].kind == FznRange:
          lo = indexRanges.elems[0].lo
          hi = indexRanges.elems[0].hi
      tr.outputArrays.add((name: decl.name, lo: lo, hi: hi))

proc translateConstraint(tr: var FznTranslator, con: FznConstraint) =
  ## Translates a single FlatZinc constraint to a Crusher constraint.
  let name = stripSolverPrefix(con.name)

  case name
  # ===== Linear constraints =====
  of "int_lin_eq":
    # int_lin_eq(coeffs, vars, rhs)
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let sp = scalarProduct[int](coeffs, exprs)
    tr.sys.addConstraint(sp == rhs)

  of "int_lin_le":
    # int_lin_le(coeffs, vars, rhs) means sum(coeffs*vars) <= rhs
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let sp = scalarProduct[int](coeffs, exprs)
    tr.sys.addConstraint(sp <= rhs)

  of "int_lin_ne":
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let sp = scalarProduct[int](coeffs, exprs)
    tr.sys.addConstraint(sp != rhs)

  of "int_lin_eq_reif":
    # int_lin_eq_reif(coeffs, vars, rhs, b) means (sum == rhs) <-> (b == 1)
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let bExpr = tr.resolveExprArg(con.args[3])
    let sp = scalarProduct[int](coeffs, exprs)
    tr.sys.addConstraint((sp == rhs) <-> (bExpr == 1))

  of "int_lin_le_reif":
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let bExpr = tr.resolveExprArg(con.args[3])
    let sp = scalarProduct[int](coeffs, exprs)
    tr.sys.addConstraint((sp <= rhs) <-> (bExpr == 1))

  of "int_lin_ne_reif":
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let bExpr = tr.resolveExprArg(con.args[3])
    let sp = scalarProduct[int](coeffs, exprs)
    tr.sys.addConstraint((sp != rhs) <-> (bExpr == 1))

  # ===== Integer comparison constraints =====
  of "int_eq":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a == b)

  of "int_ne":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a != b)

  of "int_lt":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a < b)

  of "int_le":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a <= b)

  of "int_gt":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a > b)

  of "int_ge":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a >= b)

  of "int_eq_reif":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint((a == b) <-> (r == 1))

  of "int_ne_reif":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint((a != b) <-> (r == 1))

  of "int_lt_reif":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint((a < b) <-> (r == 1))

  of "int_le_reif":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint((a <= b) <-> (r == 1))

  # ===== Arithmetic constraints =====
  of "int_plus":
    # int_plus(x, y, z) means x + y = z
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    let z = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint(x + y == z)

  of "int_times":
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    let z = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint(x * y == z)

  of "int_abs":
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(abs(x) == y)

  of "int_min":
    # int_min(x, y, z) means z = min(x, y)
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    let z = tr.resolveExprArg(con.args[2])
    let m = min[int](@[x, y])
    tr.sys.addConstraint(m == z)

  of "int_max":
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    let z = tr.resolveExprArg(con.args[2])
    let m = max[int](@[x, y])
    tr.sys.addConstraint(m == z)

  of "int_div":
    # int_div is tricky for local search - approximate with multiplication
    # x div y = z  =>  x = z * y (approximate)
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    let z = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint(z * y == x)

  of "int_mod":
    # x mod y = z => x = y * q + z for some q, and 0 <= z < |y|
    # For local search, this is hard to model exactly; skip for now
    discard

  # ===== All-different =====
  of "fzn_all_different_int", "all_different_int":
    let exprs = tr.resolveExprArray(con.args[0])
    tr.sys.addConstraint(allDifferent[int](exprs))

  # ===== Element constraints =====
  of "array_int_element", "array_int_element_nonshifted":
    # array_int_element(index, array, value)
    # FlatZinc uses 1-based indexing, Crusher uses 0-based
    let indexExpr = tr.resolveExprArg(con.args[0])
    let valueExpr = tr.resolveExprArg(con.args[2])
    let adjustedIndex = indexExpr - 1
    # Use elementExpr since adjustedIndex is an expression (not a simple RefNode)
    try:
      let constArray = tr.resolveIntArray(con.args[1])
      tr.sys.addConstraint(elementExpr(adjustedIndex, constArray, valueExpr))
    except:
      let arrayExprs = tr.resolveExprArray(con.args[1])
      tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

  of "array_var_int_element", "array_var_int_element_nonshifted":
    # array_var_int_element(index, var_array, value)
    # FlatZinc uses 1-based indexing
    let indexExpr = tr.resolveExprArg(con.args[0])
    let valueExpr = tr.resolveExprArg(con.args[2])
    let adjustedIndex = indexExpr - 1
    let arrayExprs = tr.resolveExprArray(con.args[1])
    tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

  of "array_bool_element":
    # Same as array_int_element but with booleans
    let indexExpr = tr.resolveExprArg(con.args[0])
    let valueExpr = tr.resolveExprArg(con.args[2])
    let adjustedIndex = indexExpr - 1
    try:
      let constArray = tr.resolveIntArray(con.args[1])
      tr.sys.addConstraint(elementExpr(adjustedIndex, constArray, valueExpr))
    except:
      let arrayExprs = tr.resolveExprArray(con.args[1])
      tr.sys.addConstraint(elementExpr(adjustedIndex, arrayExprs, valueExpr))

  # ===== Array aggregate constraints =====
  of "array_int_maximum":
    # array_int_maximum(max_var, array)
    let maxExpr = tr.resolveExprArg(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let m = max[int](exprs)
    tr.sys.addConstraint(m == maxExpr)

  of "array_int_minimum":
    let minExpr = tr.resolveExprArg(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let m = min[int](exprs)
    tr.sys.addConstraint(m == minExpr)

  # ===== Boolean constraints =====
  of "bool2int":
    # bool2int(b, i) means i = b (both are 0/1 integers in Crusher)
    let b = tr.resolveExprArg(con.args[0])
    let i = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(b == i)

  of "bool_eq":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a == b)

  of "bool_ne":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a != b)

  of "bool_le":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a <= b)

  of "bool_lt":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a < b)

  of "bool_and":
    # bool_and(a, b, r) means r = (a AND b) i.e. r = 1 iff a=1 and b=1
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint((a == 1) and (b == 1) <-> (r == 1))

  of "bool_or":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint(((a == 1) or (b == 1)) <-> (r == 1))

  of "bool_xor":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint(((a == 1) xor (b == 1)) <-> (r == 1))

  of "bool_not":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    tr.sys.addConstraint(a + b == 1)

  of "bool_clause":
    # bool_clause(pos_lits, neg_lits) means OR(pos) OR NOT(neg) >= 1
    # At least one positive lit is 1 or one negative lit is 0
    let posExprs = tr.resolveExprArray(con.args[0])
    let negExprs = tr.resolveExprArray(con.args[1])
    # sum(pos) + (len(neg) - sum(neg)) >= 1
    # sum(pos) - sum(neg) >= 1 - len(neg)
    var allExprs: seq[AlgebraicExpression[int]]
    var coeffs: seq[int]
    for e in posExprs:
      allExprs.add(e)
      coeffs.add(1)
    for e in negExprs:
      allExprs.add(e)
      coeffs.add(-1)
    if allExprs.len > 0:
      let sp = scalarProduct[int](coeffs, allExprs)
      tr.sys.addConstraint(sp >= 1 - negExprs.len)

  of "array_bool_and":
    # array_bool_and(array, r) means r = AND(array)
    let exprs = tr.resolveExprArray(con.args[0])
    let r = tr.resolveExprArg(con.args[1])
    # r = 1 iff sum(array) == len(array)
    let s = sum[int](exprs)
    tr.sys.addConstraint((s == exprs.len) <-> (r == 1))

  of "array_bool_or":
    let exprs = tr.resolveExprArray(con.args[0])
    let r = tr.resolveExprArg(con.args[1])
    let s = sum[int](exprs)
    tr.sys.addConstraint((s >= 1) <-> (r == 1))

  of "bool_eq_reif":
    let a = tr.resolveExprArg(con.args[0])
    let b = tr.resolveExprArg(con.args[1])
    let r = tr.resolveExprArg(con.args[2])
    tr.sys.addConstraint((a == b) <-> (r == 1))

  # ===== Global constraints =====
  of "fzn_cumulative", "fzn_cumulatives":
    # cumulative(starts, durations, heights, limit)
    let startExprs = tr.resolveExprArray(con.args[0])
    # Durations/heights might be in variable arrays - try constant first, fall back to extracting from assignment
    var durations: seq[int]
    var heights: seq[int]
    try:
      durations = tr.resolveIntArray(con.args[1])
    except:
      # Variable array containing constants - extract values from singleton domains
      let dExprs = tr.resolveExprArray(con.args[1])
      durations = newSeq[int](dExprs.len)
      for i, e in dExprs:
        if e.node.kind == LiteralNode:
          durations[i] = e.node.value
        elif e.node.kind == RefNode:
          let dom = tr.sys.baseArray.domain[e.node.position]
          if dom.len == 1:
            durations[i] = dom[0]
          else:
            durations[i] = dom[dom.len div 2]  # fallback
    try:
      heights = tr.resolveIntArray(con.args[2])
    except:
      let hExprs = tr.resolveExprArray(con.args[2])
      heights = newSeq[int](hExprs.len)
      for i, e in hExprs:
        if e.node.kind == LiteralNode:
          heights[i] = e.node.value
        elif e.node.kind == RefNode:
          let dom = tr.sys.baseArray.domain[e.node.position]
          if dom.len == 1:
            heights[i] = dom[0]
          else:
            heights[i] = dom[dom.len div 2]
    # Limit might be a variable - try constant, fall back to domain upper bound
    var limit: int
    try:
      limit = tr.resolveIntArg(con.args[3])
    except:
      # Variable limit - use domain upper bound
      let limitExpr = tr.resolveExprArg(con.args[3])
      if limitExpr.node.kind == RefNode:
        let dom = tr.sys.baseArray.domain[limitExpr.node.position]
        limit = dom[^1]  # upper bound
        # Constrain the variable to equal the limit we're using
        tr.sys.addConstraint(limitExpr == limit)
      else:
        limit = 10  # fallback
    tr.sys.addConstraint(cumulative[int](startExprs, durations, heights, limit))

  of "fzn_circuit":
    let exprs = tr.resolveExprArray(con.args[0])
    let (allRefs, positions) = isAllRefs(exprs)
    if allRefs:
      tr.sys.addConstraint(circuit[int](positions))
    else:
      # Circuit requires position-based - extract from expressions
      var positions2: seq[int]
      for e in exprs:
        if e.node.kind == RefNode:
          positions2.add(e.node.position)
      tr.sys.addConstraint(circuit[int](positions2))

  of "fzn_regular":
    # regular(x, Q, S, d, q0, F)
    let exprs = tr.resolveExprArray(con.args[0])
    let nStates = tr.resolveIntArg(con.args[1])
    let nSymbols = tr.resolveIntArg(con.args[2])
    let transFlat = tr.resolveIntArray(con.args[3])
    let q0 = tr.resolveIntArg(con.args[4])
    # F is a set of final states
    let fArg = con.args[5]
    var finalStates: seq[int]
    case fArg.kind
    of FznSetLit:
      finalStates = fArg.setElems
    of FznArrayLit:
      for e in fArg.elems:
        finalStates.add(tr.resolveIntArg(e))
    else:
      finalStates = tr.resolveIntArray(fArg)

    # Build 2D transition table from flat array
    var transition = newSeq[seq[int]](nStates)
    for i in 0..<nStates:
      transition[i] = newSeq[int](nSymbols)
      for j in 0..<nSymbols:
        transition[i][j] = transFlat[i * nSymbols + j]

    tr.sys.addConstraint(regular[int](exprs, nStates, 1, nSymbols, transition, q0, finalStates))

  of "fzn_table_int":
    # table_int(x, t) where t is flat array of tuples
    let exprs = tr.resolveExprArray(con.args[0])
    let flatTable = tr.resolveIntArray(con.args[1])
    let arity = exprs.len
    let nTuples = flatTable.len div arity
    var tuples = newSeq[seq[int]](nTuples)
    for i in 0..<nTuples:
      tuples[i] = flatTable[i * arity ..< (i + 1) * arity]
    let (allRefs, positions) = isAllRefs(exprs)
    if allRefs:
      tr.sys.addConstraint(tableIn[int](positions, tuples))
    else:
      tr.sys.addConstraint(tableIn[int](exprs, tuples))

  of "fzn_global_cardinality":
    # global_cardinality(x, cover, counts)
    let exprs = tr.resolveExprArray(con.args[0])
    let cover = tr.resolveIntArray(con.args[1])
    var constantCounts = true
    var counts: seq[int]
    try:
      counts = tr.resolveIntArray(con.args[2])
    except KeyError:
      constantCounts = false

    if constantCounts:
      tr.sys.addConstraint(globalCardinality[int](exprs, cover, counts))
    else:
      let countExprs = tr.resolveExprArray(con.args[2])

      # Check 1: All count expressions have singleton domains → use as constants
      var allSingleton = true
      var inferredCounts = newSeq[int](countExprs.len)
      for i, ce in countExprs:
        if ce.node.kind == RefNode:
          let dom = tr.sys.baseArray.domain[ce.node.position]
          if dom.len == 1:
            inferredCounts[i] = dom[0]
          else:
            allSingleton = false; break
        else:
          allSingleton = false; break

      if allSingleton:
        tr.sys.addConstraint(globalCardinality[int](exprs, cover, inferredCounts))
      else:
        # Check 2: All count exprs reference the same position + closed GCC
        var allSamePos = true
        var countPos = -1
        for ce in countExprs:
          if ce.node.kind == RefNode:
            if countPos == -1: countPos = ce.node.position
            elif ce.node.position != countPos: allSamePos = false; break
          else: allSamePos = false; break

        var closed = false
        if allSamePos and countPos >= 0:
          let coverSet = cover.toHashSet()
          closed = true
          for xExpr in exprs:
            if xExpr.node.kind == RefNode:
              for v in tr.sys.baseArray.domain[xExpr.node.position]:
                if v notin coverSet: closed = false; break
            else: closed = false
            if not closed: break

        if allSamePos and closed and exprs.len mod cover.len == 0:
          let target = exprs.len div cover.len
          var targets = newSeq[int](cover.len)
          for i in 0..<cover.len: targets[i] = target
          tr.sys.addConstraint(globalCardinality[int](exprs, cover, targets))
          tr.sys.baseArray.domain[countPos] = @[target]
        else:
          # Fallback: decompose into indicator variables + linear constraints
          # For each cover value v, create: sum_j (x_j == v ? 1 : 0) == counts[i]
          for i, v in cover:
            var indicators: seq[AlgebraicExpression[int]]
            for xExpr in exprs:
              let pos = tr.sys.baseArray.len
              let indicatorVar = tr.sys.newConstrainedVariable()
              indicatorVar.setDomain(@[0, 1])
              let indicatorExpr = tr.getExpr(pos)
              indicators.add(indicatorExpr)
              # (x_j == v) <-> (indicator == 1)
              let litV = newAlgebraicExpression[int](
                positions = initPackedSet[int](),
                node = ExpressionNode[int](kind: LiteralNode, value: v),
                linear = true
              )
              tr.sys.addConstraint((xExpr == litV) <-> (indicatorExpr == 1))
            # sum(indicators) == countExprs[i]
            tr.sys.addConstraint(sum[int](indicators) == countExprs[i])

  of "fzn_global_cardinality_closed", "fzn_global_cardinality_low_up",
     "fzn_global_cardinality_low_up_closed":
    # TODO: bounded cardinality variants
    discard

  of "fzn_count_eq":
    # count_eq(x, y, c) means count(x, y) == c
    # x is array of var int, y is the value to count, c is var int (the count)
    let arrayExprs = tr.resolveExprArray(con.args[0])
    let countValue = tr.resolveIntArg(con.args[1])
    let countExpr = tr.resolveExprArg(con.args[2])
    # Extract positions
    var arrayPos: seq[int]
    for e in arrayExprs:
      if e.node.kind == RefNode:
        arrayPos.add(e.node.position)
      else:
        raise newException(ValueError, "fzn_count_eq requires simple variable references in array")
    if countExpr.node.kind == RefNode:
      tr.sys.addConstraint(countEq[int](arrayPos, countValue, countExpr.node.position))
    else:
      raise newException(ValueError, "fzn_count_eq requires a variable for the count argument")

  of "fzn_count_eq_reif":
    # Reified form - skip for now
    discard

  of "fzn_at_least_int":
    # at_least(n, x, v) means at least n occurrences of v in x
    let n = tr.resolveIntArg(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let v = tr.resolveIntArg(con.args[2])
    tr.sys.addConstraint(atLeast[int](exprs, v, n))

  of "fzn_at_most_int":
    let n = tr.resolveIntArg(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let v = tr.resolveIntArg(con.args[2])
    tr.sys.addConstraint(atMost[int](exprs, v, n))

  of "fzn_increasing_int":
    let exprs = tr.resolveExprArray(con.args[0])
    tr.sys.addConstraint(increasing[int](exprs))

  of "fzn_decreasing_int":
    let exprs = tr.resolveExprArray(con.args[0])
    tr.sys.addConstraint(decreasing[int](exprs))

  of "fzn_all_different_except_0":
    let exprs = tr.resolveExprArray(con.args[0])
    let (allRefs, positions) = isAllRefs(exprs)
    if allRefs:
      tr.sys.addConstraint(allDifferentExcept0[int](positions))

  of "set_in":
    # set_in(x, S) means x must be in set S
    # For local search, this is handled by domain restriction
    # If S is a set literal, restrict the domain
    discard  # Domain is already set from variable declaration

  else:
    # Unknown constraint - warn and skip
    stderr.writeLine(&"[FZN] Warning: unsupported constraint '{con.name}' (normalized: '{name}'), skipping")

proc translateSolve(tr: var FznTranslator) =
  ## Handles the solve directive.
  case tr.model.solve.kind
  of Minimize, Maximize:
    if tr.model.solve.objective != nil:
      case tr.model.solve.objective.kind
      of FznIdent:
        let objName = tr.model.solve.objective.ident
        if objName in tr.varPositions:
          tr.objectivePos = tr.varPositions[objName]
        else:
          raise newException(KeyError, &"Unknown objective variable '{objName}'")
      else:
        raise newException(ValueError, "Objective must be a variable identifier")
  of Satisfy:
    tr.objectivePos = -1

proc collectDefinedVars(tr: var FznTranslator) =
  ## First pass: identify variables defined by int_lin_eq constraints with defines_var annotations.
  ## These variables will be replaced by their defining expressions instead of being created as positions.
  var definedVarNames: Table[string, bool]
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name == "int_lin_eq" and con.hasAnnotation("defines_var"):
      # Find the defines_var annotation
      var ann: FznAnnotation
      for a in con.annotations:
        if a.name == "defines_var":
          ann = a
          break
      if ann.args.len > 0 and ann.args[0].kind == FznIdent:
        let definedName = ann.args[0].ident
        # Check: the defined var must be one of the variables in the constraint,
        # and its coefficient must be 1 or -1 for exact integer arithmetic
        let coeffs = tr.resolveIntArray(con.args[0])
        let vars = con.args[1]
        if vars.kind == FznArrayLit:
          for vi, v in vars.elems:
            if v.kind == FznIdent and v.ident == definedName and (coeffs[vi] == 1 or coeffs[vi] == -1):
              definedVarNames[definedName] = true
              tr.definingConstraints.incl(ci)
              break
  # Store the set of defined variable names for use in translateVariables
  for name in definedVarNames.keys:
    tr.definedVarNames.incl(name)

proc buildDefinedExpressions(tr: var FznTranslator) =
  ## Second pass: build AlgebraicExpressions for defined variables using the positions
  ## of non-defined variables that are already created.
  for ci in tr.definingConstraints.items:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    # Only process int_lin_eq with defines_var (skip consumed count_eq intermediates)
    if name != "int_lin_eq" or not con.hasAnnotation("defines_var"):
      continue
    var ann: FznAnnotation
    for a in con.annotations:
      if a.name == "defines_var":
        ann = a
        break
    let definedName = ann.args[0].ident
    let coeffs = tr.resolveIntArray(con.args[0])
    let rhs = tr.resolveIntArg(con.args[2])
    let vars = con.args[1]

    if vars.kind != FznArrayLit:
      continue

    # Find the defined variable's position in the constraint
    var definedIdx = -1
    for vi, v in vars.elems:
      if v.kind == FznIdent and v.ident == definedName:
        definedIdx = vi
        break

    if definedIdx < 0:
      continue

    let defCoeff = coeffs[definedIdx]
    # Constraint: defCoeff * defined + sum(other_coeffs * other_vars) = rhs
    # defined = (rhs - sum(other_coeffs * other_vars)) / defCoeff
    # For defCoeff = 1: defined = rhs - sum(other_coeffs * other_vars)
    # For defCoeff = -1: defined = sum(other_coeffs * other_vars) - rhs

    # Build expression: start with the constant term (rhs / defCoeff)
    var expr: AlgebraicExpression[int]
    let sign = if defCoeff == 1: -1 else: 1  # negate other coefficients

    var first = true
    for vi, v in vars.elems:
      if vi == definedIdx:
        continue
      let otherExpr = tr.resolveExprArg(v)
      let scaledCoeff = sign * coeffs[vi]
      let term = scaledCoeff * otherExpr
      if first:
        expr = term
        first = false
      else:
        expr = expr + term

    # Add constant term: sign * (-rhs) = rhs/defCoeff for the constant part
    let constTerm = if defCoeff == 1: rhs else: -rhs
    if constTerm != 0:
      if first:
        expr = newAlgebraicExpression[int](
          positions = initPackedSet[int](),
          node = ExpressionNode[int](kind: LiteralNode, value: constTerm),
          linear = true
        )
        first = false
      else:
        expr = expr + constTerm

    if expr.isNil:
      raise newException(ValueError, &"Failed to build expression for defined variable '{definedName}'")
    tr.definedVarExprs[definedName] = expr

proc detectCountPatterns(tr: var FznTranslator) =
  ## Detects int_lin_eq → bool2int → int_eq_reif chains that implement count_eq.
  ## Pattern: for each value v, n constraints of form:
  ##   int_eq_reif(x_j, v, b_j) :: defines_var(b_j)
  ##   bool2int(b_j, ind_j) :: defines_var(ind_j)
  ##   int_lin_eq([1, -1, ..., -1], [target, ind_1, ..., ind_n], 0)
  ## This replaces O(n²) decomposed constraints with a single count_eq.

  # Build maps: variable name → defining constraint index
  # bool2int(boolVar, intVar) :: defines_var(intVar) → intVar maps to constraint index
  var bool2intDefs: Table[string, int]  # indicator var name → constraint index
  # int_eq_reif(x, val, boolVar) :: defines_var(boolVar) → boolVar maps to constraint index
  var intEqReifDefs: Table[string, int]  # bool var name → constraint index

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue  # Already consumed by defined-var elimination
    let name = stripSolverPrefix(con.name)
    if name == "bool2int" and con.hasAnnotation("defines_var"):
      # bool2int(boolVar, intVar) :: defines_var(intVar)
      if con.args.len >= 2 and con.args[1].kind == FznIdent:
        bool2intDefs[con.args[1].ident] = ci
    elif name == "int_eq_reif" and con.hasAnnotation("defines_var"):
      # int_eq_reif(x, val, boolVar) :: defines_var(boolVar)
      if con.args.len >= 3 and con.args[2].kind == FznIdent:
        intEqReifDefs[con.args[2].ident] = ci

  # Now scan for int_lin_eq constraints that match the pattern
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_eq":
      continue

    # int_lin_eq(coeffs, vars, rhs)
    # Pattern: coeffs = [1, -1, -1, ..., -1], rhs = 0
    # vars = [target, ind_1, ind_2, ..., ind_n]
    let rhs = try: tr.resolveIntArg(con.args[2]) except: continue
    if rhs != 0:
      continue

    let coeffs = try: tr.resolveIntArray(con.args[0]) except: continue
    if coeffs.len < 2:
      continue

    # Check coefficient pattern: first is 1, rest are -1
    if coeffs[0] != 1:
      continue
    var allNegOne = true
    for i in 1..<coeffs.len:
      if coeffs[i] != -1:
        allNegOne = false
        break
    if not allNegOne:
      continue

    # Extract variable names - handle both inline arrays and named array references
    let vars = con.args[1]
    var varElems: seq[FznExpr]
    if vars.kind == FznArrayLit:
      varElems = vars.elems
    elif vars.kind == FznIdent:
      # Named array reference - find the array declaration
      var found = false
      for decl in tr.model.variables:
        if decl.isArray and decl.name == vars.ident and decl.value != nil and decl.value.kind == FznArrayLit:
          varElems = decl.value.elems
          found = true
          break
      if not found:
        continue
    else:
      continue

    if varElems.len < 2:
      continue

    let targetArg = varElems[0]
    if targetArg.kind != FznIdent:
      continue
    let targetName = targetArg.ident

    # Check all indicator variables trace back through bool2int → int_eq_reif
    var countValue: int
    var countValueSet = false
    var arrayVarNames: seq[string]
    var consumedConstraints: seq[int]
    var consumedVarNames: seq[string]
    var valid = true

    for i in 1..<varElems.len:
      let indArg = varElems[i]
      if indArg.kind != FznIdent:
        valid = false
        break

      let indName = indArg.ident
      if indName notin bool2intDefs:
        valid = false
        break

      let b2iIdx = bool2intDefs[indName]
      let b2iCon = tr.model.constraints[b2iIdx]
      # bool2int(boolVar, intVar) — extract boolVar
      if b2iCon.args[0].kind != FznIdent:
        valid = false
        break
      let boolVarName = b2iCon.args[0].ident

      if boolVarName notin intEqReifDefs:
        valid = false
        break

      let eqReifIdx = intEqReifDefs[boolVarName]
      let eqReifCon = tr.model.constraints[eqReifIdx]
      # int_eq_reif(x, val, boolVar) — extract x and val
      if eqReifCon.args[0].kind != FznIdent:
        valid = false
        break
      if eqReifCon.args[1].kind != FznIntLit:
        # Try param
        let v = try: tr.resolveIntArg(eqReifCon.args[1]) except: (valid = false; 0)
        if not valid:
          break
        if not countValueSet:
          countValue = v
          countValueSet = true
        elif v != countValue:
          valid = false
          break
      else:
        let v = eqReifCon.args[1].intVal
        if not countValueSet:
          countValue = v
          countValueSet = true
        elif v != countValue:
          valid = false
          break

      arrayVarNames.add(eqReifCon.args[0].ident)
      consumedConstraints.add(b2iIdx)
      consumedConstraints.add(eqReifIdx)
      consumedVarNames.add(indName)
      consumedVarNames.add(boolVarName)

    if not valid or not countValueSet:
      continue

    # Pattern detected! Record it.
    tr.countEqPatterns[ci] = CountEqPattern(
      linEqIdx: ci,
      countValue: countValue,
      targetVarName: targetName,
      arrayVarNames: arrayVarNames
    )

    # Mark consumed constraints (skip during translation)
    # Note: the int_lin_eq itself (ci) is NOT added to definingConstraints —
    # it's handled by the countEqPatterns check in the main loop
    for idx in consumedConstraints:
      tr.definingConstraints.incl(idx)  # the bool2int and int_eq_reif

    # Mark intermediate variable names as defined (skip position creation)
    for vn in consumedVarNames:
      tr.definedVarNames.incl(vn)

    stderr.writeLine(&"[FZN] Detected count_eq pattern: count({arrayVarNames.len} vars, {countValue}) == {targetName}")

proc translate*(model: FznModel): FznTranslator =
  ## Translates a complete FznModel to a ConstraintSystem.
  result.sys = initConstraintSystem[int]()
  result.model = model
  result.varPositions = initTable[string, int]()
  result.paramValues = initTable[string, int]()
  result.arrayPositions = initTable[string, seq[int]]()
  result.arrayValues = initTable[string, seq[int]]()
  result.definedVarNames = initHashSet[string]()
  result.definedVarExprs = initTable[string, AlgebraicExpression[int]]()
  result.arrayElementNames = initTable[string, seq[string]]()
  result.countEqPatterns = initTable[int, CountEqPattern]()
  result.objectivePos = -1

  # Load parameters first (needed by collectDefinedVars for resolveIntArray)
  result.translateParameters()
  # Collect defined variables before translating variables
  result.collectDefinedVars()
  # Detect count_eq patterns before translating variables (marks intermediate vars as defined)
  result.detectCountPatterns()
  result.translateVariables()
  # Build expressions for defined variables using the now-created positions
  result.buildDefinedExpressions()

  for ci, con in model.constraints:
    if ci in result.definingConstraints:
      continue
    if ci in result.countEqPatterns:
      # Emit count_eq for detected pattern
      let pattern = result.countEqPatterns[ci]
      var arrayPos: seq[int]
      for vn in pattern.arrayVarNames:
        if vn in result.varPositions:
          arrayPos.add(result.varPositions[vn])
        else:
          raise newException(KeyError, &"Unknown variable '{vn}' in count_eq pattern")
      let targetPos = result.varPositions[pattern.targetVarName]
      result.sys.addConstraint(countEq[int](arrayPos, pattern.countValue, targetPos))
    else:
      result.translateConstraint(con)
  result.translateSolve()
