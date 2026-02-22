## FlatZinc translator - maps FznModel to ConstraintSystem[int].

import std/[tables, sequtils, strutils, strformat, packedsets, sets, math, algorithm]

import parser
import dfaExtract
import ../constraintSystem
import ../constrainedArray
import ../constraints/[stateful, countEq, matrixElement, elementState]
import ../expressions/[expressions, algebraic, sumExpression, minExpression, maxExpression]

type
  CountEqPattern* = object
    ## A detected count_eq pattern from int_lin_eq → bool2int → int_eq_reif chains
    linEqIdx*: int           # index of the int_lin_eq constraint
    countValue*: int         # the constant value being counted
    targetVarName*: string   # name of the target variable (the count)
    arrayVarNames*: seq[string]  # names of the array variables being counted over

  MatrixInfo* = object
    ## Info about a known matrix (square output array) for matrix_element detection
    arrayName*: string
    numRows*, numCols*: int
    elements*: seq[ArrayElement[int]]  # flat row-major array of ArrayElements

  GeostConversion* = object
    ## A detected pattern where multiple fzn_regular constraints over the same
    ## variable array encode tile placements, convertible to a single geost constraint.
    boardArrayName*: string           # FZN array name for board variables
    boardPositions*: seq[int]         # system positions for board vars
    tileVarPositions*: seq[int]       # system positions for tile placement vars
    allPlacements*: seq[seq[seq[int]]]  # cellsByPlacement[tile][idx] = cell indices
    tileValues*: seq[int]             # board value for each tile (1-indexed)
    sentinelBoardIndices*: seq[int]   # board array indices that are sentinels
    sentinelValue*: int               # sentinel value (ntiles+1)

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
    # Direct objective expression (for defined-variable objectives, avoids indirection)
    objectiveDefExpr*: AlgebraicExpression[int]
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
    # Geost conversion (active if tileValues.len > 0)
    geostConversion*: GeostConversion
    # Matrix infos for matrix_element pattern detection
    matrixInfos*: Table[string, MatrixInfo]
    # Domain bounds for defined variables (lo, hi) — used to add domain constraints on their expressions
    definedVarBounds*: Table[string, (int, int)]
    # Channel variable names (element defines_var outputs that should be computed, not searched)
    channelVarNames*: HashSet[string]
    # Maps constraint index -> channel var name for element constraints with defines_var
    channelConstraints*: Table[int, string]
    # Set of constraint indices that are redundant ordering constraints (transitively implied)
    redundantOrderings*: PackedSet[int]
    # Reification channel patterns: constraint index for int_eq_reif/bool2int with defines_var
    reifChannelDefs*: seq[int]      # int_eq_reif constraint indices (ordered first)
    bool2intChannelDefs*: seq[int]  # bool2int constraint indices (ordered after reif)

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
  of FznIdent:
    if arg.ident in tr.arrayPositions:
      let positions = tr.arrayPositions[arg.ident]
      result = newSeq[ArrayElement[int]](positions.len)
      for i, pos in positions:
        if pos == -1:
          # Defined variable - treat as constant if we can resolve it
          if arg.ident in tr.arrayElementNames:
            let elemName = tr.arrayElementNames[arg.ident][i]
            if elemName in tr.paramValues:
              result[i] = ArrayElement[int](isConstant: true, constantValue: tr.paramValues[elemName])
              continue
          raise newException(ValueError, &"Array '{arg.ident}' element {i} has no position or constant value")
        let dom = tr.sys.baseArray.domain[pos]
        if dom.len == 1:
          result[i] = ArrayElement[int](isConstant: true, constantValue: dom[0])
        else:
          result[i] = ArrayElement[int](isConstant: false, variablePosition: pos)
    elif arg.ident in tr.arrayValues:
      let vals = tr.arrayValues[arg.ident]
      result = newSeq[ArrayElement[int]](vals.len)
      for i, v in vals:
        result[i] = ArrayElement[int](isConstant: true, constantValue: v)
    else:
      raise newException(KeyError, &"Unknown array '{arg.ident}'")
  else:
    raise newException(ValueError, &"Expected array literal, got {arg.kind}")


proc buildMatrixInfos(tr: var FznTranslator) =
    ## Builds MatrixInfo entries for output arrays that are perfect squares.
    ## These enable matrix_element pattern detection in element constraint translation.
    for oa in tr.outputArrays:
        let name = oa.name
        if name notin tr.arrayPositions:
            continue
        let positions = tr.arrayPositions[name]
        let size = positions.len
        # Check for perfect square
        let n = int(float(size).sqrt + 0.5)
        if n * n != size:
            continue
        # Build elements array — skip arrays containing defined variables (pos == -1)
        # since they don't have real positions and can't be used for matrix element constraints
        var elements = newSeq[ArrayElement[int]](size)
        var hasDefinedVar = false
        for i in 0..<size:
            let pos = positions[i]
            if pos == -1:
                hasDefinedVar = true
                break
            let dom = tr.sys.baseArray.domain[pos]
            if dom.len == 1:
                elements[i] = ArrayElement[int](isConstant: true, constantValue: dom[0])
            else:
                elements[i] = ArrayElement[int](isConstant: false, variablePosition: pos)
        if hasDefinedVar:
            continue
        tr.matrixInfos[name] = MatrixInfo(
            arrayName: name,
            numRows: n,
            numCols: n,
            elements: elements
        )


proc matchMatrixRow(tr: FznTranslator, inlineElems: seq[ArrayElement[int]],
                     matrixInfo: MatrixInfo): int =
    ## Checks if inlineElems matches a specific row of the matrix.
    ## Returns the row index if matched, -1 otherwise.
    let numCols = matrixInfo.numCols
    if inlineElems.len != numCols:
        return -1
    for r in 0..<matrixInfo.numRows:
        var matches = true
        for c in 0..<numCols:
            let flatIdx = r * numCols + c
            let me = matrixInfo.elements[flatIdx]
            let ie = inlineElems[c]
            if me.isConstant and ie.isConstant:
                if me.constantValue != ie.constantValue:
                    matches = false
                    break
            elif not me.isConstant and not ie.isConstant:
                if me.variablePosition != ie.variablePosition:
                    matches = false
                    break
            else:
                matches = false
                break
        if matches:
            return r
    return -1

proc matchMatrixCol(tr: FznTranslator, inlineElems: seq[ArrayElement[int]],
                     matrixInfo: MatrixInfo): int =
    ## Checks if inlineElems matches a specific column of the matrix.
    ## Returns the column index if matched, -1 otherwise.
    let numRows = matrixInfo.numRows
    let numCols = matrixInfo.numCols
    if inlineElems.len != numRows:
        return -1
    for c in 0..<numCols:
        var matches = true
        for r in 0..<numRows:
            let flatIdx = r * numCols + c
            let me = matrixInfo.elements[flatIdx]
            let ie = inlineElems[r]
            if me.isConstant and ie.isConstant:
                if me.constantValue != ie.constantValue:
                    matches = false
                    break
            elif not me.isConstant and not ie.isConstant:
                if me.variablePosition != ie.variablePosition:
                    matches = false
                    break
            else:
                matches = false
                break
        if matches:
            return c
    return -1

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
      if decl.hasAnnotation("output_var"):
        tr.outputVars.add(decl.name)
      # Record domain bounds for later constraint generation
      if decl.varType.kind == FznIntRange:
        tr.definedVarBounds[decl.name] = (decl.varType.lo, decl.varType.hi)
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

proc decomposeWithIndicators(tr: var FznTranslator,
    exprs: seq[AlgebraicExpression[int]],
    cover: seq[int],
    countExprs: seq[AlgebraicExpression[int]]) =
  ## Decompose a global cardinality constraint into indicator variables.
  ## For each cover value v, creates: sum_j (x_j == v ? 1 : 0) == counts[i]
  for i, v in cover:
    var indicators: seq[AlgebraicExpression[int]]
    for xExpr in exprs:
      let pos = tr.sys.baseArray.len
      let indicatorVar = tr.sys.newConstrainedVariable()
      indicatorVar.setDomain(@[0, 1])
      let indicatorExpr = tr.getExpr(pos)
      indicators.add(indicatorExpr)
      let litV = newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: v),
        linear = true
      )
      tr.sys.addConstraint((xExpr == litV) <-> (indicatorExpr == 1))
    tr.sys.addConstraint(sum[int](indicators) == countExprs[i])

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

    # Check for unit-coefficient pattern on binary variables → atMost/atLeast
    var emittedUnitCoeff = false
    let (allRefsLe, positionsLe) = isAllRefs(exprs)
    if allRefsLe:
      var allPosOne = true
      var allNegOne = true
      for c in coeffs:
        if c != 1: allPosOne = false
        if c != -1: allNegOne = false
      if allPosOne or allNegOne:
        var allBinary = true
        for pos in positionsLe:
          let dom = tr.sys.baseArray.domain[pos]
          if dom.len != 2 or dom[0] != 0 or dom[1] != 1:
            allBinary = false
            break
        if allBinary:
          if allPosOne:
            # sum([1,1,...,1], x) <= rhs  →  atMost(rhs, x, 1)
            tr.sys.addConstraint(atMost[int](positionsLe, 1, rhs))
          else:
            # sum([-1,-1,...,-1], x) <= rhs  →  -sum(x) <= rhs  →  sum(x) >= -rhs
            tr.sys.addConstraint(atLeast[int](positionsLe, 1, -rhs))
          emittedUnitCoeff = true

    if not emittedUnitCoeff:
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
    # int_div(x, y, z) means z = x div y (integer division, rounding towards zero)
    # For non-negative x and positive constant y:
    #   z * y <= x  and  x <= z * y + (y - 1)
    # For local search with variable y, fall back to approximate equality z * y == x
    let x = tr.resolveExprArg(con.args[0])
    let y = tr.resolveExprArg(con.args[1])
    let z = tr.resolveExprArg(con.args[2])
    if con.args[1].kind == FznIntLit and con.args[1].intVal > 0:
      let yVal = con.args[1].intVal
      # z * y <= x  =>  x - z * y >= 0
      tr.sys.addConstraint(x - z * y >= 0)
      # x - z * y <= y - 1  =>  x - z * y - (y-1) <= 0
      tr.sys.addConstraint(x - z * y <= yVal - 1)
    else:
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

    # Try matrix element pattern: index is a simple RefNode and value is a simple RefNode
    var emitted = false
    if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode and
       tr.matrixInfos.len > 0:
        # Resolve inline array as mixed elements for matching
        let inlineElems = tr.resolveMixedArray(con.args[1])
        let indexPos = adjustedIndex.node.position
        let valuePos = valueExpr.node.position
        for name, minfo in tr.matrixInfos:
            # Try row match
            let rowIdx = tr.matchMatrixRow(inlineElems, minfo)
            if rowIdx >= 0:
                # Constant row, variable col: matrix[rowIdx, indexPos] == valuePos
                tr.sys.addConstraint(stateful.matrixElement[int](
                    minfo.elements, minfo.numRows, minfo.numCols,
                    rowIdx, indexPos, valuePos))
                emitted = true
                break
            # Try column match
            let colIdx = tr.matchMatrixCol(inlineElems, minfo)
            if colIdx >= 0:
                # Variable row, constant col: matrix[indexPos, colIdx] == valuePos
                tr.sys.addConstraint(stateful.matrixElement[int](
                    minfo.elements, minfo.numRows, minfo.numCols,
                    indexPos, colIdx, valuePos, rowIsVariable = true))
                emitted = true
                break

    if not emitted:
        let arrayExprs = tr.resolveExprArray(con.args[1])
        # Use position-based element if index is a RefNode, else expression-based
        if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode:
            let mixedElems = tr.resolveMixedArray(con.args[1])
            tr.sys.addConstraint(element(adjustedIndex, mixedElems, valueExpr))
        else:
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

  of "fzn_diffn":
    # diffn(x, y, dx, dy) - non-overlapping rectangles
    let xExprs = tr.resolveExprArray(con.args[0])
    let yExprs = tr.resolveExprArray(con.args[1])
    let dxExprs = tr.resolveExprArray(con.args[2])
    let dyExprs = tr.resolveExprArray(con.args[3])
    tr.sys.addConstraint(diffn[int](xExprs, yExprs, dxExprs, dyExprs))

  of "fzn_circuit":
    let exprs = tr.resolveExprArray(con.args[0])
    let (allRefs, positions) = isAllRefs(exprs)
    if allRefs:
      tr.sys.addConstraint(circuit[int](positions))
    else:
      # Circuit/subcircuit need ALL nodes including constants (fixed vars).
      # Constants get a singleton-domain position so node indexing stays correct.
      var positions2: seq[int]
      for e in exprs:
        if e.node.kind == RefNode:
          positions2.add(e.node.position)
        elif e.node.kind == LiteralNode:
          let pos = tr.sys.baseArray.len
          let v = tr.sys.newConstrainedVariable()
          v.setDomain(@[int(e.node.value)])
          positions2.add(pos)
        else:
          raise newException(ValueError, "fzn_circuit: unsupported expression node kind " & $e.node.kind)
      tr.sys.addConstraint(circuit[int](positions2))

  of "fzn_subcircuit":
    let exprs = tr.resolveExprArray(con.args[0])
    let (allRefs, positions) = isAllRefs(exprs)
    if allRefs:
      tr.sys.addConstraint(subcircuit[int](positions))
      tr.sys.addConstraint(allDifferent[int](positions))
    else:
      # Constants get a singleton-domain position so node indexing stays correct.
      var positions2: seq[int]
      for e in exprs:
        if e.node.kind == RefNode:
          positions2.add(e.node.position)
        elif e.node.kind == LiteralNode:
          let pos = tr.sys.baseArray.len
          let v = tr.sys.newConstrainedVariable()
          v.setDomain(@[int(e.node.value)])
          positions2.add(pos)
        else:
          raise newException(ValueError, "fzn_subcircuit: unsupported expression node kind " & $e.node.kind)
      tr.sys.addConstraint(subcircuit[int](positions2))
      tr.sys.addConstraint(allDifferent[int](positions2))

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
    of FznRange:
      for i in fArg.lo..fArg.hi:
        finalStates.add(i)
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
          tr.decomposeWithIndicators(exprs, cover, countExprs)

  of "fzn_global_cardinality_closed":
    # global_cardinality_closed(x, cover, counts)
    # Same as open variant but domains are restricted to cover set
    let exprs = tr.resolveExprArray(con.args[0])
    let cover = tr.resolveIntArray(con.args[1])
    let coverSet = cover.toHashSet()
    # Restrict domains to cover set
    for e in exprs:
      if e.node.kind == RefNode:
        let pos = e.node.position
        tr.sys.baseArray.domain[pos] = tr.sys.baseArray.domain[pos].filterIt(it in coverSet)
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
        tr.decomposeWithIndicators(exprs, cover, countExprs)

  of "fzn_global_cardinality_low_up_closed":
    # global_cardinality_low_up_closed(x, cover, lbound, ubound)
    # Same as open variant but domains are restricted to cover set
    let exprs = tr.resolveExprArray(con.args[0])
    let cover = tr.resolveIntArray(con.args[1])
    let lbound = tr.resolveIntArray(con.args[2])
    let ubound = tr.resolveIntArray(con.args[3])
    let n = exprs.len
    let coverSet = cover.toHashSet()
    # Restrict domains to cover set
    for e in exprs:
      if e.node.kind == RefNode:
        let pos = e.node.position
        tr.sys.baseArray.domain[pos] = tr.sys.baseArray.domain[pos].filterIt(it in coverSet)
    # Same cardinality logic as open variant
    for i in 0..<cover.len:
      if lbound[i] > 0:
        tr.sys.addConstraint(atLeast[int](exprs, cover[i], lbound[i]))
      if ubound[i] < n:
        tr.sys.addConstraint(atMost[int](exprs, cover[i], ubound[i]))

  of "fzn_global_cardinality_low_up":
    # global_cardinality_low_up(x, cover, lbound, ubound)
    # For each i: lbound[i] <= count(x, cover[i]) <= ubound[i]
    # Skip trivial bounds; emit atLeast/atMost for non-trivial ones.
    let exprs = tr.resolveExprArray(con.args[0])
    let cover = tr.resolveIntArray(con.args[1])
    let lbound = tr.resolveIntArray(con.args[2])
    let ubound = tr.resolveIntArray(con.args[3])
    let n = exprs.len
    for i in 0..<cover.len:
      if lbound[i] > 0:
        tr.sys.addConstraint(atLeast[int](exprs, cover[i], lbound[i]))
      if ubound[i] < n:
        tr.sys.addConstraint(atMost[int](exprs, cover[i], ubound[i]))

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
    # Reified form - not yet implemented
    stderr.writeLine("[FZN] Warning: fzn_count_eq_reif not implemented, constraint ignored")

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
        elif objName in tr.definedVarExprs:
          # Objective was eliminated as a defined variable — use its defining expression directly.
          # This avoids an intermediate position + binary-penalty linking constraint,
          # which would hide objective gradient from compound moves (ejection chains).
          tr.objectiveDefExpr = tr.definedVarExprs[objName]
          tr.objectivePos = -1
        else:
          raise newException(KeyError, &"Unknown objective variable '{objName}'")
      else:
        raise newException(ValueError, "Objective must be a variable identifier")
  of Satisfy:
    tr.objectivePos = -2  # distinct from -1 (defined-var objective)

proc resolveVarArrayElems(tr: FznTranslator, arg: FznExpr): seq[FznExpr] =
  ## Resolves a variable array argument to its elements, from inline literal or named declaration.
  if arg.kind == FznArrayLit:
    return arg.elems
  elif arg.kind == FznIdent:
    for decl in tr.model.variables:
      if decl.isArray and decl.name == arg.ident and decl.value != nil and decl.value.kind == FznArrayLit:
        return decl.value.elems
  return @[]

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
        let varElems = tr.resolveVarArrayElems(con.args[1])
        for vi, v in varElems:
          if v.kind == FznIdent and v.ident == definedName and (coeffs[vi] == 1 or coeffs[vi] == -1):
            definedVarNames[definedName] = true
            tr.definingConstraints.incl(ci)
            break
  # Third loop: identify int_abs, int_max, int_min with defines_var annotations
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name in ["int_abs", "int_max", "int_min", "int_times"] and con.hasAnnotation("defines_var"):
      let ann = con.getAnnotation("defines_var")
      if ann.args.len > 0 and ann.args[0].kind == FznIdent:
        let definedName = ann.args[0].ident
        # int_abs(a, b) :: defines_var(b) → b is args[1]
        # int_max(a, b, c) :: defines_var(c) → c is args[2]
        # int_min(a, b, c) :: defines_var(c) → c is args[2]
        let expectedIdx = if name == "int_abs": 1 else: 2
        if con.args[expectedIdx].kind == FznIdent and
           con.args[expectedIdx].ident == definedName:
          definedVarNames[definedName] = true
          tr.definingConstraints.incl(ci)

  # Store the set of defined variable names for use in translateVariables
  for name in definedVarNames.keys:
    tr.definedVarNames.incl(name)

  # Second loop: identify element constraints with defines_var annotations
  # These define channel variables that should be computed, not searched
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name in ["array_var_int_element", "array_var_int_element_nonshifted",
                "array_int_element", "array_int_element_nonshifted"] and
       con.hasAnnotation("defines_var"):
      # Extract the defined variable name from the 3rd argument
      if con.args[2].kind == FznIdent:
        let definedName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len > 0 and ann.args[0].kind == FznIdent and
           ann.args[0].ident == definedName:
          tr.channelVarNames.incl(definedName)
          tr.channelConstraints[ci] = definedName
          # DO NOT add to definedVarNames (channel vars need positions)
          # DO NOT add to definingConstraints (constraint still needs translation)

proc tryBuildDefinedExpression(tr: var FznTranslator, ci: int): bool =
  ## Tries to build the AlgebraicExpression for one defining constraint.
  ## Returns true if successful, false if a dependency is not yet available.
  let con = tr.model.constraints[ci]
  let name = stripSolverPrefix(con.name)
  # Only process defining constraints with defines_var
  if name notin ["int_lin_eq", "int_abs", "int_max", "int_min", "int_times"] or
     not con.hasAnnotation("defines_var"):
    return true  # not our concern, treat as done
  var ann: FznAnnotation
  for a in con.annotations:
    if a.name == "defines_var":
      ann = a
      break
  let definedName = ann.args[0].ident
  if definedName in tr.definedVarExprs:
    return true  # already built

  # Handle int_abs, int_max, int_min
  if name == "int_abs":
    # int_abs(a, b) :: defines_var(b) → b = abs(a)
    let a = con.args[0]
    if a.kind == FznIdent and a.ident in tr.definedVarNames and
       a.ident notin tr.definedVarExprs and a.ident notin tr.varPositions and
       a.ident notin tr.paramValues:
      return false  # dependency not yet built
    tr.definedVarExprs[definedName] = abs(tr.resolveExprArg(a))
    return true

  if name == "int_max":
    # int_max(a, b, c) :: defines_var(c) → c = max(a, b)
    let a = con.args[0]
    let b = con.args[1]
    for operand in [a, b]:
      if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
         operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
         operand.ident notin tr.paramValues:
        return false
    tr.definedVarExprs[definedName] = binaryMax(tr.resolveExprArg(a), tr.resolveExprArg(b))
    return true

  if name == "int_min":
    # int_min(a, b, c) :: defines_var(c) → c = min(a, b)
    let a = con.args[0]
    let b = con.args[1]
    for operand in [a, b]:
      if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
         operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
         operand.ident notin tr.paramValues:
        return false
    tr.definedVarExprs[definedName] = binaryMin(tr.resolveExprArg(a), tr.resolveExprArg(b))
    return true

  if name == "int_times":
    # int_times(a, b, c) :: defines_var(c) → c = a * b
    let a = con.args[0]
    let b = con.args[1]
    for operand in [a, b]:
      if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
         operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
         operand.ident notin tr.paramValues:
        return false
    tr.definedVarExprs[definedName] = tr.resolveExprArg(a) * tr.resolveExprArg(b)
    return true

  let coeffs = tr.resolveIntArray(con.args[0])
  let rhs = tr.resolveIntArg(con.args[2])
  let varElems = tr.resolveVarArrayElems(con.args[1])

  if varElems.len == 0:
    return true  # can't process, skip

  # Find the defined variable's position in the constraint
  var definedIdx = -1
  for vi, v in varElems:
    if v.kind == FznIdent and v.ident == definedName:
      definedIdx = vi
      break

  if definedIdx < 0:
    return true  # can't process, skip

  # Check if all dependencies are available before building
  for vi, v in varElems:
    if vi == definedIdx:
      continue
    if v.kind == FznIdent and v.ident in tr.definedVarNames and
       v.ident notin tr.definedVarExprs and v.ident notin tr.varPositions and
       v.ident notin tr.paramValues:
      return false  # dependency not yet built

  let defCoeff = coeffs[definedIdx]
  # Constraint: defCoeff * defined + sum(other_coeffs * other_vars) = rhs
  # defined = (rhs - sum(other_coeffs * other_vars)) / defCoeff
  # For defCoeff = 1: defined = rhs - sum(other_coeffs * other_vars)
  # For defCoeff = -1: defined = sum(other_coeffs * other_vars) - rhs

  # Build expression: start with the constant term (rhs / defCoeff)
  var expr: AlgebraicExpression[int]
  let sign = if defCoeff == 1: -1 else: 1  # negate other coefficients

  var first = true
  for vi, v in varElems:
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
  return true

proc buildDefinedExpressions(tr: var FznTranslator) =
  ## Second pass: build AlgebraicExpressions for defined variables using the positions
  ## of non-defined variables that are already created.
  ## Uses multiple passes to handle dependencies between defined variables.
  var remaining: seq[int]
  for ci in tr.definingConstraints.items:
    remaining.add(ci)

  var maxPasses = remaining.len + 1
  while remaining.len > 0 and maxPasses > 0:
    var nextRemaining: seq[int]
    for ci in remaining:
      if not tr.tryBuildDefinedExpression(ci):
        nextRemaining.add(ci)
    if nextRemaining.len == remaining.len:
      # No progress - break to avoid infinite loop
      for ci in nextRemaining:
        discard tr.tryBuildDefinedExpression(ci)  # will raise on error
      break
    remaining = nextRemaining
    dec maxPasses

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
    let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
    if rhs != 0:
      continue

    let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
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
      let v = try: tr.resolveIntArg(eqReifCon.args[1]) except ValueError, KeyError: (valid = false; 0)
      if not valid:
        break
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

proc detectReifChannels(tr: var FznTranslator) =
  ## Detects int_eq_reif(x, val, b) :: defines_var(b) and bool2int(b, i) :: defines_var(i)
  ## patterns and marks the defined variables as channel variables.
  ## Channel variables get positions but are not searched; their values are computed
  ## from decision variables via element-style lookups.
  ##
  ## Handles two int_eq_reif variants:
  ##   - Constant val: b = (x == val) ? 1 : 0 → element lookup on x's domain
  ##   - Variable val: b = (x == y) ? 1 : 0 → 2D element lookup on (x,y) domains

  # First pass: find int_eq_reif with defines_var, not already consumed
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if (name != "int_eq_reif" and name != "int_ne_reif") or not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 3 or con.args[2].kind != FznIdent:
      continue

    let bName = con.args[2].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
      continue

    # Don't channel if already handled by another optimization
    if bName in tr.definedVarNames or bName in tr.channelVarNames:
      continue

    # Verify args[0] is a variable (not a constant) — we need a position for the index
    let xArg = con.args[0]
    if xArg.kind != FznIdent:
      continue
    # x must resolve to a position (not a defined variable with no position)
    if xArg.ident in tr.definedVarNames:
      continue

    # For var-to-var case, verify args[1] is also a positioned variable
    let valArg = con.args[1]
    if valArg.kind == FznIdent and valArg.ident in tr.definedVarNames:
      continue

    tr.channelVarNames.incl(bName)
    tr.definingConstraints.incl(ci)
    tr.reifChannelDefs.add(ci)

  # Second pass: find bool2int with defines_var, not already consumed
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "bool2int" or not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 2 or con.args[1].kind != FznIdent:
      continue

    let iName = con.args[1].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != iName:
      continue

    if iName in tr.definedVarNames or iName in tr.channelVarNames:
      continue

    # b must be a variable with a position (either search or channel)
    let bArg = con.args[0]
    if bArg.kind != FznIdent:
      continue
    if bArg.ident in tr.definedVarNames:
      continue

    tr.channelVarNames.incl(iName)
    tr.definingConstraints.incl(ci)
    tr.bool2intChannelDefs.add(ci)

  if tr.reifChannelDefs.len > 0 or tr.bool2intChannelDefs.len > 0:
    stderr.writeLine(&"[FZN] Detected reification channels: {tr.reifChannelDefs.len} int_eq/ne_reif, {tr.bool2intChannelDefs.len} bool2int")


proc lookupVarDomain(tr: FznTranslator, varName: string): seq[int] =
  ## Look up a variable's domain from the FznModel declarations.
  for decl in tr.model.variables:
    if decl.isArray: continue
    if decl.name == varName:
      case decl.varType.kind
      of FznIntRange:
        return toSeq(decl.varType.lo..decl.varType.hi)
      of FznIntSet:
        return decl.varType.values
      of FznBool:
        return @[0, 1]
      else:
        return @[]
  return @[]


proc buildReifChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings for int_eq_reif and bool2int patterns detected
  ## by detectReifChannels. Must be called after translateVariables.
  ##
  ## int_eq_reif(x, val, b): b = element(x - lo, [1 if v==val else 0 for v in domain])
  ## int_ne_reif(x, val, b): b = element(x - lo, [0 if v==val else 1 for v in domain])
  ## int_eq_reif(x, y, b):   b = element((x-lo_x)*size_y + (y-lo_y), equality_table)
  ## bool2int(b, i):          i = element(b, [0, 1])

  # Process int_eq_reif channels first (bool2int depends on these)
  for ci in tr.reifChannelDefs:
    let con = tr.model.constraints[ci]
    let bName = con.args[2].ident
    if bName notin tr.varPositions:
      continue

    let bPos = tr.varPositions[bName]
    let xArg = con.args[0]
    let valArg = con.args[1]

    var indexExpr: AlgebraicExpression[int]
    var arrayElems: seq[ArrayElement[int]]

    let isEq = stripSolverPrefix(con.name) == "int_eq_reif"

    if valArg.kind == FznIntLit or (valArg.kind == FznIdent and valArg.ident in tr.paramValues):
      # Constant val: b = element(x - lo, [1 if v==val else 0]) (inverted for ne)
      let val = if valArg.kind == FznIntLit: valArg.intVal
                else: tr.paramValues[valArg.ident]
      let xExpr = tr.resolveExprArg(xArg)
      let domain = tr.lookupVarDomain(xArg.ident)
      if domain.len == 0:
        continue
      let lo = domain[0]  # domain is sorted

      indexExpr = xExpr - lo
      for v in domain:
        arrayElems.add(ArrayElement[int](isConstant: true,
            constantValue: if (v == val) == isEq: 1 else: 0))

    elif valArg.kind == FznIdent and valArg.ident notin tr.definedVarNames:
      # Variable val: b = element((x-lo_x)*size_y + (y-lo_y), equality_table)
      let xExpr = tr.resolveExprArg(xArg)
      let yExpr = tr.resolveExprArg(valArg)
      let domainX = tr.lookupVarDomain(xArg.ident)
      let domainY = tr.lookupVarDomain(valArg.ident)
      if domainX.len == 0 or domainY.len == 0:
        continue
      let loX = domainX[0]
      let loY = domainY[0]
      let sizeY = domainY.len

      # index = (x - lo_x) * size_y + (y - lo_y)
      indexExpr = (xExpr - loX) * sizeY + (yExpr - loY)

      # Build 2D equality table (row-major: x varies in outer loop, y in inner)
      for vx in domainX:
        for vy in domainY:
          arrayElems.add(ArrayElement[int](isConstant: true,
              constantValue: if (vx == vy) == isEq: 1 else: 0))
    else:
      continue

    let binding = ChannelBinding[int](
      channelPosition: bPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(bPos)

    # Map source positions to this binding (for channel propagation triggers)
    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  # Process bool2int channels (after reif channels so b positions are set up)
  for ci in tr.bool2intChannelDefs:
    let con = tr.model.constraints[ci]
    let iName = con.args[1].ident
    let bArg = con.args[0]

    if iName notin tr.varPositions:
      continue
    let iPos = tr.varPositions[iName]

    let bExpr = tr.resolveExprArg(bArg)

    # i = element(b, [0, 1])  — identity mapping for domain {0, 1}
    let arrayElems = @[
      ArrayElement[int](isConstant: true, constantValue: 0),
      ArrayElement[int](isConstant: true, constantValue: 1)
    ]

    let binding = ChannelBinding[int](
      channelPosition: iPos,
      indexExpression: bExpr,  # b is 0-based (domain {0,1})
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(iPos)

    for pos in bExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  let totalReifChannels = tr.reifChannelDefs.len + tr.bool2intChannelDefs.len
  if totalReifChannels > 0:
    stderr.writeLine(&"[FZN] Built {totalReifChannels} reification channel bindings " &
                     &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc detectDfaGeostPattern(tr: var FznTranslator) =
  ## Detects multiple fzn_regular constraints over the same variable array
  ## (tiling pattern) and converts them to a single geost constraint.
  ## Each regular constraint encodes one tile's valid placements as a DFA.

  # Step 1: Find all fzn_regular constraints, verify they share the same array
  var regularIndices: seq[int]
  var boardArrayArg: FznExpr = nil

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "fzn_regular":
      continue
    if con.args.len < 6:
      continue

    let arrayArg = con.args[0]
    if boardArrayArg == nil:
      boardArrayArg = arrayArg
    else:
      # Verify same array reference
      if arrayArg.kind != boardArrayArg.kind:
        return
      case arrayArg.kind
      of FznIdent:
        if arrayArg.ident != boardArrayArg.ident:
          return
      of FznArrayLit:
        # Array literals - check same elements
        if arrayArg.elems.len != boardArrayArg.elems.len:
          return
        for i in 0..<arrayArg.elems.len:
          if arrayArg.elems[i].kind != boardArrayArg.elems[i].kind:
            return
          if arrayArg.elems[i].kind == FznIdent and
             arrayArg.elems[i].ident != boardArrayArg.elems[i].ident:
            return
      else:
        return
    regularIndices.add(ci)

  if regularIndices.len < 2:
    return

  # Determine board array name
  var boardArrayName = ""
  if boardArrayArg.kind == FznIdent:
    boardArrayName = boardArrayArg.ident
  else:
    # Inline array literal - find which declared array matches
    for decl in tr.model.variables:
      if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
        if decl.value.elems.len == boardArrayArg.elems.len:
          var match = true
          for i in 0..<decl.value.elems.len:
            if decl.value.elems[i].kind == FznIdent and
               boardArrayArg.elems[i].kind == FznIdent and
               decl.value.elems[i].ident != boardArrayArg.elems[i].ident:
              match = false
              break
          if match:
            boardArrayName = decl.name
            break
    if boardArrayName == "":
      return

  # Step 2: Determine board size and sentinel positions from the model
  # Find board array declaration to get size
  var boardSize = 0
  var boardArrayDecl: FznVarDecl
  for decl in tr.model.variables:
    if decl.isArray and decl.name == boardArrayName:
      boardArrayDecl = decl
      if decl.value != nil and decl.value.kind == FznArrayLit:
        boardSize = decl.value.elems.len
      else:
        boardSize = decl.arraySize
      break
  if boardSize == 0:
    return

  # Find sentinel positions: look for int_eq constraints that fix board vars to a constant
  # Pattern: int_eq(board_element, constant) where constant is ntiles+1
  var sentinelPositions = initPackedSet[int]()
  var sentinelBoardIndices: seq[int]
  var sentinelValue = -1

  # Build a set of board element variable names for quick lookup
  var boardElemNames: seq[string]
  var boardElemNameSet: sets.HashSet[string] = initHashSet[string]()
  if boardArrayDecl.value != nil and boardArrayDecl.value.kind == FznArrayLit:
    for e in boardArrayDecl.value.elems:
      if e.kind == FznIdent:
        boardElemNames.add(e.ident)
        boardElemNameSet.incl(e.ident)
      else:
        boardElemNames.add("")

  # Map board element names to their 0-based index in the board array
  var elemToIdx: Table[string, int] = initTable[string, int]()
  for i, name in boardElemNames:
    if name != "":
      elemToIdx[name] = i

  # Scan for int_eq constraints setting board vars to constants
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name == "int_eq" and con.args.len >= 2:
      # int_eq(var, const) or int_eq(const, var)
      var varName = ""
      var constVal = -1
      if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit:
        varName = con.args[0].ident
        constVal = con.args[1].intVal
      elif con.args[1].kind == FznIdent and con.args[0].kind == FznIntLit:
        varName = con.args[1].ident
        constVal = con.args[0].intVal
      if varName in boardElemNameSet and constVal >= 0:
        let idx = elemToIdx[varName]
        sentinelBoardIndices.add(idx)
        sentinelPositions.incl(idx)
        if sentinelValue < 0:
          sentinelValue = constVal
        # Mark this constraint as consumed
        tr.definingConstraints.incl(ci)

  # Also check: the board array may contain literal integers (already sentinel)
  if boardArrayDecl.value != nil and boardArrayDecl.value.kind == FznArrayLit:
    for i, e in boardArrayDecl.value.elems:
      if e.kind == FznIntLit:
        sentinelBoardIndices.add(i)
        sentinelPositions.incl(i)
        if sentinelValue < 0:
          sentinelValue = e.intVal

  # Scan for int_ne constraints on board vars (these will be auto-satisfied by geost)
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name == "int_ne" and con.args.len >= 2:
      var varName = ""
      if con.args[0].kind == FznIdent and con.args[0].ident in boardElemNameSet:
        varName = con.args[0].ident
      elif con.args[1].kind == FznIdent and con.args[1].ident in boardElemNameSet:
        varName = con.args[1].ident
      if varName != "":
        tr.definingConstraints.incl(ci)

  let ntiles = regularIndices.len
  if sentinelValue < 0:
    sentinelValue = ntiles + 1

  # Step 3: For each regular constraint, extract placements
  var allPlacements: seq[seq[seq[int]]]
  var tileValues: seq[int]

  for ri, ci in regularIndices:
    let con = tr.model.constraints[ci]
    let nStates = tr.resolveIntArg(con.args[1])
    let nSymbols = tr.resolveIntArg(con.args[2])
    let transFlat = tr.resolveIntArray(con.args[3])
    let q0 = tr.resolveIntArg(con.args[4])
    var finalStates: seq[int]
    let fArg = con.args[5]
    case fArg.kind
    of FznSetLit:
      finalStates = fArg.setElems
    of FznRange:
      for s in fArg.lo..fArg.hi:
        finalStates.add(s)
    of FznArrayLit:
      for e in fArg.elems:
        finalStates.add(tr.resolveIntArg(e))
    else:
      finalStates = tr.resolveIntArray(fArg)

    # Build 2D transition table
    var transition = newSeq[seq[int]](nStates)
    for s in 0..<nStates:
      transition[s] = newSeq[int](nSymbols)
      for j in 0..<nSymbols:
        transition[s][j] = transFlat[s * nSymbols + j]

    # Identify which input is the tile
    let tileInputIdx = identifyTileInput(transition, nStates, nSymbols)
    if tileInputIdx < 0:
      stderr.writeLine(&"[FZN] Geost: cannot identify tile input for regular constraint {ci}, aborting")
      return

    let tileValue = tileInputIdx + 1  # 1-indexed tile value

    let placements = extractPlacementsFromDfa(
      nStates, nSymbols, transition, q0, finalStates,
      tileInputIdx, boardSize, sentinelPositions
    )

    if placements.len == 0:
      stderr.writeLine(&"[FZN] Geost: tile {tileValue} has no valid placements, aborting")
      return

    allPlacements.add(placements)
    tileValues.add(tileValue)

    # Mark this regular constraint as consumed
    tr.definingConstraints.incl(ci)

  # Step 4: Store the conversion
  tr.geostConversion = GeostConversion(
    boardArrayName: boardArrayName,
    allPlacements: allPlacements,
    tileValues: tileValues,
    sentinelBoardIndices: sentinelBoardIndices,
    sentinelValue: sentinelValue,
  )

  stderr.writeLine(&"[FZN] Detected DFA-to-geost pattern: {ntiles} tiles, {boardSize} board cells")
  for t in 0..<ntiles:
    stderr.writeLine(&"[FZN]   Tile {tileValues[t]}: {allPlacements[t].len} placements, {allPlacements[t][0].len} cells")

proc buildChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings from element constraints with defines_var annotations.
  ## Must be called after all constraints are translated and all positions are known.
  for ci, definedName in tr.channelConstraints:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)

    # The defined variable must have a position (it was NOT added to definedVarNames)
    if definedName notin tr.varPositions:
      continue

    let channelPos = tr.varPositions[definedName]

    # Build the adjusted index expression (0-based)
    let indexExpr = tr.resolveExprArg(con.args[0])
    let adjustedIndex = indexExpr - 1

    # Build the array elements
    var arrayElems: seq[ArrayElement[int]]
    if name in ["array_var_int_element", "array_var_int_element_nonshifted"]:
      arrayElems = tr.resolveMixedArray(con.args[1])
    else:
      # array_int_element: constant array
      let constArray = tr.resolveIntArray(con.args[1])
      for v in constArray:
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

    let binding = ChannelBinding[int](
      channelPosition: channelPos,
      indexExpression: adjustedIndex,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(channelPos)

    # Map source positions to this binding
    for pos in adjustedIndex.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)
    for elem in arrayElems:
      if not elem.isConstant:
        if elem.variablePosition notin tr.sys.baseArray.channelsAtPosition:
          tr.sys.baseArray.channelsAtPosition[elem.variablePosition] = @[bindingIdx]
        else:
          tr.sys.baseArray.channelsAtPosition[elem.variablePosition].add(bindingIdx)

  if tr.sys.baseArray.channelBindings.len > 0:
    stderr.writeLine(&"[FZN] Detected {tr.sys.baseArray.channelBindings.len} channel variables (element defines_var)")

proc resolveVarNames(tr: FznTranslator, arg: FznExpr): seq[string] =
  ## Resolves a FznExpr to variable names (for ordering detection).
  ## Only handles inline array literals since this runs before translateVariables.
  case arg.kind
  of FznArrayLit:
    for e in arg.elems:
      if e.kind == FznIdent:
        result.add(e.ident)
      else:
        return @[]  # non-variable element, bail out
  else:
    return @[]

proc detectRedundantOrderings(tr: var FznTranslator) =
  ## Detects transitively redundant ordering constraints.
  ## For int_lin_le([1,-1], [a, b], 0) meaning a <= b, identifies edges
  ## implied by transitivity (e.g., a<=c is redundant if a<=b and b<=c).
  type OrderEdge = object
    constraintIdx: int
    fromVar, toVar: string

  var edges: seq[OrderEdge]
  var nameToId: Table[string, int]
  var idToName: seq[string]
  var nextId = 0

  proc getId(name: string): int =
    if name in nameToId:
      return nameToId[name]
    result = nextId
    nameToId[name] = nextId
    idToName.add(name)
    inc nextId

  # Collect ordering edges: int_lin_le([1,-1], [a, b], 0) means a <= b
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    if con.name != "int_lin_le":
      continue
    # Resolve coefficients
    var coeffs: seq[int]
    try:
      coeffs = tr.resolveIntArray(con.args[0])
    except CatchableError:
      continue
    if coeffs != @[1, -1]:
      continue
    # Resolve RHS
    var rhs: int
    try:
      rhs = tr.resolveIntArg(con.args[2])
    except CatchableError:
      continue
    if rhs != 0:
      continue
    # Resolve variable names
    let varNames = tr.resolveVarNames(con.args[1])
    if varNames.len != 2:
      continue
    # Skip if either variable is defined (will be replaced by expression)
    if varNames[0] in tr.definedVarNames or varNames[1] in tr.definedVarNames:
      continue
    let fromId = getId(varNames[0])
    let toId = getId(varNames[1])
    edges.add(OrderEdge(constraintIdx: ci, fromVar: varNames[0], toVar: varNames[1]))

  if edges.len == 0:
    return

  let n = nextId

  # Build adjacency using PackedSets
  var succ = newSeq[PackedSet[int]](n)
  for i in 0..<n:
    succ[i] = initPackedSet[int]()
  # Map edge to constraint index for lookup
  var edgeConstraints: Table[(int, int), seq[int]]
  for e in edges:
    let fromId = nameToId[e.fromVar]
    let toId = nameToId[e.toVar]
    succ[fromId].incl(toId)
    let key = (fromId, toId)
    if key notin edgeConstraints:
      edgeConstraints[key] = @[]
    edgeConstraints[key].add(e.constraintIdx)

  # Compute in-degree for topological sort (Kahn's algorithm)
  var inDeg = newSeq[int](n)
  for i in 0..<n:
    for j in succ[i].items:
      inDeg[j] += 1

  var queue: seq[int]
  for i in 0..<n:
    if inDeg[i] == 0:
      queue.add(i)

  var topoOrder: seq[int]
  var qi = 0
  while qi < queue.len:
    let u = queue[qi]
    inc qi
    topoOrder.add(u)
    for v in succ[u].items:
      inDeg[v] -= 1
      if inDeg[v] == 0:
        queue.add(v)

  if topoOrder.len != n:
    # Graph has cycles — can't do transitive reduction, skip
    return

  # Compute topological index for each node
  var topoIdx = newSeq[int](n)
  for i, node in topoOrder:
    topoIdx[node] = i

  # Compute reachable sets bottom-up (reverse topological order)
  var reachable = newSeq[PackedSet[int]](n)
  for i in 0..<n:
    reachable[i] = initPackedSet[int]()

  for i in countdown(topoOrder.len - 1, 0):
    let u = topoOrder[i]
    for v in succ[u].items:
      reachable[u].incl(v)
      reachable[u] = reachable[u] + reachable[v]

  # Compute transitive reduction: for each node, keep only immediate successors
  var reducedSucc = newSeq[PackedSet[int]](n)
  for i in 0..<n:
    reducedSucc[i] = succ[i]  # start with all direct successors

  for u in topoOrder:
    # Process successors in topological order (nearest first)
    var sortedSucc: seq[int]
    for v in succ[u].items:
      sortedSucc.add(v)
    sortedSucc.sort(proc(a, b: int): int = cmp(topoIdx[a], topoIdx[b]))

    for v in sortedSucc:
      if v in reducedSucc[u]:
        # Keep v, but remove everything reachable from v
        reducedSucc[u] = reducedSucc[u] - reachable[v]
        reducedSucc[u].incl(v)  # re-include v itself

  # Mark redundant edges
  var redundantCount = 0
  for e in edges:
    let fromId = nameToId[e.fromVar]
    let toId = nameToId[e.toVar]
    if toId notin reducedSucc[fromId]:
      tr.redundantOrderings.incl(e.constraintIdx)
      inc redundantCount

  if redundantCount > 0:
    stderr.writeLine(&"[FZN] Ordering reduction: {edges.len} -> {edges.len - redundantCount} constraints ({redundantCount} redundant)")

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
  result.matrixInfos = initTable[string, MatrixInfo]()
  result.definedVarBounds = initTable[string, (int, int)]()
  result.channelVarNames = initHashSet[string]()
  result.channelConstraints = initTable[int, string]()
  result.objectivePos = -2  # no objective yet; -1 = defined-var objective, >= 0 = position

  # Load parameters first (needed by collectDefinedVars for resolveIntArray)
  result.translateParameters()
  # Collect defined variables before translating variables
  result.collectDefinedVars()
  # Detect count_eq patterns before translating variables (marks intermediate vars as defined)
  result.detectCountPatterns()
  # Detect int_eq_reif/bool2int defines_var patterns → channel variables
  result.detectReifChannels()
  # Detect DFA-to-geost pattern (needs paramValues for DFA data)
  result.detectDfaGeostPattern()
  # Detect redundant ordering constraints (transitive reduction)
  result.detectRedundantOrderings()
  result.translateVariables()
  # Build expressions for defined variables using the now-created positions
  result.buildDefinedExpressions()
  # Add domain constraints for defined variables with finite bounds
  for varName, bounds in result.definedVarBounds:
    if varName in result.definedVarExprs:
      let expr = result.definedVarExprs[varName]
      let (lo, hi) = bounds
      if lo > low(int):
        result.sys.addConstraint(expr >= lo)
      if hi < high(int):
        result.sys.addConstraint(expr <= hi)
  # Build matrix infos for matrix_element pattern detection
  result.buildMatrixInfos()

  # If geost conversion is active, record board positions and create tile variables
  let gc = result.geostConversion
  if gc.tileValues.len > 0:
    if gc.boardArrayName in result.arrayPositions:
      result.geostConversion.boardPositions = result.arrayPositions[gc.boardArrayName]
    # Create tile placement variables
    for t in 0..<gc.tileValues.len:
      let pos = result.sys.baseArray.len
      let v = result.sys.newConstrainedVariable()
      v.setDomain(toSeq(0..<gc.allPlacements[t].len))
      result.geostConversion.tileVarPositions.add(pos)

  for ci, con in model.constraints:
    if ci in result.definingConstraints:
      continue
    if ci in result.redundantOrderings:
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

  # Add geost constraint if conversion is active
  if result.geostConversion.tileValues.len > 0:
    result.sys.addConstraint(geost[int](
      result.geostConversion.tileVarPositions,
      result.geostConversion.allPlacements
    ))

  # Build channel bindings for element defines_var
  result.buildChannelBindings()
  # Build channel bindings for int_eq_reif/bool2int reification channels
  result.buildReifChannelBindings()

  result.translateSolve()
