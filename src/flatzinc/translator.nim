## FlatZinc translator - maps FznModel to ConstraintSystem[int].

import std/[tables, sequtils, strutils, strformat, packedsets, sets, math, algorithm, hashes]

import parser
import dfaExtract
import ../constraintSystem
import ../constrainedArray
import ../constraints/[stateful, countEq, matrixElement, elementState, tableConstraint, noOverlapFixedBox, conditionalCumulative, conditionalNoOverlap, conditionalDayCapacity]
import ../expressions/[expressions, algebraic, sumExpression, minExpression, maxExpression, weightedSameValue]

const
  ObjPosNone* = -2          ## No objective (satisfy problem)
  ObjPosDefinedExpr* = -1   ## Objective is a defined-variable expression
  ObjPosWeightedSV* = -3    ## Objective is a WeightedSameValueExpression

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

  CaseAnalysisDef* = object
    ## A detected case-analysis channel: target variable fully determined by
    ## source variables via exhaustive bool_clause case analysis.
    targetVarName*: string
    sourceVarNames*: seq[string]     # ultimate source variable names (search positions)
    lookupTable*: seq[int]           # flat constant lookup table
    domainOffsets*: seq[int]         # min value per source (for index computation)
    domainSizes*: seq[int]          # domain size per source (hi - lo + 1)

  NoOverlapEndpoint* = object
    ## An endpoint in a NoOverlap pattern — either a constant or a variable name
    isFixed*: bool
    fixedValue*: int
    varName*: string

  NoOverlapPattern* = object
    ## A detected NoOverlap pattern: 6-literal bool_clause encoding 3D box non-overlap
    nodeA*: array[3, NoOverlapEndpoint]
    nodeB*: array[3, NoOverlapEndpoint]
    radius*: int
    boxLower*: array[3, int]
    boxUpper*: array[3, int]
    consumedConstraints*: seq[int]
    consumedBoolVars*: seq[string]

  SetVarInfo* = object
    positions*: seq[int]  # boolean variable positions in ConstraintSystem
    lo*: int              # min element of universe
    hi*: int              # max element of universe

  SetArrayElement* = object
    isConstant*: bool
    constantValues*: seq[int]  # for literal set elements
    varName*: string           # FZN name (for variable elements)

  SetUnionChainInfo* = object
    resultName*: string              # final result set variable
    baseName*: string                # base set (first arg of first union)
    baseIsConst*: bool               # true if base is a constant set
    baseConstVals*: HashSet[int]      # constant values if baseIsConst
    leafNames*: seq[string]          # leaf set names (second arg of each union)
    intermediateNames*: seq[string]  # intermediate set names (results of all but last union)
    constraintIndices*: seq[int]     # union constraint indices in chain order

  SetComprehensionPair* = object
    sumVal*: int            # ai + bi (the value this pair contributes when active)
    productVarName*: string # the int_times product variable name (expression = AND of membership)

  SetComprehensionInfo* = object
    chainIdx*: int                       # index into setUnionChains
    pairs*: seq[SetComprehensionPair]    # contributing pairs with their sum values
    consumedConstraints*: PackedSet[int] # set_in + set_card constraint indices for singletons

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
    # Domain bounds on objective variable (deferred to optimizer, not added as hard constraints)
    objectiveLoBound*: int
    objectiveHiBound*: int
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
    leReifChannelDefs*: seq[int]    # int_le_reif/int_lt_reif channel constraint indices
    # Detected implication table patterns: (condVar, targetVar) -> allowed tuples
    implicationTables*: seq[tuple[condVar, targetVar: string, tuples: seq[seq[int]]]]
    # One-hot channel defs: indicator vars to convert to channels of integer vars
    oneHotChannelDefs*: seq[tuple[indicatorVar, intVar: string, value: int]]
    # Boundary B vars that are always 0 (from int_eq_reif(bVar, 1, false))
    constantZeroChannels*: seq[string]
    # Disjunctive pair patterns: bool_clause([b1,b2],[]) where b1,b2 come from int_lin_le_reif
    disjunctivePairs*: seq[tuple[
      coeffs1: seq[int], varNames1: seq[string], rhs1: int,
      coeffs2: seq[int], varNames2: seq[string], rhs2: int]]
    # Min/max channel defs: array_int_minimum/maximum with defines_var → channel variables
    minMaxChannelDefs*: seq[tuple[ci: int, varName: string, isMin: bool]]
    # Case-analysis channel defs: bool_clause case analysis → constant lookup channel
    caseAnalysisDefs*: seq[CaseAnalysisDef]
    # bool_clause_reif with defines_var → channel variables
    boolClauseReifChannelDefs*: seq[int]
    # set_in_reif with defines_var → channel variables
    setInReifChannelDefs*: seq[int]
    # array_bool_and/array_bool_or with defines_var → channel variables
    boolAndOrChannelDefs*: seq[int]
    # Consumed disjunctive pair indices (replaced by cumulative constraints)
    consumedDisjunctivePairs*: PackedSet[int]
    # Detected disjunctive resource groups (cliques of disjunctive pairs → cumulative)
    disjunctiveResourceGroups*: seq[tuple[varNames: seq[string], durations: seq[int]]]
    # Detected NoOverlap patterns (6-literal bool_clause → 3D box non-overlap)
    noOverlapPatterns*: seq[NoOverlapPattern]
    # Detected inverse channel patterns: element(person[p], seat, p) groups
    inverseChannelPatterns*: seq[tuple[arrayName: string, elementCIs: seq[int],
                                       indexVarNames: seq[string], resultValues: seq[int],
                                       gccCIs: seq[int]]]
    # Tracks which output variables/arrays are boolean (for true/false formatting)
    outputBoolVars*: HashSet[string]
    outputBoolArrays*: HashSet[string]
    # Element channel aliases: maps duplicate channel var name → original channel var name
    # (when multiple element constraints share same index var and constant array)
    elementChannelAliases*: Table[string, string]
    # Equality copy aliases: maps eliminated copy var name → original var name
    equalityCopyAliases*: Table[string, string]
    # Constraint indices of int_eq_reif that are equality copies (skip in buildReifChannelBindings)
    equalityCopyReifCIs*: PackedSet[int]
    # Set variable decomposition: maps FZN set var name -> boolean positions + universe bounds
    setVarBoolPositions*: Table[string, SetVarInfo]
    # Set parameter values: maps FZN set param name -> set of int values
    setParamValues*: Table[string, seq[int]]
    # Set array parameter values: maps FZN array name -> per-element set values
    setArrayValues*: Table[string, seq[seq[int]]]
    # Set array decompositions: maps FZN array name -> per-element set array info
    setArrayDecompositions*: Table[string, seq[SetArrayElement]]
    # Output set variables (for set output formatting)
    outputSetVars*: HashSet[string]
    # Output set arrays (for set array output formatting)
    outputSetArrays*: HashSet[string]
    # set_union channel defs: constraint index + result var name (non-chain unions only)
    setUnionChannelDefs*: seq[tuple[ci: int, resultName: string]]
    # Detected set_union chains (linear sequences of set_union :: defines_var)
    setUnionChains*: seq[SetUnionChainInfo]
    # Detected set comprehension patterns (chains with traced singleton→product mapping)
    setComprehensions*: seq[SetComprehensionInfo]
    # Set variable names to skip boolean creation for (singletons + intermediates)
    skipSetVarNames*: HashSet[string]
    # Reusable position for a variable fixed to 1 (for set_in channel bindings), -1 if not yet created
    fixedOnePos*: int
    # Synthetic element channels: precomputed lookup tables for conditional gain variables
    syntheticElementChannels*: seq[tuple[varName: string, originVar: string, lookupTable: seq[int]]]
    # Detected weighted same-value pattern for objective
    weightedSameValuePairs*: seq[tuple[varNameA, varNameB: string, coeff: int]]
    weightedSameValueConstant*: int
    weightedSameValueObjName*: string
    weightedSameValueExpr*: WeightedSameValueExpression[int]
    # Detected conditional no-overlap pair patterns
    conditionalNoOverlapInfos*: seq[tuple[
      startAName, startBName: string,
      durationA, durationB: int,
      resourceAName, resourceBName: string,
      resourceAFixed, resourceBFixed: int,
      condAName, condBName: string,
      consumedCIs: seq[int],
      consumedVars: seq[string]]]
    # Detected conditional cumulative patterns (room_admission elimination)
    conditionalCumulativeInfos*: seq[tuple[
      fixedTasks: seq[tuple[start, duration, height: int]],
      conditionalTasks: seq[tuple[admissionVarName, selectionVarName, roomVarName: string,
                                   duration, height, roomValue, fixedAdmission: int]],
      limit: int,
      cumulativeCi: int,
      consumedElementCIs: seq[int],
      consumedEqReifCIs: seq[int],
      consumedBoolClauseCIs: seq[int],
      consumedRaVarNames: seq[string],
      consumedBoolVarNames: seq[string]]]
    # Detected conditional day capacity patterns (H3/H4 surgeon/OT capacity)
    conditionalDayCapacityInfos*: seq[tuple[
      tasks: seq[tuple[weight: int, admissionVarName, selectionVarName: string,
                        extraCondVarName: string, extraCondVal: int]],
      capacities: seq[int],
      maxDay: int,
      consumedCIs: seq[int],
      consumedVarNames: seq[string]]]

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

proc extractSetValues(value: FznExpr): seq[int] =
  ## Extract integer values from a set literal or range expression.
  case value.kind
  of FznSetLit:
    return value.setElems
  of FznRange:
    if value.lo > value.hi:
      return @[]  # empty set (e.g., 1..0)
    return toSeq(value.lo..value.hi)
  else:
    return @[]

proc translateParameters(tr: var FznTranslator) =
  ## Process parameter declarations (constant values and arrays).
  ## Must be called before collectDefinedVars since it needs resolveIntArray.
  for decl in tr.model.parameters:
    let isSetType = decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}
    if decl.isArray:
      if isSetType:
        # Array of set parameters: store per-element set values
        if decl.value != nil and decl.value.kind == FznArrayLit:
          var setVals = newSeq[seq[int]](decl.value.elems.len)
          for i, e in decl.value.elems:
            case e.kind
            of FznSetLit, FznRange:
              setVals[i] = extractSetValues(e)
            of FznIdent:
              if e.ident in tr.setParamValues:
                setVals[i] = tr.setParamValues[e.ident]
              else:
                setVals[i] = @[]
            else:
              setVals[i] = @[]
          tr.setArrayValues[decl.name] = setVals
      elif decl.value != nil and decl.value.kind == FznArrayLit:
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
      if isSetType:
        if decl.value != nil:
          tr.setParamValues[decl.name] = extractSetValues(decl.value)
      elif decl.value != nil:
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
  var nSetVars = 0
  var nSetBools = 0
  for decl in tr.model.variables:
    if decl.isArray:
      continue
    # Skip variables that will be replaced by defining expressions
    if decl.name in tr.definedVarNames:
      if decl.hasAnnotation("output_var"):
        tr.outputVars.add(decl.name)
        if decl.varType.kind == FznBool:
          tr.outputBoolVars.incl(decl.name)
      # Record domain bounds for later constraint generation
      if decl.varType.kind == FznIntRange:
        tr.definedVarBounds[decl.name] = (decl.varType.lo, decl.varType.hi)
      continue

    # Handle set variables: decompose into boolean arrays
    if decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
      # Skip boolean creation for chain intermediates and singletons
      if decl.name in tr.skipSetVarNames:
        tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: 0, hi: -1)
        if decl.hasAnnotation("output_var"):
          tr.outputSetVars.incl(decl.name)
        continue
      var lo, hi: int
      case decl.varType.kind
      of FznSetOfIntRange:
        lo = decl.varType.setLo
        hi = decl.varType.setHi
      of FznSetOfIntSet:
        if decl.varType.setValues.len == 0:
          tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: 0, hi: -1)
          continue
        lo = decl.varType.setValues.min
        hi = decl.varType.setValues.max
      of FznSetOfInt:
        stderr.writeLine(&"[FZN] Warning: unbounded 'set of int' variable '{decl.name}', skipping decomposition")
        tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: 0, hi: -1)
        if decl.hasAnnotation("output_var"):
          tr.outputSetVars.incl(decl.name)
        continue
      else: discard

      if lo > hi:
        tr.setVarBoolPositions[decl.name] = SetVarInfo(positions: @[], lo: lo, hi: hi)
        if decl.hasAnnotation("output_var"):
          tr.outputSetVars.incl(decl.name)
        continue

      let size = hi - lo + 1
      var boolPositions = newSeq[int](size)

      # Determine fixed values if the variable has an assignment
      var fixedValues: seq[int]
      var hasFixed = false
      if decl.value != nil:
        fixedValues = extractSetValues(decl.value)
        hasFixed = true

      for i in 0..<size:
        let bpos = tr.sys.baseArray.len
        let bv = tr.sys.newConstrainedVariable()
        if hasFixed:
          # Fix boolean: 1 if element is in the fixed set, 0 otherwise
          if (lo + i) in fixedValues:
            bv.setDomain(@[1])
          else:
            bv.setDomain(@[0])
        else:
          bv.setDomain(@[0, 1])
        boolPositions[i] = bpos

      tr.setVarBoolPositions[decl.name] = SetVarInfo(
        positions: boolPositions, lo: lo, hi: hi)
      inc nSetVars
      nSetBools += size

      if decl.hasAnnotation("output_var"):
        tr.outputSetVars.incl(decl.name)
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
      if decl.varType.kind == FznBool:
        tr.outputBoolVars.incl(decl.name)

  if nSetVars > 0:
    stderr.writeLine(&"[FZN] Set decomposition: {nSetVars} set variables -> {nSetBools} boolean variables")

  # Second pass: process variable arrays (they reference already-created variables)
  for decl in tr.model.variables:
    if not decl.isArray:
      continue

    # Handle set-typed arrays: decompose into per-element SetArrayElement records
    if decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
      if decl.value != nil and decl.value.kind == FznArrayLit:
        var elems = newSeq[SetArrayElement](decl.value.elems.len)
        for i, e in decl.value.elems:
          case e.kind
          of FznIdent:
            if e.ident in tr.setVarBoolPositions:
              elems[i] = SetArrayElement(isConstant: false, varName: e.ident)
            elif e.ident in tr.setParamValues:
              elems[i] = SetArrayElement(isConstant: true, constantValues: tr.setParamValues[e.ident])
            else:
              elems[i] = SetArrayElement(isConstant: true, constantValues: @[])
          of FznSetLit, FznRange:
            elems[i] = SetArrayElement(isConstant: true, constantValues: extractSetValues(e))
          else:
            elems[i] = SetArrayElement(isConstant: true, constantValues: @[])
        tr.setArrayDecompositions[decl.name] = elems
      if decl.hasAnnotation("output_array"):
        tr.outputSetArrays.incl(decl.name)
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
      if decl.varType.kind == FznBool:
        tr.outputBoolArrays.incl(decl.name)

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

proc tryTableFunctionalDep(tr: var FznTranslator, positions: seq[int],
                            tuples: seq[seq[int]]): bool =
  ## Detects functional keys in table constraints and converts dependent columns
  ## to channel variables. Checks single-column key (col 0) first, then
  ## composite 2-column key (cols 0,1). Returns true if the table was consumed.
  ## Note: only columns 0 and (0,1) are tried as keys. This relies on FlatZinc
  ## table constraints placing key columns first, which holds for MiniZinc's
  ## standard table decomposition.
  if positions.len < 2 or tuples.len == 0:
    return false

  # === Try single-column key (column 0) ===
  block singleKey:
    var keyValues: PackedSet[int]
    var keyMin = high(int)
    var keyMax = low(int)
    for t in tuples:
      let k = t[0]
      if k in keyValues:
        break singleKey  # duplicate key — not a single-column functional dependency
      keyValues.incl(k)
      if k < keyMin: keyMin = k
      if k > keyMax: keyMax = k

    let keyRange = keyMax - keyMin + 1
    if keyRange > tuples.len * 2:
      break singleKey  # too sparse

    let keyPos = positions[0]
    let nCols = positions.len

    var lookups = newSeq[seq[int]](nCols - 1)
    for col in 1..<nCols:
      lookups[col - 1] = newSeqWith(keyRange, low(int))
    for t in tuples:
      let idx = t[0] - keyMin
      for col in 1..<nCols:
        lookups[col - 1][idx] = t[col]

    let keyDomain = tr.sys.baseArray.domain[keyPos]
    var filteredDomain: seq[int]
    for v in keyDomain:
      if v in keyValues:
        filteredDomain.add(v)
    if filteredDomain.len < keyDomain.len:
      tr.sys.baseArray.domain[keyPos] = filteredDomain

    let keyExpr = tr.getExpr(keyPos) - keyMin
    for col in 1..<nCols:
      let depPos = positions[col]
      var arrayElems = newSeq[ArrayElement[int]](keyRange)
      for i in 0..<keyRange:
        arrayElems[i] = ArrayElement[int](isConstant: true, constantValue: lookups[col - 1][i])
      tr.sys.baseArray.addChannelBinding(depPos, keyExpr, arrayElems)

    return true

  # === Try 2-column composite key (columns 0, 1) ===
  if positions.len < 3:
    return false

  # Find min/max for both key columns
  var key0Min = high(int)
  var key0Max = low(int)
  var key1Min = high(int)
  var key1Max = low(int)
  for t in tuples:
    if t[0] < key0Min: key0Min = t[0]
    if t[0] > key0Max: key0Max = t[0]
    if t[1] < key1Min: key1Min = t[1]
    if t[1] > key1Max: key1Max = t[1]

  let range0 = key0Max - key0Min + 1
  let range1 = key1Max - key1Min + 1
  let totalRange = range0 * range1

  # Only convert if linearized array is not too large (max ~500K entries)
  if totalRange > 500_000 or totalRange > tuples.len * 5:
    return false

  # Verify all (col0, col1) pairs are unique
  var compositeKeys: PackedSet[int]
  for t in tuples:
    let linearKey = (t[0] - key0Min) * range1 + (t[1] - key1Min)
    if linearKey in compositeKeys:
      return false  # duplicate composite key
    compositeKeys.incl(linearKey)

  let nCols = positions.len
  let nDepCols = nCols - 2  # columns 2..n-1 are dependent

  # Build linearized lookup arrays for dependent columns (gaps get sentinel value)
  var lookups = newSeq[seq[int]](nDepCols)
  for col in 0..<nDepCols:
    lookups[col] = newSeqWith(totalRange, low(int))
  for t in tuples:
    let idx = (t[0] - key0Min) * range1 + (t[1] - key1Min)
    for col in 2..<nCols:
      lookups[col - 2][idx] = t[col]

  # Build composite index expression: (col0_expr - key0Min) * range1 + (col1_expr - key1Min)
  let expr0 = tr.getExpr(positions[0])
  let expr1 = tr.getExpr(positions[1])
  let compositeExpr = (expr0 - key0Min) * range1 + (expr1 - key1Min)

  # Create channel bindings for dependent columns
  for col in 2..<nCols:
    let depPos = positions[col]
    var arrayElems = newSeq[ArrayElement[int]](totalRange)
    for i in 0..<totalRange:
      arrayElems[i] = ArrayElement[int](isConstant: true, constantValue: lookups[col - 2][i])
    tr.sys.baseArray.addChannelBinding(depPos, compositeExpr, arrayElems)

  return true

proc resolveSetArg(tr: FznTranslator, arg: FznExpr): tuple[isConst: bool, constVals: HashSet[int], varInfo: SetVarInfo] =
  ## Resolves a FznExpr that refers to a set (variable or constant).
  ## Constant sets are returned as HashSet[int] for O(1) membership tests.
  case arg.kind
  of FznSetLit:
    return (true, toHashSet(arg.setElems), SetVarInfo())
  of FznRange:
    if arg.lo > arg.hi:
      return (true, initHashSet[int](), SetVarInfo())
    return (true, toHashSet(toSeq(arg.lo..arg.hi)), SetVarInfo())
  of FznIdent:
    if arg.ident in tr.setVarBoolPositions:
      return (false, initHashSet[int](), tr.setVarBoolPositions[arg.ident])
    elif arg.ident in tr.setParamValues:
      return (true, toHashSet(tr.setParamValues[arg.ident]), SetVarInfo())
    else:
      raise newException(KeyError, &"Unknown set identifier '{arg.ident}'")
  else:
    raise newException(ValueError, &"Cannot resolve {arg.kind} as set")

proc getSetBoolPosition(info: SetVarInfo, element: int): int {.inline.} =
  ## Returns the boolean variable position for a given element, or -1 if outside universe.
  if element < info.lo or element > info.hi:
    return -1
  return info.positions[element - info.lo]

proc constSetExpr(info: tuple[isConst: bool, constVals: HashSet[int], varInfo: SetVarInfo],
                  tr: FznTranslator, elem: int): AlgebraicExpression[int] =
  ## Returns an expression for a set's boolean value at `elem`:
  ## literal 0/1 for constant sets, variable expression for set variables.
  if info.isConst:
    let val = if elem in info.constVals: 1 else: 0
    return newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: val),
      linear = true)
  else:
    let pos = getSetBoolPosition(info.varInfo, elem)
    if pos >= 0:
      return tr.getExpr(pos)
    else:
      return newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: 0),
        linear = true)

proc getFixedOnePos(tr: var FznTranslator): int =
  ## Returns the position of a reusable variable fixed to 1.
  ## Creates it on first call, reuses it on subsequent calls.
  if tr.fixedOnePos < 0:
    tr.fixedOnePos = tr.sys.baseArray.len
    let v = tr.sys.newConstrainedVariable()
    v.setDomain(@[1])
  return tr.fixedOnePos

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
    let sp = scalarProduct[int](coeffs, exprs)
    if con.args[3].kind == FznBoolLit:
      if con.args[3].boolVal:
        tr.sys.addConstraint(sp == rhs)
      else:
        tr.sys.addConstraint(sp != rhs)
    else:
      let bExpr = tr.resolveExprArg(con.args[3])
      tr.sys.addConstraint((sp == rhs) <-> (bExpr == 1))

  of "int_lin_le_reif":
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let sp = scalarProduct[int](coeffs, exprs)
    if con.args[3].kind == FznBoolLit:
      if con.args[3].boolVal:
        tr.sys.addConstraint(sp <= rhs)
      else:
        tr.sys.addConstraint(sp > rhs)
    else:
      let bExpr = tr.resolveExprArg(con.args[3])
      tr.sys.addConstraint((sp <= rhs) <-> (bExpr == 1))

  of "int_lin_ne_reif":
    let coeffs = tr.resolveIntArray(con.args[0])
    let exprs = tr.resolveExprArray(con.args[1])
    let rhs = tr.resolveIntArg(con.args[2])
    let sp = scalarProduct[int](coeffs, exprs)
    if con.args[3].kind == FznBoolLit:
      if con.args[3].boolVal:
        tr.sys.addConstraint(sp != rhs)
      else:
        tr.sys.addConstraint(sp == rhs)
    else:
      let bExpr = tr.resolveExprArg(con.args[3])
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

  of "array_var_bool_element", "array_var_bool_element_nonshifted":
    # Same as array_var_int_element but with booleans (bools are 0/1 ints)
    let indexExpr = tr.resolveExprArg(con.args[0])
    let valueExpr = tr.resolveExprArg(con.args[2])
    let adjustedIndex = indexExpr - 1

    var emitted = false
    if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode and
       tr.matrixInfos.len > 0:
        let inlineElems = tr.resolveMixedArray(con.args[1])
        let indexPos = adjustedIndex.node.position
        let valuePos = valueExpr.node.position
        for name, minfo in tr.matrixInfos:
            let rowIdx = tr.matchMatrixRow(inlineElems, minfo)
            if rowIdx >= 0:
                tr.sys.addConstraint(stateful.matrixElement[int](
                    minfo.elements, minfo.numRows, minfo.numCols,
                    rowIdx, indexPos, valuePos))
                emitted = true
                break
            let colIdx = tr.matchMatrixCol(inlineElems, minfo)
            if colIdx >= 0:
                tr.sys.addConstraint(stateful.matrixElement[int](
                    minfo.elements, minfo.numRows, minfo.numCols,
                    indexPos, colIdx, valuePos, rowIsVariable = true))
                emitted = true
                break

    if not emitted:
        let arrayExprs = tr.resolveExprArray(con.args[1])
        if adjustedIndex.node.kind == RefNode and valueExpr.node.kind == RefNode:
            let mixedElems = tr.resolveMixedArray(con.args[1])
            tr.sys.addConstraint(element(adjustedIndex, mixedElems, valueExpr))
        else:
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

  of "bool_clause_reif":
    # bool_clause_reif(pos_lits, neg_lits, b) means b <-> (OR(pos) OR NOT(neg))
    let posExprs = tr.resolveExprArray(con.args[0])
    let negExprs = tr.resolveExprArray(con.args[1])
    let bExpr = tr.resolveExprArg(con.args[2])
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
      tr.sys.addConstraint((sp >= 1 - negExprs.len) <-> (bExpr == 1))
    else:
      # Empty clause is always false
      tr.sys.addConstraint(bExpr == 0)

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
    # Limit might be a variable - try constant, fall back to variable limit
    var limit: int
    var limitPos = -1
    try:
      limit = tr.resolveIntArg(con.args[3])
    except:
      # Variable limit - extract position, use domain upper bound as initial value
      let limitExpr = tr.resolveExprArg(con.args[3])
      if limitExpr.node.kind == RefNode:
        limitPos = limitExpr.node.position
        let dom = tr.sys.baseArray.domain[limitPos]
        limit = dom[^1]  # upper bound as initial value
      else:
        limit = 10  # fallback
    tr.sys.addConstraint(cumulative[int](startExprs, durations, heights, limit, limitPos))

  of "fzn_disjunctive", "fzn_disjunctive_strict":
    # disjunctive(starts, durations) = cumulative(starts, durations, heights=[1,...], limit=1)
    let startExprs = tr.resolveExprArray(con.args[0])
    var durations: seq[int]
    try:
      durations = tr.resolveIntArray(con.args[1])
    except CatchableError:
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
            durations[i] = dom[dom.len div 2]
            stderr.writeLine(&"[FZN] Warning: disjunctive duration variable has non-singleton domain (size {dom.len}), using median value {durations[i]}")
    let heights = newSeqWith(durations.len, 1)
    tr.sys.addConstraint(cumulative[int](startExprs, durations, heights, 1))

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

  of "fzn_connected":
    # fzn_connected(from, to, ns, es)
    # from, to: constant int arrays (1-based node indices for edge endpoints)
    # ns: var bool array (node activity)
    # es: var bool array (edge activity)
    let fromArr = tr.resolveIntArray(con.args[0])
    let toArr = tr.resolveIntArray(con.args[1])
    let nsExprs = tr.resolveExprArray(con.args[2])
    let esExprs = tr.resolveExprArray(con.args[3])

    # Extract node positions
    var nodePositions: seq[int]
    for e in nsExprs:
      if e.node.kind == RefNode:
        nodePositions.add(e.node.position)
      elif e.node.kind == LiteralNode:
        let pos = tr.sys.baseArray.len
        let v = tr.sys.newConstrainedVariable()
        v.setDomain(@[int(e.node.value)])
        nodePositions.add(pos)
      else:
        raise newException(ValueError, "fzn_connected: unsupported ns expression node kind " & $e.node.kind)

    # Extract edge positions
    var edgePositions: seq[int]
    for e in esExprs:
      if e.node.kind == RefNode:
        edgePositions.add(e.node.position)
      elif e.node.kind == LiteralNode:
        let pos = tr.sys.baseArray.len
        let v = tr.sys.newConstrainedVariable()
        v.setDomain(@[int(e.node.value)])
        edgePositions.add(pos)
      else:
        raise newException(ValueError, "fzn_connected: unsupported es expression node kind " & $e.node.kind)

    # Convert from/to from 1-based MiniZinc to 0-based node indices
    var from0 = newSeq[int](fromArr.len)
    var to0 = newSeq[int](toArr.len)
    for i in 0..<fromArr.len:
      from0[i] = fromArr[i] - 1
      to0[i] = toArr[i] - 1

    tr.sys.addConstraint(connected[int](nodePositions, edgePositions, from0, to0))

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

    # Pre-filter: detect singleton-domain columns (constants) and filter tuples
    # to matching rows, then project out constant columns. This is critical for
    # tables like preferences_data where a user_id column is fixed per constraint.
    var singletonCols: PackedSet[int]  # column indices with singleton domains
    var singletonVals: Table[int, int] # col -> constant value for each singleton column
    let (allRefs, positions) = isAllRefs(exprs)
    if allRefs:
      for col in 0..<arity:
        let pos = positions[col]
        if tr.sys.baseArray.domain[pos].len == 1:
          singletonCols.incl(col)
          singletonVals[col] = tr.sys.baseArray.domain[pos][0]

    if singletonCols.len > 0 and singletonCols.len < arity:
      # Filter tuples to only those matching all singleton column values
      var filtered: seq[seq[int]]
      for t in tuples:
        var matches = true
        for col in singletonCols.items:
          if t[col] != singletonVals[col]:
            matches = false
            break
        if matches:
          # Project out singleton columns
          var projected = newSeq[int](arity - singletonCols.len)
          var j = 0
          for col in 0..<arity:
            if col notin singletonCols:
              projected[j] = t[col]
              inc j
          filtered.add(projected)

      # Build reduced position array (exclude singleton columns)
      var reducedPositions: seq[int]
      for col in 0..<arity:
        if col notin singletonCols:
          reducedPositions.add(positions[col])

      if filtered.len > 0:
        # Try functional dependency: if col0 values are unique, dependent cols become channels
        if not tr.tryTableFunctionalDep(reducedPositions, filtered):
          tr.sys.addConstraint(tableIn[int](reducedPositions, filtered))
      else:
        stderr.writeLine("[FznTranslator] WARNING: table constraint has 0 matching tuples after singleton filtering — infeasible")
    elif allRefs:
      # Try functional dependency on the original table
      if not tr.tryTableFunctionalDep(positions, tuples):
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
    # Pigeon-hole tightening: derive effective bounds from total item count
    # If n items must be distributed across cover.len slots with bounds [lb, ub],
    # then each slot i must have at least n - sum(ub[j] for j != i) items
    # and at most n - sum(lb[j] for j != i) items.
    let sumLbound = lbound.foldl(a + b, 0)
    let sumUbound = ubound.foldl(a + b, 0)
    var effectiveLbound = newSeq[int](cover.len)
    var effectiveUbound = newSeq[int](cover.len)
    for i in 0..<cover.len:
      effectiveLbound[i] = max(lbound[i], n - (sumUbound - ubound[i]))
      effectiveUbound[i] = min(ubound[i], n - (sumLbound - lbound[i]))
    # Same cardinality logic as open variant, using tightened bounds
    for i in 0..<cover.len:
      if effectiveLbound[i] > 0:
        tr.sys.addConstraint(atLeast[int](exprs, cover[i], effectiveLbound[i]))
      if effectiveUbound[i] < n:
        tr.sys.addConstraint(atMost[int](exprs, cover[i], effectiveUbound[i]))

  of "fzn_global_cardinality_low_up":
    # global_cardinality_low_up(x, cover, lbound, ubound)
    # For each i: lbound[i] <= count(x, cover[i]) <= ubound[i]
    # Skip trivial bounds; emit atLeast/atMost for non-trivial ones.
    # Note: open variant — items can take values outside cover set,
    # so pigeon-hole lower bound tightening does NOT apply (items can
    # escape to uncovered values). Upper bound tightening is still valid.
    let exprs = tr.resolveExprArray(con.args[0])
    let cover = tr.resolveIntArray(con.args[1])
    let lbound = tr.resolveIntArray(con.args[2])
    let ubound = tr.resolveIntArray(con.args[3])
    let n = exprs.len
    # Upper bound tightening: count[i] <= n - sum(lbound[j] for j != i)
    let sumLbound = lbound.foldl(a + b, 0)
    for i in 0..<cover.len:
      if lbound[i] > 0:
        tr.sys.addConstraint(atLeast[int](exprs, cover[i], lbound[i]))
      let effectiveUbound = min(ubound[i], n - (sumLbound - lbound[i]))
      if effectiveUbound < n:
        tr.sys.addConstraint(atMost[int](exprs, cover[i], effectiveUbound))

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
    let xArg = con.args[0]
    let sArg = con.args[1]
    let sInfo = tr.resolveSetArg(sArg)
    if sInfo.isConst:
      # S is a constant set — restrict x's domain (already handled by FlatZinc domain)
      if xArg.kind == FznIdent and xArg.ident in tr.varPositions:
        let pos = tr.varPositions[xArg.ident]
        let currentDom = tr.sys.baseArray.domain[pos]
        var newDom: seq[int]
        for v in currentDom:
          if v in sInfo.constVals:
            newDom.add(v)
        if newDom.len > 0 and newDom.len < currentDom.len:
          tr.sys.baseArray.setDomain(pos, newDom)
    else:
      # S is a set variable
      let info = sInfo.varInfo
      if xArg.kind == FznIntLit or (xArg.kind == FznIdent and xArg.ident in tr.paramValues):
        # x is a constant literal: fix S.bools[x - lo] to 1
        let xVal = tr.resolveIntArg(xArg)
        let bpos = getSetBoolPosition(info, xVal)
        if bpos >= 0:
          tr.sys.baseArray.setDomain(bpos, @[1])
      elif xArg.kind == FznIdent and xArg.ident in tr.varPositions:
        # x is a variable, S is a set variable: S.bools[x - lo] == 1
        # Restrict x's domain to S's universe
        let xPos = tr.varPositions[xArg.ident]
        let currentDom = tr.sys.baseArray.domain[xPos]
        var newDom: seq[int]
        for v in currentDom:
          if v >= info.lo and v <= info.hi:
            newDom.add(v)
        if newDom.len > 0 and newDom.len < currentDom.len:
          tr.sys.baseArray.setDomain(xPos, newDom)
        # Build element constraint: element(x - lo, S.bools) == 1
        let xExpr = tr.getExpr(xPos)
        let indexExpr = xExpr - info.lo
        var arrayElems: seq[ArrayElement[int]]
        for bpos in info.positions:
          arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: bpos))
        tr.sys.baseArray.addChannelBinding(tr.getFixedOnePos(), indexExpr, arrayElems)

  of "set_card":
    # set_card(S, c) means |S| == c
    let sArg = con.args[0]
    let cArg = con.args[1]
    let sInfo = tr.resolveSetArg(sArg)
    if sInfo.isConst:
      # S is a constant set — c must equal |S|
      let cardVal = sInfo.constVals.len
      if cArg.kind == FznIdent and cArg.ident in tr.varPositions:
        let cPos = tr.varPositions[cArg.ident]
        tr.sys.baseArray.setDomain(cPos, @[cardVal])
    else:
      # S is a set variable — sum(S.bools) == c
      let info = sInfo.varInfo
      if info.positions.len == 0:
        # Empty universe set — cardinality must be 0
        if cArg.kind == FznIdent and cArg.ident in tr.varPositions:
          tr.sys.baseArray.setDomain(tr.varPositions[cArg.ident], @[0])
      else:
        var boolExprs = newSeq[AlgebraicExpression[int]](info.positions.len)
        for i, bpos in info.positions:
          boolExprs[i] = tr.getExpr(bpos)
        let sumExpr = sum(boolExprs)
        let cExpr = tr.resolveExprArg(cArg)
        tr.sys.addConstraint(sumExpr == cExpr)

  of "set_union":
    # set_union(A, B, C) means C = A ∪ B
    # For each element e in universe: C.bools[e-lo] = max(A.bools[e-lo], B.bools[e-lo])
    # Note: unions with defines_var(C) are detected as channels and get hard channel
    # bindings in buildSetUnionChannelBindings; this soft constraint path handles
    # non-channel unions only.
    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])
    let cInfo = tr.resolveSetArg(con.args[2])
    if cInfo.isConst:
      discard  # Constant result — no constraint needed
    else:
      let cVar = cInfo.varInfo
      for idx in 0..<cVar.positions.len:
        let elem = cVar.lo + idx
        let cBoolPos = cVar.positions[idx]
        let aExpr = constSetExpr(aInfo, tr, elem)
        let bExpr = constSetExpr(bInfo, tr, elem)
        let cExpr = tr.getExpr(cBoolPos)
        tr.sys.addConstraint(cExpr == binaryMax(aExpr, bExpr))

  of "set_intersect":
    # set_intersect(A, B, C) means C = A ∩ B
    # For each element e: C.bools[e-lo] = min(A.bools[e-lo], B.bools[e-lo])
    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])
    let cInfo = tr.resolveSetArg(con.args[2])
    if cInfo.isConst:
      discard
    else:
      let cVar = cInfo.varInfo
      for idx in 0..<cVar.positions.len:
        let elem = cVar.lo + idx
        let cBoolPos = cVar.positions[idx]
        let aExpr = constSetExpr(aInfo, tr, elem)
        let bExpr = constSetExpr(bInfo, tr, elem)
        let cExpr = tr.getExpr(cBoolPos)
        tr.sys.addConstraint(cExpr == binaryMin(aExpr, bExpr))

  of "set_in_reif":
    # set_in_reif(x, S, b) means b ↔ (x ∈ S)
    let xArg = con.args[0]
    let sArg = con.args[1]
    let bArg = con.args[2]
    let sInfo = tr.resolveSetArg(sArg)
    if not sInfo.isConst and xArg.kind == FznIdent and xArg.ident in tr.setVarBoolPositions:
      # Both x and S are set variables — skip (not expected in practice)
      discard
    elif not sInfo.isConst:
      # S is a set variable, x is int/bool
      let info = sInfo.varInfo
      if xArg.kind == FznIntLit or (xArg.kind == FznIdent and xArg.ident in tr.paramValues):
        # x is a constant: b = S.bools[x - lo]
        let xVal = tr.resolveIntArg(xArg)
        let bpos = getSetBoolPosition(info, xVal)
        if bpos >= 0:
          let bExpr = tr.resolveExprArg(bArg)
          let sBoolExpr = tr.getExpr(bpos)
          tr.sys.addConstraint(bExpr == sBoolExpr)
        else:
          # x outside universe — b must be 0
          if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
            tr.sys.baseArray.setDomain(tr.varPositions[bArg.ident], @[0])
      elif xArg.kind == FznIdent and xArg.ident in tr.varPositions:
        # x is a variable: b = element(x - lo, S.bools)
        let xPos = tr.varPositions[xArg.ident]
        let xExpr = tr.getExpr(xPos)
        var arrayElems: seq[ArrayElement[int]]
        # Build array covering x's domain range (out-of-universe values map to 0)
        let xDom = tr.sys.baseArray.domain[xPos]
        let arrLo = xDom[0]
        let arrHi = xDom[^1]
        for v in arrLo..arrHi:
          let bpos = getSetBoolPosition(info, v)
          if bpos >= 0:
            arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: bpos))
          else:
            arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
        if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
          let bPos = tr.varPositions[bArg.ident]
          let adjIndexExpr = xExpr - arrLo
          tr.sys.baseArray.addChannelBinding(bPos, adjIndexExpr, arrayElems)
    else:
      # S is a constant set — b ↔ (x ∈ S) via domain lookup table
      let setAsHashSet = sInfo.constVals
      if xArg.kind == FznIdent and xArg.ident in tr.varPositions:
        let xPos = tr.varPositions[xArg.ident]
        let xExpr = tr.getExpr(xPos)
        let domain = tr.sys.baseArray.domain[xPos]
        if domain.len > 0:
          let lo = domain[0]
          let indexExpr = xExpr - lo
          var arrayElems: seq[ArrayElement[int]]
          for v in domain:
            arrayElems.add(ArrayElement[int](isConstant: true,
                constantValue: if v in setAsHashSet: 1 else: 0))
          if bArg.kind == FznIdent and bArg.ident in tr.varPositions:
            let bPos = tr.varPositions[bArg.ident]
            tr.sys.baseArray.addChannelBinding(bPos, indexExpr, arrayElems)

  of "array_var_set_element":
    # array_var_set_element(idx, [S1, S2, ...], R) means R = array[idx]
    # For each element e in R's universe: R.bools[e-lo] = element(idx, [S1.bools[e-lo], S2.bools[e-lo], ...])
    let idxArg = con.args[0]
    let arrArg = con.args[1]
    let rArg = con.args[2]

    # Resolve the result set variable
    let rInfo = tr.resolveSetArg(rArg)
    if rInfo.isConst:
      discard  # Result is constant — skip
    else:
      let rVar = rInfo.varInfo

      # Resolve the array of set variables/constants
      var setElems: seq[SetArrayElement]
      case arrArg.kind
      of FznIdent:
        if arrArg.ident in tr.setArrayDecompositions:
          setElems = tr.setArrayDecompositions[arrArg.ident]
        elif arrArg.ident in tr.setArrayValues:
          let vals = tr.setArrayValues[arrArg.ident]
          for sv in vals:
            setElems.add(SetArrayElement(isConstant: true, constantValues: sv))
        else:
          discard  # Unknown array
      of FznArrayLit:
        for e in arrArg.elems:
          let si = tr.resolveSetArg(e)
          if si.isConst:
            setElems.add(SetArrayElement(isConstant: true, constantValues: toSeq(si.constVals)))
          else:
            setElems.add(SetArrayElement(isConstant: false, varName: e.ident))
      else:
        discard

      if setElems.len > 0:
        # Resolve index expression (FZN element is 1-indexed)
        let idxExpr = tr.resolveExprArg(idxArg)
        let indexExpr = idxExpr - 1  # Convert to 0-based

        # For each boolean position in R's universe
        for idx in 0..<rVar.positions.len:
          let elem = rVar.lo + idx
          let rBoolPos = rVar.positions[idx]

          # Build array elements: for each set in the array, get the boolean for this element
          var arrayElems: seq[ArrayElement[int]]
          for se in setElems:
            if se.isConstant:
              arrayElems.add(ArrayElement[int](isConstant: true,
                  constantValue: if elem in se.constantValues: 1 else: 0))
            else:
              if se.varName in tr.setVarBoolPositions:
                let svi = tr.setVarBoolPositions[se.varName]
                let bpos = getSetBoolPosition(svi, elem)
                if bpos >= 0:
                  arrayElems.add(ArrayElement[int](isConstant: false, variablePosition: bpos))
                else:
                  arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
              else:
                arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))

          # R.bools[elem] = element(idx - 1, [array of bools for this element])
          tr.sys.baseArray.addChannelBinding(rBoolPos, indexExpr, arrayElems)

  of "set_diff":
    # set_diff(A, B, C) means C = A \ B
    # C.bools[i] = min(A.bools[i], 1 - B.bools[i])
    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])
    let cInfo = tr.resolveSetArg(con.args[2])
    if cInfo.isConst:
      discard
    else:
      let cVar = cInfo.varInfo
      for idx in 0..<cVar.positions.len:
        let elem = cVar.lo + idx
        let cBoolPos = cVar.positions[idx]
        let aExpr = constSetExpr(aInfo, tr, elem)
        let bVal = constSetExpr(bInfo, tr, elem)
        let oneExpr = newAlgebraicExpression[int](
          positions = initPackedSet[int](),
          node = ExpressionNode[int](kind: LiteralNode, value: 1),
          linear = true)
        let cExpr = tr.getExpr(cBoolPos)
        tr.sys.addConstraint(cExpr == binaryMin(aExpr, oneExpr - bVal))

  of "set_subset":
    # set_subset(A, B) means A ⊆ B
    # For each element: A.bools[i] <= B.bools[i]
    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])
    if aInfo.isConst and not bInfo.isConst:
      # Every constant element of A must be in B
      let bVar = bInfo.varInfo
      for elem in aInfo.constVals:
        let bpos = getSetBoolPosition(bVar, elem)
        if bpos >= 0:
          tr.sys.baseArray.setDomain(bpos, @[1])
    elif not aInfo.isConst and bInfo.isConst:
      # Every element of A must be in constant B
      let aVar = aInfo.varInfo
      for idx in 0..<aVar.positions.len:
        let elem = aVar.lo + idx
        if elem notin bInfo.constVals:
          tr.sys.baseArray.setDomain(aVar.positions[idx], @[0])
    elif not aInfo.isConst and not bInfo.isConst:
      # A.bools[i] <= B.bools[i] for all i in shared universe
      let aVar = aInfo.varInfo
      let bVar = bInfo.varInfo
      let lo = max(aVar.lo, bVar.lo)
      let hi = min(aVar.hi, bVar.hi)
      for elem in lo..hi:
        let aPos = getSetBoolPosition(aVar, elem)
        let bPos = getSetBoolPosition(bVar, elem)
        if aPos >= 0 and bPos >= 0:
          tr.sys.addConstraint(tr.getExpr(aPos) <= tr.getExpr(bPos))
      # Elements in A outside B's universe must be 0
      for idx in 0..<aVar.positions.len:
        let elem = aVar.lo + idx
        if elem < bVar.lo or elem > bVar.hi:
          tr.sys.baseArray.setDomain(aVar.positions[idx], @[0])

  of "set_eq":
    # set_eq(A, B) means A = B (all booleans equal)
    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])
    if aInfo.isConst and not bInfo.isConst:
      # Fix B's booleans to match constant A
      let bVar = bInfo.varInfo
      let constSet = aInfo.constVals
      for idx in 0..<bVar.positions.len:
        let elem = bVar.lo + idx
        if elem in constSet:
          tr.sys.baseArray.setDomain(bVar.positions[idx], @[1])
        else:
          tr.sys.baseArray.setDomain(bVar.positions[idx], @[0])
    elif not aInfo.isConst and bInfo.isConst:
      let aVar = aInfo.varInfo
      let constSet = bInfo.constVals
      for idx in 0..<aVar.positions.len:
        let elem = aVar.lo + idx
        if elem in constSet:
          tr.sys.baseArray.setDomain(aVar.positions[idx], @[1])
        else:
          tr.sys.baseArray.setDomain(aVar.positions[idx], @[0])
    elif not aInfo.isConst and not bInfo.isConst:
      let aVar = aInfo.varInfo
      let bVar = bInfo.varInfo
      let lo = min(aVar.lo, bVar.lo)
      let hi = max(aVar.hi, bVar.hi)
      for elem in lo..hi:
        let aPos = getSetBoolPosition(aVar, elem)
        let bPos = getSetBoolPosition(bVar, elem)
        if aPos >= 0 and bPos >= 0:
          tr.sys.addConstraint(tr.getExpr(aPos) == tr.getExpr(bPos))
        elif aPos >= 0:
          tr.sys.baseArray.setDomain(aPos, @[0])
        elif bPos >= 0:
          tr.sys.baseArray.setDomain(bPos, @[0])

  of "set_ne":
    # set_ne(A, B) means A ≠ B — at least one boolean differs
    # sum(|A[i] - B[i]|) >= 1 (exact for booleans: |a-b| = a+b - 2*min(a,b))
    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])
    if not aInfo.isConst and not bInfo.isConst:
      let aVar = aInfo.varInfo
      let bVar = bInfo.varInfo
      let lo = min(aVar.lo, bVar.lo)
      let hi = max(aVar.hi, bVar.hi)
      var diffExprs: seq[AlgebraicExpression[int]]
      for elem in lo..hi:
        let aExpr = constSetExpr(aInfo, tr, elem)
        let bExpr = constSetExpr(bInfo, tr, elem)
        diffExprs.add(aExpr + bExpr - 2 * binaryMin(aExpr, bExpr))
      if diffExprs.len > 0:
        tr.sys.addConstraint(sum(diffExprs) >= 1)

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
        if objName == tr.weightedSameValueObjName:
          # Weighted same-value objective — handled separately via WeightedSameValueExpression
          tr.objectivePos = ObjPosWeightedSV
        elif objName in tr.varPositions:
          tr.objectivePos = tr.varPositions[objName]
          # Extract domain bounds from the variable declaration for the optimizer
          for decl in tr.model.variables:
            if not decl.isArray and decl.name == objName:
              if decl.varType.kind == FznIntRange:
                tr.objectiveLoBound = decl.varType.lo
                tr.objectiveHiBound = decl.varType.hi
              break
        elif objName in tr.definedVarExprs:
          # Objective was eliminated as a defined variable — use its defining expression directly.
          # This avoids an intermediate position + binary-penalty linking constraint,
          # which would hide objective gradient from compound moves (ejection chains).
          tr.objectiveDefExpr = tr.definedVarExprs[objName]
          tr.objectivePos = ObjPosDefinedExpr
        else:
          raise newException(KeyError, &"Unknown objective variable '{objName}'")
      else:
        raise newException(ValueError, "Objective must be a variable identifier")
  of Satisfy:
    tr.objectivePos = ObjPosNone

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
  # Third loop: identify int_abs, int_max, int_min, int_times with defines_var annotations
  # int_min/int_max become channel variables (like array_int_minimum/maximum) to avoid
  # deep expression tree inlining that creates exponentially large DAGs.
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name in ["int_abs", "int_max", "int_min", "int_times"] and con.hasAnnotation("defines_var"):
      let ann = con.getAnnotation("defines_var")
      if ann.args.len > 0 and ann.args[0].kind == FznIdent:
        let definedName = ann.args[0].ident
        # int_abs(a, b) :: defines_var(b) → b is args[1]
        # int_max(a, b, c) :: defines_var(c) → c is args[2]
        # int_min(a, b, c) :: defines_var(c) → c is args[2]
        # int_times(a, b, c) :: defines_var(c) → c is args[2]
        let expectedIdx = if name == "int_abs": 1 else: 2
        if con.args[expectedIdx].kind == FznIdent and
           con.args[expectedIdx].ident == definedName:
          if name in ["int_min", "int_max"]:
            # Make int_min/int_max into channel variables to avoid deep expression DAGs
            let isMin = name == "int_min"
            tr.channelVarNames.incl(definedName)
            tr.definingConstraints.incl(ci)
            tr.minMaxChannelDefs.add((ci: ci, varName: definedName, isMin: isMin))
          else:
            definedVarNames[definedName] = true
            tr.definingConstraints.incl(ci)
    # array_int_minimum(m, array) :: defines_var(m) → channel variable (not searched)
    # array_int_maximum(m, array) :: defines_var(m) → channel variable (not searched)
    elif name in ["array_int_minimum", "array_int_maximum"] and con.hasAnnotation("defines_var"):
      let ann = con.getAnnotation("defines_var")
      if ann.args.len > 0 and ann.args[0].kind == FznIdent:
        let definedName = ann.args[0].ident
        if con.args[0].kind == FznIdent and con.args[0].ident == definedName:
          let isMin = name == "array_int_minimum"
          tr.channelVarNames.incl(definedName)
          tr.definingConstraints.incl(ci)
          tr.minMaxChannelDefs.add((ci: ci, varName: definedName, isMin: isMin))

  # Refine int_min/int_max channel decisions: only keep as channels when inputs
  # reference other channels (risk of exponential DAG growth from chained inlining).
  # Simple binary min/max (e.g., max(abs(x-y), abs(a-b))) can be safely inlined
  # as defined var expressions, giving the solver direct gradient through penalty maps.
  block:
    var refined: seq[tuple[ci: int, varName: string, isMin: bool]]
    for def in tr.minMaxChannelDefs:
      let con = tr.model.constraints[def.ci]
      let cname = stripSolverPrefix(con.name)
      var inputsRefChannel = false
      if cname in ["int_min", "int_max"]:
        for argIdx in 0..1:
          let arg = con.args[argIdx]
          if arg.kind == FznIdent and arg.ident in tr.channelVarNames:
            inputsRefChannel = true
            break
      else:
        # array_int_minimum/maximum — variable-length arrays, keep as channels
        inputsRefChannel = true
      if inputsRefChannel:
        refined.add(def)
      else:
        # Safe to inline as defined var expression
        tr.channelVarNames.excl(def.varName)
        definedVarNames[def.varName] = true
    tr.minMaxChannelDefs = refined

  # Detect int_times(a, b, c) WITHOUT defines_var where c can be treated as defined.
  # MiniZinc sometimes doesn't annotate cube variables (x^2 * x = x^3) with defines_var
  # even though the result is fully determined. These can have enormous domains (54M+).
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "int_times": continue
    if con.hasAnnotation("defines_var"): continue  # already handled above
    if con.args.len < 3: continue
    # int_times(a, b, c): c = a * b
    let cArg = con.args[2]
    if cArg.kind != FznIdent: continue
    let cName = cArg.ident
    if cName in definedVarNames or cName in tr.channelVarNames: continue
    # Check that a and b are resolvable (constants, positioned vars, or defined vars)
    var resolvable = true
    for idx in 0..1:
      let arg = con.args[idx]
      if arg.kind == FznIdent:
        let id = arg.ident
        if id notin tr.paramValues and id notin definedVarNames and
           id notin tr.channelVarNames:
          # It's a free variable — that's ok, it will get a position
          discard
      elif arg.kind != FznIntLit:
        resolvable = false
    if resolvable:
      definedVarNames[cName] = true
      tr.definingConstraints.incl(ci)

  # Store the set of defined variable names for use in translateVariables
  for name in definedVarNames.keys:
    tr.definedVarNames.incl(name)

  # Second loop: identify element constraints with defines_var annotations
  # These define channel variables that should be computed, not searched
  # Also deduplicate: when multiple constant-array element constraints share the same
  # index variable and array content, only the first becomes a channel; duplicates
  # become defined-variable aliases (eliminated, no position allocated).
  type ElementKey = tuple[indexVar: string, arrayHash: Hash, arrayLen: int]
  var elementChannelMap: Table[ElementKey, string]  # key -> first channel var name
  var elementArrayCache: Table[string, seq[int]]  # channel var name -> resolved array (for verification)
  var nElementAliases = 0
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name in ["array_var_int_element", "array_var_int_element_nonshifted",
                "array_int_element", "array_int_element_nonshifted",
                "array_var_bool_element", "array_var_bool_element_nonshifted",
                "array_bool_element"] and
       con.hasAnnotation("defines_var"):
      # Extract the defined variable name from the 3rd argument
      if con.args[2].kind == FznIdent:
        let definedName = con.args[2].ident
        let ann = con.getAnnotation("defines_var")
        if ann.args.len > 0 and ann.args[0].kind == FznIdent and
           ann.args[0].ident == definedName:
          # Try to deduplicate constant-array element constraints
          var deduplicated = false
          if name in ["array_int_element", "array_int_element_nonshifted",
                      "array_bool_element"] and
             con.args[0].kind == FznIdent:
            let indexVar = con.args[0].ident
            try:
              let constArray = tr.resolveIntArray(con.args[1])
              let key: ElementKey = (indexVar, hash(constArray), constArray.len)
              if key in elementChannelMap:
                # Verify content match (hash collision guard)
                let originalName = elementChannelMap[key]
                if elementArrayCache[originalName] == constArray:
                  # Duplicate! Make this a defined-var alias instead of a channel
                  tr.elementChannelAliases[definedName] = originalName
                  tr.definedVarNames.incl(definedName)
                  tr.definingConstraints.incl(ci)
                  deduplicated = true
                  nElementAliases += 1
              else:
                elementChannelMap[key] = definedName
                elementArrayCache[definedName] = constArray
            except KeyError:
              discard  # array resolution failed, skip dedup

          if not deduplicated:
            tr.channelVarNames.incl(definedName)
            tr.channelConstraints[ci] = definedName
            # DO NOT add to definedVarNames (channel vars need positions)
            tr.definingConstraints.incl(ci)  # Channel binding replaces this constraint
  if nElementAliases > 0:
    stderr.writeLine(&"[FZN] Deduplicated {nElementAliases} element channels (shared index+array)")

  # Dead element channel elimination: detect element channel variables that
  # are not referenced by any constraint other than their own defining constraint.
  # These are "dead" channels (e.g., stock lookups when symmetry breaking is disabled)
  # and can be eliminated.
  block:
    # Collect variable references per constraint (excluding only the channel's own
    # defining constraint, not all defining constraints — other defining constraints
    # like the objective's int_lin_eq may reference channels that must be kept alive).
    # Build a set of all variable references from non-defining constraints,
    # PLUS references from defining constraints that define OTHER variables.
    # For each element channel, it's "dead" only if no constraint other than its
    # own defining constraint references it.

    # First: build per-constraint reference sets for defining constraints
    var definingRefs: Table[int, HashSet[string]]
    for ci in tr.definingConstraints:
      let con = tr.model.constraints[ci]
      var refs = initHashSet[string]()
      for arg in con.args:
        if arg.kind == FznIdent:
          refs.incl(arg.ident)
        elif arg.kind == FznArrayLit:
          for elem in arg.elems:
            if elem.kind == FznIdent:
              refs.incl(elem.ident)
      definingRefs[ci] = refs

    # Collect all variable references from non-defining constraints
    var referencedVars = initHashSet[string]()
    for ci, con in tr.model.constraints:
      if ci in tr.definingConstraints:
        continue
      for arg in con.args:
        if arg.kind == FznIdent:
          referencedVars.incl(arg.ident)
        elif arg.kind == FznArrayLit:
          for elem in arg.elems:
            if elem.kind == FznIdent:
              referencedVars.incl(elem.ident)
      # Also check annotation args (some constraints reference vars in annotations)
      for ann in con.annotations:
        for annArg in ann.args:
          if annArg.kind == FznIdent:
            referencedVars.incl(annArg.ident)
    # Also check array variable declarations (vars referenced as array elements)
    for decl in tr.model.variables:
      if decl.value != nil and decl.value.kind == FznArrayLit:
        for elem in decl.value.elems:
          if elem.kind == FznIdent:
            referencedVars.incl(elem.ident)

    # Build reverse alias map: original channel name → set of alias names
    var aliasesOf = initTable[string, seq[string]]()
    for aliasName, originalName in tr.elementChannelAliases:
      if originalName notin aliasesOf:
        aliasesOf[originalName] = @[]
      aliasesOf[originalName].add(aliasName)

    # Check each element channel: if neither it nor any alias is referenced, eliminate it
    # A channel is referenced if:
    #   1. It appears in a non-defining constraint, OR
    #   2. It appears in a defining constraint OTHER than its own
    var nDeadChannels = 0
    var deadCIs: seq[int] = @[]
    for ci, chanName in tr.channelConstraints:
      var isReferenced = chanName in referencedVars
      if not isReferenced:
        # Check aliases
        if chanName in aliasesOf:
          for aliasName in aliasesOf[chanName]:
            if aliasName in referencedVars:
              isReferenced = true
              break
      if not isReferenced:
        # Check if any OTHER defining constraint references this channel
        for defCi, refs in definingRefs:
          if defCi == ci:
            continue  # skip own defining constraint
          if chanName in refs:
            isReferenced = true
            break
          if chanName in aliasesOf:
            for aliasName in aliasesOf[chanName]:
              if aliasName in refs:
                isReferenced = true
                break
          if isReferenced:
            break
      if not isReferenced:
        # Dead channel: convert to defined var (no position needed)
        tr.channelVarNames.excl(chanName)
        tr.definedVarNames.incl(chanName)
        deadCIs.add(ci)
        nDeadChannels += 1
    for ci in deadCIs:
      tr.channelConstraints.del(ci)
    if nDeadChannels > 0:
      stderr.writeLine(&"[FZN] Eliminated {nDeadChannels} dead element channels (unreferenced)")

proc tryBuildDefinedExpression(tr: var FznTranslator, ci: int): bool =
  ## Tries to build the AlgebraicExpression for one defining constraint.
  ## Returns true if successful, false if a dependency is not yet available.
  let con = tr.model.constraints[ci]
  let name = stripSolverPrefix(con.name)

  # Handle int_times without defines_var (detected by collectDefinedVars)
  if name == "int_times" and not con.hasAnnotation("defines_var"):
    if con.args.len < 3 or con.args[2].kind != FznIdent: return true
    let definedName = con.args[2].ident
    if definedName notin tr.definedVarNames: return true
    if definedName in tr.definedVarExprs: return true
    let a = con.args[0]
    let b = con.args[1]
    for operand in [a, b]:
      if operand.kind == FznIdent and operand.ident in tr.definedVarNames and
         operand.ident notin tr.definedVarExprs and operand.ident notin tr.varPositions and
         operand.ident notin tr.paramValues:
        return false  # dependency not yet built
    tr.definedVarExprs[definedName] = tr.resolveExprArg(a) * tr.resolveExprArg(b)
    return true

  # Only process defining constraints with defines_var
  if name notin ["int_lin_eq", "int_abs", "int_max", "int_min", "int_times",
                  "array_int_minimum", "array_int_maximum"] or
     not con.hasAnnotation("defines_var"):
    return true  # not our concern, treat as done
  var ann: FznAnnotation
  for a in con.annotations:
    if a.name == "defines_var":
      ann = a
      break
  let definedName = ann.args[0].ident
  # Min/max channel vars get positions and channel bindings, not expressions
  if definedName in tr.channelVarNames:
    return true
  if definedName in tr.definedVarExprs:
    return true  # already built
  # WeightedSameValue objective is handled separately
  if definedName == tr.weightedSameValueObjName:
    return true

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

proc detectWeightedSameValuePattern(tr: var FznTranslator) =
  ## Detects weighted same-value objective pattern:
  ##   int_eq_reif(x_i, x_j, b_ij) :: defines_var(b_ij)  -- variable-variable equality
  ##   bool2int(b_ij, ind_ij) :: defines_var(ind_ij)
  ##   int_lin_eq(coeffs, [objective, ind_1, ...], rhs) :: defines_var(objective)
  ## Produces: objective = rhs + Σ(-coeff_k * δ(x_i == x_j))

  # Build maps: variable name → defining constraint index
  var bool2intDefs: Table[string, int]  # indicator var → constraint index
  var intEqReifDefs: Table[string, int]  # bool var → constraint index

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name == "bool2int" and con.hasAnnotation("defines_var"):
      if con.args.len >= 2 and con.args[1].kind == FznIdent:
        bool2intDefs[con.args[1].ident] = ci
    elif name == "int_eq_reif" and con.hasAnnotation("defines_var"):
      if con.args.len >= 3 and con.args[2].kind == FznIdent:
        intEqReifDefs[con.args[2].ident] = ci

  # Only scan if this is a minimize/maximize problem
  if tr.model.solve.kind notin {Minimize, Maximize}:
    return
  if tr.model.solve.objective == nil or tr.model.solve.objective.kind != FznIdent:
    return
  let objectiveName = tr.model.solve.objective.ident

  # Find the int_lin_eq that defines the objective
  # Note: don't skip definingConstraints — collectDefinedVars may have already claimed this
  for ci, con in tr.model.constraints:
    if ci in tr.countEqPatterns:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_eq" or not con.hasAnnotation("defines_var"):
      continue
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent:
      continue
    if ann.args[0].ident != objectiveName:
      continue

    # Found the defining constraint for the objective
    let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
    let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue

    # Extract variable names
    let vars = con.args[1]
    var varElems: seq[FznExpr]
    if vars.kind == FznArrayLit:
      varElems = vars.elems
    elif vars.kind == FznIdent:
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

    if coeffs.len != varElems.len or varElems.len < 2:
      continue

    # First variable must be the objective (coefficient for objective itself)
    if varElems[0].kind != FznIdent or varElems[0].ident != objectiveName:
      continue
    let objCoeff = coeffs[0]  # usually 1

    # Try to trace all other variables through bool2int → int_eq_reif(varA, varB, bool)
    var pairs: seq[tuple[varNameA, varNameB: string, coeff: int]]
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
      if b2iCon.args[0].kind != FznIdent:
        valid = false
        break
      let boolVarName = b2iCon.args[0].ident

      if boolVarName notin intEqReifDefs:
        valid = false
        break

      let eqReifIdx = intEqReifDefs[boolVarName]
      let eqReifCon = tr.model.constraints[eqReifIdx]
      # int_eq_reif(argA, argB, boolVar) — both must be variable idents
      if eqReifCon.args[0].kind != FznIdent or eqReifCon.args[1].kind != FznIdent:
        valid = false
        break

      let varNameA = eqReifCon.args[0].ident
      let varNameB = eqReifCon.args[1].ident
      # Both must be real variables (not defined/consumed)
      if varNameA in tr.definedVarNames or varNameB in tr.definedVarNames:
        valid = false
        break

      # Pair coefficient: from objCoeff * objective + coeff_k * ind_k = rhs
      # => objective = (rhs - coeff_k * ind_k) / objCoeff
      # => pairCoeff = -coeff_k / objCoeff
      if (-coeffs[i] mod objCoeff) != 0:
        valid = false
        break
      let pairCoeff = -coeffs[i] div objCoeff
      pairs.add((varNameA: varNameA, varNameB: varNameB, coeff: pairCoeff))
      consumedConstraints.add(b2iIdx)
      consumedConstraints.add(eqReifIdx)
      consumedVarNames.add(indName)
      consumedVarNames.add(boolVarName)

    if not valid or pairs.len == 0:
      continue
    if (rhs mod objCoeff) != 0:
      continue

    # Pattern detected!
    tr.weightedSameValuePairs = pairs
    tr.weightedSameValueConstant = rhs div objCoeff
    tr.weightedSameValueObjName = objectiveName

    # Mark consumed constraints
    for idx in consumedConstraints:
      tr.definingConstraints.incl(idx)
    # The int_lin_eq itself is a defining constraint (we handle the objective directly)
    tr.definingConstraints.incl(ci)

    # Mark intermediate variable names as defined (skip position creation)
    for vn in consumedVarNames:
      tr.definedVarNames.incl(vn)
    # Also mark the objective as defined
    tr.definedVarNames.incl(objectiveName)

    stderr.writeLine(&"[FZN] Detected weighted same-value pattern: {pairs.len} pairs, constant={tr.weightedSameValueConstant}, objective={objectiveName}")
    break  # Only one objective

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
    # Exception: element channel aliases resolve to a single channel position
    if xArg.ident in tr.definedVarNames and xArg.ident notin tr.elementChannelAliases:
      continue

    # For var-to-var case, verify args[1] is also a positioned variable
    let valArg = con.args[1]
    if valArg.kind == FznIdent and valArg.ident in tr.definedVarNames and
       valArg.ident notin tr.elementChannelAliases:
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

  # Third pass: find bool_clause_reif with defines_var
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause_reif" or not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 3 or con.args[2].kind != FznIdent:
      continue
    let rName = con.args[2].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != rName:
      continue
    if rName in tr.definedVarNames or rName in tr.channelVarNames:
      continue
    # Verify all inputs in pos/neg arrays are positioned variables (not defined vars)
    let posElems = tr.resolveVarArrayElems(con.args[0])
    let negElems = tr.resolveVarArrayElems(con.args[1])
    if posElems.len == 0 and negElems.len == 0:
      continue  # No inputs — can't build a meaningful channel binding
    var allValid = true
    for elem in posElems:
      if elem.kind != FznIdent or elem.ident in tr.definedVarNames:
        allValid = false
        break
    if allValid:
      for elem in negElems:
        if elem.kind != FznIdent or elem.ident in tr.definedVarNames:
          allValid = false
          break
    if not allValid:
      continue
    tr.channelVarNames.incl(rName)
    tr.definingConstraints.incl(ci)
    tr.boolClauseReifChannelDefs.add(ci)

  # Fourth pass: find set_in_reif with defines_var
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "set_in_reif" or not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 3 or con.args[2].kind != FznIdent:
      continue

    let bName = con.args[2].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
      continue

    if bName in tr.definedVarNames or bName in tr.channelVarNames:
      continue

    # args[0] must be a positioned variable
    let xArg = con.args[0]
    if xArg.kind != FznIdent:
      continue
    if xArg.ident in tr.definedVarNames:
      continue

    # args[1] must be a set literal or range
    let setArg = con.args[1]
    if setArg.kind != FznSetLit and setArg.kind != FznRange:
      continue

    tr.channelVarNames.incl(bName)
    tr.definingConstraints.incl(ci)
    tr.setInReifChannelDefs.add(ci)

  # Fifth pass: find array_bool_and/array_bool_or with defines_var
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "array_bool_and" and name != "array_bool_or":
      continue
    if not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 2 or con.args[1].kind != FznIdent:
      continue
    let rName = con.args[1].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != rName:
      continue
    if rName in tr.definedVarNames or rName in tr.channelVarNames:
      continue
    # Verify all inputs are positioned variables (not defined vars)
    let inputElems = tr.resolveVarArrayElems(con.args[0])
    if inputElems.len == 0:
      continue
    var allValid = true
    for elem in inputElems:
      if elem.kind != FznIdent or elem.ident in tr.definedVarNames:
        allValid = false
        break
    if not allValid:
      continue
    tr.channelVarNames.incl(rName)
    tr.definingConstraints.incl(ci)
    tr.boolAndOrChannelDefs.add(ci)

  # Sixth pass: find int_le_reif/int_lt_reif with defines_var
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if (name != "int_le_reif" and name != "int_lt_reif") or not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 3 or con.args[2].kind != FznIdent:
      continue

    let bName = con.args[2].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != bName:
      continue

    if bName in tr.definedVarNames or bName in tr.channelVarNames:
      continue

    # Check args[0] and args[1] — at least one must be a positioned variable
    # (not a defined variable), the other can be a constant or positioned variable
    let arg0 = con.args[0]
    let arg1 = con.args[1]

    # Check arg0: must be constant, channel var, or positioned variable (not defined var)
    # Exception: element channel aliases resolve to a channel position
    if arg0.kind == FznIdent and arg0.ident in tr.definedVarNames and
       arg0.ident notin tr.elementChannelAliases:
      continue
    # Check arg1: must be constant, channel var, or positioned variable (not defined var)
    if arg1.kind == FznIdent and arg1.ident in tr.definedVarNames and
       arg1.ident notin tr.elementChannelAliases:
      continue

    tr.channelVarNames.incl(bName)
    tr.definingConstraints.incl(ci)
    tr.leReifChannelDefs.add(ci)

  if tr.reifChannelDefs.len > 0 or tr.bool2intChannelDefs.len > 0 or
     tr.boolClauseReifChannelDefs.len > 0 or tr.setInReifChannelDefs.len > 0 or
     tr.boolAndOrChannelDefs.len > 0 or tr.leReifChannelDefs.len > 0:
    stderr.writeLine(&"[FZN] Detected reification channels: {tr.reifChannelDefs.len} int_eq/ne_reif, {tr.bool2intChannelDefs.len} bool2int, {tr.boolClauseReifChannelDefs.len} bool_clause_reif, {tr.setInReifChannelDefs.len} set_in_reif, {tr.boolAndOrChannelDefs.len} array_bool_and/or, {tr.leReifChannelDefs.len} int_le/lt_reif")


proc detectSetUnionChannels(tr: var FznTranslator) =
  ## Detects set_union(A, B, C) :: defines_var(C) patterns, identifies linear chains,
  ## and traces set comprehension patterns (singleton→product→source sets).
  ## Chain intermediates and singletons are marked for skipping in translateVariables.
  ## Must be called before translateVariables.

  # Build set of known set variable names from the model
  var setVarNames: HashSet[string]
  for decl in tr.model.variables:
    if not decl.isArray and decl.varType.kind in {FznSetOfInt, FznSetOfIntRange, FznSetOfIntSet}:
      setVarNames.incl(decl.name)

  # Collect all set_union with defines_var
  type UnionRec = object
    ci: int
    aName, leafName, cName: string
  var unions: seq[UnionRec]
  var producedBy: Table[string, int]  # cName -> index into unions

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name != "set_union" or not con.hasAnnotation("defines_var"):
      continue
    if con.args.len < 3 or con.args[2].kind != FznIdent:
      continue
    let cName = con.args[2].ident
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent or ann.args[0].ident != cName:
      continue
    if cName notin setVarNames:
      continue
    let aName = if con.args[0].kind == FznIdent: con.args[0].ident else: ""
    let leafName = if con.args[1].kind == FznIdent: con.args[1].ident else: ""
    let idx = unions.len
    unions.add(UnionRec(ci: ci, aName: aName, leafName: leafName, cName: cName))
    producedBy[cName] = idx

  if unions.len == 0:
    return

  # Build forward adjacency: aName -> list of union indices where it's the accumulated input
  var fromA: Table[string, seq[int]]
  for i, u in unions:
    if u.aName.len > 0:
      fromA.mgetOrPut(u.aName, @[]).add(i)

  # Find chain starts: unions whose aName is NOT produced by another union (or is constant)
  var chainStartIndices: seq[int]
  for i, u in unions:
    if u.aName.len == 0 or u.aName notin producedBy:
      chainStartIndices.add(i)

  # Trace chains from each start
  var inChain: PackedSet[int]  # union indices that are part of a chain
  for startIdx in chainStartIndices:
    var chain: seq[int]  # indices into unions
    var current = startIdx
    while true:
      chain.add(current)
      inChain.incl(current)
      let cName = unions[current].cName
      if cName in fromA and fromA[cName].len == 1:
        current = fromA[cName][0]
      else:
        break

    if chain.len < 2:
      # Single union: handle as individual (no benefit from chain-collapsing)
      for idx in chain:
        inChain.excl(idx)
      continue

    # Build chain info
    var info = SetUnionChainInfo(
      resultName: unions[chain[^1]].cName,
      baseName: unions[chain[0]].aName,
      constraintIndices: newSeq[int](chain.len))

    # Check if base is a constant set
    if info.baseName.len == 0:
      info.baseIsConst = true
      info.baseConstVals = initHashSet[int]()
    elif info.baseName in tr.setParamValues:
      info.baseIsConst = true
      info.baseConstVals = toHashSet(tr.setParamValues[info.baseName])
    else:
      info.baseIsConst = false

    for j, idx in chain:
      info.constraintIndices[j] = unions[idx].ci
      info.leafNames.add(unions[idx].leafName)
      if j < chain.len - 1:
        info.intermediateNames.add(unions[idx].cName)

    # Mark all chain results as channel variables + mark constraints as consumed
    for idx in chain:
      let u = unions[idx]
      tr.channelVarNames.incl(u.cName)
      tr.definingConstraints.incl(u.ci)

    # Mark intermediates to skip boolean creation
    for iname in info.intermediateNames:
      tr.skipSetVarNames.incl(iname)

    tr.setUnionChains.add(info)

  # Handle non-chain unions as individual channels (existing behavior)
  for i, u in unions:
    if i in inChain:
      continue
    if u.cName in tr.channelVarNames:
      continue
    tr.channelVarNames.incl(u.cName)
    tr.definingConstraints.incl(u.ci)
    tr.setUnionChannelDefs.add((ci: u.ci, resultName: u.cName))

  # --- Set comprehension pattern detection ---
  # For each chain, try to trace singletons to their int_times products.
  # Pattern: set_card(S,1) + set_in(val_expr, S) where val_expr = k * product
  # from int_lin_eq([k,-1],[product,val_expr],0) :: defines_var(val_expr)

  # Build reverse map: variable name -> constraint that defines it (via defines_var)
  var definedByCI: Table[string, int]
  for ci, con in tr.model.constraints:
    if not con.hasAnnotation("defines_var"):
      continue
    let ann = con.getAnnotation("defines_var")
    if ann.args.len > 0 and ann.args[0].kind == FznIdent:
      definedByCI[ann.args[0].ident] = ci

  # Build singleton map: set_card(S, 1) → S name + ci
  var singletonCardCI: Table[string, int]  # S name -> set_card ci
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name == "set_card" and con.args.len >= 2:
      if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit and con.args[1].intVal == 1:
        singletonCardCI[con.args[0].ident] = ci

  # Build set_in map: set_in(val_expr, S) → (ci, val_expr)
  var singletonInCI: Table[string, tuple[ci: int, valArg: FznExpr]]
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name == "set_in" and con.args.len >= 2 and con.args[1].kind == FznIdent:
      let sName = con.args[1].ident
      if sName in singletonCardCI:
        singletonInCI[sName] = (ci: ci, valArg: con.args[0])

  for chainIdx in 0..<tr.setUnionChains.len:
    let chain = tr.setUnionChains[chainIdx]

    # Check if all leaves are singletons with traceable products
    var compInfo = SetComprehensionInfo(chainIdx: chainIdx)
    var allTraced = true

    for leafName in chain.leafNames:
      if leafName notin singletonCardCI or leafName notin singletonInCI:
        allTraced = false
        break

      let inInfo = singletonInCI[leafName]
      let valArg = inInfo.valArg

      if valArg.kind == FznIntLit:
        # Literal value (e.g., set_in(0, seed)) — contributes a fixed value
        # Not a product-traced pair; skip as a comprehension pair
        # but still consume the constraints
        compInfo.consumedConstraints.incl(inInfo.ci)
        compInfo.consumedConstraints.incl(singletonCardCI[leafName])
        tr.skipSetVarNames.incl(leafName)
        continue

      if valArg.kind != FznIdent:
        allTraced = false
        break

      let valName = valArg.ident

      # Trace val_expr to find sumVal and product variable.
      # Two patterns:
      #   1. val_expr defined by int_lin_eq([k,-1],[product,val_expr],0) → sumVal=k
      #   2. val_expr defined by int_times(a,b,val_expr) → sumVal=1 (product IS val_expr)
      if valName notin definedByCI:
        allTraced = false
        break

      let defCI = definedByCI[valName]
      let defCon = tr.model.constraints[defCI]
      let defName = stripSolverPrefix(defCon.name)

      var sumVal: int
      var productVarName: string

      if defName == "int_lin_eq" and defCon.args.len >= 3 and
         defCon.args[0].kind == FznArrayLit and defCon.args[1].kind == FznArrayLit:
        # Pattern 1: int_lin_eq([k,-1],[product,val_expr],0) → val_expr = k * product
        let coeffs = defCon.args[0].elems
        let vars = defCon.args[1].elems
        if coeffs.len == 2 and vars.len == 2 and
           coeffs[0].kind == FznIntLit and coeffs[1].kind == FznIntLit and
           coeffs[1].intVal == -1 and vars[0].kind == FznIdent:
          sumVal = coeffs[0].intVal
          productVarName = vars[0].ident
        else:
          allTraced = false
          break
      elif defName == "int_times" and defCon.args.len >= 3:
        # Pattern 2: int_times(a,b,val_expr) → val_expr = a*b, sumVal depends on max domain
        # For boolean inputs, val_expr is 0 or 1, so this contributes value 1 when active
        # Find the actual sum value from the singleton's universe
        # The singleton set S has universe lo..hi. The set_in(val_expr, S) means
        # S = {val_expr}. Since val_expr domain is 0..1 and S has set_card=1,
        # the singleton either contains {0} or {1}. So sumVal = 1.
        sumVal = 1
        productVarName = valName  # the product IS the val_expr
      else:
        allTraced = false
        break

      compInfo.pairs.add(SetComprehensionPair(sumVal: sumVal, productVarName: productVarName))
      compInfo.consumedConstraints.incl(inInfo.ci)
      compInfo.consumedConstraints.incl(singletonCardCI[leafName])
      tr.skipSetVarNames.incl(leafName)

    if allTraced and compInfo.pairs.len > 0:
      # Mark consumed constraints
      for ci in compInfo.consumedConstraints.items:
        tr.definingConstraints.incl(ci)
      tr.setComprehensions.add(compInfo)

  # Log results
  var nChainUnions = 0
  for chain in tr.setUnionChains:
    nChainUnions += chain.constraintIndices.len
  if tr.setUnionChains.len > 0:
    stderr.writeLine(&"[FZN] Detected {tr.setUnionChains.len} set_union chains ({nChainUnions} unions, {tr.skipSetVarNames.len} set vars skipped)")
  if tr.setComprehensions.len > 0:
    var nPairs = 0
    for comp in tr.setComprehensions:
      nPairs += comp.pairs.len
    stderr.writeLine(&"[FZN] Detected {tr.setComprehensions.len} set comprehension patterns ({nPairs} product pairs)")
  if tr.setUnionChannelDefs.len > 0:
    stderr.writeLine(&"[FZN] Detected {tr.setUnionChannelDefs.len} individual set_union channel variables")

proc detectEqualityCopyVars(tr: var FznTranslator) =
  ## Detects "equality copy" variables: vars that are copies of another variable
  ## linked via int_eq_reif(copy, original, indicator) :: defines_var(indicator),
  ## where the copy only appears in defines_var constraints.
  ## These copies are eliminated by aliasing them to the original variable.

  # Phase 1: Build set of variable names referenced by "real" (non-defines_var) constraints
  var nonDefinesVarRefs: HashSet[string]
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    if con.hasAnnotation("defines_var"):
      continue
    # Collect all FznIdent names from arguments
    for arg in con.args:
      if arg.kind == FznIdent:
        nonDefinesVarRefs.incl(arg.ident)
      elif arg.kind == FznArrayLit:
        for elem in arg.elems:
          if elem.kind == FznIdent:
            nonDefinesVarRefs.incl(elem.ident)

  # Build set of variables that are elements of any array referenced by constraints.
  # Variables used indirectly through array names (e.g., job_end in array_var_int_element)
  # must not be treated as equality copies, even if the referencing constraint has defines_var.
  var arrayElementVars: HashSet[string]
  block:
    # Map array names to their element variable names
    var arrElems: Table[string, seq[string]]
    for decl in tr.model.variables:
      if decl.isArray and decl.value != nil and decl.value.kind == FznArrayLit:
        var elems: seq[string]
        for e in decl.value.elems:
          if e.kind == FznIdent:
            elems.add(e.ident)
        if elems.len > 0:
          arrElems[decl.name] = elems
    # Find arrays referenced in any constraint
    for ci, con in tr.model.constraints:
      for arg in con.args:
        if arg.kind == FznIdent and arg.ident in arrElems:
          for elemName in arrElems[arg.ident]:
            arrayElementVars.incl(elemName)

  # Phase 2: Scan reifChannelDefs for int_eq_reif(A, B, indicator) where A is a copy of B
  # First pass: count how many DISTINCT comparison partners each variable has.
  # A variable compared with multiple different partners is being equality-tested,
  # not copied (e.g., community-detection: x[i] compared with many other x[j]).
  var comparisonPartners: Table[string, HashSet[string]]  # var → set of distinct partners
  for ci in tr.reifChannelDefs:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    if name != "int_eq_reif":
      continue
    let arg0 = con.args[0]
    let arg1 = con.args[1]
    if arg0.kind != FznIdent or arg1.kind != FznIdent:
      continue
    let aName = arg0.ident
    let bName = arg1.ident
    if aName notin comparisonPartners:
      comparisonPartners[aName] = initHashSet[string]()
    comparisonPartners[aName].incl(bName)
    if bName notin comparisonPartners:
      comparisonPartners[bName] = initHashSet[string]()
    comparisonPartners[bName].incl(aName)

  # Second pass: identify candidates
  var candidates: Table[string, string]  # copy → original
  var candidateCIs: Table[string, int]   # copy → constraint index
  for ci in tr.reifChannelDefs:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    if name != "int_eq_reif":
      continue
    let arg0 = con.args[0]
    let arg1 = con.args[1]
    # Both must be identifiers (variables, not constants)
    if arg0.kind != FznIdent or arg1.kind != FznIdent:
      continue
    let aName = arg0.ident
    let bName = arg1.ident
    # A (the copy) must not be in any real constraint, and not already defined/channel/param
    if aName in nonDefinesVarRefs:
      continue
    if aName in tr.definedVarNames or aName in tr.channelVarNames or aName in tr.paramValues:
      continue
    # A must not be an element of an array used in constraints (indirect reference)
    if aName in arrayElementVars:
      continue
    # B (the original) must not be a parameter
    if bName in tr.paramValues:
      continue
    # A must only be compared with ONE partner (B) — if compared with multiple
    # different variables, it's an independent decision variable being equality-tested
    if aName in comparisonPartners and comparisonPartners[aName].len > 1:
      continue
    # B must also only be compared with one partner — otherwise it's a hub variable
    # that multiple variables are tested against, not a simple copy source
    if bName in comparisonPartners and comparisonPartners[bName].len > 1:
      continue
    # First match per A wins
    if aName notin candidates:
      candidates[aName] = bName
      candidateCIs[aName] = ci

  if candidates.len == 0:
    return

  # Phase 3: Resolve chains (A→B→C becomes A→C), drop self-cycles
  var toRemove: seq[string]
  for copyName in candidates.keys:
    var target = candidates[copyName]
    var visited: HashSet[string]
    visited.incl(copyName)
    while target in candidates and target notin visited:
      visited.incl(target)
      target = candidates[target]
    if target == copyName:
      # Self-cycle (A→B→...→A) — can't resolve, skip
      toRemove.add(copyName)
    else:
      candidates[copyName] = target
  for name in toRemove:
    candidates.del(name)
    candidateCIs.del(name)

  if candidates.len == 0:
    return

  # Commit: mark copies as defined variables and store aliases + reif constraint indices
  for copyName, originalName in candidates:
    tr.definedVarNames.incl(copyName)
    tr.equalityCopyAliases[copyName] = originalName
    tr.equalityCopyReifCIs.incl(candidateCIs[copyName])

  stderr.writeLine(&"[FZN] Detected {candidates.len} equality copy variables")


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

proc resolveActualDomain(tr: FznTranslator, expr: AlgebraicExpression[int],
                         identName: string): seq[int] =
  ## Resolve the actual domain for an expression. If it maps to a single position,
  ## use the base array's domain (which reflects aliasing). Otherwise fall back to
  ## the FZN declaration domain via lookupVarDomain.
  let positions = toSeq(expr.positions.items)
  if positions.len == 1:
    return tr.sys.baseArray.domain[positions[0]].sorted()
  else:
    return tr.lookupVarDomain(identName)


proc unchannelSkippedReifs(tr: var FznTranslator, skipped: HashSet[int],
                           defs: var seq[int], label: string) =
  ## Un-channel skipped reif variables — they couldn't have bindings built due to
  ## large domains, so they must be treated as normal constraints instead.
  if skipped.len == 0: return
  for ci in skipped:
    let con = tr.model.constraints[ci]
    if con.args.len >= 3 and con.args[2].kind == FznIdent:
      let bName = con.args[2].ident
      tr.channelVarNames.excl(bName)
    tr.definingConstraints.excl(ci)
  var filtered: seq[int]
  for ci in defs:
    if ci notin skipped:
      filtered.add(ci)
  defs = filtered
  stderr.writeLine(&"[FZN] Un-channeled {skipped.len} {label} bindings (domain too large)")


proc buildReifChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings for int_eq_reif and bool2int patterns detected
  ## by detectReifChannels. Must be called after translateVariables.
  ##
  ## int_eq_reif(x, val, b): b = element(x - lo, [1 if v==val else 0 for v in domain])
  ## int_ne_reif(x, val, b): b = element(x - lo, [0 if v==val else 1 for v in domain])
  ## int_eq_reif(x, y, b):   b = element((x-lo_x)*size_y + (y-lo_y), equality_table)
  ## bool2int(b, i):          i = element(b, [0, 1])

  # Process int_eq_reif channels first (bool2int depends on these)
  var skippedReifCIs: HashSet[int]
  for ci in tr.reifChannelDefs:
    if ci in tr.equalityCopyReifCIs:
      # Equality copy: copy == original is always true, build constant-1 channel for indicator
      let con = tr.model.constraints[ci]
      let bName = con.args[2].ident
      if bName in tr.varPositions:
        let bPos = tr.varPositions[bName]
        let indexExpr = AlgebraicExpression[int](
          node: ExpressionNode[int](kind: LiteralNode, value: 0),
          positions: initPackedSet[int](),
          linear: true
        )
        let binding = ChannelBinding[int](
          channelPosition: bPos,
          indexExpression: indexExpr,
          arrayElements: @[ArrayElement[int](isConstant: true, constantValue: 1)]
        )
        tr.sys.baseArray.channelBindings.add(binding)
        tr.sys.baseArray.channelPositions.incl(bPos)
        # No entries in channelsAtPosition — no source positions, binding is constant
      continue
    let con = tr.model.constraints[ci]
    let bName = con.args[2].ident
    if bName notin tr.varPositions:
      continue

    let bPos = tr.varPositions[bName]
    let xArg = con.args[0]
    let valArg = con.args[1]

    # Skip if source var has been eliminated (e.g., dead element result)
    var deadSource = false
    for arg in [xArg, valArg]:
      if arg.kind == FznIdent and arg.ident in tr.definedVarNames and
         arg.ident notin tr.varPositions and arg.ident notin tr.definedVarExprs:
        deadSource = true
        break
    if deadSource:
      # Dead source: mark the bool output as defined to cascade elimination
      tr.channelVarNames.excl(bName)
      tr.definedVarNames.incl(bName)
      continue

    var indexExpr: AlgebraicExpression[int]
    var arrayElems: seq[ArrayElement[int]]

    let isEq = stripSolverPrefix(con.name) == "int_eq_reif"

    if valArg.kind == FznIntLit or (valArg.kind == FznIdent and valArg.ident in tr.paramValues):
      # Constant val: b = element(x - lo, [1 if v==val else 0]) (inverted for ne)
      let val = if valArg.kind == FznIntLit: valArg.intVal
                else: tr.paramValues[valArg.ident]
      let xExpr = tr.resolveExprArg(xArg)
      let domain = tr.resolveActualDomain(xExpr, xArg.ident)
      if domain.len == 0:
        skippedReifCIs.incl(ci)
        continue
      let lo = domain[0]
      let hi = domain[^1]
      if hi - lo + 1 > 100_000:
        skippedReifCIs.incl(ci)
        continue

      indexExpr = xExpr - lo
      for v in lo..hi:
        arrayElems.add(ArrayElement[int](isConstant: true,
            constantValue: if (v == val) == isEq: 1 else: 0))

    elif valArg.kind == FznIdent and valArg.ident notin tr.definedVarNames:
      # Variable val: b = element((x-lo_x)*range_y + (y-lo_y), equality_table)
      let xExpr = tr.resolveExprArg(xArg)
      let yExpr = tr.resolveExprArg(valArg)
      let domainX = tr.resolveActualDomain(xExpr, xArg.ident)
      let domainY = tr.resolveActualDomain(yExpr, valArg.ident)
      if domainX.len == 0 or domainY.len == 0:
        skippedReifCIs.incl(ci)
        continue
      let loX = domainX[0]
      let hiX = domainX[^1]
      let loY = domainY[0]
      let hiY = domainY[^1]
      let rangeX = hiX - loX + 1
      let rangeY = hiY - loY + 1
      # Guard against huge 2D tables (use ranges, not domain sizes, since we fill gaps)
      if rangeX > 10_000 or rangeY > 10_000 or
         rangeX * rangeY > 100_000:
        skippedReifCIs.incl(ci)
        continue

      # index = (x - lo_x) * range_y + (y - lo_y)
      indexExpr = (xExpr - loX) * rangeY + (yExpr - loY)

      # Build 2D equality table for full ranges (row-major: x varies in outer loop, y in inner)
      for vx in loX..hiX:
        for vy in loY..hiY:
          arrayElems.add(ArrayElement[int](isConstant: true,
              constantValue: if (vx == vy) == isEq: 1 else: 0))
    else:
      skippedReifCIs.incl(ci)
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

  tr.unchannelSkippedReifs(skippedReifCIs, tr.reifChannelDefs, "reif")

  # Process bool2int channels (after reif channels so b positions are set up)
  for ci in tr.bool2intChannelDefs:
    let con = tr.model.constraints[ci]
    let iName = con.args[1].ident
    let bArg = con.args[0]

    if iName notin tr.varPositions:
      continue

    # Skip if source var is dead (cascade from dead element chain)
    if bArg.kind == FznIdent and bArg.ident in tr.definedVarNames and
       bArg.ident notin tr.varPositions and bArg.ident notin tr.definedVarExprs:
      # Mark the output as defined too to cascade
      tr.channelVarNames.excl(iName)
      tr.definedVarNames.incl(iName)
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

  # Process bool_clause_reif channels
  for ci in tr.boolClauseReifChannelDefs:
    let con = tr.model.constraints[ci]
    let rName = con.args[2].ident
    if rName notin tr.varPositions:
      continue
    let rPos = tr.varPositions[rName]

    # Build index expression: sum(pos_exprs) - sum(neg_exprs) + len(neg)
    let posExprs = tr.resolveExprArray(con.args[0])
    let negExprs = tr.resolveExprArray(con.args[1])
    let n = posExprs.len + negExprs.len

    var indexExpr: AlgebraicExpression[int]
    if n == 0:
      # Empty clause — index is always 0 (clause always false)
      indexExpr = newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: 0),
        linear = true
      )
    else:
      # Start with first positive or negative expression
      var started = false
      for e in posExprs:
        if not started:
          indexExpr = e
          started = true
        else:
          indexExpr = indexExpr + e
      for e in negExprs:
        if not started:
          indexExpr = 0 - e
          started = true
        else:
          indexExpr = indexExpr - e
      # Add constant offset: len(neg)
      if negExprs.len > 0:
        indexExpr = indexExpr + negExprs.len

    # Array: [0, 1, 1, ..., 1] of length N+M+1
    # index 0 means all pos are 0 and all neg are 1 → clause false → r=0
    # any other index → clause true → r=1
    var arrayElems: seq[ArrayElement[int]]
    arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
    for i in 1..n:
      arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))

    let binding = ChannelBinding[int](
      channelPosition: rPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(rPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  # Process set_in_reif channels
  var skippedSetInReifCIs: HashSet[int]
  for ci in tr.setInReifChannelDefs:
    let con = tr.model.constraints[ci]
    let bName = con.args[2].ident
    if bName notin tr.varPositions:
      continue

    let bPos = tr.varPositions[bName]
    let xArg = con.args[0]
    let setArg = con.args[1]

    # Build the set of values for membership test
    var setValues: seq[int]
    case setArg.kind
    of FznRange:
      for v in setArg.lo..setArg.hi:
        setValues.add(v)
    of FznSetLit:
      setValues = setArg.setElems
    else:
      continue

    let setAsHashSet = toHashSet(setValues)

    let xExpr = tr.resolveExprArg(xArg)
    let domain = tr.resolveActualDomain(xExpr, xArg.ident)
    if domain.len == 0:
      skippedSetInReifCIs.incl(ci)
      continue
    let lo = domain[0]
    let hi = domain[^1]
    if hi - lo + 1 > 100_000:
      skippedSetInReifCIs.incl(ci)
      continue

    # b = element(x - lo, [1 if v in S else 0 for v in lo..hi])
    let indexExpr = xExpr - lo
    var arrayElems: seq[ArrayElement[int]]
    for v in lo..hi:
      arrayElems.add(ArrayElement[int](isConstant: true,
          constantValue: if v in setAsHashSet: 1 else: 0))

    let binding = ChannelBinding[int](
      channelPosition: bPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(bPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  tr.unchannelSkippedReifs(skippedSetInReifCIs, tr.setInReifChannelDefs, "set_in_reif")

  # Process int_le_reif / int_lt_reif channels
  var skippedLeReifCIs: HashSet[int]
  for ci in tr.leReifChannelDefs:
    let con = tr.model.constraints[ci]
    let bName = con.args[2].ident
    if bName notin tr.varPositions:
      continue
    let bPos = tr.varPositions[bName]
    let arg0 = con.args[0]
    let arg1 = con.args[1]
    let name = stripSolverPrefix(con.name)
    let isLe = (name == "int_le_reif")  # le: <=, lt: <

    var indexExpr: AlgebraicExpression[int]
    var arrayElems: seq[ArrayElement[int]]

    # Determine which arg is constant and which is variable
    let arg0IsConst = arg0.kind == FznIntLit or (arg0.kind == FznIdent and arg0.ident in tr.paramValues)
    let arg1IsConst = arg1.kind == FznIntLit or (arg1.kind == FznIdent and arg1.ident in tr.paramValues)

    if arg0IsConst and not arg1IsConst:
      # int_le_reif(const, x, b): b = (const <= x) for le, b = (const < x) for lt
      let c = if arg0.kind == FznIntLit: arg0.intVal
              else: tr.paramValues[arg0.ident]
      let xExpr = tr.resolveExprArg(arg1)
      let domain = tr.resolveActualDomain(xExpr, arg1.ident)
      if domain.len == 0:
        skippedLeReifCIs.incl(ci)
        continue
      let lo = domain[0]
      let hi = domain[^1]
      if hi - lo + 1 > 100_000:
        skippedLeReifCIs.incl(ci)
        continue
      indexExpr = xExpr - lo
      for v in lo..hi:
        let cmp = if isLe: (c <= v) else: (c < v)
        arrayElems.add(ArrayElement[int](isConstant: true,
            constantValue: if cmp: 1 else: 0))

    elif not arg0IsConst and arg1IsConst:
      # int_le_reif(x, const, b): b = (x <= const) for le, b = (x < const) for lt
      let c = if arg1.kind == FznIntLit: arg1.intVal
              else: tr.paramValues[arg1.ident]
      let xExpr = tr.resolveExprArg(arg0)
      let domain = tr.resolveActualDomain(xExpr, arg0.ident)
      if domain.len == 0:
        skippedLeReifCIs.incl(ci)
        continue
      let lo = domain[0]
      let hi = domain[^1]
      if hi - lo + 1 > 100_000:
        skippedLeReifCIs.incl(ci)
        continue
      indexExpr = xExpr - lo
      for v in lo..hi:
        let cmp = if isLe: (v <= c) else: (v < c)
        arrayElems.add(ArrayElement[int](isConstant: true,
            constantValue: if cmp: 1 else: 0))

    elif not arg0IsConst and not arg1IsConst:
      # int_le_reif(x, y, b): b = (x <= y) for le, b = (x < y) for lt
      let xExpr = tr.resolveExprArg(arg0)
      let yExpr = tr.resolveExprArg(arg1)
      let xName = if arg0.kind == FznIdent: arg0.ident else: ""
      let yName = if arg1.kind == FznIdent: arg1.ident else: ""
      let domainX = tr.resolveActualDomain(xExpr, xName)
      let domainY = tr.resolveActualDomain(yExpr, yName)
      if domainX.len == 0 or domainY.len == 0:
        skippedLeReifCIs.incl(ci)
        continue
      let loX = domainX[0]
      let hiX = domainX[^1]
      let loY = domainY[0]
      let hiY = domainY[^1]
      let rangeX = hiX - loX + 1
      let rangeY = hiY - loY + 1
      if rangeX > 10_000 or rangeY > 10_000 or
         rangeX * rangeY > 100_000:
        skippedLeReifCIs.incl(ci)
        continue
      indexExpr = (xExpr - loX) * rangeY + (yExpr - loY)
      for vx in loX..hiX:
        for vy in loY..hiY:
          let cmp = if isLe: (vx <= vy) else: (vx < vy)
          arrayElems.add(ArrayElement[int](isConstant: true,
              constantValue: if cmp: 1 else: 0))
    else:
      # Both constant — skip
      skippedLeReifCIs.incl(ci)
      continue

    let binding = ChannelBinding[int](
      channelPosition: bPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(bPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  tr.unchannelSkippedReifs(skippedLeReifCIs, tr.leReifChannelDefs, "le_reif")

  let totalReifChannels = tr.reifChannelDefs.len + tr.bool2intChannelDefs.len +
                          tr.boolClauseReifChannelDefs.len + tr.setInReifChannelDefs.len +
                          tr.leReifChannelDefs.len
  if totalReifChannels > 0:
    stderr.writeLine(&"[FZN] Built {totalReifChannels} reification channel bindings " &
                     &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildBoolLogicChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings for array_bool_and/array_bool_or with defines_var.
  ## array_bool_and([a,b,...], r): r = (a AND b AND ...) = element(a+b+..., [0,..,0,1])
  ## array_bool_or([a,b,...], r):  r = (a OR b OR ...) = element(a+b+..., [0,1,..,1])
  for ci in tr.boolAndOrChannelDefs:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    let isAnd = (name == "array_bool_and")
    let rName = con.args[1].ident
    if rName notin tr.varPositions:
      continue

    # Check if any input var is dead (cascade from dead element chain)
    var hasDead = false
    if con.args[0].kind == FznArrayLit:
      for elem in con.args[0].elems:
        if elem.kind == FznIdent and elem.ident in tr.definedVarNames and
           elem.ident notin tr.varPositions and elem.ident notin tr.definedVarExprs:
          hasDead = true
          break
    if hasDead:
      tr.channelVarNames.excl(rName)
      tr.definedVarNames.incl(rName)
      continue

    let rPos = tr.varPositions[rName]

    # Build index expression: sum of input expressions
    let inputExprs = tr.resolveExprArray(con.args[0])
    let n = inputExprs.len

    var indexExpr: AlgebraicExpression[int]
    if n == 0:
      indexExpr = newAlgebraicExpression[int](
        positions = initPackedSet[int](),
        node = ExpressionNode[int](kind: LiteralNode, value: 0),
        linear = true
      )
    else:
      indexExpr = inputExprs[0]
      for i in 1..<n:
        indexExpr = indexExpr + inputExprs[i]

    # Build lookup array of length n+1
    var arrayElems: seq[ArrayElement[int]]
    if isAnd:
      # AND: only all-true (index n) maps to 1
      for i in 0..<n:
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
      arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))
    else:
      # OR: only all-false (index 0) maps to 0
      arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 0))
      for i in 1..n:
        arrayElems.add(ArrayElement[int](isConstant: true, constantValue: 1))

    let binding = ChannelBinding[int](
      channelPosition: rPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(rPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  if tr.boolAndOrChannelDefs.len > 0:
    stderr.writeLine(&"[FZN] Built {tr.boolAndOrChannelDefs.len} array_bool_and/or channel bindings " &
                     &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc buildValueMapping(tr: FznTranslator, sourceValues: Table[string, int]): Table[string, int] =
  ## Given values for source (search) variables, evaluates all channel and reification
  ## variables to constants via fixed-point iteration. Used to resolve test values in
  ## case-analysis channel detection.
  result = initTable[string, int]()
  for name, val in sourceValues:
    result[name] = val
  for name, val in tr.paramValues:
    result[name] = val
  var changed = true
  while changed:
    changed = false
    # Evaluate element channel constraints
    for ci, definedName in tr.channelConstraints:
      if definedName in result: continue
      let con = tr.model.constraints[ci]
      let idxArg = con.args[0]
      var idx: int
      case idxArg.kind
      of FznIntLit: idx = idxArg.intVal
      of FznIdent:
        if idxArg.ident in result: idx = result[idxArg.ident]
        else: continue
      else: continue
      let arr = try: tr.resolveIntArray(con.args[1])
               except ValueError, KeyError: continue
      let i = idx - 1  # FZN 1-based to 0-based
      if i < 0 or i >= arr.len: continue
      result[definedName] = arr[i]
      changed = true
    # Evaluate reification channels (int_eq_reif / int_ne_reif)
    for ci in tr.reifChannelDefs:
      let con = tr.model.constraints[ci]
      let name = stripSolverPrefix(con.name)
      if con.args.len < 3 or con.args[2].kind != FznIdent: continue
      let resultVar = con.args[2].ident
      if resultVar in result: continue
      var xVal: int
      case con.args[0].kind
      of FznIdent:
        if con.args[0].ident in result: xVal = result[con.args[0].ident]
        else: continue
      of FznIntLit: xVal = con.args[0].intVal
      else: continue
      var testVal: int
      case con.args[1].kind
      of FznIntLit: testVal = con.args[1].intVal
      of FznBoolLit: testVal = if con.args[1].boolVal: 1 else: 0
      of FznIdent:
        if con.args[1].ident in result: testVal = result[con.args[1].ident]
        else: continue
      else: continue
      if name == "int_eq_reif":
        result[resultVar] = if xVal == testVal: 1 else: 0
      elif name == "int_ne_reif":
        result[resultVar] = if xVal != testVal: 1 else: 0
      changed = true
    # Evaluate bool2int channels
    for ci in tr.bool2intChannelDefs:
      let con = tr.model.constraints[ci]
      if con.args.len < 2: continue
      if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent: continue
      let iName = con.args[1].ident
      if iName in result: continue
      let bName = con.args[0].ident
      if bName notin result: continue
      result[iName] = result[bName]
      changed = true
    # Evaluate bool_clause_reif channels
    for ci in tr.boolClauseReifChannelDefs:
      let con = tr.model.constraints[ci]
      if con.args.len < 3 or con.args[2].kind != FznIdent: continue
      let resultVar = con.args[2].ident
      if resultVar in result: continue
      let posElems = tr.resolveVarArrayElems(con.args[0])
      let negElems = tr.resolveVarArrayElems(con.args[1])
      var allResolved = true
      var clauseTrue = false
      for elem in posElems:
        if elem.kind == FznIdent:
          if elem.ident in result:
            if result[elem.ident] >= 1:
              clauseTrue = true
              break
          else:
            allResolved = false
            break
        elif elem.kind == FznIntLit:
          if elem.intVal >= 1:
            clauseTrue = true
            break
        elif elem.kind == FznBoolLit:
          if elem.boolVal:
            clauseTrue = true
            break
      if not clauseTrue and allResolved:
        for elem in negElems:
          if elem.kind == FznIdent:
            if elem.ident in result:
              if result[elem.ident] == 0:
                clauseTrue = true
                break
            else:
              allResolved = false
              break
          elif elem.kind == FznIntLit:
            if elem.intVal == 0:
              clauseTrue = true
              break
          elif elem.kind == FznBoolLit:
            if not elem.boolVal:
              clauseTrue = true
              break
      if not clauseTrue and not allResolved: continue
      result[resultVar] = if clauseTrue: 1 else: 0
      changed = true
    # Evaluate set_in_reif channels
    for ci in tr.setInReifChannelDefs:
      let con = tr.model.constraints[ci]
      if con.args.len < 3 or con.args[2].kind != FznIdent: continue
      let resultVar = con.args[2].ident
      if resultVar in result: continue
      var xVal: int
      case con.args[0].kind
      of FznIdent:
        if con.args[0].ident in result: xVal = result[con.args[0].ident]
        else: continue
      of FznIntLit: xVal = con.args[0].intVal
      else: continue
      let setArg = con.args[1]
      var inSet = false
      case setArg.kind
      of FznRange:
        inSet = xVal >= setArg.lo and xVal <= setArg.hi
      of FznSetLit:
        inSet = xVal in setArg.setElems
      else: continue
      result[resultVar] = if inSet: 1 else: 0
      changed = true
    # Evaluate int_lin_eq with defines_var (for compound index expressions)
    for ci, con in tr.model.constraints:
      let cname = stripSolverPrefix(con.name)
      if cname != "int_lin_eq" or not con.hasAnnotation("defines_var"): continue
      var ann: FznAnnotation
      for a in con.annotations:
        if a.name == "defines_var":
          ann = a
          break
      if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
      let definedName = ann.args[0].ident
      if definedName in result: continue
      let coeffs = try: tr.resolveIntArray(con.args[0])
                   except ValueError, KeyError: continue
      let varElems = tr.resolveVarArrayElems(con.args[1])
      let rhs = try: tr.resolveIntArg(con.args[2])
                except ValueError, KeyError: continue
      # Find the defined variable's index and check all others are resolved
      var defIdx = -1
      var allOthersResolved = true
      for vi, v in varElems:
        if v.kind == FznIdent and v.ident == definedName:
          if coeffs[vi] == 1 or coeffs[vi] == -1:
            defIdx = vi
        elif v.kind == FznIdent:
          if v.ident notin result:
            allOthersResolved = false
            break
      if defIdx < 0 or not allOthersResolved: continue
      # Solve: coeffs[defIdx] * defVal + sum(coeffs[j] * vals[j]) = rhs
      var sumOthers = 0
      for vi, v in varElems:
        if vi == defIdx: continue
        let val = case v.kind
          of FznIntLit: v.intVal
          of FznBoolLit: (if v.boolVal: 1 else: 0)
          of FznIdent: result[v.ident]
          else: 0
        sumOthers += coeffs[vi] * val
      let defVal = (rhs - sumOthers) div coeffs[defIdx]
      result[definedName] = defVal
      changed = true
    # Evaluate all array_int_element constraints (including non-defines_var)
    for ci, con in tr.model.constraints:
      let cname = stripSolverPrefix(con.name)
      if cname != "array_int_element": continue
      if con.args.len < 3: continue
      let resultArg = con.args[2]
      if resultArg.kind != FznIdent: continue
      if resultArg.ident in result: continue
      let idxArg = con.args[0]
      var idx: int
      case idxArg.kind
      of FznIntLit: idx = idxArg.intVal
      of FznIdent:
        if idxArg.ident in result: idx = result[idxArg.ident]
        else: continue
      else: continue
      let arr = try: tr.resolveIntArray(con.args[1])
               except ValueError, KeyError: continue
      let i = idx - 1  # FZN 1-based to 0-based
      if i < 0 or i >= arr.len: continue
      result[resultArg.ident] = arr[i]
      changed = true
    # Evaluate int_lin_eq_reif / int_lin_ne_reif with defines_var
    for ci, con in tr.model.constraints:
      let cname = stripSolverPrefix(con.name)
      if cname != "int_lin_eq_reif" and cname != "int_lin_ne_reif": continue
      if not con.hasAnnotation("defines_var"): continue
      if con.args.len < 4 or con.args[3].kind != FznIdent: continue
      let resultVar = con.args[3].ident
      if resultVar in result: continue
      let coeffs = try: tr.resolveIntArray(con.args[0])
                   except ValueError, KeyError: continue
      let varElems = tr.resolveVarArrayElems(con.args[1])
      let rhs = try: tr.resolveIntArg(con.args[2])
                except ValueError, KeyError: continue
      if coeffs.len != varElems.len: continue
      var allVarsResolved = true
      var linSum = 0
      for vi, v in varElems:
        case v.kind
        of FznIntLit: linSum += coeffs[vi] * v.intVal
        of FznBoolLit: linSum += coeffs[vi] * (if v.boolVal: 1 else: 0)
        of FznIdent:
          if v.ident in result: linSum += coeffs[vi] * result[v.ident]
          else: allVarsResolved = false; break
        else: allVarsResolved = false; break
      if not allVarsResolved: continue
      if cname == "int_lin_eq_reif":
        result[resultVar] = if linSum == rhs: 1 else: 0
      else:
        result[resultVar] = if linSum != rhs: 1 else: 0
      changed = true
    # Evaluate case analysis channel defs
    for def in tr.caseAnalysisDefs:
      if def.targetVarName in result: continue
      # Compute flat index from source variable values
      var allSourcesKnown = true
      var flatIdx = 0
      for i, srcName in def.sourceVarNames:
        if srcName notin result:
          allSourcesKnown = false
          break
        let srcVal = result[srcName]
        let localIdx = srcVal - def.domainOffsets[i]
        if localIdx < 0 or localIdx >= def.domainSizes[i]:
          allSourcesKnown = false
          break
        flatIdx = flatIdx * def.domainSizes[i] + localIdx
      if not allSourcesKnown: continue
      if flatIdx < 0 or flatIdx >= def.lookupTable.len: continue
      result[def.targetVarName] = def.lookupTable[flatIdx]
      changed = true


proc detectCaseAnalysisChannels(tr: var FznTranslator) =
  ## Detects case-analysis patterns in bool_clause constraints where a target variable's
  ## value is fully determined by condition variables through exhaustive case analysis.
  ## Converts target variables to channel variables with constant lookup tables.
  ##
  ## Pattern (2-literal, first/last round):
  ##   int_eq_reif(target, val, B) :: defines_var(B)
  ##   int_ne_reif(condVar, condVal, C) :: defines_var(C)
  ##   bool_clause([B, C], [])  — condVar==condVal → target==val
  ##
  ## Pattern (3-literal, middle rounds):
  ##   bool_clause([B, C1, C2], [])  — condVar1==v1 AND condVar2==v2 → target==val
  ##
  ## Extended patterns:
  ##   int_lin_eq_reif(coeffs, vars, rhs, B) :: defines_var(B)
  ##   — condVar==condVal → target = f(otherVars)  (linear equation)
  ##
  ##   int_le_reif(condVar, threshold, C) :: defines_var(C) as condition
  ##   — condVar > threshold → target == val  (covers multiple condition values)
  ##
  ## When all condition value combinations are covered (or uncovered cases can be
  ## defaulted), the target becomes a channel with a precomputed constant lookup
  ## table indexed by source variable values.

  # Step 1: Build reverse index from reifChannelDefs
  var eqReifMap: Table[string, tuple[sourceVar: string, testVal: FznExpr]]
  var neReifMap: Table[string, tuple[condVar: string, condVal: int]]

  for ci in tr.reifChannelDefs:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    if con.args.len < 3 or con.args[2].kind != FznIdent: continue
    let resultVar = con.args[2].ident
    if name == "int_eq_reif":
      if con.args[0].kind != FznIdent: continue
      eqReifMap[resultVar] = (sourceVar: con.args[0].ident, testVal: con.args[1])
    elif name == "int_ne_reif":
      if con.args[0].kind != FznIdent: continue
      let condVal = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
      neReifMap[resultVar] = (condVar: con.args[0].ident, condVal: condVal)

  # Step 1b: Build linEqReifMap from int_lin_eq_reif :: defines_var constraints.
  # These encode: sum(coeffs[i]*vars[i]) == rhs <-> bool, allowing us to solve for
  # the target variable: target = (rhs - sum of other terms) / targetCoeff.
  type LinEqReifEntry = object
    targetVar: string
    otherVars: seq[string]
    otherCoeffs: seq[int]
    rhs: int
    targetCoeff: int
    constraintIdx: int

  var linEqReifMap: Table[string, LinEqReifEntry]

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_eq_reif" or not con.hasAnnotation("defines_var"): continue
    if con.args.len < 4 or con.args[3].kind != FznIdent: continue
    let boolVar = con.args[3].ident
    if boolVar in tr.definedVarNames or boolVar in tr.channelVarNames: continue
    let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
    let varElems = tr.resolveVarArrayElems(con.args[1])
    let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
    if coeffs.len != varElems.len: continue
    # Find a variable with coefficient 1 or -1 to be the target
    var targetIdx = -1
    for i in 0..<varElems.len:
      if varElems[i].kind == FznIdent and (coeffs[i] == 1 or coeffs[i] == -1):
        if varElems[i].ident notin tr.definedVarNames and
           varElems[i].ident notin tr.channelVarNames:
          targetIdx = i
          break
    if targetIdx < 0: continue
    var otherVars: seq[string]
    var otherCoeffs: seq[int]
    var allVarsIdent = true
    for i in 0..<varElems.len:
      if i == targetIdx: continue
      if varElems[i].kind != FznIdent:
        allVarsIdent = false
        break
      otherVars.add(varElems[i].ident)
      otherCoeffs.add(coeffs[i])
    if not allVarsIdent: continue
    linEqReifMap[boolVar] = LinEqReifEntry(
      targetVar: varElems[targetIdx].ident,
      otherVars: otherVars,
      otherCoeffs: otherCoeffs,
      rhs: rhs,
      targetCoeff: coeffs[targetIdx],
      constraintIdx: ci)

  # Step 1c: Build leReifMap from int_le_reif :: defines_var for use as conditions.
  # int_le_reif(var, threshold, bool) → bool = (var <= threshold)
  # In a bool_clause, this covers all condition values > threshold.
  type LeReifEntry = object
    condVar: string
    threshold: int
  var leReifMap: Table[string, LeReifEntry]

  for ci in tr.leReifChannelDefs:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    if name != "int_le_reif": continue
    if con.args.len < 3 or con.args[2].kind != FznIdent: continue
    let resultVar = con.args[2].ident
    if con.args[0].kind != FznIdent: continue
    let condVar = con.args[0].ident
    let threshold = try: tr.resolveIntArg(con.args[1]) except ValueError, KeyError: continue
    leReifMap[resultVar] = LeReifEntry(condVar: condVar, threshold: threshold)

  if eqReifMap.len == 0 and linEqReifMap.len == 0: return
  if neReifMap.len == 0 and leReifMap.len == 0: return

  # Step 2: Scan non-consumed bool_clause constraints with 2-3 positive literals
  type CaseEntryKind = enum cekSimple, cekLinear
  type CaseEntry = object
    condVarVals: seq[(string, int)]
    boolClauseIdx: int
    case kind: CaseEntryKind
    of cekSimple:
      testVal: FznExpr
    of cekLinear:
      linOtherVars: seq[string]
      linOtherCoeffs: seq[int]
      linRhs: int
      linTargetCoeff: int
      linReifIdx: int  # constraint index of the int_lin_eq_reif

  var casesByTarget: Table[string, seq[CaseEntry]]

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue
    let posArg = con.args[0]
    let negArg = con.args[1]
    if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
    if negArg.elems.len != 0: continue
    let nLits = posArg.elems.len
    if nLits < 2 or nLits > 3: continue

    # Classify literals: exactly 1 eq_reif (or lin_eq_reif) + rest ne_reif (or le_reif)
    var eqLitVar = ""
    var eqSourceVar = ""
    var eqTestVal: FznExpr
    var eqIsLinear = false
    var eqLinEntry: LinEqReifEntry
    var neLits: seq[(string, int)]
    var leEntries: seq[LeReifEntry]
    var allValid = true

    for elem in posArg.elems:
      if elem.kind != FznIdent:
        allValid = false
        break
      if eqLitVar == "" and elem.ident in eqReifMap:
        eqLitVar = elem.ident
        eqSourceVar = eqReifMap[elem.ident].sourceVar
        eqTestVal = eqReifMap[elem.ident].testVal
      elif eqLitVar == "" and elem.ident in linEqReifMap:
        eqLitVar = elem.ident
        eqLinEntry = linEqReifMap[elem.ident]
        eqSourceVar = eqLinEntry.targetVar
        eqIsLinear = true
      elif elem.ident in neReifMap:
        let info = neReifMap[elem.ident]
        neLits.add((info.condVar, info.condVal))
      elif elem.ident in leReifMap:
        leEntries.add(leReifMap[elem.ident])
      else:
        allValid = false
        break

    if not allValid or eqLitVar == "": continue
    if neLits.len + leEntries.len != nLits - 1: continue

    # For le_reif conditions, expand to individual condition values.
    # int_le_reif(var, threshold, bool) in bool_clause means: var > threshold → eq holds.
    # So the case applies for all domain values > threshold.
    if leEntries.len > 0:
      # Get condition variable domains for le_reif entries
      var expandedNeLists: seq[seq[(string, int)]]
      expandedNeLists.add(neLits.mapIt(@[it]))

      for le in leEntries:
        let dom = tr.lookupVarDomain(le.condVar)
        if dom.len == 0:
          allValid = false
          break
        var vals: seq[(string, int)]
        for v in dom:
          if v > le.threshold:
            vals.add((le.condVar, v))
        if vals.len == 0:
          allValid = false
          break
        expandedNeLists.add(vals)

      if not allValid: continue

      # Build cross-product of all condition combinations
      var combos: seq[seq[(string, int)]] = @[@[]]
      for group in expandedNeLists:
        var newCombos: seq[seq[(string, int)]]
        for existing in combos:
          for item in group:
            newCombos.add(existing & item)
        combos = newCombos
        if combos.len > 100_000:
          allValid = false
          break
      if not allValid: continue

      # Add a case entry for each expanded combination
      for combo in combos:
        if eqIsLinear:
          casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
            kind: cekLinear, condVarVals: combo, boolClauseIdx: ci,
            linOtherVars: eqLinEntry.otherVars, linOtherCoeffs: eqLinEntry.otherCoeffs,
            linRhs: eqLinEntry.rhs, linTargetCoeff: eqLinEntry.targetCoeff,
            linReifIdx: eqLinEntry.constraintIdx))
        else:
          casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
            kind: cekSimple, condVarVals: combo, boolClauseIdx: ci,
            testVal: eqTestVal))
    else:
      # Standard case: all conditions are ne_reif
      if eqIsLinear:
        casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
          kind: cekLinear, condVarVals: neLits, boolClauseIdx: ci,
          linOtherVars: eqLinEntry.otherVars, linOtherCoeffs: eqLinEntry.otherCoeffs,
          linRhs: eqLinEntry.rhs, linTargetCoeff: eqLinEntry.targetCoeff,
          linReifIdx: eqLinEntry.constraintIdx))
      else:
        casesByTarget.mgetOrPut(eqSourceVar, @[]).add(CaseEntry(
          kind: cekSimple, condVarVals: neLits, boolClauseIdx: ci,
          testVal: eqTestVal))

  if casesByTarget.len == 0: return

  # Step 3: Build reverse map for channel constraints (var name → constraint index)
  var channelByName: Table[string, int]
  for ci, defName in tr.channelConstraints:
    channelByName[defName] = ci

  var nTargets = 0
  var nConsumed = 0

  for targetVar, entries in casesByTarget:
    # All entries must have same set of condition variables
    var condVarNames: seq[string]
    for (cv, _) in entries[0].condVarVals:
      condVarNames.add(cv)
    condVarNames.sort()

    var valid = true
    for e in entries:
      var evNames: seq[string]
      for (cv, _) in e.condVarVals:
        evNames.add(cv)
      evNames.sort()
      if evNames != condVarNames:
        valid = false
        break
    if not valid: continue

    # Look up condition variable domains
    var condDomains: seq[seq[int]]
    for cv in condVarNames:
      let dom = tr.lookupVarDomain(cv)
      if dom.len == 0:
        valid = false
        break
      condDomains.add(dom)
    if not valid: continue

    # Check completeness: number of cases == product of condition domain sizes
    # Allow incomplete case analyses only when exactly 1 case is missing
    # (e.g., the "inactive" case for conditional assignments).
    var expectedCases = 1
    for dom in condDomains:
      expectedCases *= dom.len
    let isComplete = entries.len == expectedCases
    if entries.len > expectedCases: continue  # Duplicates — skip
    if not isComplete and (expectedCases - entries.len) > 1: continue  # Too many missing

    # Build case map (condValues → CaseEntry)
    var caseMap: Table[seq[int], CaseEntry]
    for e in entries:
      var combo: seq[int]
      var byName: Table[string, int]
      for (cv, val) in e.condVarVals:
        byName[cv] = val
      for cv in condVarNames:
        if cv notin byName:
          valid = false
          break
        combo.add(byName[cv])
      if not valid: break
      if combo in caseMap:
        valid = false
        break
      caseMap[combo] = e
    if not valid: continue

    # Collect all "expression variables" from linear entries (otherVars in lin_eq_reif)
    # and from non-linear entries with variable test values.
    # For channel/defined variables, trace transitive source variables via case analysis defs.
    var exprVarSet: HashSet[string]
    for e in entries:
      if e.kind == cekLinear:
        for ov in e.linOtherVars:
          exprVarSet.incl(ov)
      elif e.testVal.kind == FznIdent and e.testVal.ident notin tr.paramValues:
        exprVarSet.incl(e.testVal.ident)

    # Replace channel/defined variables with their transitive source variables.
    # Channel vars will be resolved via buildValueMapping during table building.
    var resolvedExprVars: HashSet[string]
    for ev in exprVarSet:
      if ev in tr.channelVarNames or ev in tr.definedVarNames:
        # Trace through case analysis defs for known transitive sources
        for caDef in tr.caseAnalysisDefs:
          if caDef.targetVarName == ev:
            for sv in caDef.sourceVarNames:
              resolvedExprVars.incl(sv)
            break
        # Other channel types (bool2int, reif chains) are resolved via buildValueMapping;
        # their dependencies on search variables are covered by the case analysis sources above.
      else:
        resolvedExprVars.incl(ev)
    exprVarSet = resolvedExprVars

    # Step 4: Trace condition variables to source variables.
    # Condition variables may be:
    # a) Element channel results → trace to the element index variable
    # b) Direct search variables → use directly as source
    type CondSourceKind = enum cskElement, cskDirect
    type CondSource = object
      kind: CondSourceKind
      varName: string        # source variable name
      constArray: seq[int]   # for cskElement: the lookup array

    var condSources: seq[CondSource]
    var sourceVarNames: seq[string]
    for cv in condVarNames:
      if cv in channelByName:
        # Element channel: trace to index variable
        let ci = channelByName[cv]
        let con = tr.model.constraints[ci]
        if con.args.len < 3:
          valid = false
          break
        let idxArg = con.args[0]
        if idxArg.kind != FznIdent:
          valid = false
          break
        let srcVar = idxArg.ident
        if srcVar in tr.definedVarNames or srcVar in tr.channelVarNames:
          valid = false
          break
        let constArr = try: tr.resolveIntArray(con.args[1])
                       except ValueError, KeyError:
                         valid = false
                         @[]
        if not valid: break
        condSources.add(CondSource(kind: cskElement, varName: srcVar, constArray: constArr))
        sourceVarNames.add(srcVar)
      else:
        # Direct search variable: use as-is
        if cv in tr.definedVarNames or cv in tr.channelVarNames:
          valid = false
          break
        condSources.add(CondSource(kind: cskDirect, varName: cv))
        sourceVarNames.add(cv)
    if not valid: continue

    # Add expression variables as additional source variables
    # (channel/defined vars already replaced with transitive sources in exprVarSet)
    for ev in exprVarSet:
      if ev in tr.definedVarNames or ev in tr.channelVarNames:
        continue  # Skip residual channel vars — resolved via buildValueMapping
      if ev notin sourceVarNames:
        sourceVarNames.add(ev)
    if sourceVarNames.len == 0: continue

    # Validate source variables are unique
    block uniqueCheck:
      for i in 0..<sourceVarNames.len:
        for j in i+1..<sourceVarNames.len:
          if sourceVarNames[i] == sourceVarNames[j]:
            valid = false
            break uniqueCheck
    if not valid: continue

    # Get source variable domains
    var sourceDomains: seq[seq[int]]
    for sv in sourceVarNames:
      let dom = tr.lookupVarDomain(sv)
      if dom.len == 0:
        valid = false
        break
      sourceDomains.add(dom)
    if not valid: continue

    # Step 5: Build constant lookup table
    var domainOffsets: seq[int]
    var domainSizes: seq[int]
    for dom in sourceDomains:
      domainOffsets.add(dom[0])
      domainSizes.add(dom[^1] - dom[0] + 1)

    var tableSize = 1
    var tableSizeOk = true
    for ds in domainSizes:
      if ds > 100_000 or (ds > 0 and tableSize > 100_000 div ds):
        tableSizeOk = false
        break
      tableSize *= ds
    if not tableSizeOk or tableSize > 100_000: continue

    # Pre-compute mini lookup tables for channel variables referenced in linear entries.
    # For each channel var not in caseAnalysisDefs, determine which source variables
    # it depends on, then build a small lookup table only over those dimensions.
    type MiniTable = object
      table: seq[int]
      srcIndices: seq[int]    # indices into sourceVarNames
      srcOffsets: seq[int]
      srcSizes: seq[int]
    var channelMiniTables: Table[string, MiniTable]
    block precompute:
      var channelVarsNeeded: HashSet[string]
      for e in entries:
        if e.kind == cekLinear:
          for ov in e.linOtherVars:
            if ov in tr.channelVarNames or ov in tr.definedVarNames:
              var isCaseAnalysis = false
              for caDef in tr.caseAnalysisDefs:
                if caDef.targetVarName == ov:
                  isCaseAnalysis = true
                  break
              if not isCaseAnalysis:
                channelVarsNeeded.incl(ov)
      # Compute base mapping once for all channel vars (all sources at domain minimum)
      var baseValues = initTable[string, int]()
      for i, sv in sourceVarNames:
        baseValues[sv] = domainOffsets[i]
      let baseMapping = tr.buildValueMapping(baseValues)

      # Determine dependencies for all channel vars at once: probe each source var
      # with a shifted value and check which channel vars changed.
      # depSets[cv] = set of source indices that affect cv.
      var depSets: Table[string, seq[int]]
      for cv in channelVarsNeeded:
        if cv notin baseMapping:
          valid = false
          break
        depSets[cv] = @[]
      if not valid: break

      for i, sv in sourceVarNames:
        if domainSizes[i] <= 1: continue
        var probeValues = baseValues
        probeValues[sv] = domainOffsets[i] + 1
        let probeMapping = tr.buildValueMapping(probeValues)
        for cv in channelVarsNeeded:
          if cv in probeMapping and probeMapping[cv] != baseMapping[cv]:
            depSets[cv].add(i)

      for cv in channelVarsNeeded:
        let depIndices = depSets[cv]
        # Build mini table over dependent source vars only
        var miniOffsets: seq[int]
        var miniSizes: seq[int]
        var miniTableSize = 1
        for di in depIndices:
          miniOffsets.add(domainOffsets[di])
          miniSizes.add(domainSizes[di])
          if miniTableSize > 1_000_000 div max(1, domainSizes[di]):
            valid = false
            break
          miniTableSize *= domainSizes[di]
        if not valid: break

        var miniTable = newSeq[int](miniTableSize)
        for mi in 0..<miniTableSize:
          var vals = baseValues
          var rem = mi
          for k in countdown(depIndices.len - 1, 0):
            let di = depIndices[k]
            let li = rem mod domainSizes[di]
            rem = rem div domainSizes[di]
            vals[sourceVarNames[di]] = domainOffsets[di] + li
          let m = tr.buildValueMapping(vals)
          if cv notin m:
            valid = false
            break
          miniTable[mi] = m[cv]
        if not valid: break
        channelMiniTables[cv] = MiniTable(
          table: miniTable, srcIndices: depIndices,
          srcOffsets: miniOffsets, srcSizes: miniSizes)
    if not valid: continue

    # For incomplete cases (exactly 1 missing), use domain minimum as default.
    # This is safe because incomplete cases arise from conditional assignments where
    # the missing case represents the "inactive" state (e.g., task not assigned to a
    # machine), and the domain minimum is the natural sentinel for that state.
    var defaultVal = 0
    if not isComplete:
      let tdom = tr.lookupVarDomain(targetVar)
      if tdom.len > 0:
        defaultVal = tdom[0]

    var lookupTable = newSeq[int](tableSize)
    var allResolved = true

    for flatIdx in 0..<tableSize:
      # Decode flat index to source values (row-major: first dim varies slowest)
      var sourceValues = initTable[string, int]()
      var remaining = flatIdx
      for i in countdown(sourceVarNames.len - 1, 0):
        let localIdx = remaining mod domainSizes[i]
        remaining = remaining div domainSizes[i]
        sourceValues[sourceVarNames[i]] = localIdx + domainOffsets[i]

      # Compute condition values from source values
      var condValues: seq[int]
      var condOk = true
      for i, cs in condSources:
        let srcVal = sourceValues[cs.varName]
        case cs.kind
        of cskElement:
          let arrIdx = srcVal - 1  # FZN 1-based to 0-based
          if arrIdx < 0 or arrIdx >= cs.constArray.len:
            condOk = false
            break
          condValues.add(cs.constArray[arrIdx])
        of cskDirect:
          condValues.add(srcVal)
      if not condOk:
        lookupTable[flatIdx] = defaultVal
        continue

      if condValues notin caseMap:
        if isComplete:
          lookupTable[flatIdx] = 0  # dummy for out-of-domain values
        else:
          lookupTable[flatIdx] = defaultVal  # uncovered case
        continue

      let entry = caseMap[condValues]

      if entry.kind == cekLinear:
        # Compute target from linear equation:
        # targetCoeff * target + sum(otherCoeffs[i] * otherVars[i]) = rhs
        # target = (rhs - sum(otherCoeffs[i] * otherVars[i])) / targetCoeff
        var numerator = entry.linRhs
        var linOk = true
        var needMapping = false
        for j in 0..<entry.linOtherVars.len:
          let ov = entry.linOtherVars[j]
          if ov in sourceValues:
            numerator -= entry.linOtherCoeffs[j] * sourceValues[ov]
          elif ov in tr.paramValues:
            numerator -= entry.linOtherCoeffs[j] * tr.paramValues[ov]
          else:
            # Try case analysis def lookup first (fast path)
            var resolved = false
            for caDef in tr.caseAnalysisDefs:
              if caDef.targetVarName == ov:
                var caIdx = 0
                var caOk = true
                for si, srcName in caDef.sourceVarNames:
                  let sv = if srcName in sourceValues: sourceValues[srcName]
                           elif srcName in tr.paramValues: tr.paramValues[srcName]
                           else: (caOk = false; 0)
                  if not caOk: break
                  let li = sv - caDef.domainOffsets[si]
                  if li < 0 or li >= caDef.domainSizes[si]: caOk = false; break
                  caIdx = caIdx * caDef.domainSizes[si] + li
                if caOk and caIdx >= 0 and caIdx < caDef.lookupTable.len:
                  numerator -= entry.linOtherCoeffs[j] * caDef.lookupTable[caIdx]
                  resolved = true
                break
            if not resolved:
              # Try pre-computed mini table
              if ov in channelMiniTables:
                let mt = channelMiniTables[ov]
                var mtIdx = 0
                for k, di in mt.srcIndices:
                  let sv = sourceValues[sourceVarNames[di]]
                  let li = sv - mt.srcOffsets[k]
                  mtIdx = mtIdx * mt.srcSizes[k] + li
                numerator -= entry.linOtherCoeffs[j] * mt.table[mtIdx]
              else:
                linOk = false
                break
        if not linOk or numerator mod entry.linTargetCoeff != 0:
          allResolved = false
          break
        lookupTable[flatIdx] = numerator div entry.linTargetCoeff
      else:
        # Resolve test value to constant (original logic)
        let testValExpr = entry.testVal
        case testValExpr.kind
        of FznIntLit:
          lookupTable[flatIdx] = testValExpr.intVal
        of FznBoolLit:
          lookupTable[flatIdx] = if testValExpr.boolVal: 1 else: 0
        of FznIdent:
          if testValExpr.ident in tr.paramValues:
            lookupTable[flatIdx] = tr.paramValues[testValExpr.ident]
          elif testValExpr.ident in sourceValues:
            lookupTable[flatIdx] = sourceValues[testValExpr.ident]
          else:
            let mapping = tr.buildValueMapping(sourceValues)
            if testValExpr.ident in mapping:
              lookupTable[flatIdx] = mapping[testValExpr.ident]
            else:
              allResolved = false
              break
        else:
          allResolved = false
          break

    if not allResolved: continue

    # Step 6: Register channel and consume constraints
    tr.channelVarNames.incl(targetVar)
    var consumedBoolClauses: HashSet[int]
    var consumedLinReifs: HashSet[int]
    for e in entries:
      if e.boolClauseIdx notin consumedBoolClauses:
        tr.definingConstraints.incl(e.boolClauseIdx)
        consumedBoolClauses.incl(e.boolClauseIdx)
        inc nConsumed
      if e.kind == cekLinear and e.linReifIdx notin consumedLinReifs:
        tr.definingConstraints.incl(e.linReifIdx)
        consumedLinReifs.incl(e.linReifIdx)

    tr.caseAnalysisDefs.add(CaseAnalysisDef(
      targetVarName: targetVar,
      sourceVarNames: sourceVarNames,
      lookupTable: lookupTable,
      domainOffsets: domainOffsets,
      domainSizes: domainSizes
    ))
    inc nTargets

  if nTargets > 0:
    stderr.writeLine(&"[FZN] Detected case-analysis channels: {nTargets} target variables, {nConsumed} bool_clause constraints consumed")


proc detectImplicationPatterns(tr: var FznTranslator) =
  ## Detects boolean implication patterns encoded as:
  ##   bool_clause([neg_b, r], [])
  ## where neg_b = int_ne_reif(B_var, 1, neg_b) :: defines_var(neg_b)
  ##   and r = int_lin_le_reif([-1,...], [Y_1,...], -1, r) :: defines_var(r)
  ##
  ## Traces through reification chains to find the underlying integer variables,
  ## builds table constraints for valid transitions, and detects one-hot channel
  ## variables for indicator-to-integer channeling.

  # Build indexes — single pass over all constraints (including consumed ones for tracing)
  var eqReifDefines: Table[string, (string, int)]          # result → (source, value)
  var eqReifNoDefines: Table[string, (string, int, int)]   # result → (source, value, ci)
  var neReifDefines: Table[string, (string, int, int)]       # result → (source, value, ci)
  var linLeReifDefines: Table[string, int]                  # result → ci
  var eqReifDefinesBySource: Table[string, string]          # source → result (value=1 only)
  var notOneVars: HashSet[string]                           # vars where int_eq_reif(var, 1, false) exists
  var notOneConstraints: Table[string, int]                  # var → constraint index for int_eq_reif(var, 1, false)

  # Pre-build set of bool/0..1 variable names for fast one-hot validation
  var boolVarNames: HashSet[string]
  for decl in tr.model.variables:
    if decl.isArray: continue
    case decl.varType.kind
    of FznBool:
      boolVarNames.incl(decl.name)
    of FznIntRange:
      if decl.varType.lo == 0 and decl.varType.hi == 1:
        boolVarNames.incl(decl.name)
    else: discard

  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    case name
    of "int_eq_reif":
      if con.args.len < 3: continue
      let srcArg = con.args[0]
      let valArg = con.args[1]
      let resultArg = con.args[2]
      if srcArg.kind != FznIdent: continue
      # Check for bool literal result: int_eq_reif(bVar, 1, false) → boundary indicator
      if resultArg.kind == FznBoolLit:
        if not resultArg.boolVal:
          let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
          if val == 1:
            notOneVars.incl(srcArg.ident)
            notOneConstraints[srcArg.ident] = ci
        continue
      if resultArg.kind != FznIdent: continue
      let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
      if con.hasAnnotation("defines_var"):
        eqReifDefines[resultArg.ident] = (srcArg.ident, val)
        if val == 1:
          eqReifDefinesBySource[srcArg.ident] = resultArg.ident
      else:
        eqReifNoDefines[resultArg.ident] = (srcArg.ident, val, ci)
    of "int_ne_reif":
      if con.args.len < 3: continue
      let srcArg = con.args[0]
      let valArg = con.args[1]
      let resultArg = con.args[2]
      if srcArg.kind != FznIdent or resultArg.kind != FznIdent: continue
      let val = try: tr.resolveIntArg(valArg) except ValueError, KeyError: continue
      if con.hasAnnotation("defines_var"):
        neReifDefines[resultArg.ident] = (srcArg.ident, val, ci)
    of "int_lin_le_reif":
      if con.args.len < 4: continue
      let resultArg = con.args[3]
      if resultArg.kind != FznIdent: continue
      if con.hasAnnotation("defines_var"):
        linLeReifDefines[resultArg.ident] = ci
    else: discard

  # Implication detection — scan bool_clause constraints
  var implicationGroups: Table[(string, string), seq[(int, int)]]
  var nConsumed = 0
  var nVacuous = 0
  var nStay = 0

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue

    let posArg = con.args[0]
    let negArg = con.args[1]
    if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
    if posArg.elems.len != 2 or negArg.elems.len != 0: continue

    let lit0 = posArg.elems[0]
    let lit1 = posArg.elems[1]
    if lit0.kind != FznIdent or lit1.kind != FznIdent: continue

    # Identify which literal is neReif
    var neReifLit, otherLit: string
    if lit0.ident in neReifDefines and lit1.ident notin neReifDefines:
      neReifLit = lit0.ident
      otherLit = lit1.ident
    elif lit1.ident in neReifDefines and lit0.ident notin neReifDefines:
      neReifLit = lit1.ident
      otherLit = lit0.ident
    elif lit0.ident in neReifDefines and lit1.ident in neReifDefines:
      # Both are neReif — try both orders for [neReif, linLeReif] or [neReif, eqReif]
      if lit0.ident in linLeReifDefines or lit0.ident in eqReifDefines:
        neReifLit = lit1.ident
        otherLit = lit0.ident
      elif lit1.ident in linLeReifDefines or lit1.ident in eqReifDefines:
        neReifLit = lit0.ident
        otherLit = lit1.ident
      else:
        continue
    else:
      continue

    # Case 1: [ne_reif, lin_le_reif] — transition pattern (agent moves to neighbor)
    if otherLit in linLeReifDefines:
      let (bVar, neVal, neReifCi) = neReifDefines[neReifLit]
      if neVal != 1: continue

      # Trace neReif through indicator chain → integer variable
      if bVar notin eqReifDefinesBySource:
        # Check vacuous boundary: bVar can never be 1 → implication is vacuously true
        if bVar in notOneVars:
          let linLeIdx = linLeReifDefines[otherLit]
          tr.definingConstraints.incl(ci)        # bool_clause
          tr.definingConstraints.incl(linLeIdx)  # int_lin_le_reif
          tr.definingConstraints.incl(neReifCi)  # int_ne_reif (trivially satisfied)
          tr.definedVarNames.incl(neReifLit)     # result var of neReif
          tr.definedVarNames.incl(otherLit)      # result var of linLeReif
          nConsumed += 3
          nVacuous += 1
        continue
      let channelVar = eqReifDefinesBySource[bVar]
      if channelVar notin eqReifNoDefines: continue
      let (condVar, condValue, _) = eqReifNoDefines[channelVar]

      # Check int_lin_le_reif: all coefficients = -1, rhs = -1 (encoding sum >= 1)
      let linLeIdx = linLeReifDefines[otherLit]
      let linLeCon = tr.model.constraints[linLeIdx]
      let coeffs = try: tr.resolveIntArray(linLeCon.args[0]) except ValueError, KeyError: continue
      let rhs = try: tr.resolveIntArg(linLeCon.args[2]) except ValueError, KeyError: continue
      if rhs != -1: continue

      var allNegOne = true
      for c in coeffs:
        if c != -1:
          allNegOne = false
          break
      if not allNegOne: continue

      let varElems = tr.resolveVarArrayElems(linLeCon.args[1])
      if varElems.len != coeffs.len or varElems.len == 0: continue

      # Trace each indicator variable → target integer variable
      var targetVar = ""
      var targetValues: seq[int]
      var valid = true

      for yi in varElems:
        if yi.kind != FznIdent:
          valid = false
          break
        if yi.ident notin eqReifDefinesBySource:
          valid = false
          break
        let chVarI = eqReifDefinesBySource[yi.ident]
        if chVarI notin eqReifNoDefines:
          valid = false
          break
        let (tVar, tValue, _) = eqReifNoDefines[chVarI]

        if targetVar == "":
          targetVar = tVar
        elif tVar != targetVar:
          valid = false
          break

        targetValues.add(tValue)

      if not valid or targetVar == "": continue

      # Record: (condVar == condValue) → (targetVar in targetValues)
      let key = (condVar, targetVar)
      if key notin implicationGroups:
        implicationGroups[key] = @[]
      for tv in targetValues:
        implicationGroups[key].add((condValue, tv))

      # Mark consumed
      tr.definingConstraints.incl(ci)        # bool_clause
      tr.definingConstraints.incl(linLeIdx)  # int_lin_le_reif
      tr.definedVarNames.incl(otherLit)      # result var of linLeReif
      nConsumed += 2

    # Case 2: [ne_reif, eq_reif] — direct implication (stay at destination)
    # Unlike Case 1, no neVal==1 guard needed: here the ne_reif directly references
    # an integer variable (e.g., int_ne_reif(agentPos, value, B)), so condValue is
    # the actual integer value, not a boolean indicator.
    elif otherLit in eqReifDefines:
      let (condVar, condValue, _) = neReifDefines[neReifLit]
      let (targetVar, targetValue) = eqReifDefines[otherLit]

      # Record: (condVar == condValue) → (targetVar == targetValue)
      let key = (condVar, targetVar)
      if key notin implicationGroups:
        implicationGroups[key] = @[]
      implicationGroups[key].add((condValue, targetValue))

      # Only consume the bool_clause — ne_reif and eq_reif already consumed by detectReifChannels
      tr.definingConstraints.incl(ci)
      nConsumed += 1
      nStay += 1

  # Build table constraints from grouped implications
  for key, tuples in implicationGroups:
    let (condVar, targetVar) = key
    var tableTuples: seq[seq[int]]
    for (cv, tv) in tuples:
      tableTuples.add(@[cv, tv])
    tr.implicationTables.add((condVar: condVar, targetVar: targetVar, tuples: tableTuples))

  # One-hot channel detection — convert indicator vars to channels of integer vars
  for channel, entry in eqReifNoDefines.pairs:
    let (intVar, v, ci) = entry
    if ci in tr.definingConstraints: continue
    if channel notin eqReifDefines: continue
    let (bV, eqVal) = eqReifDefines[channel]
    if eqVal != 1: continue
    if bV in tr.channelVarNames or bV in tr.definedVarNames: continue
    if bV notin boolVarNames: continue

    tr.oneHotChannelDefs.add((indicatorVar: bV, intVar: intVar, value: v))
    tr.definingConstraints.incl(ci)
    tr.channelVarNames.incl(bV)

  # Constant-zero channel detection — boundary B vars that are always 0
  for bVar in notOneVars:
    if bVar in tr.channelVarNames or bVar in tr.definedVarNames: continue
    if bVar notin boolVarNames: continue
    tr.constantZeroChannels.add(bVar)
    tr.channelVarNames.incl(bVar)
    if bVar in notOneConstraints:
      tr.definingConstraints.incl(notOneConstraints[bVar])

  if tr.implicationTables.len > 0:
    stderr.writeLine(&"[FZN] Detected implication table patterns: {tr.implicationTables.len} tables, {nConsumed} constraints consumed (stay={nStay}, vacuous={nVacuous}, notOneVars={notOneVars.len})")
  if tr.oneHotChannelDefs.len > 0:
    stderr.writeLine(&"[FZN] Detected one-hot channels: {tr.oneHotChannelDefs.len} indicator variables")
  if tr.constantZeroChannels.len > 0:
    stderr.writeLine(&"[FZN] Detected constant-zero channels: {tr.constantZeroChannels.len} boundary indicator variables")


proc buildOneHotChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings for one-hot indicator variables detected by
  ## detectImplicationPatterns. Each indicator B_v = (intVar == value) becomes
  ## a channel: B_v = element(intVar - lo, [1 if v==value else 0 for v in domain])

  for def in tr.oneHotChannelDefs:
    let indicatorVar = def.indicatorVar
    let intVar = def.intVar
    let value = def.value

    if indicatorVar notin tr.varPositions: continue
    if intVar notin tr.varPositions: continue

    let indicatorPos = tr.varPositions[indicatorVar]
    let intPos = tr.varPositions[intVar]
    let intExpr = tr.getExpr(intPos)
    let domain = tr.sys.baseArray.domain[intPos].sorted()
    if domain.len == 0: continue

    let lo = domain[0]
    let hi = domain[^1]
    if hi - lo + 1 > 100_000: continue
    let indexExpr = intExpr - lo

    var arrayElems: seq[ArrayElement[int]]
    for v in lo..hi:
      arrayElems.add(ArrayElement[int](isConstant: true,
          constantValue: if v == value: 1 else: 0))

    let binding = ChannelBinding[int](
      channelPosition: indicatorPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(indicatorPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

  if tr.oneHotChannelDefs.len > 0:
    stderr.writeLine(&"[FZN] Built {tr.oneHotChannelDefs.len} one-hot channel bindings " &
                     &"(total channels: {tr.sys.baseArray.channelBindings.len})")

  # Build constant-zero channel bindings for boundary indicator variables
  var nConstZero = 0
  for bVar in tr.constantZeroChannels:
    if bVar notin tr.varPositions: continue
    let bPos = tr.varPositions[bVar]

    # Constant binding: element(0, [0]) — always evaluates to 0
    let indexExpr = newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: 0),
      linear = true
    )
    let binding = ChannelBinding[int](
      channelPosition: bPos,
      indexExpression: indexExpr,
      arrayElements: @[ArrayElement[int](isConstant: true, constantValue: 0)]
    )
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(bPos)
    # No entries in channelsAtPosition — no source positions, binding is constant
    nConstZero += 1

  if nConstZero > 0:
    stderr.writeLine(&"[FZN] Built {nConstZero} constant-zero channel bindings " &
                     &"(total channels: {tr.sys.baseArray.channelBindings.len})")


proc detectConditionalGainChannels(tr: var FznTranslator) =
  ## Detects variables that are conditionally a linear function of element channels
  ## or zero, where the conditions are also element-channel-derived. Converts them
  ## to element channels with precomputed lookup tables.
  ##
  ## Pattern (per gain variable V):
  ##   int_eq_reif(V, 0, B_zero) :: defines_var(B_zero)
  ##   int_lin_eq_reif(coeffs, [V, W], rhs, B_eq) :: defines_var(B_eq)
  ##   bool_clause([B_eq], [cond1, cond2, ...])
  ##   bool_clause([cond_and_or_cond, B_zero], [])
  ## where W is an element channel and conditions are int_le_reif of element channels,
  ## all sharing the same index (origin) variable.

  # Step 1: Find int_eq_reif(V, 0, B_zero) patterns
  # These may already be consumed by reif channel detection, but we scan all constraints.
  var zeroReifVars: Table[string, tuple[ci: int, boolVar: string]]
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name == "int_eq_reif" and con.args.len >= 3:
      if con.args[0].kind == FznIdent and
         con.args[1].kind == FznIntLit and con.args[1].intVal == 0 and
         con.args[2].kind == FznIdent:
        let v = con.args[0].ident
        if v notin tr.channelVarNames and v notin tr.definedVarNames:
          zeroReifVars[v] = (ci, con.args[2].ident)

  if zeroReifVars.len == 0:
    return

  # Step 2: Find matching int_lin_eq_reif with 2 variables (one is V, other is a channel)
  type LinEqReifInfo = object
    ci: int
    gainVar: string
    otherVar: string
    gainCoeff: int
    otherCoeff: int
    rhs: int
    boolVar: string

  var linEqReifs: Table[string, LinEqReifInfo]
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_eq_reif" or con.args.len < 4: continue
    if not con.hasAnnotation("defines_var"): continue

    let coeffs = try: tr.resolveIntArray(con.args[0]) except ValueError, KeyError: continue
    if coeffs.len != 2: continue

    let vars = con.args[1]
    if vars.kind != FznArrayLit or vars.elems.len != 2: continue
    if vars.elems[0].kind != FznIdent or vars.elems[1].kind != FznIdent: continue

    let var0 = vars.elems[0].ident
    let var1 = vars.elems[1].ident
    let rhs = try: tr.resolveIntArg(con.args[2]) except ValueError, KeyError: continue
    if con.args[3].kind != FznIdent: continue
    let boolVar = con.args[3].ident

    # The "other" variable must be a channel or element channel alias
    let isVar0Channel = var0 in tr.channelVarNames or var0 in tr.elementChannelAliases
    let isVar1Channel = var1 in tr.channelVarNames or var1 in tr.elementChannelAliases

    if var0 in zeroReifVars and isVar1Channel:
      linEqReifs[var0] = LinEqReifInfo(ci: ci, gainVar: var0, otherVar: var1,
                                        gainCoeff: coeffs[0], otherCoeff: coeffs[1],
                                        rhs: rhs, boolVar: boolVar)
    elif var1 in zeroReifVars and isVar0Channel:
      linEqReifs[var1] = LinEqReifInfo(ci: ci, gainVar: var1, otherVar: var0,
                                        gainCoeff: coeffs[1], otherCoeff: coeffs[0],
                                        rhs: rhs, boolVar: boolVar)

  if linEqReifs.len == 0:
    return

  # Step 3: Index bool_clause constraints by positive literals
  type BoolClauseInfo = object
    ci: int
    posLits: seq[string]
    negLits: seq[string]

  var boolClausesByPosLit: Table[string, seq[BoolClauseInfo]]
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause" or con.args.len < 2: continue

    var info = BoolClauseInfo(ci: ci)
    if con.args[0].kind == FznArrayLit:
      for elem in con.args[0].elems:
        if elem.kind == FznIdent:
          info.posLits.add(elem.ident)
    if con.args[1].kind == FznArrayLit:
      for elem in con.args[1].elems:
        if elem.kind == FznIdent:
          info.negLits.add(elem.ident)

    for lit in info.posLits:
      if lit notin boolClausesByPosLit:
        boolClausesByPosLit[lit] = @[]
      boolClausesByPosLit[lit].add(info)

  # Step 4: Index int_le_reif definitions by their boolean output variable
  type LeReifInfo = object
    leftVar: string
    leftConst: int
    rightVar: string
    rightConst: int
    isLeftConst: bool
    isRightConst: bool

  var leReifByBool: Table[string, LeReifInfo]
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name notin ["int_le_reif", "int_lt_reif"] or con.args.len < 3: continue
    if con.args[2].kind != FznIdent: continue
    let boolVar = con.args[2].ident

    var info: LeReifInfo
    if con.args[0].kind == FznIdent:
      info.leftVar = con.args[0].ident
    elif con.args[0].kind == FznIntLit:
      info.leftConst = con.args[0].intVal
      info.isLeftConst = true
    else: continue

    if con.args[1].kind == FznIdent:
      info.rightVar = con.args[1].ident
    elif con.args[1].kind == FznIntLit:
      info.rightConst = con.args[1].intVal
      info.isRightConst = true
    else: continue

    leReifByBool[boolVar] = info

  # Step 5: Build element channel info: channel var name -> (origin var, constant array)
  type ElementInfo = object
    originVar: string
    constArray: seq[int]

  var elementInfo: Table[string, ElementInfo]
  for ci, chanName in tr.channelConstraints:
    let con = tr.model.constraints[ci]
    if con.args[0].kind == FznIdent:
      try:
        let constArray = tr.resolveIntArray(con.args[1])
        elementInfo[chanName] = ElementInfo(originVar: con.args[0].ident, constArray: constArray)
      except ValueError, KeyError: discard

  for aliasName, originalName in tr.elementChannelAliases:
    if originalName in elementInfo:
      elementInfo[aliasName] = elementInfo[originalName]

  # Step 6: Process each gain variable
  var nConverted = 0
  var consumedBoolClauses: PackedSet[int]

  for gainVar, info in linEqReifs:
    let zeroInfo = zeroReifVars[gainVar]
    let bEq = info.boolVar
    let bZero = zeroInfo.boolVar

    # Find conditional bool_clause: bool_clause([B_eq], [cond1, cond2, ...])
    if bEq notin boolClausesByPosLit: continue
    var condClause: BoolClauseInfo
    var foundCond = false
    for bc in boolClausesByPosLit[bEq]:
      if bc.posLits.len == 1 and bc.negLits.len > 0:
        condClause = bc
        foundCond = true
        break
    if not foundCond: continue

    # Find complementary bool_clause: bool_clause([..., B_zero], [])
    if bZero notin boolClausesByPosLit: continue
    var compClause: BoolClauseInfo
    var foundComp = false
    for bc in boolClausesByPosLit[bZero]:
      if bc.negLits.len == 0:
        compClause = bc
        foundComp = true
        break
    if not foundComp: continue

    # Extract conditions from negative literals of the conditional clause
    type ConditionInfo = object
      channelVar: string
      threshold: int
      isLessEqual: bool  # true: channel <= threshold, false: channel >= threshold

    var conditions: seq[ConditionInfo]
    var allConditionsTraced = true
    for condBool in condClause.negLits:
      if condBool notin leReifByBool:
        allConditionsTraced = false
        break
      let leInfo = leReifByBool[condBool]
      if leInfo.isLeftConst and not leInfo.isRightConst:
        # int_le_reif(constant, channel, bool) → channel >= constant
        conditions.add(ConditionInfo(channelVar: leInfo.rightVar, threshold: leInfo.leftConst, isLessEqual: false))
      elif not leInfo.isLeftConst and leInfo.isRightConst:
        # int_le_reif(channel, constant, bool) → channel <= constant
        conditions.add(ConditionInfo(channelVar: leInfo.leftVar, threshold: leInfo.rightConst, isLessEqual: true))
      else:
        allConditionsTraced = false
        break
    if not allConditionsTraced: continue

    # Trace price channel (W) to element info (may be alias)
    let otherVar = if info.otherVar in tr.elementChannelAliases:
                     tr.elementChannelAliases[info.otherVar]
                   else: info.otherVar
    if otherVar notin elementInfo: continue
    let priceElem = elementInfo[otherVar]
    let originVar = priceElem.originVar
    let arrayLen = priceElem.constArray.len

    # Trace condition channels and verify all share the same origin
    type CondEval = object
      constArray: seq[int]
      threshold: int
      isLessEqual: bool

    var condEvals: seq[CondEval]
    var allSameOrigin = true
    for cond in conditions:
      # Resolve alias if needed
      let condChanVar = if cond.channelVar in tr.elementChannelAliases:
                          tr.elementChannelAliases[cond.channelVar]
                        else: cond.channelVar
      if condChanVar notin elementInfo:
        allSameOrigin = false
        break
      let condElem = elementInfo[condChanVar]
      if condElem.originVar != originVar or condElem.constArray.len != arrayLen:
        allSameOrigin = false
        break
      condEvals.add(CondEval(constArray: condElem.constArray, threshold: cond.threshold,
                              isLessEqual: cond.isLessEqual))
    if not allSameOrigin: continue

    # Compute the lookup table
    if info.gainCoeff == 0: continue
    var lookupTable = newSeq[int](arrayLen)
    for v in 0..<arrayLen:
      var conditionsMet = true
      for ce in condEvals:
        let val = ce.constArray[v]
        if ce.isLessEqual:
          if val > ce.threshold:
            conditionsMet = false
            break
        else:
          if val < ce.threshold:
            conditionsMet = false
            break

      if conditionsMet:
        let price = priceElem.constArray[v]
        let numerator = info.rhs - info.otherCoeff * price
        lookupTable[v] = numerator div info.gainCoeff
      # else: lookupTable[v] = 0 (default)

    # Convert gain variable to element channel
    tr.channelVarNames.incl(gainVar)
    tr.definedVarNames.excl(gainVar)
    tr.syntheticElementChannels.add((gainVar, originVar, lookupTable))

    # Consume constraints
    tr.definingConstraints.incl(info.ci)  # int_lin_eq_reif
    tr.definingConstraints.incl(condClause.ci)
    consumedBoolClauses.incl(condClause.ci)
    tr.definingConstraints.incl(compClause.ci)
    consumedBoolClauses.incl(compClause.ci)

    nConverted += 1

  if nConverted > 0:
    stderr.writeLine(&"[FZN] Converted {nConverted} conditional gain variables to element channels")


proc detectDisjunctivePairs(tr: var FznTranslator) =
  ## Detects disjunctive pair patterns:
  ##   int_lin_le_reif(coeffs1, vars1, rhs1, b1) :: defines_var(b1)
  ##   int_lin_le_reif(coeffs2, vars2, rhs2, b2) :: defines_var(b2)
  ##   bool_clause([b1, b2], [])
  ## Where b1, b2 are bool variables only used in this one clause.
  ## Replaces all 3 constraints + 2 bool variables with:
  ##   min(max(0, expr1), max(0, expr2)) == 0
  ## where expr_i = scalar_product(coeffs_i, vars_i) - rhs_i.

  # Step 1: Build mapping from result var name → constraint index for
  # all int_lin_le_reif with defines_var annotation
  var linLeReifDefines: Table[string, int]  # result var name → constraint index
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_le_reif": continue
    if con.args.len < 4: continue
    if not con.hasAnnotation("defines_var"): continue
    let resultArg = con.args[3]
    if resultArg.kind != FznIdent: continue
    linLeReifDefines[resultArg.ident] = ci

  if linLeReifDefines.len == 0: return

  # Step 2: Count references to each bool var in non-defining constraints.
  # We only count references in bool_clause positive/negative literal lists.
  var varRefCount: Table[string, int]
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue
    # Count each literal mentioned in positive and negative arrays
    for argIdx in 0..1:
      let arr = con.args[argIdx]
      if arr.kind != FznArrayLit: continue
      for elem in arr.elems:
        if elem.kind == FznIdent:
          varRefCount.mgetOrPut(elem.ident, 0) += 1

  # Step 3: Scan bool_clause([b1, b2], []) constraints
  var nConsumed = 0
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue
    let posArg = con.args[0]
    let negArg = con.args[1]
    if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
    # Pattern: exactly 2 positive literals, no negative literals
    if posArg.elems.len != 2 or negArg.elems.len != 0: continue
    let b1 = posArg.elems[0]
    let b2 = posArg.elems[1]
    if b1.kind != FznIdent or b2.kind != FznIdent: continue
    # Check both are defined by int_lin_le_reif
    if b1.ident notin linLeReifDefines or b2.ident notin linLeReifDefines: continue
    # Check both are only used in this one clause
    if varRefCount.getOrDefault(b1.ident) != 1 or varRefCount.getOrDefault(b2.ident) != 1: continue

    # Extract coefficients, variables, and RHS from both reif constraints
    let reifIdx1 = linLeReifDefines[b1.ident]
    let reifIdx2 = linLeReifDefines[b2.ident]
    let reifCon1 = tr.model.constraints[reifIdx1]
    let reifCon2 = tr.model.constraints[reifIdx2]

    let coeffs1 = try: tr.resolveIntArray(reifCon1.args[0]) except ValueError, KeyError: continue
    let coeffs2 = try: tr.resolveIntArray(reifCon2.args[0]) except ValueError, KeyError: continue
    let rhs1 = try: tr.resolveIntArg(reifCon1.args[2]) except ValueError, KeyError: continue
    let rhs2 = try: tr.resolveIntArg(reifCon2.args[2]) except ValueError, KeyError: continue

    # Resolve variable names from the args
    var varNames1: seq[string]
    var varNames2: seq[string]
    let varArr1 = reifCon1.args[1]
    let varArr2 = reifCon2.args[1]

    block extractVars1:
      case varArr1.kind
      of FznArrayLit:
        for e in varArr1.elems:
          if e.kind == FznIdent:
            varNames1.add(e.ident)
          else:
            break extractVars1
      of FznIdent:
        if varArr1.ident in tr.arrayElementNames:
          varNames1 = tr.arrayElementNames[varArr1.ident]
        else:
          continue
      else: continue

    block extractVars2:
      case varArr2.kind
      of FznArrayLit:
        for e in varArr2.elems:
          if e.kind == FznIdent:
            varNames2.add(e.ident)
          else:
            break extractVars2
      of FznIdent:
        if varArr2.ident in tr.arrayElementNames:
          varNames2 = tr.arrayElementNames[varArr2.ident]
        else:
          continue
      else: continue

    if varNames1.len != coeffs1.len or varNames2.len != coeffs2.len: continue

    # Consume all 3 constraints and both bool variables
    tr.definingConstraints.incl(ci)        # bool_clause
    tr.definingConstraints.incl(reifIdx1)  # int_lin_le_reif for b1
    tr.definingConstraints.incl(reifIdx2)  # int_lin_le_reif for b2
    tr.definedVarNames.incl(b1.ident)
    tr.definedVarNames.incl(b2.ident)

    tr.disjunctivePairs.add((
      coeffs1: coeffs1, varNames1: varNames1, rhs1: rhs1,
      coeffs2: coeffs2, varNames2: varNames2, rhs2: rhs2))
    nConsumed += 3

  if tr.disjunctivePairs.len > 0:
    stderr.writeLine(&"[FZN] Detected {tr.disjunctivePairs.len} disjunctive pairs, " &
                     &"{nConsumed} constraints consumed, " &
                     &"{tr.disjunctivePairs.len * 2} bool variables eliminated")


proc detectDisjunctiveResources(tr: var FznTranslator) =
  ## Detects disjunctive resource groups among disjunctive pairs and replaces
  ## them with cumulative(limit=1) constraints.
  ## A disjunctive resource is a complete subgraph (clique) of pairwise
  ## disjunctive constraints where all tasks on the same resource have
  ## consistent durations.
  if tr.disjunctivePairs.len == 0:
    return

  # Step 1: Extract 2-variable disjunctive pairs with [1,-1]/[-1,1] coefficients
  # These represent: either (a - b <= -durA) or (b - a <= -durB),
  # meaning tasks don't overlap on the same resource.
  type PairInfo = object
    pairIdx: int
    posA, posB: string  # Variable names (posA < posB for canonical ordering)
    durA, durB: int     # Duration of A (when A before B), duration of B (when B before A)

  var validPairs: seq[PairInfo]
  for idx, pair in tr.disjunctivePairs:
    # Only handle simple 2-variable pairs
    if pair.varNames1.len != 2 or pair.varNames2.len != 2:
      continue
    # Check coefficient pattern: [1,-1] or [-1,1]
    var varA1, varB1, varA2, varB2: string
    var durFromDisj1, durFromDisj2: int

    # Disjunct 1: coeffs1·vars1 <= rhs1
    if pair.coeffs1 == @[1, -1]:
      # a - b <= rhs1 → a + (-rhs1) <= b → if a before b, a needs duration -rhs1
      varA1 = pair.varNames1[0]
      varB1 = pair.varNames1[1]
      durFromDisj1 = -pair.rhs1  # duration of A in "A before B" interpretation
    elif pair.coeffs1 == @[-1, 1]:
      # -a + b <= rhs1 → b - a <= rhs1 → b + (-rhs1) <= a → if b before a, b needs duration -rhs1
      varA1 = pair.varNames1[1]
      varB1 = pair.varNames1[0]
      durFromDisj1 = -pair.rhs1
    else:
      continue

    # Disjunct 2: coeffs2·vars2 <= rhs2
    if pair.coeffs2 == @[1, -1]:
      varA2 = pair.varNames2[0]
      varB2 = pair.varNames2[1]
      durFromDisj2 = -pair.rhs2
    elif pair.coeffs2 == @[-1, 1]:
      varA2 = pair.varNames2[1]
      varB2 = pair.varNames2[0]
      durFromDisj2 = -pair.rhs2
    else:
      continue

    # The two disjuncts should involve the same pair of variables
    # but in opposite directions:
    # disjunct 1: A + durA <= B (A before B)
    # disjunct 2: B + durB <= A (B before A)
    if varA1 == varA2 and varB1 == varB2:
      # Same direction — not a proper disjunctive pair for our purposes
      # Actually this means: (A+dur1<=B) or (A+dur2<=B) — skip
      continue
    elif varA1 == varB2 and varB1 == varA2:
      # disjunct1: A1+dur1<=B1, disjunct2: A2+dur2<=B2 where A1=B2, B1=A2
      # So: A+durA<=B or B+durB<=A — correct pattern
      validPairs.add(PairInfo(
        pairIdx: idx,
        posA: varA1, posB: varB1,
        durA: durFromDisj1, durB: durFromDisj2))
    else:
      continue

  if validPairs.len == 0:
    return

  # Step 2: Build adjacency and validate duration consistency
  # Each position (variable name) should have a consistent duration across all pairs.
  # Variables with inconsistent durations are excluded; remaining consistent pairs are kept.
  var varDuration: Table[string, int]  # var → its duration
  var inconsistentVars: HashSet[string]

  # First pass: detect duration inconsistencies
  for pi in validPairs:
    if pi.posA in varDuration:
      if varDuration[pi.posA] != pi.durA:
        inconsistentVars.incl(pi.posA)
    else:
      varDuration[pi.posA] = pi.durA
    if pi.posB in varDuration:
      if varDuration[pi.posB] != pi.durB:
        inconsistentVars.incl(pi.posB)
    else:
      varDuration[pi.posB] = pi.durB

  # Second pass: build adjacency from consistent pairs only
  var adjacency: Table[string, Table[string, int]]  # var → {partner → pairIdx}
  for pi in validPairs:
    if pi.posA in inconsistentVars or pi.posB in inconsistentVars:
      continue
    if pi.posA notin adjacency:
      adjacency[pi.posA] = initTable[string, int]()
    adjacency[pi.posA][pi.posB] = pi.pairIdx

    if pi.posB notin adjacency:
      adjacency[pi.posB] = initTable[string, int]()
    adjacency[pi.posB][pi.posA] = pi.pairIdx

  if adjacency.len == 0:
    return

  # Step 3: Find cliques by greedy detection
  var assigned: HashSet[string]  # Variables already assigned to a resource group
  type ResourceGroup = object
    members: seq[string]
    pairIndices: seq[int]

  var groups: seq[ResourceGroup]

  # Sort variables by degree (highest first) for better clique detection
  var varsByDegree: seq[(int, string)]
  for v, partners in adjacency:
    varsByDegree.add((partners.len, v))
  varsByDegree.sort(proc(a, b: (int, string)): int = -cmp(a[0], b[0]))

  for (_, startVar) in varsByDegree:
    if startVar in assigned:
      continue

    # Try to build a clique starting from startVar
    var clique = @[startVar]
    # Candidates: all partners of startVar not yet assigned
    var candidates: seq[string]
    for partner in adjacency[startVar].keys:
      if partner notin assigned:
        candidates.add(partner)

    # Greedily add candidates that are connected to all current clique members
    for candidate in candidates:
      var connectedToAll = true
      for member in clique:
        if member == candidate:
          connectedToAll = false
          break
        if candidate notin adjacency.getOrDefault(member):
          connectedToAll = false
          break
      if connectedToAll:
        clique.add(candidate)

    if clique.len < 2:
      continue

    # Verify it's a complete subgraph and collect pair indices
    var pairIndices: seq[int]
    var isComplete = true
    for i in 0..<clique.len:
      for j in (i+1)..<clique.len:
        if clique[j] notin adjacency.getOrDefault(clique[i]):
          isComplete = false
          break
        pairIndices.add(adjacency[clique[i]][clique[j]])
      if not isComplete:
        break

    if not isComplete:
      continue

    for member in clique:
      assigned.incl(member)
    groups.add(ResourceGroup(members: clique, pairIndices: pairIndices))

  if groups.len == 0:
    return

  # Step 4: Mark consumed pairs and create cumulative constraints
  var totalConsumed = 0
  var totalTasks = 0

  for group in groups:
    for pidx in group.pairIndices:
      tr.consumedDisjunctivePairs.incl(pidx)
      inc totalConsumed

    totalTasks += group.members.len

    # Collect positions and durations for cumulative constraint
    # We store var names here; positions will be resolved during constraint emission
    # (after translateVariables has run)
    var memberNames = group.members
    var durations: seq[int]
    for m in memberNames:
      durations.add(varDuration[m])

    # Store for later emission (positions aren't resolved yet)
    tr.disjunctiveResourceGroups.add((varNames: memberNames, durations: durations))

  stderr.writeLine(&"[FZN] Detected {groups.len} disjunctive resource groups ({totalTasks} tasks total), " &
                   &"{totalConsumed} pairs consumed -> {groups.len} cumulative constraints")


proc detectNoOverlapPatterns(tr: var FznTranslator) =
  ## Detects 6-literal bool_clause patterns encoding 3D box non-overlap:
  ##   bool_clause([b1,b2,b3,b4,b5,b6], [])
  ## where each bi is defined by int_le_reif, and the 6 comparisons form
  ## 3 pairs (one per dimension) checking separation between a variable
  ## pipe leg box and a fixed obstacle box.
  ##
  ## Chain: bool_clause → int_le_reif → int_lin_eq → int_min/int_max → node endpoints
  ##
  ## Replaces 7 constraints (1 bool_clause + 6 int_le_reif) + chain intermediates
  ## with a single NoOverlapFixedBox constraint.

  # Step 1: Build reverse indices
  # Note: leReifDefs only includes unconsumed int_le_reif constraints,
  # but linEqDefs and minMaxDefs include ALL constraints (even already consumed ones)
  # because we need them for tracing the chain through defined variables and channels.
  var leReifDefs: Table[string, int]   # bool var name → int_le_reif constraint index
  var linEqDefs: Table[string, int]    # defined var name → int_lin_eq constraint index
  var minMaxDefs: Table[string, int]   # channel var name → int_min/int_max constraint index

  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if not con.hasAnnotation("defines_var"): continue
    let ann = con.getAnnotation("defines_var")
    if ann.args.len == 0 or ann.args[0].kind != FznIdent: continue
    let defVar = ann.args[0].ident
    case name
    of "int_le_reif":
      # Only include unconsumed int_le_reif
      if ci notin tr.definingConstraints and con.args.len >= 3 and con.args[2].kind == FznIdent:
        leReifDefs[defVar] = ci
    of "int_lin_eq":
      linEqDefs[defVar] = ci
    of "int_min", "int_max":
      minMaxDefs[defVar] = ci
    else: discard

  if leReifDefs.len == 0: return

  type
    LegTrace = object
      ## Result of tracing a leg variable chain
      epA: NoOverlapEndpoint  # first endpoint of min/max
      epB: NoOverlapEndpoint  # second endpoint of min/max
      isMin: bool             # true for int_min (leg lower), false for int_max (leg upper)
      offset: int             # offset from int_lin_eq (typically -radius or +radius)
      innerVar: string        # the int_min/int_max output variable
      linEqCi: int            # constraint index of int_lin_eq
      minMaxCi: int           # constraint index of int_min/int_max

  proc traceLeg(tr: FznTranslator, legVarName: string): tuple[ok: bool, trace: LegTrace] =
    ## Trace a leg variable: legVar → int_lin_eq → int_min/int_max → endpoints
    if legVarName notin linEqDefs:
      return (false, LegTrace())

    let linCi = linEqDefs[legVarName]
    let linCon = tr.model.constraints[linCi]

    # Parse int_lin_eq(coeffs, vars, rhs)
    let coeffsArg = linCon.args[0]
    let varsArg = linCon.args[1]
    let rhsArg = linCon.args[2]

    var coeffs: seq[int]
    try:
      coeffs = tr.resolveIntArray(coeffsArg)
    except ValueError, KeyError:
      return (false, LegTrace())

    var rhs: int
    try:
      rhs = tr.resolveIntArg(rhsArg)
    except ValueError, KeyError:
      return (false, LegTrace())

    # Resolve variable names
    var varNames: seq[string]
    case varsArg.kind
    of FznArrayLit:
      for e in varsArg.elems:
        if e.kind == FznIdent:
          varNames.add(e.ident)
        else:
          return (false, LegTrace())
    of FznIdent:
      if varsArg.ident in tr.arrayElementNames:
        varNames = tr.arrayElementNames[varsArg.ident]
      else:
        return (false, LegTrace())
    else:
      return (false, LegTrace())

    if varNames.len != coeffs.len or varNames.len != 2:
      return (false, LegTrace())

    # Find which var is the leg var and which is the inner (min/max output)
    var innerIdx = -1
    var legIdx = -1
    for i in 0..<2:
      if varNames[i] == legVarName:
        legIdx = i
      else:
        innerIdx = i
    if innerIdx < 0 or legIdx < 0:
      return (false, LegTrace())

    let innerVarName = varNames[innerIdx]
    let legCoeff = coeffs[legIdx]
    let innerCoeff = coeffs[innerIdx]

    # Expect coeffs like [1, -1]: legCoeff*legVar + innerCoeff*innerVar = rhs
    # => legVar = (rhs - innerCoeff*innerVar) / legCoeff
    # For [1,-1],[legVar,innerVar],rhs: legVar - innerVar = rhs => legVar = innerVar + rhs
    # Only accept the standard form: legCoeff=1, innerCoeff=-1 or legCoeff=-1, innerCoeff=1
    if not ((legCoeff == 1 and innerCoeff == -1) or (legCoeff == -1 and innerCoeff == 1)):
      return (false, LegTrace())

    # legCoeff=1, innerCoeff=-1: leg - inner = rhs → leg = inner + rhs → offset = rhs
    # legCoeff=-1, innerCoeff=1: -leg + inner = rhs → leg = inner - rhs → offset = -rhs
    let offset = if legCoeff == 1: rhs else: -rhs

    # Trace inner to int_min/int_max
    if innerVarName notin minMaxDefs:
      return (false, LegTrace())

    let mmCi = minMaxDefs[innerVarName]
    let mmCon = tr.model.constraints[mmCi]
    let mmName = stripSolverPrefix(mmCon.name)
    let isMin = (mmName == "int_min")

    # Parse int_min/int_max(a, b, output)
    if mmCon.args.len < 3:
      return (false, LegTrace())

    let aArg = mmCon.args[0]
    let bArg = mmCon.args[1]

    proc makeEndpoint(arg: FznExpr): NoOverlapEndpoint =
      if arg.kind == FznIntLit:
        return NoOverlapEndpoint(isFixed: true, fixedValue: arg.intVal)
      elif arg.kind == FznIdent:
        if arg.ident in tr.paramValues:
          return NoOverlapEndpoint(isFixed: true, fixedValue: tr.paramValues[arg.ident])
        else:
          return NoOverlapEndpoint(isFixed: false, varName: arg.ident)
      return NoOverlapEndpoint(isFixed: true, fixedValue: 0)  # fallback

    result = (true, LegTrace(
      epA: makeEndpoint(aArg),
      epB: makeEndpoint(bArg),
      isMin: isMin,
      offset: offset,
      innerVar: innerVarName,
      linEqCi: linCi,
      minMaxCi: mmCi,
    ))

  # Step 2: Count references to each bool var in non-defining constraints
  # Track which bool_clause constraints each bool appears in, so we can check
  # if ALL its references are covered by NoOverlap patterns.
  var boolVarRefClauses: Table[string, seq[int]]  # bool var → list of bool_clause constraint indices
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue
    for argIdx in 0..1:
      let arr = con.args[argIdx]
      if arr.kind != FznArrayLit: continue
      for elem in arr.elems:
        if elem.kind == FznIdent:
          boolVarRefClauses.mgetOrPut(elem.ident, @[]).add(ci)

  # Step 3: Scan 6-literal bool_clause constraints
  var nConsumed = 0
  var nSixLit = 0
  var nFailPair = 0
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue
    let posArg = con.args[0]
    let negArg = con.args[1]
    if posArg.kind != FznArrayLit or negArg.kind != FznArrayLit: continue
    if posArg.elems.len != 6 or negArg.elems.len != 0: continue
    nSixLit += 1

    # All 6 literals must be defined by int_le_reif
    var lits: array[6, string]
    var allLeReif = true
    for i in 0..5:
      if posArg.elems[i].kind != FznIdent:
        allLeReif = false
        break
      lits[i] = posArg.elems[i].ident
      if lits[i] notin leReifDefs:
        allLeReif = false
        break
    if not allLeReif: continue

    # (allExclusive check deferred to two-pass consumption below)

    # For each lit, extract the int_le_reif args: (a, b, boolVar)
    # One of a/b is a constant (box bound), the other is a defined leg var
    type LeReifInfo = object
      constVal: int
      legVarName: string
      constIsArg0: bool  # true: int_le_reif(const, legVar, b), false: int_le_reif(legVar, const, b)
      leReifCi: int

    var infos: array[6, LeReifInfo]
    var allValid = true
    for i in 0..5:
      let leReifCi = leReifDefs[lits[i]]
      let leReifCon = tr.model.constraints[leReifCi]
      let a0 = leReifCon.args[0]
      let a1 = leReifCon.args[1]
      let a0IsConst = a0.kind == FznIntLit or (a0.kind == FznIdent and a0.ident in tr.paramValues)
      let a1IsConst = a1.kind == FznIntLit or (a1.kind == FznIdent and a1.ident in tr.paramValues)

      if a0IsConst and not a1IsConst and a1.kind == FznIdent:
        let cv = if a0.kind == FznIntLit: a0.intVal else: tr.paramValues[a0.ident]
        infos[i] = LeReifInfo(constVal: cv, legVarName: a1.ident, constIsArg0: true, leReifCi: leReifCi)
      elif not a0IsConst and a1IsConst and a0.kind == FznIdent:
        let cv = if a1.kind == FznIntLit: a1.intVal else: tr.paramValues[a1.ident]
        infos[i] = LeReifInfo(constVal: cv, legVarName: a0.ident, constIsArg0: false, leReifCi: leReifCi)
      else:
        allValid = false
        break
    if not allValid: continue

    # Trace each leg variable
    var traces: array[6, LegTrace]
    var tracesOk = true
    for i in 0..5:
      let (ok, trace) = traceLeg(tr, infos[i].legVarName)
      if not ok:
        tracesOk = false
        break
      traces[i] = trace
    if not tracesOk: continue

    # Group into 3 pairs by dimension.
    # Each pair should have one isMin (leg lower) and one !isMin (leg upper)
    # with the same endpoint variables (epA, epB).
    # NOTE: The 6 items are NOT necessarily in consecutive dimension pairs —
    # we must match by endpoint signature.
    var pattern: NoOverlapPattern
    var pairOk = true
    var radius = 0

    # Build endpoint key for matching
    proc endpointKey(ep: NoOverlapEndpoint): string =
      if ep.isFixed: "F" & $ep.fixedValue
      else: "V" & ep.varName

    # Match traces into pairs by (epA_key, epB_key)
    type DimPair = object
      minIdx, maxIdx: int
    var pairs: seq[DimPair]
    var used: array[6, bool]

    for i in 0..5:
      if used[i]: continue
      let keyA = endpointKey(traces[i].epA)
      let keyB = endpointKey(traces[i].epB)
      var found = false
      for j in (i+1)..5:
        if used[j]: continue
        if endpointKey(traces[j].epA) == keyA and endpointKey(traces[j].epB) == keyB:
          # Found matching pair — verify one isMin and one isMax
          if traces[i].isMin == traces[j].isMin:
            continue  # both min or both max — not a valid pair
          if traces[i].isMin:
            pairs.add(DimPair(minIdx: i, maxIdx: j))
          else:
            pairs.add(DimPair(minIdx: j, maxIdx: i))
          used[i] = true
          used[j] = true
          found = true
          break
      if not found:
        pairOk = false
        break

    if pairs.len != 3:
      pairOk = false

    if pairOk:
      for d in 0..2:
        let tMin = traces[pairs[d].minIdx]
        let tMax = traces[pairs[d].maxIdx]

        # Verify consistent radius: offset should be -radius for min, +radius for max
        let r = tMax.offset
        if tMin.offset != -r:
          pairOk = false
          break
        if d == 0:
          radius = r
        elif r != radius:
          pairOk = false
          break

        pattern.nodeA[d] = tMin.epA
        pattern.nodeB[d] = tMin.epB

        # Extract box bounds from int_le_reif constants.
        # The 6 separation conditions form 3 pairs (one per dimension):
        #   b_upper: int_le_reif(boxUpper, legLower, b) → b = (boxUpper <= legLower) → separated above
        #   b_lower: int_le_reif(legUpper, boxLower, b) → b = (legUpper <= boxLower) → separated below
        # So for the min trace (legLower): constIsArg0=true → constVal is boxUpper
        # For the max trace (legUpper): constIsArg0=false → constVal is boxLower
        let infoMin = infos[pairs[d].minIdx]
        let infoMax = infos[pairs[d].maxIdx]

        var gotLower = false
        var gotUpper = false

        if infoMin.constIsArg0:
          # int_le_reif(C, legLower, b) → b = (C <= legLower) → boxUpper = C
          pattern.boxUpper[d] = infoMin.constVal
          gotUpper = true
        else:
          # int_le_reif(legLower, C, b) → b = (legLower <= C) → boxLower = C
          pattern.boxLower[d] = infoMin.constVal
          gotLower = true

        if infoMax.constIsArg0:
          # int_le_reif(C, legUpper, b) → b = (C <= legUpper) → boxUpper = C
          pattern.boxUpper[d] = infoMax.constVal
          gotUpper = true
        else:
          # int_le_reif(legUpper, C, b) → b = (legUpper <= C) → boxLower = C
          pattern.boxLower[d] = infoMax.constVal
          gotLower = true

        if not gotLower or not gotUpper:
          pairOk = false
          break

    if not pairOk:
      nFailPair += 1
      continue

    pattern.radius = radius

    # Always consume the bool_clause itself
    pattern.consumedConstraints.add(ci)
    # Store the bool var names and their int_le_reif indices for two-pass consumption
    for i in 0..5:
      pattern.consumedBoolVars.add(lits[i])

    # Mark the bool_clause as consumed
    tr.definingConstraints.incl(ci)

    tr.noOverlapPatterns.add(pattern)
    nConsumed += 1

  if nSixLit > 0 and nFailPair > 0:
    stderr.writeLine(&"[FZN] NoOverlap: {nSixLit} 6-lit clauses, {tr.noOverlapPatterns.len} matched, " &
                     &"{nFailPair} unmatched (pair mismatch)")

  # Two-pass consumption: now that ALL patterns are detected, check each bool var.
  # A bool can be consumed if ALL bool_clause constraints referencing it are NoOverlap patterns
  # (i.e., all their constraint indices are in definingConstraints).
  var nBoolsConsumed = 0
  var nLeReifConsumed = 0
  var consumedBools: HashSet[string]
  for pattern in tr.noOverlapPatterns:
    for boolVar in pattern.consumedBoolVars:
      if boolVar in consumedBools: continue
      # Check if ALL clauses referencing this bool are consumed (= became NoOverlap patterns)
      let refs = boolVarRefClauses.getOrDefault(boolVar, @[])
      var allCovered = true
      for clauseCi in refs:
        if clauseCi notin tr.definingConstraints:
          allCovered = false
          break
      if allCovered and refs.len > 0:
        consumedBools.incl(boolVar)
        tr.definedVarNames.incl(boolVar)
        nBoolsConsumed += 1
        # Also consume its defining int_le_reif constraint
        if boolVar in leReifDefs:
          let leReifCi = leReifDefs[boolVar]
          if leReifCi notin tr.definingConstraints:
            tr.definingConstraints.incl(leReifCi)
            nLeReifConsumed += 1

  nConsumed += nLeReifConsumed
  if tr.noOverlapPatterns.len > 0:
    stderr.writeLine(&"[FZN] Detected {tr.noOverlapPatterns.len} NoOverlap patterns, " &
                     &"{nConsumed} constraints consumed, {nBoolsConsumed} bools eliminated, " &
                     &"{nLeReifConsumed} int_le_reif consumed")


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
    if name in ["array_var_int_element", "array_var_int_element_nonshifted",
                "array_var_bool_element", "array_var_bool_element_nonshifted"]:
      arrayElems = tr.resolveMixedArray(con.args[1])
    else:
      # array_int_element / array_bool_element: constant array
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

proc buildSyntheticElementChannelBindings(tr: var FznTranslator) =
  ## Builds element channel bindings for synthetic channels (precomputed lookup tables
  ## from detectConditionalGainChannels).
  for syn in tr.syntheticElementChannels:
    if syn.varName notin tr.varPositions:
      continue
    let channelPos = tr.varPositions[syn.varName]

    if syn.originVar notin tr.varPositions:
      continue
    let originPos = tr.varPositions[syn.originVar]
    let indexExpr = tr.getExpr(originPos) - 1  # FZN is 1-based

    var arrayElems: seq[ArrayElement[int]]
    for v in syn.lookupTable:
      arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

    let binding = ChannelBinding[int](
      channelPosition: channelPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(channelPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)

proc buildMinMaxChannelBindings(tr: var FznTranslator) =
  ## Builds min/max channel bindings from array_int_minimum/maximum and int_min/int_max
  ## constraints with defines_var annotations. Must be called after buildDefinedExpressions
  ## so that defined-var inputs can be resolved.
  for def in tr.minMaxChannelDefs:
    let con = tr.model.constraints[def.ci]
    if def.varName notin tr.varPositions:
      continue
    let channelPos = tr.varPositions[def.varName]
    let name = stripSolverPrefix(con.name)
    var inputExprs: seq[AlgebraicExpression[int]]
    if name in ["int_min", "int_max"]:
      # int_min(a, b, c) / int_max(a, b, c) → inputs are [a, b]
      inputExprs = @[tr.resolveExprArg(con.args[0]), tr.resolveExprArg(con.args[1])]
    else:
      # array_int_minimum(m, array) / array_int_maximum(m, array) → inputs are array
      inputExprs = tr.resolveExprArray(con.args[1])
    if inputExprs.len == 0:
      continue
    tr.sys.baseArray.addMinMaxChannelBinding(channelPos, def.isMin, inputExprs)

  if tr.sys.baseArray.minMaxChannelBindings.len > 0:
    stderr.writeLine(&"[FZN] Detected {tr.sys.baseArray.minMaxChannelBindings.len} min/max channel variables")

proc buildSetUnionChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings for set_union patterns:
  ## - Individual unions: max(A_bool, B_bool) per boolean
  ## - Chains with comprehension pattern: N-ary max over product expressions
  ## - Chains without comprehension: N-ary max over leaf booleans

  let zeroExpr = newAlgebraicExpression[int](
    positions = initPackedSet[int](),
    node = ExpressionNode[int](kind: LiteralNode, value: 0),
    linear = true)
  let oneExpr = newAlgebraicExpression[int](
    positions = initPackedSet[int](),
    node = ExpressionNode[int](kind: LiteralNode, value: 1),
    linear = true)

  var nIndividual = 0
  var nChainBindings = 0
  var nCompBindings = 0

  # --- Handle individual (non-chain) set_union channels ---
  for def in tr.setUnionChannelDefs:
    let con = tr.model.constraints[def.ci]
    let cName = def.resultName
    if cName notin tr.setVarBoolPositions:
      continue
    let cVar = tr.setVarBoolPositions[cName]
    if cVar.positions.len == 0:
      continue

    let aInfo = tr.resolveSetArg(con.args[0])
    let bInfo = tr.resolveSetArg(con.args[1])

    for idx in 0..<cVar.positions.len:
      let elem = cVar.lo + idx
      let cBoolPos = cVar.positions[idx]

      var aExpr: AlgebraicExpression[int]
      var aIsConst = false
      var aConstVal = 0
      if aInfo.isConst:
        aIsConst = true
        aConstVal = if elem in aInfo.constVals: 1 else: 0
      else:
        let aPos = getSetBoolPosition(aInfo.varInfo, elem)
        if aPos >= 0:
          aExpr = tr.getExpr(aPos)
        else:
          aIsConst = true
      if aIsConst:
        aExpr = if aConstVal == 1: oneExpr else: zeroExpr

      var bExpr: AlgebraicExpression[int]
      var bIsConst = false
      var bConstVal = 0
      if bInfo.isConst:
        bIsConst = true
        bConstVal = if elem in bInfo.constVals: 1 else: 0
      else:
        let bPos = getSetBoolPosition(bInfo.varInfo, elem)
        if bPos >= 0:
          bExpr = tr.getExpr(bPos)
        else:
          bIsConst = true
      if bIsConst:
        bExpr = if bConstVal == 1: oneExpr else: zeroExpr

      if aIsConst and bIsConst:
        tr.sys.baseArray.setDomain(cBoolPos, @[max(aConstVal, bConstVal)])
      else:
        tr.sys.baseArray.addMinMaxChannelBinding(cBoolPos, false, @[aExpr, bExpr])
        inc nIndividual

  # --- Handle chains with set comprehension pattern ---
  # R.bools[v] = max over products where sumVal=v of (product_expression)
  # R.bools[0] = 1 if base contains 0 (always true for gt-sort)
  var comprehensionChainIndices: PackedSet[int]
  for comp in tr.setComprehensions:
    comprehensionChainIndices.incl(comp.chainIdx)
    let chain = tr.setUnionChains[comp.chainIdx]
    let rName = chain.resultName
    if rName notin tr.setVarBoolPositions:
      continue
    let rVar = tr.setVarBoolPositions[rName]
    if rVar.positions.len == 0:
      continue

    # Group pairs by sumVal
    var pairsBySumVal: Table[int, seq[string]]  # sumVal -> product var names
    for pair in comp.pairs:
      pairsBySumVal.mgetOrPut(pair.sumVal, @[]).add(pair.productVarName)

    for idx in 0..<rVar.positions.len:
      let v = rVar.lo + idx
      let rBoolPos = rVar.positions[idx]

      if chain.baseIsConst and v in chain.baseConstVals:
        # Base set always contributes this value
        tr.sys.baseArray.setDomain(rBoolPos, @[1])
        continue

      if v notin pairsBySumVal:
        # No pair contributes this value
        if not chain.baseIsConst:
          # If base is variable, include its boolean
          let baseInfo = tr.setVarBoolPositions.getOrDefault(chain.baseName)
          let bPos = getSetBoolPosition(baseInfo, v)
          if bPos >= 0:
            tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, @[tr.getExpr(bPos)])
            inc nCompBindings
          else:
            tr.sys.baseArray.setDomain(rBoolPos, @[0])
        else:
          tr.sys.baseArray.setDomain(rBoolPos, @[0])
        continue

      # Collect product expressions for all pairs with this sumVal
      var inputExprs: seq[AlgebraicExpression[int]]

      # Include base boolean if base is a variable set
      if not chain.baseIsConst:
        let baseInfo = tr.setVarBoolPositions.getOrDefault(chain.baseName)
        let bPos = getSetBoolPosition(baseInfo, v)
        if bPos >= 0:
          inputExprs.add(tr.getExpr(bPos))

      for productName in pairsBySumVal[v]:
        if productName in tr.definedVarExprs:
          inputExprs.add(tr.definedVarExprs[productName])
        elif productName in tr.varPositions:
          inputExprs.add(tr.getExpr(tr.varPositions[productName]))

      if inputExprs.len == 0:
        tr.sys.baseArray.setDomain(rBoolPos, @[0])
      elif inputExprs.len == 1:
        # Single input: direct channel binding (avoid max overhead)
        tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, inputExprs)
        inc nCompBindings
      else:
        # N-ary max over all product expressions
        tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, inputExprs)
        inc nCompBindings

  # --- Handle chains WITHOUT comprehension pattern (plain chain collapse) ---
  for chainIdx in 0..<tr.setUnionChains.len:
    if chainIdx in comprehensionChainIndices:
      continue
    let chain = tr.setUnionChains[chainIdx]
    let rName = chain.resultName
    if rName notin tr.setVarBoolPositions:
      continue
    let rVar = tr.setVarBoolPositions[rName]
    if rVar.positions.len == 0:
      continue

    for idx in 0..<rVar.positions.len:
      let v = rVar.lo + idx
      let rBoolPos = rVar.positions[idx]

      var inputExprs: seq[AlgebraicExpression[int]]

      # Include base
      if chain.baseIsConst:
        if v in chain.baseConstVals:
          tr.sys.baseArray.setDomain(rBoolPos, @[1])
          continue
      else:
        let baseInfo = tr.setVarBoolPositions.getOrDefault(chain.baseName)
        let bPos = getSetBoolPosition(baseInfo, v)
        if bPos >= 0:
          inputExprs.add(tr.getExpr(bPos))

      # Include all leaves
      for leafName in chain.leafNames:
        if leafName in tr.setVarBoolPositions:
          let leafInfo = tr.setVarBoolPositions[leafName]
          let lPos = getSetBoolPosition(leafInfo, v)
          if lPos >= 0:
            inputExprs.add(tr.getExpr(lPos))

      if inputExprs.len == 0:
        tr.sys.baseArray.setDomain(rBoolPos, @[0])
      else:
        tr.sys.baseArray.addMinMaxChannelBinding(rBoolPos, false, inputExprs)
        inc nChainBindings

  if nIndividual > 0:
    stderr.writeLine(&"[FZN] Built {nIndividual} individual set_union channel bindings")
  if nChainBindings > 0:
    stderr.writeLine(&"[FZN] Built {nChainBindings} chain-collapsed set_union channel bindings")
  if nCompBindings > 0:
    stderr.writeLine(&"[FZN] Built {nCompBindings} set comprehension channel bindings (from {tr.setComprehensions.len} patterns)")

proc buildCaseAnalysisChannelBindings(tr: var FznTranslator) =
  ## Builds channel bindings for case-analysis patterns detected by
  ## detectCaseAnalysisChannels. Each target variable becomes a channel
  ## with a constant lookup table indexed by source variable positions.
  var nBuilt = 0
  for def in tr.caseAnalysisDefs:
    if def.targetVarName notin tr.varPositions: continue
    let channelPos = tr.varPositions[def.targetVarName]

    # Build array elements (all constants from precomputed lookup table)
    var arrayElems: seq[ArrayElement[int]]
    for v in def.lookupTable:
      arrayElems.add(ArrayElement[int](isConstant: true, constantValue: v))

    # Build index expression from source positions
    # Row-major: index = (src0 - off0) * size1 * ... * sizeN + ... + (srcN - offN)
    var indexExpr: AlgebraicExpression[int]
    var valid = true
    for i, srcName in def.sourceVarNames:
      if srcName notin tr.varPositions:
        valid = false
        break
      let srcPos = tr.varPositions[srcName]
      let srcExpr = tr.getExpr(srcPos)
      let termExpr = srcExpr - def.domainOffsets[i]
      if i == 0:
        indexExpr = termExpr
      else:
        indexExpr = indexExpr * def.domainSizes[i] + termExpr
    if not valid: continue

    # Create and register channel binding
    let binding = ChannelBinding[int](
      channelPosition: channelPos,
      indexExpression: indexExpr,
      arrayElements: arrayElems
    )
    let bindingIdx = tr.sys.baseArray.channelBindings.len
    tr.sys.baseArray.channelBindings.add(binding)
    tr.sys.baseArray.channelPositions.incl(channelPos)

    for pos in indexExpr.positions.items:
      if pos notin tr.sys.baseArray.channelsAtPosition:
        tr.sys.baseArray.channelsAtPosition[pos] = @[bindingIdx]
      else:
        tr.sys.baseArray.channelsAtPosition[pos].add(bindingIdx)
    inc nBuilt

  if nBuilt > 0:
    stderr.writeLine(&"[FZN] Built {nBuilt} case-analysis channel bindings " &
                     &"(total channels: {tr.sys.baseArray.channelBindings.len})")

proc buildInverseChannelBindings(tr: var FznTranslator) =
  ## Builds inverse channel groups from patterns detected by detectInverseChannelPatterns.
  for pattern in tr.inverseChannelPatterns:
    let arrayPositions = tr.arrayPositions[pattern.arrayName]
    # Resolve forward (index) positions
    var forwardPositions: seq[int]
    for vn in pattern.indexVarNames:
      forwardPositions.add(tr.varPositions[vn])

    # Determine the forward base (minimum result value = the "name" of forwardPositions[0])
    # and sort by result value to align positions with their result values
    var pairs: seq[(int, int, string)]  # (resultValue, forwardPosition, varName)
    for i in 0..<pattern.resultValues.len:
      pairs.add((pattern.resultValues[i], forwardPositions[i], pattern.indexVarNames[i]))
    pairs.sort(proc(a, b: (int, int, string)): int = cmp(a[0], b[0]))

    var sortedForward: seq[int]
    var sortedResults: seq[int]
    for (rv, fp, _) in pairs:
      sortedForward.add(fp)
      sortedResults.add(rv)

    let forwardBase = sortedResults[0]
    # Verify result values are consecutive
    var consecutive = true
    for i in 1..<sortedResults.len:
      if sortedResults[i] != sortedResults[i-1] + 1:
        consecutive = false
        break
    if not consecutive:
      stderr.writeLine(&"[FZN] Warning: inverse channel on '{pattern.arrayName}' has non-consecutive results, skipping")
      continue

    # Inverse base is 1 (FlatZinc arrays are 1-based)
    let inverseBase = 1

    # Default value: find a value in the inverse domain that is NOT in the result values
    # Typically 0 for alldifferent_except_0 patterns
    let resultSet = sortedResults.toHashSet()
    var defaultValue = 0
    if defaultValue in resultSet:
      # Find any value not in the result set from the inverse domain
      let dom = tr.sys.baseArray.domain[arrayPositions[0]]
      for v in dom:
        if v notin resultSet:
          defaultValue = v
          break

    tr.sys.baseArray.addInverseChannelGroup(
      sortedForward, arrayPositions, forwardBase, inverseBase, defaultValue)

    # Domain reduction: if the inverse array has all-constant elements,
    # each forward position is uniquely determined.
    # element(forward[i], constantArray, i+forwardBase) means constantArray[forward[i]] = i+forwardBase
    # So forward[i] = the unique index where constantArray has value (i+forwardBase).
    var nReduced = 0
    block:
      # Get the array declaration elements
      var arrayArg = FznExpr(kind: FznIdent, ident: pattern.arrayName)
      let elems = tr.resolveVarArrayElems(arrayArg)
      if elems.len > 0:
        # Check if all elements are integer literals (constant array)
        var allConstant = true
        var constValues: seq[int]
        for elem in elems:
          if elem.kind == FznIntLit:
            constValues.add(elem.intVal)
          else:
            allConstant = false
            break

        if allConstant:
          # Build value -> 1-based index lookup
          var valueToIndex: Table[int, int]
          for idx, v in constValues:
            valueToIndex[v] = idx + inverseBase  # 1-based FlatZinc index

          # Reduce each forward position's domain to its unique value
          for i, fpos in sortedForward:
            let targetValue = i + forwardBase  # what constantArray[forward[i]] must equal
            if targetValue in valueToIndex:
              let requiredIdx = valueToIndex[targetValue]
              tr.sys.baseArray.domain[fpos] = @[requiredIdx]
              inc nReduced

    stderr.writeLine(&"[FZN] Built inverse channel group on '{pattern.arrayName}': " &
                     &"{sortedForward.len} forward + {arrayPositions.len} inverse positions, " &
                     &"forwardBase={forwardBase}, defaultValue={defaultValue}" &
                     (if nReduced > 0: &", {nReduced} forward domains fixed" else: ""))

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

proc detectInversePatterns(tr: var FznTranslator) =
  ## Detects involution patterns from array_var_int_element constraints.
  ## Pattern: for an n-element array A, n constraints of the form
  ##   array_var_int_element(A[i], A, i)  for i in 1..n
  ## encode the involution A[A[i]] = i. These are replaced by an InverseGroup
  ## that maintains the invariant via compound moves.
  ## Also removes matching fzn_all_different_int constraints (implied by involution).

  # Step 1: Group array_var_int_element constraints by their array argument
  var arrayGroups: Table[string, seq[int]]  # array name -> constraint indices
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name notin ["array_var_int_element", "array_var_int_element_nonshifted",
                   "array_var_bool_element", "array_var_bool_element_nonshifted"]:
      continue
    if con.hasAnnotation("defines_var"):
      continue
    # Array argument is arg[1]
    let arrArg = con.args[1]
    if arrArg.kind != FznIdent:
      continue
    let arrName = arrArg.ident
    if arrName notin arrayGroups:
      arrayGroups[arrName] = @[]
    arrayGroups[arrName].add(ci)

  # Step 2: For each group, check if it forms an involution pattern
  for arrName, ciList in arrayGroups:
    # Get the element names for this array
    if arrName notin tr.arrayElementNames:
      continue
    let elemNames = tr.arrayElementNames[arrName]
    let n = elemNames.len
    if ciList.len != n:
      continue  # must have exactly one constraint per element

    # Build map: element name -> 0-based index in the array
    var nameToIdx: Table[string, int]
    for i, name in elemNames:
      nameToIdx[name] = i

    # Check each constraint: arg[0] must be one of the array elements,
    # arg[2] must be the constant (1-based index) of that element
    var matched = newSeq[bool](n)
    var allMatch = true
    for ci in ciList:
      let con = tr.model.constraints[ci]
      # arg[0] = index (should be one of the array's element variables)
      if con.args[0].kind != FznIdent:
        allMatch = false
        break
      let indexName = con.args[0].ident
      # The index might be a defined variable — resolve through definedVarNames
      # But for the involution, the index should be one of the array elements directly
      if indexName notin nameToIdx:
        allMatch = false
        break
      let elemIdx = nameToIdx[indexName]  # 0-based

      # arg[2] = value (should be constant = elemIdx + 1, i.e., 1-based)
      if con.args[2].kind != FznIntLit:
        allMatch = false
        break
      let constVal = con.args[2].intVal
      if constVal != elemIdx + 1:
        allMatch = false
        break

      if matched[elemIdx]:
        allMatch = false  # duplicate
        break
      matched[elemIdx] = true

    if not allMatch:
      continue
    # Verify all elements matched
    var complete = true
    for m in matched:
      if not m:
        complete = false
        break
    if not complete:
      continue

    # All checks passed — this is an involution group!
    # Get positions for all elements
    if arrName notin tr.arrayPositions:
      continue
    let positions = tr.arrayPositions[arrName]
    if positions.len != n:
      continue

    # Mark all element constraints as consumed
    for ci in ciList:
      tr.definingConstraints.incl(ci)

    # Find and mark matching fzn_all_different_int constraints on the same positions
    let posSet = toPackedSet(positions)
    var nAllDiffRemoved = 0
    for ci2, con2 in tr.model.constraints:
      if ci2 in tr.definingConstraints:
        continue
      let cname = stripSolverPrefix(con2.name)
      if cname notin ["fzn_all_different_int", "all_different_int"]:
        continue
      # Check if the constraint's variable set matches our positions
      let varElems = tr.resolveVarArrayElems(con2.args[0])
      if varElems.len != n:
        continue
      var allInGroup = true
      for elem in varElems:
        if elem.kind != FznIdent or elem.ident notin nameToIdx:
          allInGroup = false
          break
      if allInGroup:
        tr.definingConstraints.incl(ci2)
        inc nAllDiffRemoved

    # Register the inverse group (valueOffset = -1 for 1-based FlatZinc indexing)
    tr.sys.baseArray.addInverseGroup(positions, -1)

    stderr.writeLine(&"[FZN] Detected involution on array '{arrName}': {n} positions, " &
                     &"{ciList.len} element + {nAllDiffRemoved} all_different constraints consumed")


proc detectInverseChannelPatterns(tr: var FznTranslator) =
  ## Detects inverse channel patterns from array_var_int_element constraints.
  ## Pattern: for an array A of size S, P constraints of the form
  ##   array_var_int_element(index_p, A, p)  for p in 1..P
  ## where index_p are distinct positioned variables NOT in A, and p is a constant.
  ## This encodes A[index_p] = p, i.e., A is the inverse of the index variables.
  ## The A positions become channel variables.
  ## Also consumes matching GCC/alldifferent_except_0 constraints on A.

  # Step 1: Group array_var_int_element constraints by their array argument
  var arrayGroups: Table[string, seq[int]]  # array name -> constraint indices
  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints:
      continue
    let name = stripSolverPrefix(con.name)
    if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]:
      continue
    if con.hasAnnotation("defines_var"):
      continue
    # Array argument is arg[1] — must be a named array
    let arrArg = con.args[1]
    if arrArg.kind != FznIdent:
      continue
    # Index arg[0] must be a named variable
    if con.args[0].kind != FznIdent:
      continue
    # Result arg[2] must be a constant integer
    if con.args[2].kind != FznIntLit:
      continue
    let arrName = arrArg.ident
    if arrName notin arrayGroups:
      arrayGroups[arrName] = @[]
    arrayGroups[arrName].add(ci)

  # Step 2: For each group, check if it forms an inverse channel pattern
  for arrName, ciList in arrayGroups:
    if arrName notin tr.arrayPositions:
      continue
    let arrayPositions = tr.arrayPositions[arrName]
    let arraySize = arrayPositions.len

    # Get element names for the array (to detect involution overlap)
    var arrayElemNames: HashSet[string]
    if arrName in tr.arrayElementNames:
      for n in tr.arrayElementNames[arrName]:
        arrayElemNames.incl(n)

    # Collect index var names and result values
    var indexVarNames: seq[string]
    var resultValues: seq[int]
    var resultSet: HashSet[int]
    var allValid = true
    var isInvolution = true  # check if index vars ARE the array elements
    for ci in ciList:
      let con = tr.model.constraints[ci]
      let indexName = con.args[0].ident
      let resultVal = con.args[2].intVal

      # Index must be a positioned variable
      if indexName notin tr.varPositions:
        allValid = false
        break
      # Check for duplicate result values
      if resultVal in resultSet:
        allValid = false
        break
      resultSet.incl(resultVal)
      indexVarNames.add(indexName)
      resultValues.add(resultVal)

      # Check if this is an involution (index var is from the same array)
      if indexName notin arrayElemNames:
        isInvolution = false

    if not allValid:
      continue
    # Skip involution patterns (handled by detectInversePatterns)
    if isInvolution:
      continue
    # Need at least 2 constraints
    if ciList.len < 2:
      continue
    # All index vars must be distinct
    if indexVarNames.toHashSet().len != indexVarNames.len:
      continue

    # Result values must be valid indices into the array (1-based)
    var resultValsValid = true
    for rv in resultValues:
      if rv < 1 or rv > arraySize:
        resultValsValid = false
        break
    if not resultValsValid:
      continue

    # Find matching GCC or alldifferent_except_0 constraints on the array positions
    let arrayPosSet = toPackedSet(arrayPositions)
    var gccCIs: seq[int]
    for ci2, con2 in tr.model.constraints:
      if ci2 in tr.definingConstraints:
        continue
      let cname = stripSolverPrefix(con2.name)
      case cname
      of "fzn_global_cardinality", "fzn_global_cardinality_closed",
         "fzn_global_cardinality_low_up", "fzn_global_cardinality_low_up_closed":
        # Check if the x array covers our array positions
        let varElems = tr.resolveVarArrayElems(con2.args[0])
        if varElems.len == 0: continue
        var positions: seq[int]
        var match = true
        for elem in varElems:
          if elem.kind != FznIdent or elem.ident notin tr.varPositions:
            match = false
            break
          positions.add(tr.varPositions[elem.ident])
        if not match: continue
        if toPackedSet(positions) == arrayPosSet:
          gccCIs.add(ci2)
      of "fzn_all_different_int", "all_different_int", "fzn_alldifferent_except_0":
        let varElems = tr.resolveVarArrayElems(con2.args[0])
        if varElems.len == 0: continue
        var positions: seq[int]
        var match = true
        for elem in varElems:
          if elem.kind != FznIdent or elem.ident notin tr.varPositions:
            match = false
            break
          positions.add(tr.varPositions[elem.ident])
        if not match: continue
        if toPackedSet(positions) == arrayPosSet:
          gccCIs.add(ci2)
      else:
        discard

    # Mark element constraints as consumed
    for ci in ciList:
      tr.definingConstraints.incl(ci)
    # Mark GCC/alldifferent constraints as consumed
    for ci2 in gccCIs:
      tr.definingConstraints.incl(ci2)

    # Store the pattern
    tr.inverseChannelPatterns.add((
      arrayName: arrName,
      elementCIs: ciList,
      indexVarNames: indexVarNames,
      resultValues: resultValues,
      gccCIs: gccCIs
    ))

    stderr.writeLine(&"[FZN] Detected inverse channel on array '{arrName}': " &
                     &"{ciList.len} element + {gccCIs.len} GCC/alldiff constraints consumed, " &
                     &"{arraySize} inverse positions become channels")


proc detectConditionalNoOverlapPairs(tr: var FznTranslator) =
  ## Detects conditional no-overlap pair patterns from room-conflict constraints:
  ##
  ## Patient-patient (3+2 or 3+1 bool_clause):
  ##   int_lin_ne_reif([1,-1], [room_A, room_B], 0, B_ne) :: defines_var(B_ne)
  ##   int_lin_le_reif([-1,1], [adm_A, adm_B], -stay_B, B_le1) :: defines_var(B_le1)
  ##   int_lin_le_reif([-1,1], [adm_B, adm_A], -stay_A, B_le2) :: defines_var(B_le2)
  ##   bool_clause([B_le1, B_le2, B_ne], [sel_A, sel_B])  -- both optional
  ##   bool_clause([B_le1, B_le2, B_ne], [sel_A])          -- B is mandatory
  ##
  ## Occupant-patient (2+1 bool_clause):
  ##   int_ne_reif(room_A, occ_room, B_ne) :: defines_var(B_ne)
  ##   int_le_reif(occ_end, adm_A, B_le) :: defines_var(B_le)
  ##   bool_clause([B_ne, B_le], [sel_A])

  type
    ConditionalNoOverlapInfo = object
      startAName, startBName: string
      durationA, durationB: int
      resourceAName, resourceBName: string  # "" if fixed
      resourceAFixed, resourceBFixed: int
      condAName, condBName: string          # "" if always true
      consumedCIs: seq[int]                 # constraint indices to consume
      consumedVars: seq[string]             # intermediate bool vars to eliminate

  # Step 1: Index reification constraints with defines_var
  type ReifInfo = object
    ci: int
    constraintType: string  # "int_lin_ne_reif", "int_lin_le_reif", "int_ne_reif", "int_le_reif"
    varNames: seq[string]
    coeffs: seq[int]
    rhs: int

  var reifByOutputVar: Table[string, ReifInfo]  # output bool var -> info

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    if not con.hasAnnotation("defines_var"): continue
    let name = stripSolverPrefix(con.name)
    if name notin ["int_lin_ne_reif", "int_lin_le_reif", "int_ne_reif", "int_le_reif"]: continue

    var info: ReifInfo
    info.ci = ci
    info.constraintType = name

    case name
    of "int_lin_ne_reif":
      # int_lin_ne_reif(coeffs, vars, rhs, result_bool)
      if con.args.len < 4 or con.args[3].kind != FznIdent: continue
      try:
        info.coeffs = tr.resolveIntArray(con.args[0])
        let varExprs = tr.resolveVarArrayElems(con.args[1])
        info.varNames = newSeq[string](varExprs.len)
        for i, e in varExprs:
          if e.kind != FznIdent: continue
          info.varNames[i] = e.ident
        info.rhs = tr.resolveIntArg(con.args[2])
      except: continue
      reifByOutputVar[con.args[3].ident] = info

    of "int_lin_le_reif":
      # int_lin_le_reif(coeffs, vars, rhs, result_bool)
      if con.args.len < 4 or con.args[3].kind != FznIdent: continue
      try:
        info.coeffs = tr.resolveIntArray(con.args[0])
        let varExprs = tr.resolveVarArrayElems(con.args[1])
        info.varNames = newSeq[string](varExprs.len)
        for i, e in varExprs:
          if e.kind != FznIdent: continue
          info.varNames[i] = e.ident
        info.rhs = tr.resolveIntArg(con.args[2])
      except: continue
      reifByOutputVar[con.args[3].ident] = info

    of "int_ne_reif":
      # int_ne_reif(var, val, result_bool) or int_ne_reif(val, var, result_bool)
      if con.args.len < 3 or con.args[2].kind != FznIdent: continue
      info.varNames = @[]
      info.coeffs = @[]
      # Extract var and constant
      if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit:
        info.varNames = @[con.args[0].ident]
        info.rhs = con.args[1].intVal
      elif con.args[0].kind == FznIntLit and con.args[1].kind == FznIdent:
        info.varNames = @[con.args[1].ident]
        info.rhs = con.args[0].intVal
      else: continue
      reifByOutputVar[con.args[2].ident] = info

    of "int_le_reif":
      # int_le_reif(a, b, result_bool) — a <= b
      if con.args.len < 3 or con.args[2].kind != FznIdent: continue
      # We need: const <= var (meaning var >= const, i.e., admission >= occ_end)
      if con.args[0].kind == FznIntLit and con.args[1].kind == FznIdent:
        info.varNames = @[con.args[1].ident]
        info.rhs = con.args[0].intVal  # the constant (occ_end)
      elif con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit:
        info.varNames = @[con.args[0].ident]
        info.rhs = con.args[1].intVal
      else: continue
      reifByOutputVar[con.args[2].ident] = info

    else: discard

  if reifByOutputVar.len == 0: return

  # Step 2: Scan bool_clause constraints for the no-overlap patterns
  var nPatientPatient = 0
  var nOccupantPatient = 0
  var detected: seq[ConditionalNoOverlapInfo]

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue

    # Extract positive and negative literals
    var posLits, negLits: seq[string]
    if con.args[0].kind == FznArrayLit:
      for e in con.args[0].elems:
        if e.kind == FznIdent: posLits.add(e.ident)
    if con.args[1].kind == FznArrayLit:
      for e in con.args[1].elems:
        if e.kind == FznIdent: negLits.add(e.ident)

    # Pattern A: 3 positive, 1-2 negative (patient-patient no-overlap)
    # bool_clause([B_le1, B_le2, B_ne], [sel_A, sel_B]) or [sel_A]
    if posLits.len == 3 and negLits.len in {1, 2}:
      # Find which positive lits are lin_le_reif and which is lin_ne_reif
      var leReifs: seq[ReifInfo]
      var neReif: ReifInfo
      var hasNe = false
      var allFound = true

      for lit in posLits:
        if lit notin reifByOutputVar:
          allFound = false
          break
        let info = reifByOutputVar[lit]
        if info.constraintType == "int_lin_le_reif":
          leReifs.add(info)
        elif info.constraintType == "int_lin_ne_reif":
          neReif = info
          hasNe = true
        else:
          allFound = false
          break

      if allFound and hasNe and leReifs.len == 2:
        # Validate structure:
        # neReif: [1,-1], [roomA, roomB], 0 → roomA != roomB
        # leReif1: [-1,1], [admA, admB], -stayB → admA >= admB + stayB
        # leReif2: [-1,1], [admB, admA], -stayA → admB >= admA + stayA
        if neReif.coeffs == @[1, -1] and neReif.rhs == 0 and neReif.varNames.len == 2 and
           leReifs[0].coeffs == @[-1, 1] and leReifs[0].varNames.len == 2 and
           leReifs[1].coeffs == @[-1, 1] and leReifs[1].varNames.len == 2:
          let roomAName = neReif.varNames[0]
          let roomBName = neReif.varNames[1]

          # Extract admission vars and durations from le_reifs
          # leReif: [-1,1]*[x,y] <= -d means y - x <= -d, i.e., x >= y + d
          # So if leReif1 has vars [admA, admB] and rhs -stayB: admA >= admB + stayB
          #    leReif2 has vars [admB, admA] and rhs -stayA: admB >= admA + stayA
          let admA1 = leReifs[0].varNames[0]  # admA (the one that must be >= other + dur)
          let admB1 = leReifs[0].varNames[1]
          let durB = -leReifs[0].rhs  # stayB
          let admB2 = leReifs[1].varNames[0]
          let admA2 = leReifs[1].varNames[1]
          let durA = -leReifs[1].rhs  # stayA

          # Verify consistency: the two le_reifs should involve the same admission pairs
          if admA1 == admA2 and admB1 == admB2 and durA > 0 and durB > 0:
            var info: ConditionalNoOverlapInfo
            info.startAName = admA1
            info.startBName = admB1
            info.durationA = durA
            info.durationB = durB
            info.resourceAName = roomAName
            info.resourceBName = roomBName
            info.resourceAFixed = -1
            info.resourceBFixed = -1

            # Condition vars from negative literals (selection vars)
            if negLits.len >= 1:
              info.condAName = negLits[0]
            if negLits.len >= 2:
              info.condBName = negLits[1]

            info.consumedCIs = @[ci, neReif.ci, leReifs[0].ci, leReifs[1].ci]
            info.consumedVars = @[]
            for lit in posLits:
              info.consumedVars.add(lit)

            detected.add(info)
            nPatientPatient += 1

    # Pattern B: 2 positive, 1 negative (occupant-patient no-overlap)
    # bool_clause([B_ne, B_le], [sel_A])
    elif posLits.len == 2 and negLits.len == 1:
      var neReif: ReifInfo
      var leReif: ReifInfo
      var hasNe, hasLe = false

      for lit in posLits:
        if lit notin reifByOutputVar: continue
        let info = reifByOutputVar[lit]
        if info.constraintType in ["int_ne_reif", "int_lin_ne_reif"]:
          neReif = info
          hasNe = true
        elif info.constraintType in ["int_le_reif", "int_lin_le_reif"]:
          leReif = info
          hasLe = true

      if hasNe and hasLe:
        var info: ConditionalNoOverlapInfo
        info.condAName = negLits[0]  # selection var

        if neReif.constraintType == "int_ne_reif" and neReif.varNames.len == 1:
          # int_ne_reif(room, occ_room_val, B) → room != occ_room_val
          info.resourceAName = neReif.varNames[0]
          info.resourceBFixed = neReif.rhs
        elif neReif.constraintType == "int_lin_ne_reif" and neReif.varNames.len == 2 and
             neReif.coeffs == @[1, -1] and neReif.rhs == 0:
          info.resourceAName = neReif.varNames[0]
          info.resourceBName = neReif.varNames[1]
        else:
          continue

        if leReif.constraintType == "int_le_reif" and leReif.varNames.len == 1:
          # int_le_reif(occ_end, adm, B) → adm >= occ_end
          # Occupant: fixed start=0, duration=occ_end (occupies [0, occ_end))
          # Patient: start=adm, duration=stay
          # No overlap: adm >= occ_end OR occ_end <= adm (same thing)
          # We model this as: occupant has start=0, dur=occ_end; patient has start=adm, dur=stay
          # But we don't know patient's duration here — look it up later
          info.startAName = leReif.varNames[0]  # admission var
          info.durationB = leReif.rhs            # occupant end time = start(0) + duration
          info.startBName = ""                   # occupant has fixed start
          info.durationA = 0                     # will be filled if we can find it
        else:
          continue

        info.consumedCIs = @[ci, neReif.ci, leReif.ci]
        info.consumedVars = @[]
        for lit in posLits:
          info.consumedVars.add(lit)

        detected.add(info)
        nOccupantPatient += 1

  if detected.len == 0: return

  # Step 3: Consume detected patterns
  for info in detected:
    for ci in info.consumedCIs:
      tr.definingConstraints.incl(ci)
    for v in info.consumedVars:
      tr.definedVarNames.incl(v)

  # Store for later constraint creation (after translateVariables)
  for info in detected:
    tr.conditionalNoOverlapInfos.add((
      startAName: info.startAName, startBName: info.startBName,
      durationA: info.durationA, durationB: info.durationB,
      resourceAName: info.resourceAName, resourceBName: info.resourceBName,
      resourceAFixed: info.resourceAFixed, resourceBFixed: info.resourceBFixed,
      condAName: info.condAName, condBName: info.condBName,
      consumedCIs: info.consumedCIs, consumedVars: info.consumedVars))

  stderr.writeLine(&"[FZN] Detected {nPatientPatient} patient-patient + {nOccupantPatient} occupant-patient conditional no-overlap pairs")


proc detectConditionalCumulativePattern(tr: var FznTranslator) =
  ## Detects the room_admission encoding pattern:
  ##   array_var_int_element(room[p], [ra[1,p]..ra[n,p]], result) :: defines_var(result)
  ##   int_eq_reif(result, admission[p], B) :: defines_var(B)
  ##   fzn_cumulative([fixed..., ra[r,1]..ra[r,n]], durations, heights, limit) for each room r
  ##
  ## Replaces with ConditionalCumulative constraints where tasks are active
  ## only when room[p] == r AND selection[p] == true.

  type
    ElementInfo = object
      ci: int
      indexVarName: string      # room[p]
      arrayVarNames: seq[string] # [ra[1,p], ra[2,p], ...]
      resultVarName: string      # element output (channel), "" if constant result
      resultConstVal: int        # constant result value (when resultVarName == "")

  # Pre-build array name -> element names and constant values from model variable declarations
  # (arrayElementNames is populated later in translateVariables, so we build a local one)
  var localArrayElements: Table[string, seq[string]]
  var localArrayConstVals: Table[string, seq[int]]  # parallel: const value when name is ""
  for decl in tr.model.variables:
    if decl.value != nil and decl.value.kind == FznArrayLit:
      var elemNames: seq[string]
      var constVals: seq[int]
      for e in decl.value.elems:
        if e.kind == FznIdent:
          elemNames.add(e.ident)
          constVals.add(0)
        elif e.kind == FznIntLit:
          elemNames.add("")
          constVals.add(e.intVal)
        else:
          elemNames.add("")
          constVals.add(0)
      localArrayElements[decl.name] = elemNames
      localArrayConstVals[decl.name] = constVals

  template resolveArrayNames(arrArg: FznExpr): seq[string] =
    block:
      var res: seq[string]
      if arrArg.kind == FznIdent:
        if arrArg.ident in localArrayElements:
          res = localArrayElements[arrArg.ident]
        elif arrArg.ident in tr.arrayElementNames:
          res = tr.arrayElementNames[arrArg.ident]
      elif arrArg.kind == FznArrayLit:
        for elem in arrArg.elems:
          if elem.kind == FznIdent:
            res.add(elem.ident)
          else:
            res.add("")
      res

  # Step 1: Find element constraints with ra var arrays
  # Scan ALL constraints, not just channelConstraints — some element constraints have
  # constant results (mandatory patients with fixed admission days) and no defines_var.
  var elementInfos: seq[ElementInfo]
  var elementByResult: Table[string, int]

  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
    if con.args.len < 3: continue
    if con.args[0].kind != FznIdent: continue
    # Result can be variable (FznIdent) or constant (FznIntLit)
    let hasVarResult = con.args[2].kind == FznIdent
    let hasConstResult = con.args[2].kind == FznIntLit
    if not hasVarResult and not hasConstResult: continue

    let arrayVarNames = resolveArrayNames(con.args[1])
    if arrayVarNames.len == 0: continue

    # All array elements must be variables (not constants, not already defined/channel)
    var allVars = true
    for vn in arrayVarNames:
      if vn == "" or vn in tr.definedVarNames or vn in tr.channelVarNames:
        allVars = false
        break
    if not allVars: continue

    if hasVarResult:
      elementByResult[con.args[2].ident] = elementInfos.len
      elementInfos.add(ElementInfo(
        ci: ci,
        indexVarName: con.args[0].ident,
        arrayVarNames: arrayVarNames,
        resultVarName: con.args[2].ident,
        resultConstVal: 0
      ))
    else:
      # Constant result: mandatory patient with fixed admission day
      elementInfos.add(ElementInfo(
        ci: ci,
        indexVarName: con.args[0].ident,
        arrayVarNames: arrayVarNames,
        resultVarName: "",
        resultConstVal: con.args[2].intVal
      ))

  if elementInfos.len == 0: return

  # Step 2: Find int_eq_reif(result, admission, B) for each element result
  # NOTE: scan ALL constraints including definingConstraints (reif channels consumed them)
  type EqReifInfo = object
    admissionVarName: string
    selectionVarName: string  # filled in step 3

  var eqReifByResult: Table[string, EqReifInfo]

  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name != "int_eq_reif": continue
    if con.args.len < 3: continue
    if con.args[0].kind != FznIdent or con.args[1].kind != FznIdent or con.args[2].kind != FznIdent:
      continue
    let resultName = con.args[0].ident
    if resultName notin elementByResult: continue
    eqReifByResult[resultName] = EqReifInfo(
      admissionVarName: con.args[1].ident,
      selectionVarName: ""
    )

  if eqReifByResult.len == 0: return

  # Step 3: Find bool_clause linking selection to eq_reif bool vars
  # Pattern: bool_clause([B], [sel]) where B is the eq_reif bool output
  # Build set of eq_reif bool var names for quick lookup
  var eqReifBoolVars: Table[string, string]  # boolVarName -> resultVarName
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name != "int_eq_reif": continue
    if con.args.len < 3: continue
    if con.args[0].kind != FznIdent or con.args[2].kind != FznIdent: continue
    if con.args[0].ident in eqReifByResult:
      eqReifBoolVars[con.args[2].ident] = con.args[0].ident

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "bool_clause": continue
    if con.args.len < 2: continue
    var posLits, negLits: seq[string]
    if con.args[0].kind == FznArrayLit:
      for e in con.args[0].elems:
        if e.kind == FznIdent: posLits.add(e.ident)
    if con.args[1].kind == FznArrayLit:
      for e in con.args[1].elems:
        if e.kind == FznIdent: negLits.add(e.ident)
    if posLits.len == 1 and negLits.len == 1:
      if posLits[0] in eqReifBoolVars:
        let resultName = eqReifBoolVars[posLits[0]]
        if resultName in eqReifByResult:
          eqReifByResult[resultName].selectionVarName = negLits[0]

  # Step 4: Find cumulative constraints with ra vars as start times
  # Build ra_var -> (elementIdx, roomIdx) lookup
  var allRaVarNames = initHashSet[string]()
  var raVarToElementRoom: Table[string, tuple[elemIdx, roomIdx: int]]
  for ei, einfo in elementInfos:
    for ri, vn in einfo.arrayVarNames:
      allRaVarNames.incl(vn)
      raVarToElementRoom[vn] = (ei, ri)

  type ConditionalCumulativeInfo = object
    fixedTasks: seq[tuple[start, duration, height: int]]
    conditionalTasks: seq[tuple[admissionVarName, selectionVarName, roomVarName: string,
                                 duration, height, roomValue, fixedAdmission: int]]
    limit: int
    cumulativeCi: int
    consumedRaVarNames: seq[string]

  var conditionalCumulatives: seq[ConditionalCumulativeInfo]

  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name notin ["fzn_cumulative", "fzn_cumulatives"]: continue
    if ci in tr.definingConstraints: continue

    # Resolve start array names and const values
    let startArg = con.args[0]
    var startNames: seq[string]
    var startConstVals: seq[int]  # parallel: const value when name is ""
    if startArg.kind == FznIdent:
      if startArg.ident in localArrayElements:
        startNames = localArrayElements[startArg.ident]
        startConstVals = localArrayConstVals[startArg.ident]
      elif startArg.ident in tr.arrayElementNames:
        startNames = tr.arrayElementNames[startArg.ident]
        startConstVals = newSeq[int](startNames.len)
      else: continue
    elif startArg.kind == FznArrayLit:
      for e in startArg.elems:
        if e.kind == FznIdent:
          startNames.add(e.ident)
          startConstVals.add(0)
        elif e.kind == FznIntLit:
          startNames.add("")
          startConstVals.add(e.intVal)
        else:
          startNames.add("")
          startConstVals.add(0)
    else: continue

    if startNames.len == 0: continue

    # Check if this cumulative has ra vars
    var raCount = 0
    for sn in startNames:
      if sn in allRaVarNames: raCount += 1
    if raCount == 0: continue

    var durations, heights: seq[int]
    var limit: int
    try:
      durations = tr.resolveIntArray(con.args[1])
      heights = tr.resolveIntArray(con.args[2])
      limit = tr.resolveIntArg(con.args[3])
    except: continue
    if durations.len != startNames.len or heights.len != startNames.len: continue

    var ccinfo: ConditionalCumulativeInfo
    ccinfo.limit = limit
    ccinfo.cumulativeCi = ci
    var allMatched = true
    var roomValue = -1

    for i, sn in startNames:
      if sn in tr.paramValues:
        ccinfo.fixedTasks.add((tr.paramValues[sn], durations[i], heights[i]))
      elif sn == "":
        # Inline constant in the start array
        ccinfo.fixedTasks.add((startConstVals[i], durations[i], heights[i]))
      elif sn in allRaVarNames:
        let (elemIdx, roomIdx) = raVarToElementRoom[sn]
        if roomValue < 0:
          roomValue = roomIdx
        elif roomIdx != roomValue:
          allMatched = false
          break
        let einfo = elementInfos[elemIdx]
        if einfo.resultVarName == "":
          # Constant-result element: mandatory patient with fixed admission day
          # This is a conditional task (depends on room assignment) but admission is fixed
          ccinfo.conditionalTasks.add((
            admissionVarName: "",  # signals fixed admission
            selectionVarName: "",  # always active (mandatory)
            roomVarName: einfo.indexVarName,
            duration: durations[i],
            height: heights[i],
            roomValue: roomIdx + 1,  # FZN 1-based
            fixedAdmission: einfo.resultConstVal
          ))
        elif einfo.resultVarName in eqReifByResult:
          # Optional patient: element(room[p], ra_array, result), eq_reif(result, admission, B)
          let eqInfo = eqReifByResult[einfo.resultVarName]
          ccinfo.conditionalTasks.add((
            admissionVarName: eqInfo.admissionVarName,
            selectionVarName: eqInfo.selectionVarName,
            roomVarName: einfo.indexVarName,
            duration: durations[i],
            height: heights[i],
            roomValue: roomIdx + 1,  # FZN 1-based
            fixedAdmission: -1
          ))
        else:
          # Mandatory patient: element(room[p], ra_array, admission[p]) directly
          # The element result IS the admission var; no selection condition needed
          ccinfo.conditionalTasks.add((
            admissionVarName: einfo.resultVarName,
            selectionVarName: "",  # always active (mandatory)
            roomVarName: einfo.indexVarName,
            duration: durations[i],
            height: heights[i],
            roomValue: roomIdx + 1,
            fixedAdmission: -1
          ))
        ccinfo.consumedRaVarNames.add(sn)
      else:
        # Non-ra variable start time - can't convert
        allMatched = false
        break

    if not allMatched or roomValue < 0: continue
    conditionalCumulatives.add(ccinfo)

  if conditionalCumulatives.len == 0: return

  # Step 5: Consume cumulative constraints and mark ra vars as non-searchable
  for ccinfo in conditionalCumulatives:
    tr.definingConstraints.incl(ccinfo.cumulativeCi)

  # Mark ra vars as channel vars so they're not searched (but still get positions)
  var nRaChanneled = 0
  var consumedRaSet = initHashSet[string]()
  for ccinfo in conditionalCumulatives:
    for raName in ccinfo.consumedRaVarNames:
      consumedRaSet.incl(raName)
      if raName notin tr.channelVarNames and raName notin tr.definedVarNames:
        tr.channelVarNames.incl(raName)
        nRaChanneled += 1

  # Also mark ra vars from constant-result elements (mandatory patients with fixed admission)
  for ei, einfo in elementInfos:
    if einfo.resultVarName == "":
      for vn in einfo.arrayVarNames:
        consumedRaSet.incl(vn)
        if vn notin tr.channelVarNames and vn notin tr.definedVarNames:
          tr.channelVarNames.incl(vn)
          nRaChanneled += 1

  # Also remove element channel constraints whose arrays reference consumed ra vars.
  # These channels are dead (cumulative replaced by conditional cumulative)
  # and would waste time propagating.
  var elementsToRemove: seq[int]
  for ci, chanVar in tr.channelConstraints:
    let con = tr.model.constraints[ci]
    let name = stripSolverPrefix(con.name)
    if name notin ["array_var_int_element", "array_var_int_element_nonshifted"]: continue
    let arrayNames = resolveArrayNames(con.args[1])
    var hasRa = false
    for vn in arrayNames:
      if vn in consumedRaSet:
        hasRa = true
        break
    if hasRa:
      elementsToRemove.add(ci)
      if chanVar in eqReifByResult:
        # Intermediate result: eq_reif links it to admission. Safe to eliminate.
        tr.channelVarNames.excl(chanVar)
        tr.definedVarNames.incl(chanVar)
      else:
        # Mandatory patient: admission var IS the element result.
        # Remove channel status so it becomes a search position.
        # The element constraint in the main constraint set ensures consistency.
        tr.channelVarNames.excl(chanVar)

  for ci in elementsToRemove:
    tr.channelConstraints.del(ci)

  # Also consume constant-result element constraints (mandatory patients)
  for ei, einfo in elementInfos:
    if einfo.resultVarName == "":
      tr.definingConstraints.incl(einfo.ci)

  stderr.writeLine(&"[FZN] Marked {nRaChanneled} ra vars as channels, removed {elementsToRemove.len} dead element channels for conditional cumulative")

  # Store for later constraint creation
  for ccinfo in conditionalCumulatives:
    var condTaskTuples: seq[tuple[admissionVarName, selectionVarName, roomVarName: string,
                                   duration, height, roomValue, fixedAdmission: int]]
    for ct in ccinfo.conditionalTasks:
      condTaskTuples.add(ct)
    var fixedTaskTuples: seq[tuple[start, duration, height: int]]
    for ft in ccinfo.fixedTasks:
      fixedTaskTuples.add(ft)
    tr.conditionalCumulativeInfos.add((
      fixedTasks: fixedTaskTuples,
      conditionalTasks: condTaskTuples,
      limit: ccinfo.limit,
      cumulativeCi: ccinfo.cumulativeCi,
      consumedElementCIs: newSeq[int](),
      consumedEqReifCIs: newSeq[int](),
      consumedBoolClauseCIs: newSeq[int](),
      consumedRaVarNames: ccinfo.consumedRaVarNames,
      consumedBoolVarNames: newSeq[string]()))

  stderr.writeLine(&"[FZN] Detected {conditionalCumulatives.len} conditional cumulative constraints (replacing regular cumulatives)")


proc detectConditionalDayCapacityPattern(tr: var FznTranslator) =
  ## Detects the H3/H4 surgeon/OT capacity encoding pattern:
  ##   int_lin_le(coeffs, [D_1, ..., D_n], capacity)
  ## where each D_i is:
  ##   bool2int(C_i, D_i) :: defines_var(D_i)
  ##   array_bool_and([sel[p], B_day, (B_ot)?], C_i) :: defines_var(C_i)
  ##   int_eq_reif(admission[p], day, B_day) :: defines_var(B_day)
  ##   int_eq_reif(ot[p], otVal, B_ot) :: defines_var(B_ot)  [H4 only]
  ##
  ## Replaces with ConditionalDayCapacity constraints.

  # Step 1: Build lookup tables from FZN constraints
  # bool2int: outputVar -> inputVar
  var bool2intInput: Table[string, string]
  # array_bool_and: outputVar -> seq of input vars
  var boolAndInputs: Table[string, seq[string]]
  # int_eq_reif: outputVar -> (sourceVar, value)
  var eqReifSource: Table[string, tuple[sourceVar: string, value: int]]

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name == "bool2int" and con.annotations.len > 0:
      # bool2int(B, I) :: defines_var(I)
      if con.args[0].kind == FznIdent and con.args[1].kind == FznIdent:
        bool2intInput[con.args[1].ident] = con.args[0].ident
    elif name == "array_bool_and" and con.annotations.len > 0:
      # array_bool_and([...], R) :: defines_var(R)
      if con.args[0].kind == FznArrayLit and con.args[1].kind == FznIdent:
        var inputs: seq[string]
        for elem in con.args[0].elems:
          if elem.kind == FznIdent:
            inputs.add(elem.ident)
          elif elem.kind == FznBoolLit:
            if not elem.boolVal:
              inputs = @[]  # false literal => always false, skip
              break
            # true literal: skip (doesn't affect AND result)
          else:
            inputs = @[]
            break
        if inputs.len >= 1:
          boolAndInputs[con.args[1].ident] = inputs
    elif name == "int_eq_reif" and con.annotations.len > 0:
      # int_eq_reif(X, val, B) :: defines_var(B)
      if con.args[0].kind == FznIdent and con.args[1].kind == FznIntLit and
         con.args[2].kind == FznIdent:
        eqReifSource[con.args[2].ident] = (con.args[0].ident, con.args[1].intVal)

  # Also scan definingConstraints for eq_reif that were already consumed by reif channel detection
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name == "int_eq_reif" and con.args[0].kind == FznIdent and
       con.args[1].kind == FznIntLit and con.args[2].kind == FznIdent:
      if con.args[2].ident notin eqReifSource:
        eqReifSource[con.args[2].ident] = (con.args[0].ident, con.args[1].intVal)
    if name == "bool2int" and con.args[0].kind == FznIdent and con.args[1].kind == FznIdent:
      if con.args[1].ident notin bool2intInput:
        bool2intInput[con.args[1].ident] = con.args[0].ident
    if name == "array_bool_and" and con.args[0].kind == FznArrayLit and con.args[1].kind == FznIdent:
      if con.args[1].ident notin boolAndInputs:
        var inputs: seq[string]
        for elem in con.args[0].elems:
          if elem.kind == FznIdent:
            inputs.add(elem.ident)
          elif elem.kind == FznBoolLit:
            if not elem.boolVal:
              inputs = @[]
              break
          else:
            inputs = @[]
            break
        if inputs.len >= 1:
          boolAndInputs[con.args[1].ident] = inputs

  # Step 2: Find int_lin_le constraints with many bool2int variables
  # Identify the selection and admission arrays
  var selectionVarNames: HashSet[string]
  var admissionVarNames: HashSet[string]
  var otVarNames: HashSet[string]

  # Look at output arrays to identify variable roles
  for v in tr.model.variables:
    if v.isArray and v.value != nil and v.value.kind == FznArrayLit:
      if v.name.startsWith("selection"):
        for elem in v.value.elems:
          if elem.kind == FznIdent:
            selectionVarNames.incl(elem.ident)
      elif v.name.startsWith("admission"):
        for elem in v.value.elems:
          if elem.kind == FznIdent:
            admissionVarNames.incl(elem.ident)
      elif v.name == "ot" or v.name.startsWith("ot_"):
        for elem in v.value.elems:
          if elem.kind == FznIdent:
            otVarNames.incl(elem.ident)

  # Step 3: Trace each candidate int_lin_le
  type
    TaskInfo = object
      weight: int
      admissionVarName: string
      selectionVarName: string
      extraCondVarName: string  # "" if none
      extraCondVal: int
      day: int

  type
    PerDayConstraint = object
      ci: int
      day: int
      capacity: int
      tasks: seq[TaskInfo]
      consumedVarNames: seq[string]

  var nDetected = 0
  var perDayConstraints: seq[PerDayConstraint]

  for ci, con in tr.model.constraints:
    if ci in tr.definingConstraints: continue
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_le": continue

    if con.args[2].kind != FznIntLit:
      continue

    # Resolve coefficient and variable arrays (can be inline FznArrayLit or named FznIdent)
    var coeffs: seq[FznExpr]
    var vars: seq[FznExpr]
    if con.args[0].kind == FznArrayLit:
      coeffs = con.args[0].elems
    elif con.args[0].kind == FznIdent:
      # Resolve named parameter array
      if con.args[0].ident in tr.arrayValues:
        for v in tr.arrayValues[con.args[0].ident]:
          coeffs.add(FznExpr(kind: FznIntLit, intVal: v))
      else:
        continue
    else:
      continue

    if con.args[1].kind == FznArrayLit:
      vars = con.args[1].elems
    elif con.args[1].kind == FznIdent:
      # Resolve named variable array
      for v in tr.model.variables:
        if v.isArray and v.name == con.args[1].ident and v.value != nil and v.value.kind == FznArrayLit:
          vars = v.value.elems
          break
      if vars.len == 0:
        continue
    else:
      continue

    let rhs = con.args[2].intVal

    if coeffs.len != vars.len or coeffs.len < 10:
      continue

    let isFirstCandidate = perDayConstraints.len == 0 and nDetected == 0

    var tasks: seq[TaskInfo]
    var allValid = true
    var commonDay = -1
    var consumedVarNames: seq[string]

    for idx in 0..<vars.len:
      if vars[idx].kind != FznIdent or coeffs[idx].kind != FznIntLit:
        allValid = false
        break

      let dVarName = vars[idx].ident
      let weight = coeffs[idx].intVal

      if dVarName notin bool2intInput:
        allValid = false
        break
      let cVarName = bool2intInput[dVarName]

      var selVar = ""
      var day = -1
      var admVar = ""
      var extraSource = ""
      var extraVal = -1

      if cVarName in boolAndInputs:
        # Normal case: bool2int input is an array_bool_and output
        let andInputs = boolAndInputs[cVarName]

        if andInputs.len < 1 or andInputs.len > 3:
          allValid = false
          break

        for inp in andInputs:
          if inp in selectionVarNames:
            selVar = inp
          elif inp in eqReifSource:
            let (srcVar, val) = eqReifSource[inp]
            if srcVar in admissionVarNames:
              admVar = srcVar
              day = val
            elif srcVar in otVarNames:
              extraSource = srcVar
              extraVal = val
            else:
              allValid = false
              break
          else:
            allValid = false
            break
      elif cVarName in eqReifSource:
        # Mandatory patient case: bool2int input is directly eq_reif output
        # (selection=true was constant-folded away, no AND needed)
        let (srcVar, val) = eqReifSource[cVarName]
        if srcVar in admissionVarNames:
          admVar = srcVar
          day = val
          selVar = "MANDATORY"  # sentinel: always active
        else:
          allValid = false
      else:
        allValid = false

      if not allValid: break
      if admVar == "" or day < 0:
        allValid = false
        break

      if commonDay < 0:
        commonDay = day
      elif commonDay != day:
        allValid = false
        break

      tasks.add(TaskInfo(
        weight: weight,
        admissionVarName: admVar,
        selectionVarName: selVar,
        extraCondVarName: extraSource,
        extraCondVal: extraVal,
        day: day))
      consumedVarNames.add(dVarName)
      consumedVarNames.add(cVarName)

    if not allValid or tasks.len == 0:
      continue

    perDayConstraints.add(PerDayConstraint(
      ci: ci, day: commonDay, capacity: rhs, tasks: tasks,
      consumedVarNames: consumedVarNames))

  # Group by task signature (same patients, same conditions, different days)
  # Signature = sorted list of (admissionVar, selectionVar, extraCondVarName, extraCondVal, weight)
  var groups: Table[string, seq[int]]  # signature -> indices into perDayConstraints

  for i, pdc in perDayConstraints:
    var sig = ""
    for t in pdc.tasks:
      sig.add(t.admissionVarName & ":" & t.selectionVarName & ":" &
              t.extraCondVarName & ":" & $t.extraCondVal & ":" & $t.weight & ";")
    groups.mgetOrPut(sig, @[]).add(i)

  # Build ConditionalDayCapacity constraints from groups
  for sig, indices in groups:
    var maxDay = 0
    for i in indices:
      if perDayConstraints[i].day > maxDay:
        maxDay = perDayConstraints[i].day

    # Build capacity array: default to max int (unconstrained) for days not mentioned
    var capacities = newSeq[int](maxDay + 1)
    for d in 0..maxDay:
      capacities[d] = high(int32).int  # unconstrained by default

    var consumedCIs: seq[int]
    var consumedVarNames: seq[string]

    for i in indices:
      let pdc = perDayConstraints[i]
      if pdc.day <= maxDay:
        capacities[pdc.day] = pdc.capacity
      consumedCIs.add(pdc.ci)
      for vn in pdc.consumedVarNames:
        consumedVarNames.add(vn)

    # Build task list from the first constraint (all have same structure)
    let firstPdc = perDayConstraints[indices[0]]
    var taskInfos: seq[tuple[weight: int, admissionVarName, selectionVarName: string,
                              extraCondVarName: string, extraCondVal: int]]
    for t in firstPdc.tasks:
      taskInfos.add((weight: t.weight,
                      admissionVarName: t.admissionVarName,
                      selectionVarName: t.selectionVarName,
                      extraCondVarName: t.extraCondVarName,
                      extraCondVal: t.extraCondVal))

    # Mark consumed
    for ci in consumedCIs:
      tr.definingConstraints.incl(ci)
    for vn in consumedVarNames:
      if vn notin tr.channelVarNames and vn notin tr.definedVarNames:
        tr.definedVarNames.incl(vn)

    tr.conditionalDayCapacityInfos.add((
      tasks: taskInfos,
      capacities: capacities,
      maxDay: maxDay,
      consumedCIs: consumedCIs,
      consumedVarNames: consumedVarNames))

    nDetected += indices.len

  stderr.writeLine(&"[FZN] Detected {nDetected} int_lin_le → {tr.conditionalDayCapacityInfos.len} ConditionalDayCapacity constraints")


proc detectRedundantOrderings(tr: var FznTranslator) =
  ## Detects transitively redundant ordering constraints.
  ## Handles weighted edges: int_lin_le([-1,1], [a,b], -d) means b >= a + d (edge a→b weight d).
  ## Edge u→v weight w is redundant if there exists a path u→...→v with total weight >= w.
  type OrderEdge = object
    constraintIdx: int
    fromVar, toVar: string
    weight: int  # a + weight <= b

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

  # Collect ordering edges from int_lin_le with 2 variables
  # Patterns:
  #   [1,-1], [a,b], rhs  →  a - b <= rhs  →  a + (-rhs) <= b  →  edge a→b weight -rhs
  #   [-1,1], [a,b], rhs  →  -a + b <= rhs  →  b + (-rhs) <= a  →  edge b→a weight -rhs
  #   [c,-c], [a,b], rhs (c>0)  →  c(a-b) <= rhs  →  a - b <= rhs/c  →  edge a→b weight -rhs/c
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
    if coeffs.len != 2:
      continue
    # Need one positive and one negative coefficient of same magnitude
    if not ((coeffs[0] > 0 and coeffs[1] < 0 and coeffs[0] == -coeffs[1]) or
            (coeffs[0] < 0 and coeffs[1] > 0 and -coeffs[0] == coeffs[1])):
      continue
    # Resolve RHS
    var rhs: int
    try:
      rhs = tr.resolveIntArg(con.args[2])
    except CatchableError:
      continue
    # Compute weight: for coeffs [c,-c] with c>0: edge a→b weight -rhs/c
    let c = abs(coeffs[0])
    if c > 1 and rhs mod c != 0:
      continue  # Non-integer weight, skip
    let scaledRhs = rhs div c
    # Resolve variable names
    let varNames = tr.resolveVarNames(con.args[1])
    if varNames.len != 2:
      continue
    # Skip if either variable is defined (will be replaced by expression)
    if varNames[0] in tr.definedVarNames or varNames[1] in tr.definedVarNames:
      continue
    # Determine edge direction based on coefficient signs
    var fromVar, toVar: string
    if coeffs[0] > 0:
      # [+c, -c]: a - b <= rhs/c → a + (-rhs/c) <= b → edge a→b
      fromVar = varNames[0]
      toVar = varNames[1]
    else:
      # [-c, +c]: b - a <= rhs/c → b + (-rhs/c) <= a → edge b→a
      fromVar = varNames[1]
      toVar = varNames[0]
    let weight = -scaledRhs  # from + weight <= to
    discard getId(fromVar)
    discard getId(toVar)
    edges.add(OrderEdge(constraintIdx: ci, fromVar: fromVar, toVar: toVar, weight: weight))

  if edges.len == 0:
    return

  let n = nextId

  # Build adjacency: node → {successor → max weight}
  var succ = newSeq[Table[int, int]](n)
  for i in 0..<n:
    succ[i] = initTable[int, int]()
  # Map (from, to, weight) to constraint indices
  var edgeConstraints: Table[(int, int, int), seq[int]]
  for e in edges:
    let fromId = nameToId[e.fromVar]
    let toId = nameToId[e.toVar]
    # Keep max weight for adjacency
    if toId in succ[fromId]:
      succ[fromId][toId] = max(succ[fromId][toId], e.weight)
    else:
      succ[fromId][toId] = e.weight
    let key = (fromId, toId, e.weight)
    if key notin edgeConstraints:
      edgeConstraints[key] = @[]
    edgeConstraints[key].add(e.constraintIdx)

  # Compute in-degree for topological sort (Kahn's algorithm)
  var inDeg = newSeq[int](n)
  for i in 0..<n:
    for j in succ[i].keys:
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
    for v in succ[u].keys:
      inDeg[v] -= 1
      if inDeg[v] == 0:
        queue.add(v)

  if topoOrder.len != n:
    # Graph has cycles — can't do transitive reduction, skip
    return

  # Compute longest-path distances bottom-up (reverse topological order)
  # dist[u][v] = longest path weight from u to v
  const NoPath = low(int) div 2  # Safe sentinel that won't overflow when added to a weight
  var dist = newSeq[Table[int, int]](n)
  for i in 0..<n:
    dist[i] = initTable[int, int]()

  for i in countdown(topoOrder.len - 1, 0):
    let u = topoOrder[i]
    for v, w in succ[u]:
      # Direct edge u→v
      dist[u][v] = max(dist[u].getOrDefault(v, NoPath), w)
      # Transitive: u→v→...→target
      for target, d in dist[v]:
        dist[u][target] = max(dist[u].getOrDefault(target, NoPath), w + d)

  # Mark redundant edges: edge u→v weight w is redundant if
  # there exists an intermediate node x (x≠v) with succ[u][x] + dist[x][v] >= w
  var redundantCount = 0
  for e in edges:
    let fromId = nameToId[e.fromVar]
    let toId = nameToId[e.toVar]
    var isRedundant = false
    # Check if any other neighbor provides a path with >= weight
    for x, wx in succ[fromId]:
      if x == toId:
        continue
      let pathWeight = wx + dist[x].getOrDefault(toId, NoPath)
      if pathWeight >= e.weight:
        isRedundant = true
        break
    # Also: if multiple constraints exist for the same (from, to) pair,
    # keep only the one with the largest weight
    if not isRedundant:
      let maxWeight = succ[fromId][toId]  # This is the max weight for this edge
      if e.weight < maxWeight:
        isRedundant = true  # A stronger constraint exists for this edge
    if isRedundant:
      tr.redundantOrderings.incl(e.constraintIdx)
      inc redundantCount

  if redundantCount > 0:
    stderr.writeLine(&"[FZN] Ordering reduction: {edges.len} -> {edges.len - redundantCount} constraints ({redundantCount} redundant)")

proc estimateRangeImpl(tr: FznTranslator, node: ExpressionNode[int],
                       cache: var Table[pointer, (int, int)]): (int, int) =
  ## Conservative interval arithmetic to estimate the range of an expression.
  ## Returns (min, max) values the expression can take.
  ## Uses memoization cache to avoid exponential re-traversal of shared DAG nodes.
  let key = cast[pointer](node)
  if key in cache:
    return cache[key]
  var result: (int, int)
  case node.kind
  of LiteralNode:
    result = (node.value, node.value)
  of RefNode:
    let dom = tr.sys.baseArray.domain[node.position]
    if dom.len > 0:
      result = (dom[0], dom[^1])
    else:
      result = (low(int), high(int))
  of UnaryOpNode:
    let (cMin, cMax) = tr.estimateRangeImpl(node.target, cache)
    case node.unaryOp
    of Negation:
      result = (-cMax, -cMin)
    of AbsoluteValue:
      if cMin >= 0: result = (cMin, cMax)
      elif cMax <= 0: result = (-cMax, -cMin)
      else: result = (0, max(-cMin, cMax))
  of BinaryOpNode:
    let (lMin, lMax) = tr.estimateRangeImpl(node.left, cache)
    let (rMin, rMax) = tr.estimateRangeImpl(node.right, cache)
    case node.binaryOp
    of Addition:
      result = (lMin + rMin, lMax + rMax)
    of Subtraction:
      result = (lMin - rMax, lMax - rMin)
    of Multiplication:
      let products = [lMin*rMin, lMin*rMax, lMax*rMin, lMax*rMax]
      result = (min(products), max(products))
    of Maximum:
      result = (max(lMin, rMin), max(lMax, rMax))
    of Minimum:
      result = (min(lMin, rMin), min(lMax, rMax))
  cache[key] = result
  return result

proc estimateRange(tr: FznTranslator, node: ExpressionNode[int]): (int, int) =
  var cache = initTable[pointer, (int, int)]()
  tr.estimateRangeImpl(node, cache)


proc pruneZeroCapacityDays(tr: var FznTranslator) =
  ## Prune admission domains by detecting zero-capacity day constraints.
  ##
  ## Pattern: int_lin_le(coeffs, bool_vars, 0) where each bool_var is a
  ## channel encoding "selection[p] AND admission[p]==d" (surgeon capacity)
  ## or "selection[p] AND admission[p]==d AND ot[p]==o" (OT capacity).
  ##
  ## When capacity=0, no patient can be admitted on that day (for surgeon)
  ## or on that day+OT combo. For surgeon zero days, we directly prune
  ## the admission domain. For OT, we only prune if ALL OTs are zero on that day.

  # Step 1: Build defines_var map for chain tracing
  var definerOf: Table[string, int]  # varName → constraint index
  for ci, con in tr.model.constraints:
    if con.hasAnnotation("defines_var"):
      let ann = con.getAnnotation("defines_var")
      if ann.args.len > 0 and ann.args[0].kind == FznIdent:
        definerOf[ann.args[0].ident] = ci

  # Step 2: Find zero-capacity int_lin_le constraints and trace to find day values
  type CapInfo = object
    day: int
    isOtConstrained: bool  # true = OT-specific, false = surgeon (all OTs)

  var zeroCaps: seq[CapInfo]

  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_le":
      continue
    if con.args.len < 3:
      continue

    # Check RHS <= 0
    let rhsArg = con.args[2]
    if rhsArg.kind != FznIntLit or rhsArg.intVal > 0:
      continue

    # Check all coefficients are positive
    let coeffArg = con.args[0]
    if coeffArg.kind != FznArrayLit:
      continue
    var allPositive = true
    for elem in coeffArg.elems:
      if elem.kind != FznIntLit or elem.intVal <= 0:
        allPositive = false
        break
    if not allPositive:
      continue

    # Need many variables (capacity constraint spans all patients)
    let varsArg = con.args[1]
    if varsArg.kind != FznArrayLit or varsArg.elems.len < 5:
      continue

    # Trace first variable back: bool2int → array_bool_and → int_eq_reif
    let firstVar = varsArg.elems[0]
    if firstVar.kind != FznIdent or firstVar.ident notin definerOf:
      continue
    let b2iCon = tr.model.constraints[definerOf[firstVar.ident]]
    if stripSolverPrefix(b2iCon.name) != "bool2int" or b2iCon.args.len < 2:
      continue
    let boolVar = b2iCon.args[0]
    if boolVar.kind != FznIdent or boolVar.ident notin definerOf:
      continue
    let andCon = tr.model.constraints[definerOf[boolVar.ident]]
    if stripSolverPrefix(andCon.name) != "array_bool_and" or andCon.args.len < 2:
      continue
    let andInputs = andCon.args[0]
    if andInputs.kind != FznArrayLit:
      continue

    # Determine constraint type by AND input count:
    # 2 inputs = surgeon (sel + adm==d), 3 inputs = OT (sel + adm==d + ot==o)
    let isOtConstrained = andInputs.elems.len >= 3

    # Find int_eq_reif among the AND inputs to extract the day value
    var foundDay = -1
    for inp in andInputs.elems:
      if inp.kind != FznIdent or inp.ident notin definerOf:
        continue
      let eqCon = tr.model.constraints[definerOf[inp.ident]]
      if stripSolverPrefix(eqCon.name) != "int_eq_reif" or eqCon.args.len < 3:
        continue
      # int_eq_reif(var, constant, result) — we want the constant (day value)
      if eqCon.args[1].kind == FznIntLit:
        # Verify the first arg is an admission variable (has a non-tiny domain)
        let varArg = eqCon.args[0]
        if varArg.kind == FznIdent and varArg.ident in tr.varPositions:
          let pos = tr.varPositions[varArg.ident]
          let dom = tr.sys.baseArray.domain[pos]
          if dom.len > 2:  # admission-like domain, not a boolean
            foundDay = eqCon.args[1].intVal
            break

    if foundDay >= 0:
      zeroCaps.add(CapInfo(day: foundDay, isOtConstrained: isOtConstrained))

  if zeroCaps.len == 0:
    return

  # Step 3: Determine which days to prune
  # Surgeon zero days (isOtConstrained=false) → directly prune
  # OT zero days (isOtConstrained=true) → only prune if ALL OT slots for that day are zero
  var surgeonZeroDays: PackedSet[int]
  var otZeroDayCount: Table[int, int]  # day → count of zero-capacity OT slots
  var otTotalPerDay: Table[int, int]   # day → total OT constraints for that day

  for cap in zeroCaps:
    if not cap.isOtConstrained:
      surgeonZeroDays.incl(cap.day)
    else:
      discard otZeroDayCount.mgetOrPut(cap.day, 0)
      otZeroDayCount[cap.day] += 1

  # Count total OT constraints per day from ALL int_lin_le (not just zero ones)
  for ci, con in tr.model.constraints:
    let name = stripSolverPrefix(con.name)
    if name != "int_lin_le":
      continue
    if con.args.len < 3:
      continue
    let varsArg = con.args[1]
    if varsArg.kind != FznArrayLit or varsArg.elems.len < 5:
      continue
    # Quick trace to check if this is an OT constraint
    let firstVar = varsArg.elems[0]
    if firstVar.kind != FznIdent or firstVar.ident notin definerOf:
      continue
    let b2iCon = tr.model.constraints[definerOf[firstVar.ident]]
    if stripSolverPrefix(b2iCon.name) != "bool2int" or b2iCon.args.len < 2:
      continue
    let boolVar = b2iCon.args[0]
    if boolVar.kind != FznIdent or boolVar.ident notin definerOf:
      continue
    let andCon = tr.model.constraints[definerOf[boolVar.ident]]
    if stripSolverPrefix(andCon.name) != "array_bool_and" or andCon.args.len < 2:
      continue
    let andInputs = andCon.args[0]
    if andInputs.kind != FznArrayLit or andInputs.elems.len < 3:
      continue
    # This is an OT constraint — find its day
    for inp in andInputs.elems:
      if inp.kind != FznIdent or inp.ident notin definerOf:
        continue
      let eqCon = tr.model.constraints[definerOf[inp.ident]]
      if stripSolverPrefix(eqCon.name) != "int_eq_reif" or eqCon.args.len < 3:
        continue
      if eqCon.args[1].kind == FznIntLit:
        let varArg = eqCon.args[0]
        if varArg.kind == FznIdent and varArg.ident in tr.varPositions:
          let pos = tr.varPositions[varArg.ident]
          let dom = tr.sys.baseArray.domain[pos]
          if dom.len > 2:
            let day = eqCon.args[1].intVal
            discard otTotalPerDay.mgetOrPut(day, 0)
            otTotalPerDay[day] += 1
            break

  # Days where ALL OTs have zero capacity
  var otFullyZeroDays: PackedSet[int]
  for day, zeroCount in otZeroDayCount:
    if day in otTotalPerDay and zeroCount >= otTotalPerDay[day]:
      otFullyZeroDays.incl(day)

  let pruneDays = surgeonZeroDays + otFullyZeroDays
  if pruneDays.len == 0:
    return

  # Step 4: Prune admission variable domains
  if "admission" notin tr.arrayPositions:
    return

  let admPositions = tr.arrayPositions["admission"]
  var totalPruned = 0
  for pos in admPositions:
    if pos < 0: continue  # constant placeholder
    var domain = tr.sys.baseArray.domain[pos]
    var newDomain: seq[int]
    for v in domain:
      if v notin pruneDays:
        newDomain.add(v)
    if newDomain.len < domain.len:
      totalPruned += domain.len - newDomain.len
      tr.sys.baseArray.domain[pos] = newDomain

  var dayList: seq[int]
  for d in pruneDays.items:
    dayList.add(d)
  dayList.sort()
  stderr.writeLine(&"[FZN] Zero-capacity day pruning: removed {totalPruned} values from {admPositions.len} admission vars (zero days: {dayList})")


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
  result.objectivePos = ObjPosNone
  result.objectiveLoBound = low(int)
  result.objectiveHiBound = high(int)
  result.elementChannelAliases = initTable[string, string]()
  result.equalityCopyAliases = initTable[string, string]()
  result.equalityCopyReifCIs = initPackedSet[int]()
  result.setVarBoolPositions = initTable[string, SetVarInfo]()
  result.setParamValues = initTable[string, seq[int]]()
  result.setArrayValues = initTable[string, seq[seq[int]]]()
  result.setArrayDecompositions = initTable[string, seq[SetArrayElement]]()
  result.outputSetVars = initHashSet[string]()
  result.outputSetArrays = initHashSet[string]()
  result.skipSetVarNames = initHashSet[string]()
  result.fixedOnePos = -1

  # Load parameters first (needed by collectDefinedVars for resolveIntArray)
  result.translateParameters()
  # Collect defined variables before translating variables
  result.collectDefinedVars()
  # Detect count_eq patterns before translating variables (marks intermediate vars as defined)
  result.detectCountPatterns()
  # Detect weighted same-value objective pattern (Σ coeff_k * δ(x_i == x_j) + constant)
  result.detectWeightedSameValuePattern()
  # Detect int_eq_reif/bool2int defines_var patterns → channel variables
  result.detectReifChannels()
  # Detect set_union defines_var patterns → channel variables for set decomposition
  result.detectSetUnionChannels()
  # Detect equality copy variables (vars only in defines_var constraints, aliased to original)
  result.detectEqualityCopyVars()
  # Detect case-analysis channels (bool_clause exhaustive case patterns → lookup tables)
  # Run as fixpoint: first pass channels simple targets (e.g. job_time), subsequent passes
  # channel targets that depend on earlier results (e.g. job_end depending on job_time).
  block:
    var prevCount = -1
    var iterations = 0
    while result.caseAnalysisDefs.len != prevCount and iterations < 10:
      prevCount = result.caseAnalysisDefs.len
      result.detectCaseAnalysisChannels()
      inc iterations
  # Detect implication-to-table and one-hot channel patterns
  result.detectImplicationPatterns()
  # Detect conditional gain patterns (reified value assignment → element channel)
  result.detectConditionalGainChannels()
  # Detect disjunctive pair patterns (bool_clause + int_lin_le_reif)
  result.detectDisjunctivePairs()
  # Detect disjunctive resource groups (cliques of pairs → cumulative)
  result.detectDisjunctiveResources()
  # Detect NoOverlap patterns (6-literal bool_clause → 3D box non-overlap)
  result.detectNoOverlapPatterns()
  # Detect DFA-to-geost pattern (needs paramValues for DFA data)
  result.detectDfaGeostPattern()
  # Detect conditional no-overlap pair patterns (room-conflict bool_clause chains)
  result.detectConditionalNoOverlapPairs()
  # Detect conditional cumulative patterns (room_admission elimination)
  result.detectConditionalCumulativePattern()
  # Detect conditional day capacity patterns (H3/H4 surgeon/OT capacity)
  result.detectConditionalDayCapacityPattern()
  # Detect redundant ordering constraints (transitive reduction)
  result.detectRedundantOrderings()
  result.translateVariables()
  # Mark channelVarNames positions as channelPositions (for vars like ra vars
  # that are marked as channels during detection but don't have channel bindings)
  for vn in result.channelVarNames:
    if vn in result.varPositions:
      result.sys.baseArray.channelPositions.incl(result.varPositions[vn])
  # Prune admission domains using zero-capacity day detection
  result.pruneZeroCapacityDays()
  # Build expressions for defined variables using the now-created positions
  result.buildDefinedExpressions()
  # Build expressions for element channel aliases (duplicate → original channel's position)
  for aliasName, originalName in result.elementChannelAliases:
    if originalName in result.varPositions:
      result.definedVarExprs[aliasName] = result.getExpr(result.varPositions[originalName])
    elif originalName in result.definedVarExprs:
      result.definedVarExprs[aliasName] = result.definedVarExprs[originalName]
  # Build expressions for equality copy aliases (copy → original's expression)
  for copyName, originalName in result.equalityCopyAliases:
    if originalName in result.varPositions:
      result.definedVarExprs[copyName] = result.getExpr(result.varPositions[originalName])
    elif originalName in result.definedVarExprs:
      result.definedVarExprs[copyName] = result.definedVarExprs[originalName]
  # Build set of variable names that are inputs to min/max channels.
  # Bounds on these intermediate variables are MiniZinc domain analysis artifacts,
  # not problem constraints. The min/max channel propagation maintains correct values
  # regardless of whether intermediate inputs are within their declared domains.
  var minMaxInputNames: HashSet[string]
  for def in result.minMaxChannelDefs:
    let con = result.model.constraints[def.ci]
    # Extract input array variable names
    let inputArg = con.args[1]
    case inputArg.kind
    of FznArrayLit:
      for elem in inputArg.elems:
        if elem.kind == FznIdent:
          minMaxInputNames.incl(elem.ident)
    else:
      # Named array reference — resolve through resolveVarArrayElems
      let resolved = result.resolveVarArrayElems(inputArg)
      for elem in resolved:
        if elem.kind == FznIdent:
          minMaxInputNames.incl(elem.ident)
  # Also add transitive inputs: if a min/max input is itself a defined variable
  # whose expression references other defined variables, those are also safe to skip
  if minMaxInputNames.len > 0:
    var changed = true
    while changed:
      changed = false
      for ci in result.definingConstraints.items:
        let con = result.model.constraints[ci]
        let name = stripSolverPrefix(con.name)
        if name != "int_lin_eq" or not con.hasAnnotation("defines_var"):
          continue
        let ann = con.getAnnotation("defines_var")
        if ann.args.len == 0 or ann.args[0].kind != FznIdent:
          continue
        let definedName = ann.args[0].ident
        if definedName notin minMaxInputNames:
          continue
        # This defined variable is a min/max input — add all its dependencies too
        let varElems = result.resolveVarArrayElems(con.args[1])
        for v in varElems:
          if v.kind == FznIdent and v.ident in result.definedVarNames and
             v.ident notin minMaxInputNames:
            minMaxInputNames.incl(v.ident)
            changed = true
  # Determine objective variable name — its domain bounds are deferred to optimizer
  # rather than added as hard constraints (too tight for local search to satisfy directly)
  var objectiveVarName = ""
  if result.model.solve.kind in {Minimize, Maximize}:
    if result.model.solve.objective != nil and result.model.solve.objective.kind == FznIdent:
      objectiveVarName = result.model.solve.objective.ident

  # Add domain constraints for defined variables with finite bounds,
  # but skip bounds that are naturally satisfied by the expression's range
  # or where the variable is an input to a min/max channel (bounds are MiniZinc
  # domain artifacts, not problem constraints)
  var nBoundsSkipped = 0
  var nChannelBoundsSkipped = 0
  var nObjBoundsSkipped = 0
  for varName, bounds in result.definedVarBounds:
    if varName in result.definedVarExprs:
      let expr = result.definedVarExprs[varName]
      # Skip bounds on element channel aliases (same range as original channel)
      if varName in result.elementChannelAliases:
        nBoundsSkipped += 2
        continue
      # Skip bounds on min/max channel input variables
      if varName in minMaxInputNames:
        nChannelBoundsSkipped += 2
        continue
      # Skip bounds on objective variable — defer to optimizer for two-phase solving
      if varName == objectiveVarName:
        let (lo, hi) = bounds
        result.objectiveLoBound = lo
        result.objectiveHiBound = hi
        nObjBoundsSkipped += 2
        continue
      let (lo, hi) = bounds
      let (exprMin, exprMax) = result.estimateRange(expr.node)
      if lo > low(int) and lo > exprMin:
        result.sys.addConstraint(expr >= lo)
      else:
        inc nBoundsSkipped
      if hi < high(int) and hi < exprMax:
        result.sys.addConstraint(expr <= hi)
      else:
        inc nBoundsSkipped
  # Handle objective bounds for weighted same-value objective (not in definedVarExprs)
  if result.weightedSameValueObjName != "" and result.weightedSameValueObjName in result.definedVarBounds:
    let (lo, hi) = result.definedVarBounds[result.weightedSameValueObjName]
    result.objectiveLoBound = lo
    result.objectiveHiBound = hi
    nObjBoundsSkipped += 2
  if nBoundsSkipped > 0 or nChannelBoundsSkipped > 0 or nObjBoundsSkipped > 0:
    stderr.writeLine(&"[FZN] Skipped {nBoundsSkipped + nChannelBoundsSkipped + nObjBoundsSkipped} defined-var bounds (range={nBoundsSkipped} channel={nChannelBoundsSkipped} objective={nObjBoundsSkipped})")
  if nObjBoundsSkipped > 0:
    stderr.writeLine(&"[FZN] Objective domain bounds [{result.objectiveLoBound}..{result.objectiveHiBound}] deferred to optimizer")
  # Build matrix infos for matrix_element pattern detection
  result.buildMatrixInfos()

  # Detect involution patterns (array_var_int_element groups encoding A[A[i]]=i)
  result.detectInversePatterns()

  # Detect inverse channel patterns (element(person[p], seat, p) groups)
  result.detectInverseChannelPatterns()

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

  # Add table constraints for detected implication patterns
  var nTableDomainRestrictions = 0
  for tbl in result.implicationTables:
    let condHasPos = tbl.condVar in result.varPositions
    let targetHasPos = tbl.targetVar in result.varPositions
    if condHasPos and targetHasPos:
      let condPos = result.varPositions[tbl.condVar]
      let targetPos = result.varPositions[tbl.targetVar]
      result.sys.addConstraint(tableInGacSafe[int](@[condPos, targetPos], tbl.tuples))
    elif not condHasPos and targetHasPos:
      # condVar was eliminated — check if it's a constant
      if tbl.condVar in result.definedVarExprs:
        let expr = result.definedVarExprs[tbl.condVar]
        if expr.node.kind == LiteralNode:
          let constVal = expr.node.value
          let targetPos = result.varPositions[tbl.targetVar]
          # Filter tuples to those matching the constant condVar value
          var allowed: PackedSet[int]
          for t in tbl.tuples:
            if t[0] == constVal:
              allowed.incl(t[1])
          if allowed.len > 0:
            # Restrict targetVar's domain to intersection with allowed values
            let currentDom = result.sys.baseArray.domain[targetPos]
            var newDom: seq[int]
            for v in currentDom:
              if v in allowed:
                newDom.add(v)
            if newDom.len > 0 and newDom.len < currentDom.len:
              result.sys.baseArray.setDomain(targetPos, newDom)
              inc nTableDomainRestrictions
    elif condHasPos and not targetHasPos:
      # targetVar was eliminated — check if it's a constant
      if tbl.targetVar in result.definedVarExprs:
        let expr = result.definedVarExprs[tbl.targetVar]
        if expr.node.kind == LiteralNode:
          let constVal = expr.node.value
          let condPos = result.varPositions[tbl.condVar]
          # Filter tuples to those matching the constant targetVar value
          var allowed: PackedSet[int]
          for t in tbl.tuples:
            if t[1] == constVal:
              allowed.incl(t[0])
          if allowed.len > 0:
            let currentDom = result.sys.baseArray.domain[condPos]
            var newDom: seq[int]
            for v in currentDom:
              if v in allowed:
                newDom.add(v)
            if newDom.len > 0 and newDom.len < currentDom.len:
              result.sys.baseArray.setDomain(condPos, newDom)
              inc nTableDomainRestrictions
  if nTableDomainRestrictions > 0:
    stderr.writeLine(&"[FZN] Table domain restrictions from eliminated variables: {nTableDomainRestrictions}")

  # Add disjunctive pair constraints: min(max(0, expr1), max(0, expr2)) == 0
  for pairIdx, pair in result.disjunctivePairs:
    if pairIdx in result.consumedDisjunctivePairs:
      continue
    var exprs1 = newSeq[AlgebraicExpression[int]](pair.varNames1.len)
    for i, vn in pair.varNames1:
      exprs1[i] = result.resolveExprArg(FznExpr(kind: FznIdent, ident: vn))
    var exprs2 = newSeq[AlgebraicExpression[int]](pair.varNames2.len)
    for i, vn in pair.varNames2:
      exprs2[i] = result.resolveExprArg(FznExpr(kind: FznIdent, ident: vn))
    # Build: coeffs[0]*vars[0] + coeffs[1]*vars[1] + ... - rhs
    var linExpr1 = newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: -pair.rhs1),
      linear = true)
    for i in 0..<pair.coeffs1.len:
      linExpr1 = linExpr1 + pair.coeffs1[i] * exprs1[i]
    var linExpr2 = newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: -pair.rhs2),
      linear = true)
    for i in 0..<pair.coeffs2.len:
      linExpr2 = linExpr2 + pair.coeffs2[i] * exprs2[i]
    let zero = newAlgebraicExpression[int](
      positions = initPackedSet[int](),
      node = ExpressionNode[int](kind: LiteralNode, value: 0),
      linear = true)
    let viol1 = binaryMax(zero, linExpr1)
    let viol2 = binaryMax(zero, linExpr2)
    let disjPenalty = binaryMin(viol1, viol2)
    result.sys.addConstraint(disjPenalty == 0)

    # Populate domain reduction metadata (positions instead of var names)
    block:
      var positions1: seq[int]
      var skip = false
      for vn in pair.varNames1:
        if vn in result.varPositions:
          positions1.add(result.varPositions[vn])
        else:
          skip = true
          break
      if not skip:
        var positions2: seq[int]
        for vn in pair.varNames2:
          if vn in result.varPositions:
            positions2.add(result.varPositions[vn])
          else:
            skip = true
            break
        if not skip:
          result.sys.baseArray.disjunctivePairs.add((
            coeffs1: pair.coeffs1, positions1: positions1, rhs1: pair.rhs1,
            coeffs2: pair.coeffs2, positions2: positions2, rhs2: pair.rhs2))

  if result.sys.baseArray.disjunctivePairs.len > 0:
    stderr.writeLine(&"[FZN] Disjunctive pairs for domain reduction: {result.sys.baseArray.disjunctivePairs.len}")

  # Emit cumulative constraints for detected disjunctive resource groups
  for group in result.disjunctiveResourceGroups:
    var positions: seq[int]
    var allResolved = true
    for vn in group.varNames:
      if vn in result.varPositions:
        positions.add(result.varPositions[vn])
      elif vn in result.definedVarExprs:
        # Defined var — shouldn't happen for start_time variables, but skip gracefully
        allResolved = false
        break
      else:
        allResolved = false
        break
    if not allResolved:
      continue
    let heights = newSeqWith(group.durations.len, 1)
    result.sys.addConstraint(cumulative[int](positions, group.durations, heights, 1))

  # Build NoOverlap constraints from detected patterns
  for pattern in result.noOverlapPatterns:
    var nodeA: array[3, FixedBoxEndpoint]
    var nodeB: array[3, FixedBoxEndpoint]
    var allResolved = true

    for d in 0..2:
      # Resolve endpoint A
      if pattern.nodeA[d].isFixed:
        nodeA[d] = FixedBoxEndpoint(isFixed: true, fixedValue: pattern.nodeA[d].fixedValue)
      else:
        if pattern.nodeA[d].varName notin result.varPositions:
          allResolved = false
          break
        nodeA[d] = FixedBoxEndpoint(isFixed: false, position: result.varPositions[pattern.nodeA[d].varName])

      # Resolve endpoint B
      if pattern.nodeB[d].isFixed:
        nodeB[d] = FixedBoxEndpoint(isFixed: true, fixedValue: pattern.nodeB[d].fixedValue)
      else:
        if pattern.nodeB[d].varName notin result.varPositions:
          allResolved = false
          break
        nodeB[d] = FixedBoxEndpoint(isFixed: false, position: result.varPositions[pattern.nodeB[d].varName])

    if not allResolved: continue

    result.sys.addConstraint(noOverlapFixedBox[int](
      nodeA, nodeB, pattern.radius, pattern.boxLower, pattern.boxUpper))

  if result.noOverlapPatterns.len > 0:
    stderr.writeLine(&"[FZN] Built {result.noOverlapPatterns.len} NoOverlapFixedBox constraints")

  # Build ConditionalNoOverlapPair constraints from detected patterns
  var nBuiltNoOverlap = 0
  template resolvePosName(name: string): int =
    if name == "": -1
    elif name in result.varPositions: result.varPositions[name]
    else: -1

  for info in result.conditionalNoOverlapInfos:
    let startAPos = resolvePosName(info.startAName)
    let startBPos = resolvePosName(info.startBName)
    if startAPos < 0: continue  # can't resolve

    let resourceAPos = resolvePosName(info.resourceAName)
    let resourceBPos = resolvePosName(info.resourceBName)
    let condAPos = resolvePosName(info.condAName)
    let condBPos = resolvePosName(info.condBName)

    # For occupant-patient pattern: startB is fixed (occupant at time 0),
    # durationB is the occupant's length of stay (=occupancy end time)
    # We model: occupant has start=0, dur=occEnd; patient has start=adm, dur=stay
    # But we need patient's duration. For occupant pattern, durationA was set to 0
    # because we couldn't determine it during detection. Skip these for now
    # if durationA is unknown.
    if info.durationA == 0 and startBPos < 0:
      # Occupant-patient pattern: we don't have patient duration.
      # These are simpler constraints, keep them as boolean constraints.
      # Un-consume them
      for ci in info.consumedCIs:
        result.definingConstraints.excl(ci)
      for v in info.consumedVars:
        result.definedVarNames.excl(v)
      continue

    if startBPos < 0:
      # Fixed start B (occupant) — not yet handled, skip
      for ci in info.consumedCIs:
        result.definingConstraints.excl(ci)
      for v in info.consumedVars:
        result.definedVarNames.excl(v)
      continue

    result.sys.addConstraint(conditionalNoOverlapPair[int](
      startAPos, startBPos,
      info.durationA, info.durationB,
      resourceAPos, resourceBPos,
      info.resourceAFixed, info.resourceBFixed,
      condAPos, condBPos))
    nBuiltNoOverlap += 1

  if nBuiltNoOverlap > 0:
    stderr.writeLine(&"[FZN] Built {nBuiltNoOverlap} ConditionalNoOverlapPair constraints")

  # Build ConditionalCumulative constraints from detected patterns
  for ccinfo in result.conditionalCumulativeInfos:
    var fixedTasks: seq[FixedTask]
    for ft in ccinfo.fixedTasks:
      fixedTasks.add(FixedTask(start: ft.start, duration: ft.duration, height: ft.height))

    var condTasks: seq[ConditionalTask]
    var allResolved = true
    var maxTime = 0

    for ct in ccinfo.conditionalTasks:
      let roomPos = if ct.roomVarName in result.varPositions:
        result.varPositions[ct.roomVarName] else: -1
      if roomPos < 0:
        allResolved = false
        break

      var conditions: seq[TaskCondition]
      conditions.add(TaskCondition(position: roomPos, value: ct.roomValue))

      # Add selection condition if present
      if ct.selectionVarName != "":
        let selPos = if ct.selectionVarName in result.varPositions:
          result.varPositions[ct.selectionVarName] else: -1
        if selPos < 0:
          allResolved = false
          break
        conditions.add(TaskCondition(position: selPos, value: 1))

      if ct.fixedAdmission >= 0 and ct.admissionVarName == "":
        # Fixed-admission task: conditional on room, but start time is constant
        condTasks.add(ConditionalTask(
          startPosition: -1,
          fixedStart: ct.fixedAdmission,
          duration: ct.duration,
          height: ct.height,
          conditions: conditions
        ))
        maxTime = max(maxTime, ct.fixedAdmission + ct.duration)
      else:
        let admPos = if ct.admissionVarName in result.varPositions:
          result.varPositions[ct.admissionVarName] else: -1
        if admPos < 0:
          allResolved = false
          break

        condTasks.add(ConditionalTask(
          startPosition: admPos,
          fixedStart: -1,
          duration: ct.duration,
          height: ct.height,
          conditions: conditions
        ))

        # Estimate maxTime from admission domain upper bounds + duration
        let dom = result.sys.baseArray.domain[admPos]
        if dom.len > 0:
          let maxAdm = dom[dom.len - 1]
          maxTime = max(maxTime, maxAdm + ct.duration)

    if not allResolved: continue

    # Also account for fixed tasks in maxTime
    for ft in fixedTasks:
      maxTime = max(maxTime, ft.start + ft.duration)

    result.sys.addConstraint(conditionalCumulative[int](fixedTasks, condTasks, ccinfo.limit, maxTime))

  if result.conditionalCumulativeInfos.len > 0:
    stderr.writeLine(&"[FZN] Built {result.conditionalCumulativeInfos.len} ConditionalCumulative constraints")

  # Build ConditionalDayCapacity constraints
  for cdcinfo in result.conditionalDayCapacityInfos:
    var tasks: seq[DayCapacityTask]
    var allResolved = true
    for tinfo in cdcinfo.tasks:
      let admPos = result.varPositions.getOrDefault(tinfo.admissionVarName, -1)
      var selPos = -1
      if tinfo.selectionVarName != "" and tinfo.selectionVarName != "MANDATORY":
        selPos = result.varPositions.getOrDefault(tinfo.selectionVarName, -1)
      if admPos < 0 or (selPos < 0 and tinfo.selectionVarName != "" and tinfo.selectionVarName != "MANDATORY"):
        stderr.writeLine(&"[FZN] WARNING: ConditionalDayCapacity task variable not found: adm={tinfo.admissionVarName}({admPos}) sel={tinfo.selectionVarName}({selPos})")
        allResolved = false
        break
      var extraPos = -1
      if tinfo.extraCondVarName != "":
        extraPos = result.varPositions.getOrDefault(tinfo.extraCondVarName, -1)
        if extraPos < 0:
          stderr.writeLine(&"[FZN] WARNING: ConditionalDayCapacity extra condition variable not found: {tinfo.extraCondVarName}")
          allResolved = false
          break
      tasks.add(DayCapacityTask(
        weight: tinfo.weight,
        admissionPos: admPos,
        selectionPos: selPos,
        selectionVal: 1,  # selection[p] == true (1)
        extraCondPos: extraPos,
        extraCondVal: tinfo.extraCondVal))
    if not allResolved: continue
    result.sys.addConstraint(conditionalDayCapacity[int](tasks, cdcinfo.capacities, cdcinfo.maxDay))

  if result.conditionalDayCapacityInfos.len > 0:
    stderr.writeLine(&"[FZN] Built {result.conditionalDayCapacityInfos.len} ConditionalDayCapacity constraints")

  # Detect transition table chains and apply bidirectional multi-hop reachability
  # domain reduction. MiniZinc may eliminate boundary variables (e.g., agentAtTimeT[1,a]=58
  # becomes a constant). We extract the graph from transition tables, identify the chain
  # structure from the output array, and compute forward/backward BFS to restrict all
  # timestep variables — not just the ones adjacent to boundaries.
  block:
    # Build adjacency from tables: condPos → targetPos → tuples
    var tableGraph: Table[int, Table[int, seq[seq[int]]]]
    for cons in result.sys.baseArray.constraints:
      if cons.stateType != TableConstraintType: continue
      let tbl = cons.tableConstraintState
      if tbl.mode != TableIn or tbl.sortedPositions.len != 2: continue
      if tbl.tuples.len < MinTransitionTableSize: continue  # Skip small (non-transition) tables
      let p0 = tbl.sortedPositions[0]
      let p1 = tbl.sortedPositions[1]
      if p0 notin tableGraph:
        tableGraph[p0] = initTable[int, seq[seq[int]]]()
      tableGraph[p0][p1] = tbl.tuples

    if tableGraph.len > 0:
      # Extract graph adjacency as union across ALL transition tables
      var graphAdj: Table[int, PackedSet[int]]  # node -> forward neighbors
      var reverseAdj: Table[int, PackedSet[int]]  # node -> backward neighbors
      for condPos, targets in tableGraph:
        for targetPos, tuples in targets:
          for t in tuples:
            if t[0] notin graphAdj:
              graphAdj[t[0]] = initPackedSet[int]()
            graphAdj[t[0]].incl(t[1])
            if t[1] notin reverseAdj:
              reverseAdj[t[1]] = initPackedSet[int]()
            reverseAdj[t[1]].incl(t[0])

      if graphAdj.len > 0:
        # Find chain structure from output arrays
        for arrName, arrPositions in result.arrayPositions:
          if arrPositions.len < 20: continue
          # Skip arrays with eliminated variables (position=-1 sentinel from defined var elimination)
          var hasEliminatedVars = false
          for pos in arrPositions:
            if pos < 0:
              hasEliminatedVars = true
              break
          if hasEliminatedVars: continue
          # Detect stride from initial singletons (eliminated boundary variables)
          var startSingletons = 0
          for i in 0..<arrPositions.len:
            if result.sys.baseArray.domain[arrPositions[i]].len == 1:
              inc startSingletons
            else:
              break
          if startSingletons == 0: continue
          let stride = startSingletons

          # Verify first row of variables exists
          if arrPositions.len <= stride: continue
          if result.sys.baseArray.domain[arrPositions[stride]].len <= 1: continue

          # Detect end singletons
          var endSingletons = 0
          for i in countdown(arrPositions.len - 1, 0):
            if result.sys.baseArray.domain[arrPositions[i]].len == 1:
              inc endSingletons
            else:
              break

          # Compute number of timesteps: total array / stride
          let totalSteps = arrPositions.len div stride
          if totalSteps < 3: continue
          if stride * totalSteps != arrPositions.len: continue

          # Validate this is actually a transition chain: check that consecutive
          # timestep positions for ALL agents have table constraints between them.
          # This prevents false matches on non-transition arrays that happen to have
          # leading singletons and pass the length divisibility check.
          var isChain = true
          for a in 0..<stride:
            for t in 0..<totalSteps - 1:
              let p0 = arrPositions[t * stride + a]
              let p1 = arrPositions[(t + 1) * stride + a]
              if p0 notin tableGraph or p1 notin tableGraph[p0]:
                isChain = false
                break
            if not isChain: break
          if not isChain: continue

          # Extract start and end values per agent
          var startValues: seq[int]
          var endValues: seq[int]
          var hasStart = true
          var hasEnd = (endSingletons == stride)
          for a in 0..<stride:
            let sPos = arrPositions[a]
            if result.sys.baseArray.domain[sPos].len != 1:
              hasStart = false
              break
            startValues.add(result.sys.baseArray.domain[sPos][0])
          if not hasStart: continue

          if hasEnd:
            for a in 0..<stride:
              let ePos = arrPositions[(totalSteps - 1) * stride + a]
              if result.sys.baseArray.domain[ePos].len != 1:
                hasEnd = false
                break
              endValues.add(result.sys.baseArray.domain[ePos][0])

          # Bidirectional BFS: compute reachable sets per agent per timestep
          var nChainRestrictions = 0
          for a in 0..<stride:
            # Forward BFS from start node
            var forward: seq[PackedSet[int]]
            forward.setLen(totalSteps)
            forward[0].incl(startValues[a])
            for t in 1..<totalSteps:
              for node in forward[t-1].items:
                if node in graphAdj:
                  forward[t] = forward[t] + graphAdj[node]

            # Backward BFS from end node (if known)
            var backward: seq[PackedSet[int]]
            if hasEnd:
              backward.setLen(totalSteps)
              backward[totalSteps - 1].incl(endValues[a])
              for t in countdown(totalSteps - 2, 0):
                for node in backward[t+1].items:
                  if node in reverseAdj:
                    backward[t] = backward[t] + reverseAdj[node]

            # Restrict domains at each non-boundary timestep
            for t in 1..<totalSteps - (if hasEnd: 1 else: 0):
              let pos = arrPositions[t * stride + a]
              let currentDom = result.sys.baseArray.domain[pos]
              if currentDom.len <= 1: continue

              # Intersect with forward reachability
              var reachable = forward[t]
              # Intersect with backward reachability if available
              if hasEnd and backward[t].len > 0:
                reachable = reachable * backward[t]

              if reachable.len == 0: continue  # Safety: don't empty a domain

              var newDom: seq[int]
              for v in currentDom:
                if v in reachable:
                  newDom.add(v)
              if newDom.len > 0 and newDom.len < currentDom.len:
                result.sys.baseArray.setDomain(pos, newDom)
                inc nChainRestrictions

          if nChainRestrictions > 0:
            stderr.writeLine(&"[FZN] Bidirectional reachability restrictions: {nChainRestrictions} positions ({stride} agents, {totalSteps} timesteps)")

  # Add geost constraint if conversion is active
  if result.geostConversion.tileValues.len > 0:
    result.sys.addConstraint(geost[int](
      result.geostConversion.tileVarPositions,
      result.geostConversion.allPlacements
    ))

  # Build channel bindings for element defines_var
  result.buildChannelBindings()
  # Build channel bindings for synthetic element channels (conditional gain variables)
  result.buildSyntheticElementChannelBindings()
  # Build channel bindings for int_eq_reif/bool2int reification channels
  result.buildReifChannelBindings()
  # Build channel bindings for array_bool_and/or with defines_var
  result.buildBoolLogicChannelBindings()
  # Build channel bindings for one-hot indicator variables
  result.buildOneHotChannelBindings()
  # Build channel bindings for array_int_minimum/maximum defines_var
  result.buildMinMaxChannelBindings()
  # Build channel bindings for set_union defines_var (max of boolean pairs)
  result.buildSetUnionChannelBindings()
  # Build channel bindings for case-analysis channels (constant lookup tables)
  result.buildCaseAnalysisChannelBindings()
  # Build inverse channel groups (inverse relationship: seat[person[p]] = p)
  result.buildInverseChannelBindings()

  result.translateSolve()

  # Build WeightedSameValueExpression if pattern was detected
  if result.weightedSameValueObjName != "":
    var wsvPairs: seq[WeightedSameValuePair[int]]
    for pair in result.weightedSameValuePairs:
      let posA = result.varPositions[pair.varNameA]
      let posB = result.varPositions[pair.varNameB]
      wsvPairs.add((posA: posA, posB: posB, coeff: pair.coeff))
    result.weightedSameValueExpr = newWeightedSameValueExpression[int](
      wsvPairs, result.weightedSameValueConstant)
