## Test: validate that the defined expression for "objective" in community-detection
## matches the direct computation from the int_lin_eq coefficients.

import std/[os, strutils, strformat, tables, packedsets]
import crusher
import flatzinc/[parser, translator, output]

proc main() =
  let filename = "/tmp/community_dolphin.fzn"
  if not fileExists(filename):
    echo "Need /tmp/community_dolphin.fzn"
    quit(1)

  echo "Parsing..."
  let model = parseFznFile(filename)
  echo &"Parsed: {model.variables.len} variables, {model.constraints.len} constraints"

  echo "Translating..."
  var tr = translate(model)
  let nPos = tr.sys.baseArray.len
  echo &"System has {nPos} positions"

  # Create assignment with first domain value for each position
  var assignment = newSeq[int](nPos)
  for pos in 0..<nPos:
    if pos < tr.sys.baseArray.domain.len and tr.sys.baseArray.domain[pos].len > 0:
      assignment[pos] = tr.sys.baseArray.domain[pos][0]

  # Set x variables to the user's reported solution
  let userX = @[1, 3, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 1, 1]
  echo &"Setting x array ({userX.len} elements)..."

  if "x" in tr.arrayPositions:
    let xPositions = tr.arrayPositions["x"]
    var setCount = 0
    var defVarCount = 0
    for i, pos in xPositions:
      if pos >= 0 and i < userX.len:
        assignment[pos] = userX[i]
        inc setCount
      elif pos == -1:
        inc defVarCount
    echo &"Set {setCount} x positions, {defVarCount} are defined vars (out of {xPositions.len})"

    # Show which x elements are defined vars and what their FZN variable names are
    if "x" in tr.arrayElementNames:
      let elemNames = tr.arrayElementNames["x"]
      echo "Defined var x elements:"
      for i, pos in xPositions:
        if pos == -1 and i < elemNames.len:
          let eName = elemNames[i]
          let inDefExprs = eName in tr.definedVarExprs
          var exprInfo = ""
          if inDefExprs:
            let expr = tr.definedVarExprs[eName]
            exprInfo = &" expr.positions.len={expr.positions.len}"
            if expr.node.kind == RefNode:
              exprInfo &= &" RefNode(pos={expr.node.position})"
            elif expr.node.kind == BinaryOpNode:
              exprInfo &= &" BinaryOp({expr.node.binaryOp})"
            elif expr.node.kind == LiteralNode:
              exprInfo &= &" Literal({expr.node.value})"
          echo &"  x[{i+1}] = {eName}: inDefinedVarExprs={inDefExprs}{exprInfo}, expected={userX[i]}"
    else:
      echo "No arrayElementNames for x"
  else:
    echo "ERROR: No x array found!"
    quit(1)

  tr.sys.assignment = assignment

  # Propagate channels - do multiple passes until stable
  echo "Propagating channels..."
  var changed = true
  var passes = 0
  while changed and passes < 10:
    changed = false
    inc passes
    # Element channels
    for i, binding in tr.sys.baseArray.channelBindings:
      let idxVal = binding.indexExpression.evaluate(tr.sys.assignment)
      if idxVal >= 0 and idxVal < binding.arrayElements.len:
        let elem = binding.arrayElements[idxVal]
        let newVal = if elem.isConstant: elem.constantValue
                     else: tr.sys.assignment[elem.variablePosition]
        if tr.sys.assignment[binding.channelPosition] != newVal:
          tr.sys.assignment[binding.channelPosition] = newVal
          changed = true

    # Min/max channels
    for binding in tr.sys.baseArray.minMaxChannelBindings:
      var bestVal = if binding.isMin: high(int) else: low(int)
      for expr in binding.inputExprs:
        let v = expr.evaluate(tr.sys.assignment)
        if binding.isMin:
          bestVal = min(bestVal, v)
        else:
          bestVal = max(bestVal, v)
      if tr.sys.assignment[binding.channelPosition] != bestVal:
        tr.sys.assignment[binding.channelPosition] = bestVal
        changed = true

  echo &"Channel propagation converged after {passes} passes"

  echo ""
  echo "=== EXPRESSION VALIDATION ==="

  if not tr.definedVarExprs.hasKey("objective"):
    echo "ERROR: No defined expression for 'objective'"
    quit(1)

  let objExpr = tr.definedVarExprs["objective"]
  let objVal = objExpr.evaluate(tr.sys.assignment)
  echo &"Expression evaluates to: {objVal}"

  # Find the int_lin_eq that defines "objective"
  for ci, con in model.constraints:
    if con.name == "int_lin_eq" and con.hasAnnotation("defines_var"):
      let ann = con.getAnnotation("defines_var")
      if ann.args.len > 0 and ann.args[0].kind == FznIdent and ann.args[0].ident == "objective":
        let coeffs = tr.resolveIntArray(con.args[0])
        let rhs = tr.resolveIntArg(con.args[2])
        let varElems = tr.resolveVarArrayElems(con.args[1])

        # Find objective index
        var definedIdx = -1
        for vi, v in varElems:
          if v.kind == FznIdent and v.ident == "objective":
            definedIdx = vi
            break

        # Compute direct sum of indicator terms
        var directOtherSum: int64 = 0
        var termCount = 0
        var oneCount = 0
        var zeroCount = 0
        for vi, v in varElems:
          if vi == definedIdx: continue
          var val: int
          if v.kind == FznIdent:
            if v.ident in tr.varPositions:
              val = tr.sys.assignment[tr.varPositions[v.ident]]
            elif v.ident in tr.definedVarExprs:
              val = tr.definedVarExprs[v.ident].evaluate(tr.sys.assignment)
            elif v.ident in tr.paramValues:
              val = tr.paramValues[v.ident]
            else:
              echo &"  UNKNOWN: {v.ident}"
              continue
          elif v.kind == FznIntLit:
            val = v.intVal
          elif v.kind == FznBoolLit:
            val = if v.boolVal: 1 else: 0
          else:
            continue
          directOtherSum += int64(coeffs[vi]) * int64(val)
          inc termCount
          if val == 1: inc oneCount
          elif val == 0: inc zeroCount

        let defCoeff = coeffs[definedIdx]
        let expectedObj = (int64(rhs) - directOtherSum) div int64(defCoeff)
        echo &"\nint_lin_eq: {varElems.len} vars, rhs={rhs}, defCoeff={defCoeff}"
        echo &"Indicators: {oneCount} ones, {zeroCount} zeros, {termCount} total"
        echo &"Direct other sum = {directOtherSum}"
        echo &"Expected objective from FZN = {expectedObj}"
        echo &"Expression evaluates to: {objVal}"
        echo &"MZN formula gives: 138079"

        if expectedObj != int64(objVal):
          echo &"EXPRESSION MISMATCH: expected={expectedObj} got={objVal}"

        # Now trace each indicator to its source x variables
        # For each indicator, find the bool2int + int_eq_reif chain
        echo "\n=== INDICATOR TRACING ==="

        # Build maps: variable name -> defining constraint
        var defConstraintMap: Table[string, int]  # varName -> constraint index
        for ci2, con2 in model.constraints:
          if con2.hasAnnotation("defines_var"):
            let ann2 = con2.getAnnotation("defines_var")
            if ann2.args.len > 0 and ann2.args[0].kind == FznIdent:
              defConstraintMap[ann2.args[0].ident] = ci2

        var mismatches = 0
        for vi, v in varElems:
          if vi == definedIdx: continue
          if v.kind != FznIdent: continue

          # Get indicator value
          var indicVal: int
          if v.ident in tr.varPositions:
            indicVal = tr.sys.assignment[tr.varPositions[v.ident]]
          elif v.ident in tr.definedVarExprs:
            indicVal = tr.definedVarExprs[v.ident].evaluate(tr.sys.assignment)
          else:
            continue

          # Trace: indicator_var is defined by a bool2int constraint
          # bool2int(bool_var, int_var) :: defines_var(int_var)
          # which means int_var = bool_var
          # The bool_var is defined by int_eq_reif(x_a, x_b, bool_var) or similar
          # BUT with our channel handling, the indicator might be a channel var

          # Find the bool2int that defines this indicator
          if v.ident in defConstraintMap:
            let b2iCI = defConstraintMap[v.ident]
            let b2iCon = model.constraints[b2iCI]
            if b2iCon.name == "bool2int":
              # Get the boolean variable
              let boolArg = b2iCon.args[0]
              if boolArg.kind == FznIdent and boolArg.ident in defConstraintMap:
                let eqReifCI = defConstraintMap[boolArg.ident]
                let eqReifCon = model.constraints[eqReifCI]
                if eqReifCon.name == "int_eq_reif":
                  # int_eq_reif(x_a, x_b, bool_var)
                  let xAarg = eqReifCon.args[0]
                  let xBarg = eqReifCon.args[1]

                  # Get x_a and x_b values
                  var xAval, xBval: int
                  var xAname, xBname: string
                  if xAarg.kind == FznIdent:
                    xAname = xAarg.ident
                    if xAarg.ident in tr.varPositions:
                      xAval = tr.sys.assignment[tr.varPositions[xAarg.ident]]
                    elif xAarg.ident in tr.definedVarExprs:
                      xAval = tr.definedVarExprs[xAarg.ident].evaluate(tr.sys.assignment)
                    elif xAarg.ident in tr.paramValues:
                      xAval = tr.paramValues[xAarg.ident]
                  elif xAarg.kind == FznIntLit:
                    xAval = xAarg.intVal
                    xAname = $xAval

                  if xBarg.kind == FznIdent:
                    xBname = xBarg.ident
                    if xBarg.ident in tr.varPositions:
                      xBval = tr.sys.assignment[tr.varPositions[xBarg.ident]]
                    elif xBarg.ident in tr.definedVarExprs:
                      xBval = tr.definedVarExprs[xBarg.ident].evaluate(tr.sys.assignment)
                    elif xBarg.ident in tr.paramValues:
                      xBval = tr.paramValues[xBarg.ident]
                  elif xBarg.kind == FznIntLit:
                    xBval = xBarg.intVal
                    xBname = $xBval

                  let expectedIndic = if xAval == xBval: 1 else: 0
                  if indicVal != expectedIndic:
                    inc mismatches
                    if mismatches <= 20:
                      echo &"  MISMATCH vi={vi}: {v.ident} = {indicVal}, but {xAname}={xAval}, {xBname}={xBval}, expected={expectedIndic}, coeff={coeffs[vi]}"

        echo &"\nTotal indicator mismatches: {mismatches}"
        break

main()
