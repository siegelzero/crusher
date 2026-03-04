## FlatZinc output formatter - prints solutions in standard FlatZinc output format.
## MiniZinc's solns2out tool reads this output and applies the model's output format.

import std/[strutils, strformat, tables, sets, algorithm, sequtils]

import parser
import translator
import ../expressions/expressions

proc formatBool(val: int): string {.inline.} =
  if val != 0: "true" else: "false"

proc formatSet(values: seq[int]): string =
  ## Formats a set of integers as a FlatZinc set literal.
  if values.len == 0: return "{}"
  var sorted = values.sorted()
  "{" & sorted.mapIt($it).join(", ") & "}"

proc reconstructSet(tr: FznTranslator, info: SetVarInfo): seq[int] =
  ## Reconstructs set membership from boolean variable assignments.
  for idx in 0..<info.positions.len:
    if tr.sys.assignment[info.positions[idx]] != 0:
      result.add(info.lo + idx)

proc formatSolution*(tr: FznTranslator): string =
  ## Formats the current solution in FlatZinc output format.
  ## Prints output_var and output_array annotated variables.
  var lines: seq[string]

  # Output single set variables
  for name in tr.outputSetVars:
    if name in tr.setVarBoolPositions:
      let info = tr.setVarBoolPositions[name]
      let values = tr.reconstructSet(info)
      lines.add(&"{name} = {formatSet(values)};")

  # Output single variables
  for name in tr.outputVars:
    let isBool = name in tr.outputBoolVars
    if name in tr.definedVarExprs:
      let expr = tr.definedVarExprs[name]
      let val = expr.evaluate(tr.sys.assignment)
      if isBool:
        lines.add(&"{name} = {formatBool(val)};")
      else:
        lines.add(&"{name} = {val};")
    elif name in tr.varPositions:
      let pos = tr.varPositions[name]
      let val = tr.sys.assignment[pos]
      if isBool:
        lines.add(&"{name} = {formatBool(val)};")
      else:
        lines.add(&"{name} = {val};")

  # Output set arrays
  for name in tr.outputSetArrays:
    if name in tr.setArrayDecompositions:
      let elems = tr.setArrayDecompositions[name]
      var vals = newSeq[string](elems.len)
      for i, elem in elems:
        if elem.isConstant:
          vals[i] = formatSet(elem.constantValues)
        elif elem.varName in tr.setVarBoolPositions:
          let info = tr.setVarBoolPositions[elem.varName]
          vals[i] = formatSet(tr.reconstructSet(info))
        else:
          vals[i] = "{}"
      # Find output_array annotation for index range
      var lo = 1
      var hi = elems.len
      for decl in tr.model.variables:
        if decl.isArray and decl.name == name and decl.hasAnnotation("output_array"):
          let ann = decl.getAnnotation("output_array")
          if ann.args.len > 0 and ann.args[0].kind == FznArrayLit:
            let indexRanges = ann.args[0]
            if indexRanges.elems.len > 0 and indexRanges.elems[0].kind == FznRange:
              lo = indexRanges.elems[0].lo
              hi = indexRanges.elems[0].hi
          break
      lines.add(&"{name} = array1d({lo}..{hi}, [{vals.join(\", \")}]);")

  # Output arrays
  for arr in tr.outputArrays:
    let isBoolArr = arr.name in tr.outputBoolArrays
    if arr.name in tr.arrayPositions:
      let positions = tr.arrayPositions[arr.name]
      var vals = newSeq[string](positions.len)
      for i, pos in positions:
        if pos == -1:
          # Defined variable - evaluate expression
          if arr.name in tr.arrayElementNames:
            let elemName = tr.arrayElementNames[arr.name][i]
            if elemName in tr.definedVarExprs:
              let v = tr.definedVarExprs[elemName].evaluate(tr.sys.assignment)
              vals[i] = if isBoolArr: formatBool(v) else: $v
              continue
          vals[i] = if isBoolArr: "false" else: "0"  # fallback
        else:
          let v = tr.sys.assignment[pos]
          vals[i] = if isBoolArr: formatBool(v) else: $v
      lines.add(&"{arr.name} = array1d({arr.lo}..{arr.hi}, [{vals.join(\", \")}]);")
    elif arr.name in tr.arrayValues:
      # Constant array
      let vals = tr.arrayValues[arr.name]
      var strs = newSeq[string](vals.len)
      for i, v in vals:
        strs[i] = if isBoolArr: formatBool(v) else: $v
      lines.add(&"{arr.name} = array1d({arr.lo}..{arr.hi}, [{strs.join(\", \")}]);")

  result = lines.join("\n")

proc printSolution*(tr: FznTranslator) =
  ## Prints one solution followed by the separator.
  echo tr.formatSolution()
  echo "----------"

proc printUnsatisfiable*() =
  echo "=====UNSATISFIABLE====="

proc printUnknown*() =
  echo "=====UNKNOWN====="

proc printComplete*() =
  ## Printed after all solutions (or after optimization completes).
  echo "=========="
