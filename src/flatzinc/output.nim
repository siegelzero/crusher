## FlatZinc output formatter - prints solutions in standard FlatZinc output format.
## MiniZinc's solns2out tool reads this output and applies the model's output format.

import std/[strutils, strformat, tables, sets]

import translator
import ../expressions/expressions

proc formatBool(val: int): string {.inline.} =
  if val != 0: "true" else: "false"

proc formatSolution*(tr: FznTranslator): string =
  ## Formats the current solution in FlatZinc output format.
  ## Prints output_var and output_array annotated variables.
  var lines: seq[string]

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
