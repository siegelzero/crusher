## FlatZinc output formatter - prints solutions in standard FlatZinc output format.
## MiniZinc's solns2out tool reads this output and applies the model's output format.

import std/[strutils, strformat, tables]

import translator

proc formatSolution*(tr: FznTranslator): string =
  ## Formats the current solution in FlatZinc output format.
  ## Prints output_var and output_array annotated variables.
  var lines: seq[string]

  # Output single variables
  for name in tr.outputVars:
    if name in tr.varPositions:
      let pos = tr.varPositions[name]
      let val = tr.sys.assignment[pos]
      lines.add(&"{name} = {val};")

  # Output arrays
  for arr in tr.outputArrays:
    if arr.name in tr.arrayPositions:
      let positions = tr.arrayPositions[arr.name]
      var vals = newSeq[string](positions.len)
      for i, pos in positions:
        vals[i] = $tr.sys.assignment[pos]
      lines.add(&"{arr.name} = array1d({arr.lo}..{arr.hi}, [{vals.join(\", \")}]);")
    elif arr.name in tr.arrayValues:
      # Constant array
      let vals = tr.arrayValues[arr.name]
      var strs = newSeq[string](vals.len)
      for i, v in vals:
        strs[i] = $v
      lines.add(&"{arr.name} = array1d({arr.lo}..{arr.hi}, [{strs.join(\", \")}]);")

  result = lines.join("\n")

proc printSolution*(tr: FznTranslator) =
  ## Prints one solution followed by the separator.
  echo tr.formatSolution()
  echo "----------"

proc printUnsatisfiable*() =
  echo "=====UNSATISFIABLE====="

proc printComplete*() =
  ## Printed after all solutions (or after optimization completes).
  echo "=========="
