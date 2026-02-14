## fzcrusher - FlatZinc solver CLI entry point.
## Reads a .fzn file, translates to a Crusher ConstraintSystem, solves, and prints output.
##
## Usage: fzcrusher [options] <file.fzn>
##   -a            all solutions (not yet implemented; prints first)
##   -p <N>        number of parallel workers (0 = auto)
##   -v            verbose output
##   -s            print statistics
##   -t <N>        tabu threshold (default 10000)
##   -f            fast mode (lower tabu threshold)

import std/[os, strutils, strformat, times, posix]

import crusher
import flatzinc/[parser, translator, output]

proc redirectStdoutToStderr() =
  ## Redirect stdout to stderr so solver internal output doesn't corrupt FZN output.
  discard dup2(stderr.getFileHandle(), stdout.getFileHandle())

proc restoreStdout(savedFd: cint) =
  ## Restore stdout from saved file descriptor.
  discard dup2(savedFd, stdout.getFileHandle())
  discard close(savedFd)

proc main() =
  var filename = ""
  var parallel = true
  var verbose = false
  var stats = false
  var tabuThreshold = 10000
  var numWorkers = 0
  var allSolutions = false

  # Parse command line arguments
  var i = 1
  while i <= paramCount():
    let arg = paramStr(i)
    case arg
    of "-a":
      allSolutions = true
    of "-p":
      inc i
      if i <= paramCount():
        numWorkers = parseInt(paramStr(i))
    of "-v":
      verbose = true
    of "-s":
      stats = true
    of "-t":
      inc i
      if i <= paramCount():
        tabuThreshold = parseInt(paramStr(i))
    of "-f":
      tabuThreshold = 1000
    else:
      if arg.startsWith("-"):
        stderr.writeLine(&"Unknown option: {arg}")
      else:
        filename = arg
    inc i

  if filename == "":
    stderr.writeLine("Usage: fzcrusher [options] <file.fzn>")
    stderr.writeLine("Options:")
    stderr.writeLine("  -a          all solutions")
    stderr.writeLine("  -p <N>      parallel workers (0=auto)")
    stderr.writeLine("  -v          verbose")
    stderr.writeLine("  -s          statistics")
    stderr.writeLine("  -t <N>      tabu threshold (default 10000)")
    stderr.writeLine("  -f          fast mode")
    quit(1)

  if not fileExists(filename):
    stderr.writeLine(&"Error: file not found: {filename}")
    quit(1)

  let startTime = cpuTime()

  # Parse the FlatZinc file
  if verbose:
    stderr.writeLine(&"[FZN] Parsing {filename}...")
  let model = parseFznFile(filename)
  if verbose:
    stderr.writeLine(&"[FZN] Parsed: {model.variables.len} variables, {model.parameters.len} parameters, {model.constraints.len} constraints")

  # Translate to ConstraintSystem
  if verbose:
    stderr.writeLine("[FZN] Translating...")
  var tr = translate(model)
  if verbose:
    stderr.writeLine(&"[FZN] System has {tr.sys.baseArray.len} positions, {tr.sys.baseArray.constraints.len} constraints")

  # Redirect stdout to stderr during solving (solver echo goes to stderr)
  let savedFd = dup(stdout.getFileHandle())
  redirectStdoutToStderr()

  # Solve
  let solveStart = cpuTime()
  var solved = false
  case model.solve.kind
  of Satisfy:
    try:
      tr.sys.resolve(
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = numWorkers,
        verbose = verbose
      )
      solved = true
    except NoSolutionFoundError:
      discard

  of Minimize:
    try:
      let objExpr = tr.getExpr(tr.objectivePos)
      minimize(tr.sys, objExpr,
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = numWorkers,
        verbose = verbose
      )
      solved = true
    except NoSolutionFoundError:
      discard

  of Maximize:
    try:
      let objExpr = tr.getExpr(tr.objectivePos)
      maximize(tr.sys, objExpr,
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = numWorkers,
        verbose = verbose
      )
      solved = true
    except NoSolutionFoundError:
      discard

  # Restore stdout for solution output
  flushFile(stdout)
  restoreStdout(savedFd)

  if solved:
    tr.printSolution()
    printComplete()
  else:
    printUnsatisfiable()

  if stats:
    let totalTime = cpuTime() - startTime
    let solveTime = cpuTime() - solveStart
    stderr.writeLine(&"%%%mzn-stat: solveTime={solveTime:.3f}")
    stderr.writeLine(&"%%%mzn-stat: initTime={solveStart - startTime:.3f}")
    stderr.writeLine(&"%%%mzn-stat: nodes={tr.sys.lastIterations}")
    stderr.writeLine("%%%mzn-stat-end")

main()
