## fzcrusher - FlatZinc solver CLI entry point.
## Reads a .fzn file, translates to a Crusher ConstraintSystem, solves, and prints output.
##
## Usage: fzcrusher [options] <file.fzn>
##   -a            all solutions (not yet implemented; prints first)
##   -p <N>        number of parallel workers (0 = auto)
##   -v            verbose output
##   -s            print statistics
##   -t <ms>       time limit in milliseconds (MiniZinc standard flag)
##   --time-limit <ms>  alias for -t
##   --tabu <N>    tabu threshold (default 10000)
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
  var timeLimitMs = 0

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
    of "-t", "--time-limit":
      inc i
      if i <= paramCount():
        timeLimitMs = parseInt(paramStr(i))
    of "--tabu":
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
    stderr.writeLine("  -a              all solutions")
    stderr.writeLine("  -p <N>          parallel workers (0=auto)")
    stderr.writeLine("  -v              verbose")
    stderr.writeLine("  -s              statistics")
    stderr.writeLine("  -t <ms>         time limit in milliseconds")
    stderr.writeLine("  --time-limit <ms>  alias for -t")
    stderr.writeLine("  --tabu <N>      tabu threshold (default 10000)")
    stderr.writeLine("  -f              fast mode")
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

  # Compute deadline from time limit
  let deadline = if timeLimitMs > 0: epochTime() + timeLimitMs.float / 1000.0 else: 0.0

  # Redirect stdout to stderr during solving (solver echo goes to stderr)
  let savedFd = dup(stdout.getFileHandle())
  redirectStdoutToStderr()

  # Solve
  let solveStart = cpuTime()
  var solved = false
  var timedOut = false
  case model.solve.kind
  of Satisfy:
    try:
      tr.sys.resolve(
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = numWorkers,
        verbose = verbose,
        deadline = deadline
      )
      solved = true
    except TimeLimitExceededError:
      timedOut = true
    except NoSolutionFoundError:
      discard

  of Minimize:
    try:
      let objExpr = if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
                    else: tr.objectiveDefExpr
      minimize(tr.sys, objExpr,
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = numWorkers,
        verbose = verbose,
        deadline = deadline
      )
      solved = true
    except TimeLimitExceededError:
      timedOut = true
    except NoSolutionFoundError:
      discard

  of Maximize:
    try:
      let objExpr = if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
                    else: tr.objectiveDefExpr
      maximize(tr.sys, objExpr,
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = numWorkers,
        verbose = verbose,
        deadline = deadline
      )
      solved = true
    except TimeLimitExceededError:
      timedOut = true
    except NoSolutionFoundError:
      discard

  # Restore stdout for solution output
  flushFile(stdout)
  restoreStdout(savedFd)

  if solved:
    # Reconstruct board values from tile placements if geost conversion was used
    let gc = tr.geostConversion
    if gc.tileValues.len > 0:
      # Set sentinel positions
      for idx in gc.sentinelBoardIndices:
        tr.sys.assignment[gc.boardPositions[idx]] = gc.sentinelValue
      # Set tile placements
      for t in 0..<gc.tileValues.len:
        let placementIdx = tr.sys.assignment[gc.tileVarPositions[t]]
        for cellIdx in gc.allPlacements[t][placementIdx]:
          tr.sys.assignment[gc.boardPositions[cellIdx]] = gc.tileValues[t]

    tr.printSolution()
    if tr.sys.searchCompleted:
      printComplete()
  elif timedOut:
    printUnknown()
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
