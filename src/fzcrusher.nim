## fzcrusher - FlatZinc solver CLI entry point.
## Reads a .fzn file, translates to a Crusher ConstraintSystem, solves, and prints output.
##
## Usage: fzcrusher [options] <file.fzn>
##   -a            all solutions (not yet implemented; prints first)
##   -f            free search (Crusher ignores search annotations; accepted as a no-op)
##   -i            print intermediate (improving) solutions during optimization
##   -p <N>        number of parallel workers (0 = auto)
##   -v            verbose output
##   -s            print statistics
##   -t <ms>       time limit in milliseconds (MiniZinc standard flag)
##   --time-limit <ms>  alias for -t
##   --tabu <N>    tabu threshold (default 10000)

import std/[os, strutils, strformat, times, posix]

import crusher
import flatzinc/[parser, translator, output]
import expressions/[weightedSameValue, binaryPairwiseSum]

proc immediateExit(status: cint) {.importc: "_exit", header: "<unistd.h>", noReturn.}

# Global state for SIGTERM handler — allows graceful output on MiniZinc kill
var gSavedFd: cint = -1
var gTranslator: ptr FznTranslator = nil
var gHasSolution: ptr bool = nil

proc sigTermHandler(sig: cint) {.noconv.} =
  flushFile(stdout)
  if gSavedFd >= 0:
    discard dup2(gSavedFd, stdout.getFileHandle())
  if gTranslator != nil and gHasSolution != nil and gHasSolution[]:
    if gTranslator[].sys.bestAssignmentValid and
       gTranslator[].sys.bestFeasibleAssignment.len > 0:
      gTranslator[].sys.assignment = gTranslator[].sys.bestFeasibleAssignment
    gTranslator[].printSolution()
  else:
    printUnknown()
  flushFile(stdout)
  flushFile(stderr)
  immediateExit(0)

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
  var streamSolutions = false
  var timeLimitMs = 0

  # Parse command line arguments
  var i = 1
  while i <= paramCount():
    let arg = paramStr(i)
    case arg
    of "-a":
      allSolutions = true
    of "-f":
      # Free search: Crusher is a local-search solver and ignores the model's
      # search annotations, so free search is its native mode. Accept as a no-op.
      discard
    of "-i":
      streamSolutions = true
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
    stderr.writeLine("  -f              free search (no-op; Crusher ignores search annotations)")
    stderr.writeLine("  -i              print intermediate solutions during optimization")
    stderr.writeLine("  -p <N>          parallel workers (0=auto)")
    stderr.writeLine("  -v              verbose")
    stderr.writeLine("  -s              statistics")
    stderr.writeLine("  -t <ms>         time limit in milliseconds")
    stderr.writeLine("  --time-limit <ms>  alias for -t")
    stderr.writeLine("  --tabu <N>      tabu threshold (default 10000)")
    quit(1)

  if not fileExists(filename):
    stderr.writeLine(&"Error: file not found: {filename}")
    quit(1)

  let startTime = cpuTime()
  let wallStart = epochTime()

  # Parse and translate. Any failure here (e.g. an unsupported FlatZinc
  # construct such as a float literal) must degrade to UNKNOWN rather than
  # crash with a stack trace — every challenge instance must yield valid output.
  var model: FznModel
  var tr: FznTranslator
  try:
    if verbose:
      stderr.writeLine(&"[FZN] Parsing {filename}...")
    model = parseFznFile(filename)
    if verbose:
      stderr.writeLine(&"[FZN] Parsed: {model.variables.len} variables, {model.parameters.len} parameters, {model.constraints.len} constraints")

    # Translate to ConstraintSystem
    if verbose:
      stderr.writeLine("[FZN] Translating...")
    tr = translate(model)
    if verbose:
      stderr.writeLine(&"[FZN] System has {tr.sys.baseArray.len} positions, {tr.sys.baseArray.constraints.len} constraints")
  except CatchableError as e:
    stderr.writeLine(&"[FZN] Parse/translate failed: {e.msg}")
    printUnknown()
    flushFile(stdout)
    immediateExit(0)

  # If translation dropped any constraint Crusher cannot enforce natively, a
  # found assignment may violate the model. Report UNKNOWN instead of emitting
  # an invalid solution.
  if tr.unsupportedConstraints.len > 0:
    stderr.writeLine(&"[FZN] {tr.unsupportedConstraints.len} unsupported constraint(s) " &
      "could not be enforced; reporting UNKNOWN: " & tr.unsupportedConstraints.join(", "))
    printUnknown()
    flushFile(stdout)
    immediateExit(0)

  # MiniZinc's --time-limit includes its own compilation time (before we start).
  # Anchor to process start and subtract a small margin. If our deadline doesn't
  # fire in time, the SIGTERM handler will output the best solution.
  let deadline = if timeLimitMs > 0: wallStart + timeLimitMs.float / 1000.0 - 2.0 else: 0.0

  # Redirect stdout to stderr during solving (solver echo goes to stderr)
  let savedFd = dup(stdout.getFileHandle())
  redirectStdoutToStderr()

  # Install signal handlers for graceful shutdown (output best solution found so far)
  gSavedFd = savedFd
  gTranslator = addr tr
  gHasSolution = addr tr.sys.hasFeasibleSolution
  signal(SIGTERM, sigTermHandler)
  signal(SIGINT, sigTermHandler)
  signal(SIGPIPE, SIG_IGN)  # Ignore broken pipe (MiniZinc may close stdout early)

  # Intermediate-solution streaming (`-i`). During solving, stdout is redirected to
  # stderr, so we write each improving solution directly to the *real* stdout (savedFd)
  # via a raw write — no buffering, no interference with the redirected solver output.
  # Streaming is disabled for geost-converted models because their board values are only
  # reconstructed in the final output path (formatSolution alone would be incomplete);
  # the final print / SIGTERM handler still emits a correct solution for those.
  let canStream = streamSolutions and tr.geostConversion.tileValues.len == 0
  var lastStreamedAssignment: seq[int] = @[]
  proc streamSolution(assignment: seq[int]) =
    tr.sys.assignment = assignment
    let s = tr.formatSolution() & "\n----------\n"
    if savedFd >= 0 and s.len > 0:
      discard posix.write(savedFd, cast[pointer](s.cstring), s.len)
      lastStreamedAssignment = assignment
  let onSol: proc(assignment: seq[int]) {.closure.} =
    if canStream: streamSolution else: nil

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
      tr.sys.hasFeasibleSolution = true
    except TimeLimitExceededError:
      timedOut = true
    except NoSolutionFoundError:
      discard

  of Minimize:
    try:
      if tr.objectivePos == ObjPosWeightedSV:
        minimize(tr.sys, tr.weightedSameValueExpr,
          parallel = parallel,
          tabuThreshold = tabuThreshold,
          numWorkers = numWorkers,
          verbose = verbose,
          deadline = deadline,
          lowerBound = tr.objectiveLoBound,
          upperBound = tr.objectiveHiBound,
          onSolution = onSol
        )
      elif tr.objectivePos == ObjPosBinaryPairwiseSum:
        minimize(tr.sys, tr.binaryPairwiseSumExpr,
          parallel = parallel,
          tabuThreshold = tabuThreshold,
          numWorkers = numWorkers,
          verbose = verbose,
          deadline = deadline,
          lowerBound = tr.objectiveLoBound,
          upperBound = tr.objectiveHiBound,
          onSolution = onSol
        )
      else:
        let objExpr = if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
                      elif tr.objectivePos == ObjPosDefinedExpr: tr.objectiveDefExpr
                      else: raise newException(ValueError, "No objective expression for minimize")
        minimize(tr.sys, objExpr,
          parallel = parallel,
          tabuThreshold = tabuThreshold,
          numWorkers = numWorkers,
          verbose = verbose,
          deadline = deadline,
          lowerBound = tr.objectiveLoBound,
          upperBound = tr.objectiveHiBound,
          onSolution = onSol
        )
      solved = true
    except TimeLimitExceededError:
      timedOut = true
      if tr.sys.hasFeasibleSolution:
        solved = true
    except NoSolutionFoundError:
      if tr.sys.hasFeasibleSolution:
        solved = true
    except CatchableError as e:
      stderr.writeLine(&"[FZN] Unexpected error during minimize: {e.msg}")
      stderr.writeLine(e.getStackTrace())
      if tr.sys.hasFeasibleSolution:
        solved = true

  of Maximize:
    try:
      if tr.objectivePos == ObjPosWeightedSV:
        maximize(tr.sys, tr.weightedSameValueExpr,
          parallel = parallel,
          tabuThreshold = tabuThreshold,
          numWorkers = numWorkers,
          verbose = verbose,
          deadline = deadline,
          lowerBound = tr.objectiveLoBound,
          upperBound = tr.objectiveHiBound,
          onSolution = onSol
        )
      elif tr.objectivePos == ObjPosBinaryPairwiseSum:
        maximize(tr.sys, tr.binaryPairwiseSumExpr,
          parallel = parallel,
          tabuThreshold = tabuThreshold,
          numWorkers = numWorkers,
          verbose = verbose,
          deadline = deadline,
          lowerBound = tr.objectiveLoBound,
          upperBound = tr.objectiveHiBound,
          onSolution = onSol
        )
      else:
        let objExpr = if tr.objectivePos >= 0: tr.getExpr(tr.objectivePos)
                      elif tr.objectivePos == ObjPosDefinedExpr: tr.objectiveDefExpr
                      else: raise newException(ValueError, "No objective expression for maximize")
        maximize(tr.sys, objExpr,
          parallel = parallel,
          tabuThreshold = tabuThreshold,
          numWorkers = numWorkers,
          verbose = verbose,
          deadline = deadline,
          lowerBound = tr.objectiveLoBound,
          upperBound = tr.objectiveHiBound,
          onSolution = onSol
        )
      solved = true
    except TimeLimitExceededError:
      timedOut = true
      if tr.sys.hasFeasibleSolution:
        solved = true
    except NoSolutionFoundError:
      if tr.sys.hasFeasibleSolution:
        solved = true
    except CatchableError as e:
      stderr.writeLine(&"[FZN] Unexpected error during maximize: {e.msg}")
      stderr.writeLine(e.getStackTrace())
      if tr.sys.hasFeasibleSolution:
        solved = true

  # Restore stdout for solution output
  flushFile(stdout)
  restoreStdout(savedFd)
  gSavedFd = -1  # Mark as restored so signal handler won't use closed fd

  # Ignore signals during output/cleanup — MiniZinc may send SIGTERM
  # near the time limit boundary. Using SIG_IGN prevents any handler
  # from running ARC destructors that would crash.
  signal(SIGTERM, SIG_IGN)
  signal(SIGINT, SIG_IGN)

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

    # Print the final solution, unless `-i` already streamed this exact assignment
    # (avoid a redundant trailing duplicate block). Streaming never fires for geost
    # models, so those always print here.
    if not (canStream and lastStreamedAssignment.len > 0 and
            tr.sys.assignment == lastStreamedAssignment):
      tr.printSolution()
    if tr.sys.optimalityProven:
      printComplete()  # Domain reduction proved no better solution exists
  else:
    # Crusher cannot prove unsatisfiability either, so always report UNKNOWN.
    printUnknown()

  if stats:
    let solveTime = cpuTime() - solveStart
    stderr.writeLine(&"%%%mzn-stat: solveTime={solveTime:.3f}")
    stderr.writeLine(&"%%%mzn-stat: initTime={solveStart - startTime:.3f}")
    stderr.writeLine(&"%%%mzn-stat: nodes={tr.sys.lastIterations}")
    stderr.writeLine("%%%mzn-stat-end")

  # Exit immediately — skip ARC destructors to avoid SIGSEGV during cleanup.
  flushFile(stdout)
  flushFile(stderr)
  immediateExit(0)

main()
