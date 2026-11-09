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
##   --memory <MiB>  memory budget; caps workers so peak memory fits (also reads
##                   the MEMORY_LIMIT env var and the cgroup limit)

import std/[os, strutils, strformat, times, posix, tables, packedsets, algorithm, sets]

import crusher
import flatzinc/[parser, translator, output]
import expressions/[weightedSameValue, binaryPairwiseSum]

proc immediateExit(status: cint) {.importc: "_exit", header: "<unistd.h>", noReturn.}

# Global state for SIGTERM handler — allows graceful output on MiniZinc kill
var gSavedFd: cint = -1
var gTranslator: ptr FznTranslator = nil
var gHasSolution: ptr bool = nil
var gWatchdogThread: Thread[float]

proc watchdogProc(deadline: float) {.thread.} =
  ## Hard time-limit backstop: the search loops check the deadline
  ## cooperatively, but any code path that misses a check (long auxiliary
  ## scans, rare scheduling stalls) would otherwise overrun the limit.
  ## Deliver SIGTERM to ourselves shortly after the deadline so the signal
  ## handler prints the best incumbent and exits cleanly.
  while epochTime() < deadline:
    sleep(250)
  stderr.writeLine("[Watchdog] deadline passed — sending SIGTERM (t=" &
                   $epochTime() & ")")
  stderr.flushFile()
  discard posix.kill(posix.getpid(), SIGTERM)

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
  var memoryLimitMB = 0

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
    of "--memory":
      # Memory budget override (MiB, or with a g/m suffix). Caps the worker count
      # so peak memory stays under budget. Also read from the MEMORY_LIMIT env var
      # and the cgroup limit when this flag is absent (see memoryBudget.nim).
      inc i
      if i <= paramCount():
        memoryLimitMB = parseMemMB(paramStr(i))
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
    stderr.writeLine("  --memory <MiB>  memory budget; caps workers to fit (also reads MEMORY_LIMIT)")
    quit(1)

  if not fileExists(filename):
    stderr.writeLine(&"Error: file not found: {filename}")
    quit(1)

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
      stderr.writeLine(&"[Mem] after parse: rss={currentRssBytes() div MiB}MiB")

    # Translate to ConstraintSystem
    if verbose:
      stderr.writeLine("[FZN] Translating...")
    tr = translate(model, timeBudgetSecs = timeLimitMs.float / 1000.0)
    if verbose:
      stderr.writeLine(&"[FZN] System has {tr.sys.baseArray.len} positions, {tr.sys.baseArray.constraints.len} constraints")
      stderr.writeLine(&"[Mem] after translate: rss={currentRssBytes() div MiB}MiB")
    if existsEnv("CRUSHER_DEBUG_VAR"):
      # Debug: how the translator classified named FZN variables (comma list)
      for nm in getEnv("CRUSHER_DEBUG_VAR").split(','):
        let pos = tr.varPositions.getOrDefault(nm, -1)
        var info = &"[DebugVar] {nm}: pos={pos} channelName={nm in tr.channelVarNames} " &
                   &"defined={nm in tr.definedVarNames} definedExpr={nm in tr.definedVarExprs}"
        if pos >= 0:
          let dom = tr.sys.baseArray.domain[pos]
          info &= &" channelPos={pos in tr.sys.baseArray.channelPositions} domLen={dom.len}"
          if dom.len > 0: info &= &" dom=[{min(dom)}..{max(dom)}]"
          for b in tr.sys.baseArray.channelBindings:
            if b.channelPosition == pos: info &= " elemBinding"
          for b in tr.sys.baseArray.expressionChannelBindings:
            if b.channelPosition == pos: info &= " exprBinding"
          for b in tr.sys.baseArray.minMaxChannelBindings:
            if b.channelPosition == pos: info &= " minMaxBinding"
        elif nm in tr.definedVarExprs:
          info &= " expr=" & $tr.definedVarExprs[nm].positions.len & "pos"
        stderr.writeLine(info)
    if existsEnv("CRUSHER_DEBUG_BIGDOM"):
      # Debug: positions with huge explicit domains (memory/time hogs)
      var n = 0
      for name, p in tr.varPositions.pairs:
        let dl = tr.sys.baseArray.domain[p].len
        if dl > 100_000:
          inc n
          if n <= 15:
            stderr.writeLine("[BigDom] " & name & " pos=" & $p & " len=" & $dl &
                             " channel=" & $(p in tr.sys.baseArray.channelPositions))
      stderr.writeLine("[BigDom] total positions with >100k values: " & $n)
    if existsEnv("CRUSHER_DEBUG_SEARCHVARS"):
      # Debug: every non-channel, non-fixed position (name, domain size, constraint count)
      var rows: seq[(int, string)]
      for name, p in tr.varPositions.pairs:
        if p in tr.sys.baseArray.channelPositions: continue
        let dl = tr.sys.baseArray.domain[p].len
        if dl <= 1: continue
        var nc = 0
        for c in tr.sys.baseArray.constraints:
          if p in c.positions: inc nc
        rows.add((p, "[SearchVar] pos=" & $p & " " & name & " dom=" & $dl &
                     " [" & $min(tr.sys.baseArray.domain[p]) & ".." & $max(tr.sys.baseArray.domain[p]) &
                     "] cons=" & $nc))
      rows.sort(proc (a, b: (int, string)): int = cmp(a[0], b[0]))
      for r in rows: stderr.writeLine(r[1])
      stderr.writeLine("[SearchVar] total: " & $rows.len)
    if existsEnv("CRUSHER_DEBUG_POS"):
      # Debug: name and constraints of the given system positions
      var want: seq[int]
      for x in getEnv("CRUSHER_DEBUG_POS").split(','): want.add(parseInt(x))
      for name, p in tr.varPositions.pairs:
        if p in want:
          var cs: seq[string]
          for ci, c in tr.sys.baseArray.constraints:
            if p in c.positions: cs.add($ci & ":" & $c.stateType & "/" & $c.positions.len)
          stderr.writeLine("[DebugPos] pos=" & $p & " name=" & name & " channel=" &
                           $(p in tr.sys.baseArray.channelPositions) & " constraints=" & cs.join(" "))
    if existsEnv("CRUSHER_DEBUG_VARS"):
      # Debug: where did these FZN variables end up, and which constraints read them?
      for vn in getEnv("CRUSHER_DEBUG_VARS").split(','):
        if vn in tr.varPositions:
          let p = tr.varPositions[vn]
          var cs: seq[string]
          for ci, c in tr.sys.baseArray.constraints:
            if p in c.positions: cs.add($ci & ":" & $c.stateType & "/" & $c.positions.len)
          let dom = tr.sys.baseArray.domain[p]
          let domStr = if dom.len <= 8: $dom else: $dom.len & " values [" & $min(dom) & ".." & $max(dom) & "]"
          stderr.writeLine("[DebugVars] " & vn & " pos=" & $p & " channel=" &
                           $(p in tr.sys.baseArray.channelPositions) & " dom=" & domStr &
                           " constraints=" & cs.join(" "))
        elif vn in tr.definedVarExprs:
          stderr.writeLine("[DebugVars] " & vn & " defined expr over " & $tr.definedVarExprs[vn].positions.len & " positions")
        else:
          stderr.writeLine("[DebugVars] " & vn & " has no position")
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
  # The margin shrinks for short limits: a flat 2 s put the deadline at process
  # start for -t 2000, so parallel search never ran (UNKNOWN on trivial models).
  let deadlineMargin = min(2.0, max(0.1, timeLimitMs.float / 1000.0 * 0.1))
  let deadline = if timeLimitMs > 0: wallStart + timeLimitMs.float / 1000.0 - deadlineMargin else: 0.0

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

  # Hard watchdog: SIGTERM ourselves 10s past the deadline if still running
  # (cooperative deadline checks normally exit well before this fires).
  if deadline > 0:
    createThread(gWatchdogThread, watchdogProc, deadline + 10.0)

  # Honour a memory budget (--memory / MEMORY_LIMIT / cgroup) by capping the
  # worker count — peak memory is dominated by per-worker state copies, so fewer
  # workers means lower peak. No-op (workers unchanged) when no budget applies.
  let effectiveWorkers = memoryFittedWorkerCount(tr.sys, numWorkers, memoryLimitMB, verbose)

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
  let solveWallStart = epochTime()
  var solved = false
  var timedOut = false
  # A presolved (constant) objective turns optimization into satisfaction:
  # any feasible solution is optimal.
  let solveKind = if tr.objectivePos == ObjPosConstant: Satisfy else: model.solve.kind
  case solveKind
  of Satisfy:
    try:
      tr.sys.resolve(
        parallel = parallel,
        tabuThreshold = tabuThreshold,
        numWorkers = effectiveWorkers,
        verbose = verbose,
        deadline = deadline
      )
      solved = true
      tr.sys.hasFeasibleSolution = true
      if tr.objectivePos == ObjPosConstant:
        tr.sys.optimalityProven = true
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
          numWorkers = effectiveWorkers,
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
          numWorkers = effectiveWorkers,
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
          numWorkers = effectiveWorkers,
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
          numWorkers = effectiveWorkers,
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
          numWorkers = effectiveWorkers,
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
          numWorkers = effectiveWorkers,
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
    if existsEnv("CRUSHER_DUMP_ALL"):
      tr.dumpAllVarValues(getEnv("CRUSHER_DUMP_ALL"))
    if not (canStream and lastStreamedAssignment.len > 0 and
            tr.sys.assignment == lastStreamedAssignment):
      tr.printSolution()
    if tr.sys.optimalityProven:
      printComplete()  # Domain reduction proved no better solution exists
  else:
    # Debug aid: dump the final (infeasible) assignment so tests/fzncheck.py
    # can name the original constraints the search left violated.
    if existsEnv("CRUSHER_DUMP_ALL") and tr.sys.assignment.len > 0:
      tr.dumpAllVarValues(getEnv("CRUSHER_DUMP_ALL"))
    # Crusher cannot prove unsatisfiability either, so always report UNKNOWN.
    printUnknown()

  if stats:
    # Wall-clock times — cpuTime() sums across threads, inflating parallel
    # solves by roughly the worker count.
    let solveTime = epochTime() - solveWallStart
    stderr.writeLine(&"%%%mzn-stat: solveTime={solveTime:.3f}")
    stderr.writeLine(&"%%%mzn-stat: initTime={solveWallStart - wallStart:.3f}")
    stderr.writeLine(&"%%%mzn-stat: nodes={tr.sys.lastIterations}")
    stderr.writeLine("%%%mzn-stat-end")

  # Exit immediately — skip ARC destructors to avoid SIGSEGV during cleanup.
  flushFile(stdout)
  flushFile(stderr)
  immediateExit(0)

main()
