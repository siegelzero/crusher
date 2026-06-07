## Memory-budget helpers for bounding peak memory in parallel search.
##
## Crusher's peak memory is dominated by per-worker full-state copies: each
## worker (and each scatter-population member) deep-copies the penalty maps,
## per-constraint caches, and channel lookup tables. Peak therefore scales with
## the number of concurrent copies, which tracks the worker count. The single
## most effective lever for honouring a memory cap — the MiniZinc Challenge's
## `MEMORY_LIMIT` env var (MiB), a `--memory` override, or a Docker cgroup limit
## — is to cap that worker count to what the budget allows.
##
## Strategy ("measure one, then scale"): read the budget, build ONE real worker
## state and measure its resident-set delta, then pick the largest worker count
## whose copies fit under `budget * headroom`. This is correctness-neutral — it
## only reduces parallelism, never the validity of the search. When no budget
## applies it is a no-op and the worker count is unchanged.

import std/[os, strutils]

import tabu
import parallelResolution
import ../constraintSystem
import ../constrainedArray

const
  MiB* = 1024 * 1024
  DefaultHeadroom* = 0.85
    ## Fraction of the budget Crusher plans to use. The remainder absorbs the
    ## MiniZinc driver, solns2out, page cache, and allocator fragmentation that
    ## the cgroup charges but that never show up in fzcrusher's own RSS.
  UnlimitedThreshold = 1'i64 shl 53
    ## cgroup v1 reports "unlimited" as a huge page-aligned sentinel; a limit at
    ## or above this is treated as no limit.

################################################################################
# Current resident-set size
################################################################################

when defined(linux):
  import std/posix
  let gPageSize =
    block:
      let p = sysconf(SC_PAGESIZE)
      if p > 0: int(p) else: 4096

  proc currentRssBytes*(): int =
    ## Resident set size from /proc/self/statm (field 2 = resident pages). Cheap
    ## enough to poll; this is the real challenge target (Linux container).
    try:
      let fields = readFile("/proc/self/statm").splitWhitespace()
      if fields.len >= 2:
        return parseInt(fields[1]) * gPageSize
    except CatchableError:
      discard
    return 0
elif defined(posix):
  import std/posix

  proc currentRssBytes*(): int =
    ## getrusage peak RSS — used for dev on macOS/BSD. macOS reports bytes; other
    ## BSDs report kilobytes. (Peak, not current, but adequate for sizing.)
    var ru: Rusage
    if getrusage(RUSAGE_SELF, addr ru) == 0:
      when defined(macosx): return int(ru.ru_maxrss)
      else: return int(ru.ru_maxrss) * 1024
    return 0
else:
  proc currentRssBytes*(): int = 0

################################################################################
# Budget resolution
################################################################################

proc parseMemMB*(s: string): int =
  ## Parse a memory size to whole MiB. Accepts a plain integer (MiB, matching
  ## MEMORY_LIMIT's convention) or a `g`/`m`-suffixed value (optionally with a
  ## trailing `b`). Returns 0 if empty or unparseable.
  var t = s.strip().toLowerAscii()
  if t.len == 0: return 0
  if t.endsWith("b"): t = t[0 ..< ^1].strip()
  var mult = 1
  if t.endsWith("g"):
    mult = 1024
    t = t[0 ..< ^1].strip()
  elif t.endsWith("m"):
    t = t[0 ..< ^1].strip()
  try:
    let v = parseInt(t)
    if v > 0: return v * mult
  except ValueError:
    discard
  return 0

proc cgroupLimitBytes(): int =
  ## Best-effort read of the container's cgroup memory limit (v2 then v1).
  ## Returns 0 if none / unbounded / unreadable.
  for path in ["/sys/fs/cgroup/memory.max",                     # cgroup v2
               "/sys/fs/cgroup/memory/memory.limit_in_bytes"]:  # cgroup v1
    try:
      let s = readFile(path).strip()
      if s == "max": continue
      let v = parseBiggestInt(s)
      if v > 0 and v < UnlimitedThreshold:
        return int(v)
    except CatchableError:
      discard
  return 0

proc resolveBudgetBytes*(overrideMB: int = 0): int =
  ## Memory budget in bytes (0 = unlimited). Priority: explicit override
  ## (`--memory`) > `MEMORY_LIMIT` env (MiB) > cgroup limit.
  if overrideMB > 0:
    return overrideMB * MiB
  let envMB = parseMemMB(getEnv("MEMORY_LIMIT"))
  if envMB > 0:
    return envMB * MiB
  return cgroupLimitBytes()

################################################################################
# Fitting
################################################################################

proc fitWorkerCount*(requestedWorkers, baseBytes, perStateBytes, budgetBytes: int,
                     headroom = DefaultHeadroom): int =
  ## Largest worker count whose copies fit under `budget * headroom`. Peak
  ## parallel search holds ~2 full state copies per worker (the lazy spawn
  ## buffer, and the scatter population sized 2*workers), so budget 2*perState
  ## per worker. Falls back to `requestedWorkers` when there's nothing to bound.
  if budgetBytes <= 0 or perStateBytes <= 0 or requestedWorkers <= 1:
    return max(1, requestedWorkers)
  let usable = float(budgetBytes) * headroom - float(baseBytes)
  if usable <= 0.0:
    return 1  # base alone is over budget — run minimal and let the search try
  let perWorker = 2 * perStateBytes
  let fitted = int(usable / float(perWorker))
  return max(1, min(requestedWorkers, fitted))

proc measurePerStateBytes*[T](system: ConstraintSystem[T]): tuple[base, perState: int] =
  ## Build one parallel-equivalent worker state and return (baseRSS, RSS delta).
  ## Requires reduceDomain to have run (shared domain set up) so the probe sizes
  ## its penalty maps exactly like a real worker. The probe is released on return
  ## (RSS won't shrink, but the *delta* is the marginal per-worker cost we need).
  let base = currentRssBytes()
  let probeArray = system.baseArray.deepCopy()
  let probe = newTabuState[T](probeArray)
  let after = currentRssBytes()
  # Reference `probe` after the measurement so ARC can't release it early.
  result = (base, if probe.isNil: 0 else: max(0, after - base))

proc ensureReducedDomain[T](system: ConstraintSystem[T]) =
  ## Mirror resolve's prefix so the probe (and the subsequent real resolve) sees
  ## the reduced, shared domain. Both steps are idempotent/guarded, so resolve
  ## will skip them — reduceDomain (which adds derived constraints) runs once.
  system.baseArray.detectElementInverseChannels()
  if system.baseArray.reducedDomain.len == 0:
    system.baseArray.reducedDomain = reduceDomain(system.baseArray)
    system.baseArray.sharedDomainPtr = addr system.baseArray.reducedDomain

proc memoryFittedWorkerCount*[T](system: ConstraintSystem[T], requestedWorkers: int,
                                 overrideMB: int = 0, verbose = false): int =
  ## Worker count to use under the active memory budget. Returns
  ## `requestedWorkers` unchanged when no budget applies (so `0` stays "auto" and
  ## the no-limit path is byte-for-byte identical to before). With a budget,
  ## resolves the domain, measures one worker state, and returns the fitted count.
  let budget = resolveBudgetBytes(overrideMB)
  if budget <= 0:
    return requestedWorkers
  let requested = if requestedWorkers > 0: requestedWorkers else: getOptimalWorkerCount()
  ensureReducedDomain(system)
  let (base, perState) = measurePerStateBytes(system)
  result = fitWorkerCount(requested, base, perState, budget)
  if verbose or result < requested:
    stderr.writeLine("[Mem] limit=" & $(budget div MiB) & "MiB rss=" & $(base div MiB) &
      "MiB state~" & $(perState div MiB) & "MiB; workers " & $requested & " -> " & $result)
