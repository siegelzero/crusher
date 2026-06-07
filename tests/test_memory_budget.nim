## Tests for the parallel-search memory budget (Lever A): parsing a budget,
## fitting the worker count to it, and the --memory / MEMORY_LIMIT precedence.
## Fitting is correctness-neutral — it only bounds peak memory by reducing the
## number of concurrent worker/population state copies, never the search itself.

import std/[unittest, os, sequtils]
import crusher

suite "Memory budget — worker fitting":

  test "parseMemMB: MiB default plus g/m suffixes":
    check parseMemMB("2048") == 2048
    check parseMemMB("2g") == 2048
    check parseMemMB("2G") == 2048
    check parseMemMB("2gb") == 2048
    check parseMemMB("512m") == 512
    check parseMemMB("  512  ") == 512
    check parseMemMB("") == 0
    check parseMemMB("abc") == 0
    check parseMemMB("0") == 0

  test "fitWorkerCount: caps the multiplier, never below 1 or above the request":
    # No budget, or no per-state estimate → request unchanged.
    check fitWorkerCount(8, 800*MiB, 678*MiB, 0) == 8
    check fitWorkerCount(8, 800*MiB, 0, 4096*MiB) == 8
    # A single requested worker is never reduced.
    check fitWorkerCount(1, 800*MiB, 678*MiB, 4096*MiB) == 1
    # Tight budget: peak holds ~2*perState per worker, so only 1 of 8 fits in 4 GiB.
    check fitWorkerCount(8, 800*MiB, 678*MiB, 4096*MiB) == 1
    # Generous budget leaves the full request intact.
    check fitWorkerCount(8, 800*MiB, 200*MiB, 200000*MiB) == 8
    # Base alone over budget → minimal, never 0.
    check fitWorkerCount(8, 5000*MiB, 678*MiB, 4096*MiB) == 1
    check fitWorkerCount(0, 0, 0, 0) == 1
    # Mid-range: usable = 16384*0.85 - 1000 = 12926 MiB; perWorker = 2*1000; → 6.
    check fitWorkerCount(16, 1000*MiB, 1000*MiB, 16384*MiB) == 6

  test "resolveBudgetBytes precedence: --memory override beats MEMORY_LIMIT env":
    let had = getEnv("MEMORY_LIMIT")
    putEnv("MEMORY_LIMIT", "4096")
    check resolveBudgetBytes(0) == 4096 * MiB        # env, interpreted as MiB
    check resolveBudgetBytes(2048) == 2048 * MiB     # explicit override wins
    if had.len > 0: putEnv("MEMORY_LIMIT", had) else: delEnv("MEMORY_LIMIT")

  test "memoryFittedWorkerCount: exercises the probe; honours huge budget and request floor":
    var sys = initConstraintSystem[int]()
    var x = sys.newConstrainedSequence(8)
    x.setDomain(toSeq(0..7))
    var s: AlgebraicExpression[int] = x[0]
    for i in 1..<8:
      s = s + x[i]
    sys.addConstraint(s <= 20)

    # Huge budget → request preserved (also exercises ensureReducedDomain + probe
    # build end-to-end without crashing).
    check memoryFittedWorkerCount(sys, 8, overrideMB = 1_000_000) == 8
    # A single requested worker is never reduced, whatever the budget.
    check memoryFittedWorkerCount(sys, 1, overrideMB = 1) == 1
