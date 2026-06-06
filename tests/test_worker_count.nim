import unittest, os, cpuinfo

import ../src/search/parallelResolution

# The MiniZinc Challenge harness sets NUM_CPUS to the container's core
# allocation and expects the solver to honour it. getOptimalWorkerCount() is the
# single chokepoint every auto-worker path (-p 0) routes through.

suite "NUM_CPUS worker count":
  test "honours NUM_CPUS when set to a positive integer":
    putEnv("NUM_CPUS", "3")
    check getOptimalWorkerCount() == 3
    # Used verbatim with no cap — the harness budget wins over the local default.
    putEnv("NUM_CPUS", "16")
    check getOptimalWorkerCount() == 16
    delEnv("NUM_CPUS")

  test "ignores malformed or non-positive NUM_CPUS and falls back":
    let fallback = min(countProcessors(), 8)
    putEnv("NUM_CPUS", "garbage")
    check getOptimalWorkerCount() == fallback
    putEnv("NUM_CPUS", "0")
    check getOptimalWorkerCount() == fallback
    putEnv("NUM_CPUS", "-4")
    check getOptimalWorkerCount() == fallback
    delEnv("NUM_CPUS")

  test "falls back to detected CPU count when NUM_CPUS is unset":
    delEnv("NUM_CPUS")
    check getOptimalWorkerCount() == min(countProcessors(), 8)
