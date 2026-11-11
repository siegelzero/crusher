## Tests for the dense bounded dual simplex (src/search/lpSimplex.nim).

import unittest
import std/[math]
import search/lpSimplex

proc near(a, b: float): bool = abs(a - b) < 1e-6

suite "LP dual simplex":

  test "two-variable optimum":
    # min -x - y  s.t.  x + 2y <= 4,  3x + y <= 6,  0 <= x, y <= 10
    var m = LpModel(n: 2, lb: @[0.0, 0.0], ub: @[10.0, 10.0], cost: @[-1.0, -1.0])
    m.addRow(@[0, 1], @[1.0, 2.0], -LpInf, 4.0)
    m.addRow(@[0, 1], @[3.0, 1.0], -LpInf, 6.0)
    var s = initSolver(m)
    check s.solve() == lpOptimal
    check near(s.value(0), 1.6)
    check near(s.value(1), 1.2)
    check near(s.objective(), -2.8)

  test "equality and greater-equal rows":
    # min x + 2y + 3z  s.t.  x + y + z = 10,  y - z >= 2,  x <= 3
    var m = LpModel(n: 3, lb: @[0.0, 0.0, 0.0], ub: @[3.0, 20.0, 20.0], cost: @[1.0, 2.0, 3.0])
    m.addRow(@[0, 1, 2], @[1.0, 1.0, 1.0], 10.0, 10.0)
    m.addRow(@[1, 2], @[1.0, -1.0], 2.0, LpInf)
    var s = initSolver(m)
    check s.solve() == lpOptimal
    # x = 3 (cheapest), then y = 7, z = 0
    check near(s.value(0), 3.0)
    check near(s.value(1), 7.0)
    check near(s.value(2), 0.0)
    check near(s.objective(), 17.0)

  test "infeasibility is detected":
    var m = LpModel(n: 2, lb: @[0.0, 0.0], ub: @[1.0, 1.0], cost: @[0.0, 0.0])
    m.addRow(@[0, 1], @[1.0, 1.0], 3.0, LpInf)
    var s = initSolver(m)
    check s.solve() == lpInfeasible

  test "warm start after fixing a variable":
    var m = LpModel(n: 2, lb: @[0.0, 0.0], ub: @[10.0, 10.0], cost: @[-1.0, -1.0])
    m.addRow(@[0, 1], @[1.0, 2.0], -LpInf, 4.0)
    m.addRow(@[0, 1], @[3.0, 1.0], -LpInf, 6.0)
    var s = initSolver(m)
    check s.solve() == lpOptimal
    let snap = s.snapshot()
    s.setBounds(0, 2.0, 2.0)          # x = 2 -> y <= 1 (from 3x + y <= 6... y <= 0)
    check s.solve() == lpOptimal
    check near(s.value(0), 2.0)
    check near(s.value(1), 0.0)
    s.setBounds(0, 3.0, 3.0)          # 3x = 9 > 6: infeasible
    check s.solve() == lpInfeasible
    s.restore(snap)
    check near(s.value(0), 1.6)
    s.setBounds(1, 0.0, 1.0)          # y <= 1 -> x = 5/3
    check s.solve() == lpOptimal
    check near(s.value(1), 1.0)
    check near(s.value(0), 5.0 / 3.0)

  test "random LPs agree with brute-force vertex enumeration":
    # Small random boxed LPs in 2 variables: compare with a grid search.
    var seed = 12345'u32
    proc rnd(): float =
      seed = seed * 1103515245'u32 + 12345'u32
      float((seed shr 16) and 0x7fff) / 32768.0
    for trial in 0..<200:
      var m = LpModel(n: 2, lb: @[0.0, 0.0], ub: @[5.0, 5.0],
                      cost: @[rnd() * 4 - 2, rnd() * 4 - 2])
      for k in 0..<3:
        m.addRow(@[0, 1], @[rnd() * 4 - 2, rnd() * 4 - 2], -LpInf, rnd() * 6)
      var s = initSolver(m)
      let st = s.solve()
      # Grid search (resolution 0.01) for the best feasible objective
      var best = Inf
      for i in 0..500:
        for j in 0..500:
          let x = i.float * 0.01
          let y = j.float * 0.01
          var ok = true
          for r in m.rows:
            if r.val[0] * x + r.val[1] * y > r.hi + 1e-9: ok = false; break
          if ok: best = min(best, m.cost[0] * x + m.cost[1] * y)
      if best == Inf:
        check st == lpInfeasible
      else:
        check st == lpOptimal
        if st == lpOptimal:
          # LP optimum is at most the grid optimum and close to it
          check s.objective() <= best + 1e-6
          check s.objective() >= best - 0.1
          # and feasible
          for r in m.rows:
            check r.val[0] * s.value(0) + r.val[1] * s.value(1) <= r.hi + 1e-6
