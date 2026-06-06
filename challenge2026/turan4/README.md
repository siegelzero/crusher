# turan4 — maximum C4-free graph (Zarankiewicz problem)

## Problem

Given `n`, find a simple undirected graph on `n` vertices that contains **no
4-cycle** and has the **maximum possible number of edges**. A graph is C4-free
iff every pair of distinct vertices has at most one common neighbour, encoded
directly as

```
forall i<j:  sum_{k != i,j} adj[i,k] * adj[j,k]  <=  1
```

The optimum is the Zarankiewicz number `ex(n; C4)`. When `n = q^2 + q + 1` for a
prime power `q`, the incidence graph of a projective plane of order `q` is
extremal. This is a hard combinatorial optimisation problem: the optimum is
known only for relatively small `n`, and it is a natural fit for local search.

Pure integer model — 0/1 adjacency variables, no floats, no sets. The solve item
carries an `int_search(..., input_order, indomain_max, complete)` annotation as
required by the challenge.

## Files

- `turan4.mzn` — the model.
- `turan4_toy.dzn` — toy instance (`n = 6`, optimum 7) for testing.
- `turan4_n{15,18,21,24,27,30,33,36,40,44,46,48}.dzn` — 12 graded instances.

Difficulty grows with `n`: the FlatZinc has `Θ(n^3)` product terms and `Θ(n^2)`
edge variables, and the gap to the optimum widens, so the instances span from
quickly-solved (small `n`) to hard (large `n`). Flattening is cheap throughout
(well under 2 s even at the largest `n`).

## Optima and bounds — OEIS [A006855](https://oeis.org/A006855)

The optimum `ex(n; C4)` is OEIS A006855 ("Maximum number of edges in a graph
containing no 4-cycle"). It has an asymptotic upper bound `(n/4)(sqrt(4n-3)+1)`
[Kővári–Sós–Turán; see Aigner–Ziegler, *Proofs from THE BOOK*, ch. 20].

Exact optima are currently known only up to `n = 40`; the instances `n = 15..40`
therefore have a ground-truth optimum, while `n = 44, 46, 48` lie in the **open**
range where only bounds are published — these are research-frontier instances.

| n  | optimum / [lower, upper] | status |
|----|--------------------------|--------|
| 6  | 7   | exact (toy) |
| 15 | 30  | exact |
| 18 | 39  | exact |
| 21 | 50  | exact |
| 24 | 59  | exact |
| 27 | 71  | exact |
| 30 | 85  | exact |
| 33 | 96  | exact |
| 36 | 110 | exact |
| 40 | 127 | exact |
| 44 | [148, 151] | open |
| 46 | [157, 165] | open |
| 48 | [168, 176] | open |

Exact values and the `n = 41..49` bounds are from B. McKay and M. Alekseyev via
A006855.
