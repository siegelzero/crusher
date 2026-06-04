# Crusher Constraint Reference

This document describes the global constraints available in Crusher. Each entry
gives the public Nim API function, its meaning, and the **violation cost** the
constraint contributes to the total penalty that tabu search minimizes.

Because Crusher is a local-search solver, every constraint is *soft* internally:
instead of a boolean satisfied/violated flag it exposes a non-negative integer
cost (0 means satisfied), and supports an incremental `moveDelta` so the search
can evaluate a candidate assignment change in (usually) O(1)–O(k) time. A
solution is found when the total cost reaches 0.

## How constraints are used

Constructors return a `StatefulConstraint[T]` that you hand to
`sys.addConstraint(...)`:

```nim
import std/sequtils
import crusher

var sys = initConstraintSystem[int]()
var x = sys.newConstrainedSequence(5)
x.setDomain(toSeq(1..5))

sys.addConstraint(allDifferent[int]([0, 1, 2, 3, 4]))
sys.resolve()
```

Most constraints accept **two interchangeable input forms**:

- **Position-based**: an `openArray[int]` of variable indices (fastest).
- **Expression-based**: a `seq[AlgebraicExpression[T]]`, e.g. `@[x[0] + 1, x[1] - 2, ...]`.
  When every expression is a bare variable reference the wrapper automatically
  falls back to the faster position-based path.

Where both forms exist this document shows the position-based signature; the
expression-based overload has the same name and trailing arguments.

## Constraint index

| Category | Constraints |
|----------|-------------|
| [Distinctness](#distinctness-constraints) | `allDifferent`, `allDifferentExcept0` |
| [Counting & cardinality](#counting--cardinality-constraints) | `atLeast`, `atMost`, `globalCardinality`, `globalCardinalityBounded`, `countEq`, `nvalue`, `conjunctSumAtMost` |
| [Ordering & lexicographic](#ordering--lexicographic-constraints) | `increasing`, `strictlyIncreasing`, `decreasing`, `strictlyDecreasing`, `lexLt`, `lexLe` |
| [Sequencing](#sequencing-constraints) | `sequence` |
| [Scheduling & packing](#scheduling--packing-constraints) | `cumulative`, `conditionalCumulative`, `reservoir`, `multiknapsack`, `diffn`, `diffnK`, `geost`, `noOverlapFixedBox`, `multiResourceNoOverlap`, `conditionalNoOverlapPair`, `conditionalDayCapacity` |
| [Graph & routing](#graph--routing-constraints) | `circuit`, `subcircuit`, `circuitTimeProp`, `connected` |
| [Extensional & automaton](#extensional--automaton-constraints) | `tableIn`, `tableInGacSafe`, `tableNotIn`, `regular` |
| [Element & indexing](#element--indexing-constraints) | `element`, `matrixElement`, `matrixElementVarVar`, `valueSupport` |
| [Arithmetic & relational](#arithmetic--relational-constraints) | comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`) over expressions |
| [Linear & boolean](#linear--boolean-constraints) | `pseudoBoolLinLe`, `conditionalLinear`, `setIntersectCard`, boolean composition |
| [Specialized](#specialized-constraints) | `irdcs`, `isoscelesFreeGrid` |

---

## Distinctness constraints

### AllDifferent

**Function**: `allDifferent(positions)` / `allDifferent(expressions)`

**Definition**: Ensures all variables take pairwise different values.

**Mathematical Form**: `∀i,j ∈ positions, i ≠ j : x[i] ≠ x[j]`

**Usage Examples**:
```nim
# All variables must have different values
sys.addConstraint(allDifferent[int]([0, 1, 2, 3, 4]))

# N-Queens: distinct columns and distinct diagonals
sys.addConstraint(allDifferent(colVars))
var diagonals: seq[AlgebraicExpression[int]]
for i in 0..<n: diagonals.add(x[i] + i)       # expression form
sys.addConstraint(allDifferent(diagonals))
```

**Applications**: N-Queens, resource assignment, scheduling, permutation
problems, graph coloring, Sudoku row/column/box uniqueness.

**Violation Cost**: Sum of duplicate conflicts — for each value appearing `k > 1`
times, the surplus `k - 1` is counted. Zero when all values are distinct.

**Performance**: O(1) incremental updates using value-frequency counts.

---

### AllDifferentExcept0

**Function**: `allDifferentExcept0(positions)` / `allDifferentExcept0(expressions)`

**Definition**: Like `allDifferent`, but the value `0` is exempt — any number of
variables may be `0`. All *non-zero* values must be distinct.

**Mathematical Form**: `∀i,j, i ≠ j : (x[i] ≠ 0 ∧ x[j] ≠ 0) ⇒ x[i] ≠ x[j]`

**Usage Examples**:
```nim
# Non-zero entries must be unique; 0 means "unused/empty"
sys.addConstraint(allDifferentExcept0[int]([0, 1, 2, 3, 4]))
```

**Applications**: Optional assignments where 0 is a "null" slot — partial
permutations, sparse rosters, open-shop scheduling, subcircuit successor arrays.

**Violation Cost**: Sum of duplicate conflicts among non-zero values (zeros never
conflict).

---

## Counting & cardinality constraints

### AtLeast

**Function**: `atLeast(positions, targetValue, minOccurrences)` / `atLeast(expressions, ...)`

**Definition**: `targetValue` must appear at least `minOccurrences` times.

**Mathematical Form**: `|{i ∈ positions : x[i] = targetValue}| ≥ minOccurrences`

**Usage Examples**:
```nim
# At least 3 occurrences of value 1
sys.addConstraint(atLeast[int]([0, 1, 2, 3, 4], 1, 3))
```

**Applications**: minimum staffing, minimum resource utilization, mandatory
inspections.

**Violation Cost**: `max(0, minOccurrences - actualCount)`.

---

### AtMost

**Function**: `atMost(positions, targetValue, maxOccurrences)` / `atMost(expressions, ...)`

**Definition**: `targetValue` may appear at most `maxOccurrences` times.

**Mathematical Form**: `|{i ∈ positions : x[i] = targetValue}| ≤ maxOccurrences`

**Usage Examples**:
```nim
# At most 2 occurrences of value 5
sys.addConstraint(atMost[int]([0, 1, 2, 3, 4], 5, 2))
```

**Applications**: capacity limits, overtime limits, risk caps.

**Violation Cost**: `max(0, actualCount - maxOccurrences)`.

---

### Global Cardinality

**Function**:
`globalCardinality(positions, cover, counts)` /
`globalCardinalityBounded(positions, cover, lowerBounds, upperBounds)`
(both also have expression-based overloads)

**Definition**: Constrains the occurrence counts of several values
simultaneously, either to exact targets or to ranges.

**Mathematical Form**:
- Exact: `∀v ∈ cover : |{i : x[i] = v}| = count[v]`
- Bounded: `∀v ∈ cover : lowerBound[v] ≤ |{i : x[i] = v}| ≤ upperBound[v]`

**Usage Examples**:
```nim
# Exactly 2 ones, 3 twos, 1 three
sys.addConstraint(globalCardinality[int]([0,1,2,3,4,5], [1,2,3], [2,3,1]))

# 1–3 type A, 2–4 type B, 0–2 type C
sys.addConstraint(globalCardinalityBounded[int](
    [0,1,2,3,4,5,6,7,8], [A, B, C], [1,2,0], [3,4,2]))
```

**Applications**: team composition, balanced category distribution, product mix,
skill distribution.

**Violation Cost**:
- Exact: `Σ |actualCount[v] - count[v]|`
- Bounded: `Σ (max(0, lower[v] - count[v]) + max(0, count[v] - upper[v]))`

---

### CountEq

**Function**: `countEq(arrayPositions, countValue, targetPosition)`

**Definition**: The number of times `countValue` occurs in `arrayPositions` must
equal the *variable* at `targetPosition` (a variable count, not a constant). The
target may itself be one of the array elements.

**Mathematical Form**: `|{i ∈ arrayPositions : x[i] = countValue}| = x[targetPosition]`

**Usage Examples**:
```nim
# Number of cells equal to 0 must equal the value stored at position n
sys.addConstraint(countEq[int](toSeq(0..<n), 0, n))
```

**Applications**: magic/self-describing sequences, count channeling, statistics
variables that feed back into the model.

**Violation Cost**: `|actualCount - x[targetPosition]|`.

---

### NValue

**Function**: `nvalue(arrayPositions, targetPosition)`

**Definition**: The number of *distinct* values among `arrayPositions` must equal
the variable at `targetPosition`.

**Mathematical Form**: `|{x[i] : i ∈ arrayPositions}| = x[targetPosition]`

**Usage Examples**:
```nim
# Use exactly k distinct colors, where k is the variable at position n
sys.addConstraint(nvalue[int](toSeq(0..<n), n))
```

**Applications**: minimizing/bounding the number of distinct resources, colors,
or shifts used; diversity requirements.

**Violation Cost**: `|distinctCount - x[targetPosition]|`. O(1) incremental
updates via per-value occurrence counts (detecting when a value's count crosses
the zero boundary).

---

### ConjunctSumAtMost

**Function**: `conjunctSumAtMost(groups, targetValue, maxOccurrences)`

**Definition**: Bounds how many *groups* of positions have **all** their members
equal to `targetValue`. A generalization of `atMost` to conjunctions of
equalities.

**Mathematical Form**: `|{g ∈ groups : ∀p ∈ g . x[p] = targetValue}| ≤ maxOccurrences`

**Usage Examples**:
```nim
# At most one of these binary triples may be all-ones
sys.addConstraint(conjunctSumAtMost[int](@[@[0,1,2], @[3,4,5]], 1, 1))
```

**Notes**: When every group is a single position the constraint collapses to a
plain position-based `atMost` and the wrapper redirects automatically. Used as
the encoding backend for clause-style "no group may be all selected" patterns
(see `isoscelesFreeGrid`).

**Violation Cost**: `max(0, (#groups fully equal to targetValue) - maxOccurrences)`.

---

## Ordering & lexicographic constraints

### Increasing / StrictlyIncreasing / Decreasing / StrictlyDecreasing

**Functions**:
`increasing(positions)`, `strictlyIncreasing(positions)`,
`decreasing(positions)`, `strictlyDecreasing(positions)`
(each with an expression-based overload)

**Definition**: Enforce a monotonic order over consecutive variables.

| Function | Form |
|----------|------|
| `increasing` | `x[i] ≤ x[i+1]` |
| `strictlyIncreasing` | `x[i] < x[i+1]` |
| `decreasing` | `x[i] ≥ x[i+1]` |
| `strictlyDecreasing` | `x[i] > x[i+1]` |

**Usage Examples**:
```nim
sys.addConstraint(increasing[int]([0, 1, 2, 3, 4]))
sys.addConstraint(strictlyIncreasing(eventTimeVars))   # unique, ordered timestamps
```

**Applications**: chronological ordering, symmetry breaking, ranking systems,
monotone resource depletion, strictly improving benchmarks.

**Violation Cost**: Sum of per-pair ordering violations. For a violated pair the
cost is the magnitude by which the order is broken (strict variants add 1 for
equal adjacent values).

---

### Lexicographic ordering (lexLt / lexLe)

**Functions**:
`lexLt(leftPositions, rightPositions)` (strict, `L < R`)
`lexLe(leftPositions, rightPositions)` (non-strict, `L ≤ R`)
(both with expression-based overloads)

**Definition**: Compares two equal-length vectors lexicographically — the first
differing component decides the order.

**Mathematical Form**: `L ≤_lex R` ⇔ `∃k : (∀j<k. L[j]=R[j]) ∧ L[k] < R[k]`,
plus equality for the non-strict case.

**Usage Examples**:
```nim
# Break row symmetry in a matrix: each row ≤ the next, lexicographically
for r in 0..<n-1:
    sys.addConstraint(lexLe[int](rowVars[r], rowVars[r+1]))
```

**Applications**: symmetry breaking over rows/columns of a matrix, canonical
ordering of interchangeable subsequences.

**Violation Cost**: Graduated cost based on the first position where the required
lexicographic relation is broken.

---

## Sequencing constraints

### Sequence

**Function**: `sequence(positions, minInSet, maxInSet, windowSize, targetSet)`
(with expression-based overload)

**Definition**: Among any `windowSize` consecutive variables, between `minInSet`
and `maxInSet` (inclusive) must take values from `targetSet`.

**Mathematical Form**:
`∀i : minInSet ≤ |{j ∈ [i, i+windowSize-1] : x[j] ∈ targetSet}| ≤ maxInSet`

**Usage Examples**:
```nim
# In any 7 consecutive days, at least 2 must be rest days
sys.addConstraint(sequence[int](days, 2, 7, 7, [REST]))

# No more than 3 consecutive night shifts
sys.addConstraint(sequence[int](days, 0, 3, 4, [NIGHT]))
```

**Applications**: shift regulations, rest-period enforcement, rate limiting,
regular inspection/maintenance patterns.

**Violation Cost**: Summed over all windows:
`Σ_window (max(0, minInSet - count) + max(0, count - maxInSet))`. Incremental
updates touch only affected windows.

---

## Scheduling & packing constraints

### Cumulative

**Function**:
```nim
cumulative(originPositions, durations, heights, limit,
           limitPosition = -1, durationPositions = @[], heightPositions = @[])
```
(with expression-based overload for `originExpressions`)

**Definition**: Resource-constrained scheduling — at every time point the total
height (demand) of overlapping tasks must not exceed `limit`.

**Mathematical Form**:
`∀t : Σ(i where origin[i] ≤ t < origin[i] + duration[i]) height[i] ≤ limit`

**Parameters**:
- `originPositions` / `originExpressions`: task start times.
- `durations`, `heights`: per-task constants (fallbacks).
- `limit`: capacity. If `limitPosition >= 0`, capacity is itself a variable.
- `durationPositions` / `heightPositions`: optional per-task positions making
  duration/height *variable* (`-1` for an entry keeps the constant).

**Usage Examples**:
```nim
let durations = @[3, 9, 10, 6, 2]
let heights   = @[1, 2,  1, 1, 3]
sys.addConstraint(cumulative[int]([0,1,2,3,4], durations, heights, 8))

# Variable-height tasks and a variable capacity bound:
sys.addConstraint(cumulative[int](origins, durations, heights, 0,
                                  limitPosition = capVar,
                                  heightPositions = heightVars))
```

**Applications**: project/machine scheduling, job scheduling with CPU/memory
limits, capacity-constrained routing, energy/workforce planning.

**Violation Cost**: Sum over time of `max(0, demand(t) - limit)`. Uses
event-based timeline tracking so only affected time points are recomputed; offers
`getGoodStartTimes`/`batchMovePenalty` helpers for efficient neighborhood
evaluation.

---

### ConditionalCumulative

**Function**: `conditionalCumulative(fixedTasks, tasks, limit, maxTime = 500)`

**Definition**: A cumulative constraint where each task contributes to the
resource profile only when **all of its conditions hold** (e.g.
`room[p] == r AND selected[p]`). Tasks may have fixed or variable starts.

**Usage Examples**:
```nim
# Tasks consume capacity only when assigned to this room and chosen
sys.addConstraint(conditionalCumulative[int](fixedTasks, condTasks, capacity))
```

**Applications**: room/resource scheduling where task presence depends on
assignment decisions; cumulative within a selected subset.

**Violation Cost**: Same form as `cumulative` (summed overload across time),
counting only active tasks.

---

### Reservoir

**Function**: `reservoir(taskPositions, consumptions, maxDiff)`

**Definition**: A producer/consumer level constraint. Ordering events by start
time, the running cumulative consumption must stay within `[-maxDiff, maxDiff]`
after each event (positive `consumption` produces, negative consumes).

**Mathematical Form**: for each event `i` (in start-time order),
`prefixSum[i] = Σ(j : start[j] ≤ start[i]) consumption[j]`, require
`|prefixSum[i]| ≤ maxDiff`.

**Usage Examples**:
```nim
sys.addConstraint(reservoir[int](startVars, @[+5, -3, +2, -4], 8))
```

**Applications**: inventory / tank level bounds, mass and energy balance,
battery charge limits, buffer occupancy.

**Violation Cost**: `Σ_i max(0, |prefixSum[i]| - maxDiff)`.

---

### Multiknapsack

**Function**: `multiknapsack(positions, weights, capacities)`
(with expression-based overload)

**Definition**: For each value `v`, the total weight of items assigned to `v`
must not exceed that value's capacity. (Bin packing where the variable's *value*
selects the bin.)

**Mathematical Form**: `∀v : Σ(i where x[i] = v) weights[i] ≤ capacity[v]`

**Parameters**:
- `positions`: item variables (each chooses a bin/value).
- `weights`: per-item weight.
- `capacities`: array of `(value, capacity)` pairs.

**Usage Examples**:
```nim
# 3 bins with capacities 5, 7, 4
sys.addConstraint(multiknapsack[int]([0,1,2,3,4], [2,3,1,4,2],
                                     [(1,5), (2,7), (3,4)]))
```

**Applications**: bin packing, server/task allocation, load balancing,
weight/volume-limited routing.

**Violation Cost**: `Σ_v max(0, load[v] - capacity[v])`. O(1) incremental
updates.

---

### Diffn (2D no-overlap)

**Function**: `diffn(xExprs, yExprs, dxExprs, dyExprs)`

**Definition**: A set of axis-aligned rectangles must not pairwise overlap.
Inputs are expression sequences for the X/Y origins and the widths/heights.

**Mathematical Form**: for all `i ≠ j`, NOT
(`x[i] < x[j]+dx[j] ∧ x[j] < x[i]+dx[i] ∧ y[i] < y[j]+dy[j] ∧ y[j] < y[i]+dy[i]`).

**Usage Examples**:
```nim
sys.addConstraint(diffn[int](xs, ys, widths, heights))
```

**Applications**: rectangle packing, floor planning, VLSI placement, strip
packing, 2D cutting stock.

**Violation Cost**: Sum of pairwise overlap areas/penalties; `batchMovePenalty`
supports efficient placement moves.

---

### DiffnK (k-dimensional no-overlap)

**Function**: `diffnK(n, k, posExprs, sizeExprs)`

**Definition**: Generalizes `diffn` to `n` boxes in `k` dimensions. Two boxes
overlap iff they overlap in **every** dimension; zero-size boxes never overlap
(non-strict semantics).

**Usage Examples**:
```nim
# n boxes in 3D
sys.addConstraint(diffnK[int](n, 3, posExprs, sizeExprs))
```

**Applications**: 3D bin/container packing, multi-dimensional resource–time
reservation, hyper-rectangle layout.

**Violation Cost**: Number of overlapping pairs.

---

### Geost

**Function**: `geost(placementPositions, cellsByPlacement)`

**Definition**: A local-search formulation of the classic *geost* constraint.
Each object selects a placement from its domain; placements are defined by the
set of discrete grid **cells** they cover. No two objects may cover the same
cell.

**Parameters**:
- `placementPositions`: one variable per object selecting its placement.
- `cellsByPlacement[obj][placement]`: cells covered by that placement of that
  object.

**Usage Examples**:
```nim
# 5 polyomino pieces, each with a list of candidate placements
sys.addConstraint(geost[int](@[0,1,2,3,4], cellsByPlacement))
```

**Applications**: polyomino/puzzle packing, irregular-shape placement, tiling.

**Violation Cost**: Number of cell collisions between placed objects.
See <https://sofdem.github.io/gccat/gccat/Cgeost.html>.

---

### NoOverlapFixedBox

**Function**: `noOverlapFixedBox(nodeA, nodeB, radius, boxLower, boxUpper)`

**Definition**: A variable 3D "pipe leg" (the capsule between two endpoint nodes,
with a given `radius`) must not overlap a *fixed* axis-aligned 3D box.

**Usage Examples**:
```nim
sys.addConstraint(noOverlapFixedBox[int](nodeA, nodeB, radius,
                                         [xLo,yLo,zLo], [xHi,yHi,zHi]))
```

**Applications**: 3D pipe/cable routing around obstacles, robot path clearance,
keep-out zones.

**Violation Cost**: Penetration depth of the pipe leg into the forbidden box.

---

### MultiResourceNoOverlap

**Function**: `multiResourceNoOverlap(overlapPos, assignPairs)`

**Definition**: Given an `overlap` indicator variable for a pair of activities,
if they overlap in time (`overlap = 1`) they may not share **any** resource.

**Usage Examples**:
```nim
sys.addConstraint(multiResourceNoOverlap[int](overlapVar, assignPairs))
```

**Applications**: disjunctive scheduling with multiple shared resources,
exam/room conflict avoidance.

**Violation Cost**: Number of shared resources when the two activities overlap.

---

### ConditionalNoOverlapPair

**Function**:
```nim
conditionalNoOverlapPair(startAPos, startBPos, durationA, durationB,
                         resourceAPos, resourceBPos, resourceAFixed,
                         resourceBFixed, condAPos, condBPos)
```

**Definition**: Two tasks must not overlap in time **if** both are active
(their condition variables hold) **and** they are assigned to the same resource.

**Applications**: pairwise disjunctive scheduling where presence and resource
assignment are themselves decisions.

**Violation Cost**: Temporal overlap of the two intervals when the guard
conditions and resource match are all satisfied.

---

### ConditionalDayCapacity

**Function**: `conditionalDayCapacity(tasks, capacities, maxDay)`

**Definition**: For each day, the summed weight of active tasks must stay within
that day's capacity. A task is active subject to its admission day, selection
flag, and an optional extra condition.

**Mathematical Form**: `∀ day d : Σ_i weight[i] · active(i, d) ≤ capacity[d]`

**Applications**: hospital admissions / bed capacity, daily headcount limits,
per-day throughput caps with optional task presence.

**Violation Cost**: `Σ_d max(0, load[d] - capacity[d])`; supports
`batchMovePenalty` over a candidate domain.

---

## Graph & routing constraints

### Circuit

**Function**: `circuit(positions, valueOffset = 1)`

**Definition**: The variables form a *successor* function that must be a single
Hamiltonian circuit visiting all `n` nodes. `valueOffset = 1` for 1-based
successor values, `0` for 0-based.

**Note**: `circuit` does **not** imply `allDifferent`; add both when you need a
permutation:
```nim
sys.addConstraint(allDifferent(x))
sys.addConstraint(circuit(x))
```

**Applications**: TSP and vehicle routing, sequencing tours, Hamiltonian-cycle
problems.

**Violation Cost**: `max(0, numCycles - 1) + numTailNodes` — penalizes
fragmentation into multiple sub-tours and dangling tails.

---

### Subcircuit

**Function**: `subcircuit(positions, valueOffset = 1)`

**Definition**: The variables form **at most one** circuit; a self-loop
(`i → i`) marks a node as *not* part of the circuit. Like `circuit`, does not
imply `allDifferent`.

**Applications**: routing where only a subset of nodes is visited (prize-
collecting TSP, optional stops), partial tours.

**Violation Cost**: `max(0, numNonTrivialCycles - 1) + numTailNodes`.

---

### CircuitTimeProp

**Function**:
```nim
circuitTimeProp(predPositions, distanceMatrix, earlyTimes, lateTimes,
                depotIndex, depotDeparture, arrivalPositions,
                departurePositions, valueOffset = 1)
```

**Definition**: A circuit constraint coupled with **time propagation** along the
route — it derives arrival/departure times from the predecessor structure and a
distance matrix, enforcing time-window feasibility. Supports an objective bound
(`setObjectiveBound` / `clearObjectiveBound`) for makespan/duration tightening.

**Applications**: vehicle routing with time windows (VRPTW), routing where
travel times feed scheduling constraints and the objective.

**Violation Cost**: Combined circuit-structure penalty plus time-window
violations (and objective-bound excess when a bound is set).

---

### Connected

**Function**: `connected(nodePositions, edgePositions, edgeFrom, edgeTo)`

**Definition**: The set of *active* nodes (boolean variables, non-zero = active)
must form a single connected component. Edges are active iff both endpoints are
active.

**Usage Examples**:
```nim
sys.addConstraint(connected[int](nodeVars, edgeVars, edgeFrom, edgeTo))
```

**Applications**: connected subgraph selection, network design, contiguity
constraints in districting/territory problems.

**Violation Cost**: `max(0, numComponents - 1)` over the active subgraph.

---

## Extensional & automaton constraints

### Table (tableIn / tableInGacSafe / tableNotIn)

**Functions**:
`tableIn(positions, tuples)` — the variable tuple must equal one allowed tuple.
`tableNotIn(positions, tuples)` — the tuple must differ from every forbidden tuple.
`tableInGacSafe(positions, tuples)` — `tableIn` flagged safe for GAC domain
reduction (lets small tables bypass the transition-table size threshold).
(All with expression-based overloads.)

**Definition**: Extensional (table) constraints listing allowed/forbidden
combinations explicitly.

**Usage Examples**:
```nim
# (x0,x1,x2) must be one of these rows
sys.addConstraint(tableIn[int]([0,1,2], @[@[1,1,1], @[2,3,4], @[0,0,0]]))

# (x0,x1) must avoid these forbidden pairs
sys.addConstraint(tableNotIn[int]([0,1], @[@[1,2], @[3,4]]))
```

**Applications**: compatibility/conflict tables, configuration rules, decoded
logic, transition relations.

**Violation Cost**:
- `tableIn`: minimum Hamming distance from the current tuple to any allowed tuple
  (graduated, guiding search toward a valid row).
- `tableNotIn`: `1` if the tuple exactly matches a forbidden tuple, else `0`.

---

### Regular

**Function**:
```nim
regular(positions, nStates, inputMin, inputMax, transition,
        initialState, finalStates)
```
(with expression-based overload)

**Definition**: The sequence of variable values must be accepted by a
deterministic finite automaton (DFA), given its state count, input alphabet range
`[inputMin, inputMax]`, transition table, start state, and accepting states.

**Usage Examples**:
```nim
# Shift pattern legality encoded as a DFA
sys.addConstraint(regular[int](days, nStates, 0, 2, transition, 1, @[1, 2]))
```

**Applications**: rostering pattern rules, sequence legality, formal-language
membership over a variable string.

**Violation Cost**: Recovery-based error counting — each time the DFA would enter
the fail state it counts 1 penalty and recovers to a precomputed background state,
giving a cost roughly proportional to the number of distinct rule violations.

---

## Element & indexing constraints

### Element

**Function**: `element(indexExpr, array, valueExpr)`

**Definition**: Enforces `array[indexExpr] = valueExpr`. The array may be
constants, variables (expressions), a mixed `ArrayElement` sequence, or a
`ConstrainedSequence`; the value may be an expression or a constant.

**Mathematical Form**: `array[index] = value`

**Usage Examples**:
```nim
let lookup = [0, 1, 4, 9, 16, 25]                 # squares
sys.addConstraint(element[int](idx, lookup, outVar))

let vars = @[x[0], x[1], x[2], x[3]]              # array of variables
sys.addConstraint(element[int](idx, vars, valVar))
```

**Applications**: lookup tables, configuration selection, routing/path choice,
state-transition tables, dynamic resource mapping. Element is also the core
**channel variable** mechanism (see CLAUDE.md) — derived positions recomputed
after each move.

**Violation Cost**: Graduated cost based on the mismatch between `array[index]`
and `value`; handles bounds checking automatically.

---

### MatrixElement

**Functions**:
- `matrixElement(matrixElements, numRows, numCols, rowConstant, colPosition, valuePosition)` — constant row, variable column.
- `matrixElement(matrixElements, numRows, numCols, rowPosition, colConstant, valuePosition, rowIsVariable)` — variable row, constant column.
- `matrixElementVarVar(matrixElements, numRows, numCols, rowPosition, colPosition, valuePosition)` — variable row and column.

**Definition**: 2D element — `matrix[row * numCols + col] = value`, where the
matrix entries may be constants or variables and the row/col indices may be
constant or variable.

**Usage Examples**:
```nim
# value = M[row][colVar], row fixed
sys.addConstraint(matrixElement[int](M, nRows, nCols, row, colVar, valVar))

# value = M[rowVar][colVar]
sys.addConstraint(matrixElementVarVar[int](M, nRows, nCols, rowVar, colVar, valVar))
```

**Applications**: 2D lookup tables, cost/distance matrices indexed by variable
coordinates, grid addressing.

**Violation Cost**: Graduated mismatch between the indexed matrix entry and the
value variable; `batchMovePenalty` supports efficient evaluation.

---

### ValueSupport

**Function**: `valueSupport(cellPos, neighbourPositions, maxVal)`

**Definition**: If a cell holds value `N > 1`, then all values `1 .. N-1` must
appear among its neighbours (a "supported value" / build-up rule).

**Mathematical Form**: `x[cell] = N > 1 ⇒ {1, …, N-1} ⊆ {x[j] : j ∈ neighbours}`

**Applications**: grid "neighbours" puzzles, layered/level placement where a
level requires all lower levels nearby, build-up/reachability rules.

**Violation Cost**: Count of predecessor values `1 .. N-1` missing from the
neighbourhood.

---

## Arithmetic & relational constraints

### Relational comparisons (`==`, `!=`, `<`, `<=`, `>`, `>=`)

**Operators**: `==`, `!=`, `<`, `<=`, `>`, `>=` applied to two expressions.

**Definition**: The foundational arithmetic constraint. Comparing two algebraic
expressions (a variable, an arithmetic expression, or an aggregate such as a
`SumExpression`, `MinExpression`, or `MaxExpression`) produces a
`StatefulConstraint` enforcing that relation. These are what you write for the
everyday "linear constraints" of a model.

**Usage Examples**:
```nim
sys.addConstraint(x[0] == i)                 # equality to a constant
sys.addConstraint(x[0] + x[1] <= 10)         # linear inequality
sys.addConstraint(2*x[0] - x[1] != 3)
sys.addConstraint(sum(x) == 100)             # aggregate-to-constant
sys.addConstraint(min(a, b) >= c)            # min/max expression relation
```

**Applications**: linear (in)equalities, budget/total constraints, channeling
between variables, the bread-and-butter relations underlying most models.

**Violation Cost**: Graduated, magnitude-aware penalty equal to how far the
relation is from holding — e.g. `max(0, lhs - rhs)` for `≤`, `|lhs - rhs|` for
`=` — giving search a gradient toward feasibility. Equalities and inequalities
over the same operands share an incremental evaluator (`RelationalConstraint`)
that caches the running sum for O(1) `moveDelta`.

---

## Linear & boolean constraints

### PseudoBoolLinLe

**Function**: `pseudoBoolLinLe(positions, coefficients, rhs)`

**Definition**: A pseudo-boolean linear inequality over binary variables:
`Σ coefficients[i] · x[positions[i]] ≤ rhs`, with all `x ∈ {0, 1}`.

**Usage Examples**:
```nim
# 3·b0 + 2·b1 + 5·b2 ≤ 6
sys.addConstraint(pseudoBoolLinLe[int]([0,1,2], [3,2,5], 6))
```

**Applications**: budget/weight constraints over yes-no decisions, 0/1 knapsack
bounds, weighted boolean cardinality.

**Violation Cost**: `max(0, Σ coefficients[i]·x[i] - rhs)` (magnitude-aware).

---

### ConditionalLinear

**Function**: `conditionalLinear(...)` *(translator-internal; constructed from
FlatZinc)*

**Definition**: A linear inequality enforced only when a guard variable takes a
specific value: `guard == guardActiveValue ⇒ Σ coeffs[i]·x[i] ≤ rhs`, else no
constraint. Provides magnitude-aware (gradient) penalties for guarded linear
constraints, unlike a binary `bool_clause` encoding.

**Violation Cost**: `max(0, currentSum - rhs)` when the guard is active, else `0`.

---

### SetIntersectCard

**Function**: `setIntersectCard(leftPositions, rightPositions, maxCard, minCard = 0)`

**Definition**: Bounds the cardinality of the intersection of two sets
represented as parallel arrays of binary variables:
`minCard ≤ Σ_i min(A[i], B[i]) ≤ maxCard`.

**Usage Examples**:
```nim
# The two selected sets may share at most 3 elements
sys.addConstraint(setIntersectCard[int](setA, setB, 3))
```

**Applications**: overlap limits between chosen sets, diversity/disjointness
requirements, shared-element budgets.

**Violation Cost**: Amount by which the intersection size falls outside
`[minCard, maxCard]`. O(1) incremental updates for binary variables.

---

### Boolean composition

Any two `StatefulConstraint`s (or a `StatefulConstraint` and an
`AlgebraicConstraint`) can be combined into a new soft constraint whose penalty
is derived from its operands' penalties:

```nim
sys.addConstraint(c1 and c2)
sys.addConstraint(c1 or  c2)
sys.addConstraint(c1 xor c2)
sys.addConstraint(c1 implies c2)     # also: c1 -> c2
sys.addConstraint(c1 iff c2)         # also: c1 <-> c2
sys.addConstraint(not c1)
```

Use `toStateful(algebraicConstraint)` to lift a bare algebraic relation (e.g.
`x[0] + x[1] == 5`) into a `StatefulConstraint` so it can participate in boolean
composition. The combined penalty reflects the logical operator (for example,
`and` sums the operand penalties; `or` takes the minimum; `not`/`implies`/`iff`
derive from operand satisfaction), giving search a smooth gradient through
nested logic.

---

## Specialized constraints

### IRDCS

**Function**: `irdcs(n, singletonPenalty = 1)` / `irdcs(positions, singletonPenalty = 1)`

**Definition**: Incongruent Restricted Disjoint Covering System over the interval
`[1, n]`. Each position is assigned a modulus; all positions sharing a modulus
must share the same residue (mod that modulus); and each modulus used must cover
at least 2 positions. `singletonPenalty` weights moduli covering only one
position.

**Applications**: number-theoretic covering-system research (see "Odd
Incongruent Restricted Disjoint Covering Systems", Emanuel, *INTEGERS* 12A, 2012).

**Violation Cost**: Penalty for residue conflicts plus `singletonPenalty` per
under-covered (singleton) modulus.

---

### IsoscelesFreeGrid

**Function**: `isoscelesFreeGrid(positions, n)`

**Definition**: On an `n×n` grid (row-major binary variables, `1` = selected),
forbids any three selected cells from forming an isosceles triangle — including
the degenerate collinear-midpoint case. The bad triples are enumerated in Nim at
construction time (O(n⁴)) and encoded as a single `conjunctSumAtMost` with
`maxOccurrences = 0`, avoiding the O(n⁶) blow-up of the parametric MiniZinc
formulation.

**Usage Examples**:
```nim
# No three chosen cells form an isosceles triangle on a 16×16 grid
sys.addConstraint(isoscelesFreeGrid[int](toSeq(0..<16*16), 16))
```

**Applications**: the "no-isosceles-triangle" combinatorial geometry problem and
related point-configuration puzzles.

**Violation Cost**: Number of selected bad triples (each forbidden triple whose
three cells are all `1`).

---

## A note on FlatZinc-internal constraints

A few constraint types exist primarily as optimized targets for the FlatZinc
translator and have no hand-written Nim wrapper:

- **`conditionalLinear`** — guarded linear inequality (documented above);
  recovered from reified linear FlatZinc constraints.
- **`multiMachineNoOverlap`** — consolidates many `cumulative(limit = 1)`
  machine-disjunctive constraints (optionally with a sequence-dependent setup
  matrix) into one constraint, avoiding an explosion of channel bindings.
- **`disjunctiveClause`** — a disjunction of conjunctions of linear inequality
  terms; satisfied when at least one disjunct holds. Penalty is the minimum, over
  disjuncts, of the summed term violations. Recovered from reified
  linear/clause patterns in FlatZinc.

They are listed here for completeness; you normally encounter them only when
solving `.fzn`/`.mzn` models, not when writing the Nim API directly.

---

## Constraint composition

All constraints can be combined within a single `ConstraintSystem`:

```nim
var sys = initConstraintSystem[int]()
var variables = sys.newConstrainedSequence(10)
variables.setDomain(toSeq(1..5))

sys.addConstraint(allDifferent[int]([0,1,2,3,4]))
sys.addConstraint(sequence[int]([0,1,2,3,4,5,6,7,8,9], 2, 4, 5, [1,2]))
sys.addConstraint(multiknapsack[int]([5,6,7,8,9], [3,2,4,1,5], [(3,8),(4,10),(5,6)]))

sys.resolve()
```

---

## Performance considerations

- **Incremental updates**: every constraint supports `moveDelta` so tabu search
  evaluates a candidate move in (usually) O(1)–O(k) time rather than rescanning.
- **Position vs. expression form**: prefer the position-based overload when your
  inputs are bare variables — it skips expression evaluation. Wrappers
  auto-detect this and downgrade pure-reference expressions for you.
- **Penalty maps**: dense `[position][domainIdx]` maps give O(1) total-violation
  deltas; very large domains fall back to on-demand `costDelta` (see
  `src/search/tabu.nim`).
- **Domain reduction**: smaller domains and GAC-safe tables improve search speed.

---

## Integration with search

Crusher's constraints are fully integrated with:
- **Tabu search** — constraint-aware best-move selection via penalty maps.
- **Parallel search** — thread-safe `deepCopy` for per-worker constraint state.
- **Channel propagation** — element/min/max/count_eq derived variables update
  automatically after each move, with channel-dependent penalty maps for indirect
  cost (see `src/constrainedArray.nim` and `src/search/tabuChannelDep.nim`).
- **Optimization** — minimize/maximize via iterative bound tightening.

For implementation details, see the source files in `src/constraints/`.
