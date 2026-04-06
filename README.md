# Crusher

Crusher is a parallel tabu-search constraint solver written in [Nim](https://nim-lang.org/). It uses local-search metaheuristics (not backtracking) to solve constraint satisfaction and optimization problems. It can be used as a native Nim library or as a FlatZinc backend for [MiniZinc](https://www.minizinc.org/).

## Features

- **Tabu search** with penalty maps for O(1) move evaluation
- **Parallel search** across multiple worker threads with scatter search and path relinking
- **FlatZinc interface** (`fzcrusher`) that plugs into the MiniZinc toolchain
- **40+ global constraints** including allDifferent, cumulative, circuit, diffn, regular, table, geost, and more
- **Channel variables** (element, min/max, count_eq) that propagate automatically, with channel-dependent penalty maps for indirect cost reasoning
- **Algebraic expressions** for objectives: linear sums, piecewise-linear, min/max, weighted-same-value
- **Pattern detection** in the FlatZinc translator to recover global constraints from decomposed models (reification chains, implication-to-table, element-to-inverse, etc.)
- **Optimization** via iterative bound tightening with minimize/maximize support

## Requirements

- **Nim** >= 2.2 (tested with 2.2.6)
- **MiniZinc** (optional, for `.mzn` model compilation and `mztest`)

## Building

```bash
make fzcrusher    # Build the FlatZinc solver binary
make test         # Compile and run all tests
make mztest       # Run MiniZinc integration tests (requires minizinc CLI)
```

All targets compile with `nim c --threads:on --mm:arc --deepcopy:on -d:release`.

## Usage

### As a FlatZinc solver

```bash
# Solve a FlatZinc file with a 30-second time limit
./fzcrusher --time-limit 30000 problem.fzn

# Parallel with 8 workers, verbose output, statistics
./fzcrusher -p 8 -v -s --time-limit 60000 problem.fzn

# Fast mode (lower tabu threshold for quicker convergence)
./fzcrusher -f --time-limit 10000 problem.fzn
```

**Always pass `--time-limit <ms>`** to avoid unbounded runs. The time limit is in milliseconds.

| Flag | Description |
|------|-------------|
| `-p <N>` | Number of parallel workers (0 = auto) |
| `-v` | Verbose output to stderr |
| `-s` | Print solve statistics |
| `-t <ms>`, `--time-limit <ms>` | Time limit in milliseconds |
| `--tabu <N>` | Tabu threshold (default 10000) |
| `-f` | Fast mode (threshold = 1000) |
| `-a` | All solutions mode |

### With MiniZinc

Crusher registers as a MiniZinc solver backend. Point MiniZinc at the solver configuration:

```bash
minizinc --solver minizinc/crusher.msc model.mzn data.dzn --time-limit 30000
```

### As a Nim library

```nim
import std/sequtils
import crusher

# Latin Square: each row and column contains every value exactly once
proc latinSquare(n: int) =
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    X.setDomain(toSeq(0..<n))

    for row in X.rows():
        sys.addConstraint(allDifferent(row))

    for col in X.columns():
        sys.addConstraint(allDifferent(col))

    # Fix first row and column to break symmetry
    for i in 0..<n:
        sys.addConstraint(X[0, i] == i)
        sys.addConstraint(X[i, 0] == i)

    sys.resolve(parallel=true, verbose=true)
    echo X
```

More examples are in the `models/` directory (magic squares, Latin squares, Langford sequences, employee scheduling, knapsack, MIP, etc.).

## Project Structure

```
src/
  fzcrusher.nim              # CLI entry point for FlatZinc solver
  crusher.nim                # Library re-exports
  constraintSystem.nim       # Top-level ConstraintSystem[T] container
  constrainedArray.nim       # Constraint/domain/channel management
  utils.nim                  # Shared utilities
  constraints/               # 40+ constraint implementations
    types.nim                #   Discriminated union of all constraint types
    stateful.nim             #   Dispatch for moveDelta, penalty, deepCopy, etc.
    allDifferent.nim, circuit.nim, cumulative.nim, diffn.nim,
    regular.nim, tableConstraint.nim, geost.nim, ...
  search/                    # Search algorithms
    tabu.nim                 #   Core tabu search with penalty maps
    tabuChannelDep.nim       #   Channel-dependent penalty computation
    resolution.nim           #   Top-level solve dispatch
    optimization.nim         #   Minimize/maximize with bound tightening
    parallelResolution.nim   #   Multi-worker parallel search
    scatterSearch.nim        #   Path relinking and LNS intensification
  expressions/               # Algebraic objective function trees
    sumExpression.nim, minExpression.nim, maxExpression.nim,
    piecewiseLinear.nim, weightedSameValue.nim, ...
  flatzinc/                  # FlatZinc frontend
    parser.nim               #   .fzn file parser
    translator.nim           #   FlatZinc-to-ConstraintSystem translation
    translatorChannels.nim   #   Channel variable detection
    translatorPatterns.nim   #   Pattern detection (reification, tables, etc.)
    output.nim               #   Solution output formatting
tests/                       # ~90 test files compiled via test_all.nim
models/                      # Example models using the Nim API
minizinc/                    # MiniZinc solver config and library overrides
csplib/                      # CSPLib benchmark problem instances
```

## How It Works

Crusher solves problems through **tabu search**, a local-search metaheuristic:

1. **Parse** a FlatZinc file (or build a `ConstraintSystem` directly in Nim)
2. **Translate** FlatZinc constraints into internal global constraints, detecting patterns to recover structure lost during MiniZinc's decomposition
3. **Initialize** dense penalty maps (`[position][domainIdx]`) giving the total constraint violation delta for each possible variable assignment
4. **Search** by iteratively selecting the best non-tabu move (variable assignment that most reduces total penalty), using O(1) lookup from penalty maps
5. **Channel propagation** automatically updates derived variables (element, min/max, count_eq bindings) after each move, with channel-dependent penalty maps capturing indirect costs
6. **Parallel workers** explore different neighborhoods simultaneously; scatter search combines promising solutions via path relinking

The solver reports `UNKNOWN` (not `UNSAT`) when no solution is found, since local search cannot prove unsatisfiability.

## Constraint Reference

See [CONSTRAINTS.md](CONSTRAINTS.md) for detailed documentation of all supported global constraints.

