# CSPLib prob001: Car Sequencing

- **Source**: https://www.csplib.org/Problems/prob001/
- **Proposed by**: Barbara Smith (1996)
- **Complexity**: NP-complete

## Problem Description

A number of cars are to be produced on an assembly line. Different cars
require different options (e.g., air conditioning, sunroof, etc.). The
assembly line has different stations that install each option. Each station
has a limited capacity: it can only handle a certain fraction of the cars
passing through.

The problem is to determine a production sequence for the cars so that the
capacity constraints of every station are respected.

## Formal Specification

**Given:**
- `n` cars to be sequenced (slots on the assembly line)
- `k` car classes, each with a demand (number of cars of that class)
- `m` options, each with a capacity constraint `p/q` meaning: in any `q`
  consecutive cars, at most `p` can require that option
- A requirement matrix: which classes require which options

**Find:** A sequence of `n` cars (assigning each slot a class) such that:
1. The demand for each class is exactly met
2. For every option with capacity `p/q`, in every window of `q` consecutive
   slots, at most `p` cars require that option

## Instances

### Small (Van Hentenryck, OPL p.184)

10 cars, 6 classes, 5 options. Used in the test and the Picat model.

```
Classes:  1  2  3  4  5  6
Demand:   1  1  2  2  2  2

Option 1 (1/2): classes 1, 5, 6
Option 2 (2/3): classes 3, 4, 6
Option 3 (1/3): classes 1, 5
Option 4 (2/5): classes 1, 2, 4
Option 5 (1/5): class 3
```

### Standard Benchmarks (100 and 200 cars)

The full CSPLib benchmark set contains 79 instances:
- 9 instances with 100 cars (from Regin & Puget, CP97)
- 70 instances with 200 cars (from Caroline Gagne)

Available at: https://www.csplib.org/Problems/prob001/data/

## Models

| File | Language | Notes |
|------|----------|-------|
| `test_car_sequencing.nim` | Crusher/Nim | Tabu search, uses `sequence` + `globalCardinality` constraints |
| `car.pi` | Picat (CP) | From hakank.org, based on Van Hentenryck's OPL model |

## Running

```bash
# Crusher test
nim c -r --threads:on --mm:arc --deepcopy:on -d:release csplib/prob001_car_sequencing/test_car_sequencing.nim

# Picat model (requires Picat installed)
picat csplib/prob001_car_sequencing/car.pi
```
