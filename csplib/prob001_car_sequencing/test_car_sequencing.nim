## CSPLib prob001: Car Sequencing
## ================================
##
## Sequence cars on an assembly line so that station capacity constraints
## are respected. Each car class requires certain options; each option's
## station can handle at most p out of q consecutive cars.
##
## Model:
##   - Decision variables: slots[0..n-1], domain = car classes (1..k)
##   - Demand: globalCardinality ensures exact class counts
##   - Capacity: sequence constraint per option (at most p in any q consecutive)
##
## See: https://www.csplib.org/Problems/prob001/

import std/[sequtils, unittest]
import crusher

type
  CarSeqInstance = object
    name: string
    nSlots: int       # total cars to produce
    nClasses: int     # number of car classes
    nOptions: int     # number of options
    demand: seq[int]  # demand[c] = how many cars of class c (0-indexed)
    options: seq[seq[int]]  # options[o][c] = 1 if class c requires option o
    capacity: seq[array[2, int]]  # capacity[o] = [maxInWindow, windowSize]

proc solve(inst: CarSeqInstance,
           tabuThreshold: int = 500,
           populationSize: int = 16,
           scatterThreshold: int = 10): seq[int] =
  var sys = initConstraintSystem[int]()
  var slots = sys.newConstrainedSequence(inst.nSlots)
  slots.setDomain(toSeq(1..inst.nClasses))

  let positions = toSeq(0..<inst.nSlots)

  # Demand: exactly demand[c] cars of class (c+1)
  sys.addConstraint(globalCardinality[int](
    positions,
    toSeq(1..inst.nClasses),
    inst.demand
  ))

  # Capacity: for each option, at most p in any window of q consecutive slots
  for o in 0..<inst.nOptions:
    var targetClasses: seq[int] = @[]
    for c in 0..<inst.nClasses:
      if inst.options[o][c] == 1:
        targetClasses.add(c + 1)

    if targetClasses.len > 0:
      sys.addConstraint(sequence[int](
        positions,
        0,                      # minInSet
        inst.capacity[o][0],    # maxInSet (p)
        inst.capacity[o][1],    # windowSize (q)
        targetClasses
      ))

  sys.resolve(parallel=true, verbose=true, tabuThreshold=tabuThreshold,
              populationSize=populationSize, scatterThreshold=scatterThreshold)
  return slots.assignment

proc verify(inst: CarSeqInstance, assignment: seq[int]) =
  # Check demand
  for c in 1..inst.nClasses:
    var count = 0
    for v in assignment:
      if v == c: count += 1
    assert count == inst.demand[c-1],
      "Class " & $c & ": expected " & $inst.demand[c-1] & " got " & $count

  # Check capacity constraints
  for o in 0..<inst.nOptions:
    var targetClasses: seq[int] = @[]
    for c in 0..<inst.nClasses:
      if inst.options[o][c] == 1:
        targetClasses.add(c + 1)

    let p = inst.capacity[o][0]
    let q = inst.capacity[o][1]
    for i in 0..(inst.nSlots - q):
      var count = 0
      for j in 0..<q:
        if assignment[i + j] in targetClasses:
          count += 1
      assert count <= p,
        "Option " & $o & " violated at position " & $i &
        ": " & $count & " > " & $p & " in window of " & $q


# ============================================================================
# Instances
# ============================================================================

# Small instance from Van Hentenryck, "The OPL Optimization Programming
# Language", p.184. Also used in the CSPLib Picat model (car.pi).
let small = CarSeqInstance(
  name: "Van Hentenryck (OPL p.184)",
  nSlots: 10,
  nClasses: 6,
  nOptions: 5,
  demand: @[1, 1, 2, 2, 2, 2],
  options: @[
    @[1, 0, 0, 0, 1, 1],  # option 0: classes 1, 5, 6
    @[0, 0, 1, 1, 0, 1],  # option 1: classes 3, 4, 6
    @[1, 0, 0, 0, 1, 0],  # option 2: classes 1, 5
    @[1, 1, 0, 1, 0, 0],  # option 3: classes 1, 2, 4
    @[0, 0, 1, 0, 0, 0],  # option 4: class 3
  ],
  capacity: @[
    [1, 2],  # option 0: at most 1 in 2 consecutive
    [2, 3],  # option 1: at most 2 in 3 consecutive
    [1, 3],  # option 2: at most 1 in 3 consecutive
    [2, 5],  # option 3: at most 2 in 5 consecutive
    [1, 5],  # option 4: at most 1 in 5 consecutive
  ]
)


# ============================================================================
# Tests
# ============================================================================

suite "CSPLib prob001: Car Sequencing":

  test "Small instance (10 cars, 6 classes)":
    let assignment = solve(small)
    echo "Solution: ", assignment
    verify(small, assignment)
    check assignment.len == small.nSlots
