## Bus Scheduling Problem
##
## From Taha "Introduction to Operations Research", page 58
## Ported from: https://www.hakank.org/picat/bus_schedule.pi
##
## Problem: Schedule buses during a day across 6 time slots.
## Each bus works for 2 consecutive time slots.
## Minimize total number of buses while meeting demand at each slot.
##
## Demands = [8, 10, 7, 12, 4, 4]
## Optimal solution: 26 buses with distribution [0, 8, 2, 5, 7, 4]

import std/[sequtils, strformat]
import ../src/crusher

const
    TimeSlots = 6
    Demands = [8, 10, 7, 12, 4, 4]
    OptimalBuses = 26
    MaxBusesPerSlot = 45  # sum of demands

proc solveBusSchedule() =
    echo "Bus Scheduling Problem (Taha, page 58)"
    echo "======================================"
    echo ""
    echo "Demands per slot: ", Demands
    echo "Each bus works 2 consecutive slots"
    echo ""

    var sys = initConstraintSystem[int]()

    # X[i] = number of buses starting at time slot i
    var X = sys.newConstrainedSequence(TimeSlots)
    X.setDomain(toSeq(0..MaxBusesPerSlot))

    # Coverage constraints: buses from slot i and i+1 cover slot i's demand
    # X[i] + X[i+1] >= Demands[i] for i in 0..4
    for i in 0..<(TimeSlots - 1):
        sys.addConstraint(X[i] + X[i + 1] >= Demands[i])

    # Cyclic constraint: X[5] + X[0] = Demands[5] (around the clock)
    # Note: Picat uses equality here, not >=
    sys.addConstraint(X[TimeSlots - 1] + X[0] == Demands[TimeSlots - 1])

    # Objective: minimize total buses
    var busExprs: seq[AlgebraicExpression[int]] = @[]
    for i in 0..<TimeSlots:
        busExprs.add(X[i])
    let totalBuses = sum(busExprs)

    echo "Starting optimization..."
    echo ""

    sys.minimize(totalBuses, parallel=true, verbose=false)

    let solution = X.assignment
    var total = 0
    for i in 0..<TimeSlots:
        total += solution[i]

    echo "Solution"
    echo "========"
    echo ""
    echo "Buses starting at each slot: ", solution
    echo "Total buses: ", total
    echo ""

    # Verify coverage
    echo "Coverage verification:"
    var valid = true
    for i in 0..<(TimeSlots - 1):
        let coverage = solution[i] + solution[i + 1]
        let ok = coverage >= Demands[i]
        let status = if ok: "OK" else: "FAIL"
        echo fmt"  Slot {i}: {solution[i]} + {solution[i+1]} = {coverage} >= {Demands[i]} {status}"
        if not ok: valid = false

    let wrapCoverage = solution[TimeSlots - 1] + solution[0]
    let wrapOk = wrapCoverage == Demands[TimeSlots - 1]
    let wrapStatus = if wrapOk: "OK" else: "FAIL"
    echo fmt"  Slot {TimeSlots-1} (wrap): {solution[TimeSlots-1]} + {solution[0]} = {wrapCoverage} == {Demands[TimeSlots-1]} {wrapStatus}"
    if not wrapOk: valid = false

    echo ""
    if total == OptimalBuses and valid:
        echo "SUCCESS: Found optimal solution!"
    elif valid:
        echo fmt"Found valid solution with {total} buses (optimal: {OptimalBuses})"
    else:
        echo "FAIL: Solution violates constraints!"

when isMainModule:
    solveBusSchedule()
