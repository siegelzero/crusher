## CSPLib prob016: Traffic Lights
## ===============================
##
## Model a four-way traffic junction with 8 lights: 4 vehicle lights (V1-V4)
## and 4 pedestrian lights (P1-P4). Vehicle lights cycle through
## {red, red-yellow, green, yellow} and pedestrian lights through {red, green}.
##
## For each adjacent pair (Vi, Pi, Vj, Pj) where j = (i+1) mod 4, only these
## combinations are permitted:
##
##   Vi    Pi   Vj    Pj
##   r     r    g     g
##   ry    r    y     r
##   g     g    r     r
##   y     r    ry    r
##
## Encoding: Vehicle lights: r=0, ry=1, g=2, y=3
##           Pedestrian lights: r=0, g=1
##
## Observations that simplify the model:
##   1. Pi is fully determined by Vi: Pi = 1 iff Vi = 2 (green), else Pi = 0
##      -> modeled as element(Vi, [0, 0, 1, 0], Pi)
##   2. Adjacent vehicle lights always differ by exactly 2:
##      -> modeled as abs(Vi - Vj) == 2
##
## There are exactly 4 valid global configurations (one per starting phase).
##
## See: https://www.csplib.org/Problems/prob016/

import std/[sequtils, strutils, unittest]
import crusher

const
    VehicleLabels = ["r", "ry", "g", "y"]
    PedestrianLabels = ["r", "g"]

    # The four allowed tuples for each adjacent pair (Vi, Pi, Vj, Pj)
    AllowedTuples = [
        (0, 0, 2, 1),  # r  r  g  g
        (1, 0, 3, 0),  # ry r  y  r
        (2, 1, 0, 0),  # g  g  r  r
        (3, 0, 1, 0),  # y  r  ry r
    ]

proc solve(tabuThreshold: int = 1000,
           populationSize: int = 16,
           scatterThreshold: int = 1,
           verbose: bool = true): (seq[int], seq[int]) =
    var sys = initConstraintSystem[int]()

    # 4 vehicle lights with domain {r=0, ry=1, g=2, y=3}
    var vehicle = sys.newConstrainedSequence(4)
    vehicle.setDomain(toSeq(0..3))

    # 4 pedestrian lights with domain {r=0, g=1}
    var pedestrian = sys.newConstrainedSequence(4)
    pedestrian.setDomain(@[0, 1])

    # Pedestrian light is determined by vehicle light:
    #   P = 1 (green) iff V = 2 (green), else P = 0 (red)
    let pedMapping = @[0, 0, 1, 0]
    for i in 0..<4:
        sys.addConstraint(element(vehicle[i], pedMapping, pedestrian[i]))

    # Adjacent vehicle lights must differ by exactly 2
    for i in 0..<4:
        let j = (i + 1) mod 4
        sys.addConstraint(abs(vehicle[i] - vehicle[j]) == 2)

    sys.resolve(parallel=true, tabuThreshold=tabuThreshold,
                populationSize=populationSize,
                scatterThreshold=scatterThreshold, verbose=verbose)

    return (vehicle.assignment, pedestrian.assignment)


proc verify(vehicle: seq[int], pedestrian: seq[int]) =
    assert vehicle.len == 4, "Expected 4 vehicle lights"
    assert pedestrian.len == 4, "Expected 4 pedestrian lights"

    # Check domains
    for i in 0..<4:
        assert vehicle[i] in {0, 1, 2, 3},
            "Vehicle light " & $i & " value " & $vehicle[i] & " out of domain"
        assert pedestrian[i] in {0, 1},
            "Pedestrian light " & $i & " value " & $pedestrian[i] & " out of domain"

    # Check each adjacent pair against allowed tuples
    for i in 0..<4:
        let j = (i + 1) mod 4
        let tuple4 = (vehicle[i], pedestrian[i], vehicle[j], pedestrian[j])
        var valid = false
        for allowed in AllowedTuples:
            if tuple4 == allowed:
                valid = true
                break
        assert valid,
            "Invalid pair at lights " & $i & "-" & $j & ": (" &
            VehicleLabels[vehicle[i]] & ", " & PedestrianLabels[pedestrian[i]] & ", " &
            VehicleLabels[vehicle[j]] & ", " & PedestrianLabels[pedestrian[j]] & ")"


proc display(vehicle: seq[int], pedestrian: seq[int]) =
    echo "  Light  Vehicle  Pedestrian"
    for i in 0..<4:
        echo "    ", i+1, "      ", VehicleLabels[vehicle[i]].alignLeft(7),
             PedestrianLabels[pedestrian[i]]


suite "CSPLib prob016: Traffic Lights":

    test "Traffic lights - find valid configuration":
        let (vehicle, pedestrian) = solve()
        display(vehicle, pedestrian)
        verify(vehicle, pedestrian)
        check vehicle.len == 4
        check pedestrian.len == 4
