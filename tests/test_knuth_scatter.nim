import std/[sequtils, unittest]
import crusher

suite "Knuth 1960 IBM 650 (Scatter Search)":
  test "Knuth's integer programming problem":
    var sys = initConstraintSystem[int]()

    var x = sys.newConstrainedSequence(8)
    x.setDomain(toSeq 0..200)

    var t = sys.newConstrainedSequence(29)
    t.setDomain(toSeq 0..20)

    var z = sys.newConstrainedSequence(12)
    z.setDomain(toSeq 0..100)

    var w = sys.newConstrainedSequence(2)
    w.setDomain(toSeq 0..200)

    # 43 constraints
    sys.addConstraint(x[0] + 2 <= 2*z[0])
    sys.addConstraint(50*t[0] + x[1] - 2*z[0] >= 24)
    sys.addConstraint(x[1] + 2 <= 2*z[1])
    sys.addConstraint(50*t[1] - 50*t[0] + x[2] - 2*z[1] >= 5)
    sys.addConstraint(50*t[2] - 50*t[1] - x[2] >= 6)
    sys.addConstraint(50*t[3] - 50*t[2] + x[3] >= 15)
    sys.addConstraint(x[3] + 3 <= 2*z[2])
    sys.addConstraint(50*t[4] - 50*t[3] + x[4] - 2*z[2] >= 4)
    sys.addConstraint(x[4] + 2 <= 2*z[3])
    sys.addConstraint(50*t[5] - 50*t[4] + x[2] - 2*z[3] >= 12)
    sys.addConstraint(x[2] <= 2*z[4] + 1)
    sys.addConstraint(50*t[6] - 50*t[5] + x[5] - 2*z[4] >= 35)
    sys.addConstraint(x[5] <= 2*z[5])
    sys.addConstraint(50*t[7] - 50*t[6] + x[6] - 2*z[5] >= 3)
    sys.addConstraint(50*t[8] - 50*t[7] + x[4] - x[6] >= 10)
    sys.addConstraint(x[4] <= 2*z[6] + 1)
    sys.addConstraint(50*t[9] - 50*t[8] + x[1] - 2*z[6] >= 8)
    sys.addConstraint(50*t[10] - 50*t[9] + x[6] - x[1] >= 3)
    sys.addConstraint(x[6] <= 2*z[7] + 1)
    sys.addConstraint(50*t[11] - 50*t[10] + x[7] - 2*z[7] >= 7)
    sys.addConstraint(50*t[11] - 50*t[10] + x[7] + w[0] - 2*z[7] >= 21)
    sys.addConstraint(x[7] + w[0] <= 2*z[8] + 1)
    sys.addConstraint(50*t[12] - 50*t[11] + x[3] - 2*z[8] >= 35)
    sys.addConstraint(x[3] + 2 <= 2*z[9])
    sys.addConstraint(50*t[13] - 50*t[12] + x[1] - 2*z[9] >= 34)
    sys.addConstraint(50*t[14] - 50*t[13] + x[3] - x[1] >= 6)
    sys.addConstraint(50*t[15] - 50*t[14] + x[7] - 2*z[2] >= 30)
    sys.addConstraint(50*t[16] - 50*t[15] + x[2] - 2*z[8] >= 8)
    sys.addConstraint(50*t[17] - 50*t[16] + x[1] - 2*z[4] >= 34)
    sys.addConstraint(x[1] <= 2*z[10] + 1)
    sys.addConstraint(50*t[18] - 50*t[17] - 2*z[10] >= 9)
    sys.addConstraint(50*t[19] - 50*t[18] + x[0] >= 9)
    sys.addConstraint(50*t[20] - 50*t[7] + x[1] - x[6] >= 9)
    sys.addConstraint(50*t[21] - 50*t[20] + x[3] - 2*z[10] >= 8)
    sys.addConstraint(50*t[22] - 50*t[21] + x[2] - x[3] >= 6)
    sys.addConstraint(50*t[23] - 50*t[22] + x[4] - x[2] >= 6)
    sys.addConstraint(50*t[24] - 50*t[23] + x[6] - x[4] >= 3)
    sys.addConstraint(50*t[25] - 50*t[5] + x[5] - 2*z[4] >= 21)
    sys.addConstraint(50*t[11] - 50*t[10] + x[7] + w[1] - 2*z[7] >= 24)
    sys.addConstraint(x[7] + w[1] <= 2*z[11] + 1)
    sys.addConstraint(50*t[6] - 50*t[11] - 50*t[25] + 50*t[26] + x[3] - 2*z[11] >= 35)
    sys.addConstraint(50*t[27] - 50*t[11] - 2*z[8] >= 15)
    sys.addConstraint(50*t[28] - 50*t[27] + x[0] >= 3)

    # Use scatter search to find a feasible solution
    sys.scatterResolve(poolSize = 10, iterations = 10, tabuThreshold = 1000,
                       relinkThreshold = 500, verbose = true)

    let xSol = x.assignment()
    let tSol = t.assignment()
    let zSol = z.assignment()
    let wSol = w.assignment()

    # All variables must be nonnegative
    for v in xSol: check v >= 0
    for v in tSol: check v >= 0
    for v in zSol: check v >= 0
    for v in wSol: check v >= 0

    # Verify all 43 constraints
    check xSol[0] + 2 <= 2*zSol[0]
    check 50*tSol[0] + xSol[1] - 2*zSol[0] >= 24
    check xSol[1] + 2 <= 2*zSol[1]
    check 50*tSol[1] - 50*tSol[0] + xSol[2] - 2*zSol[1] >= 5
    check 50*tSol[2] - 50*tSol[1] - xSol[2] >= 6
    check 50*tSol[3] - 50*tSol[2] + xSol[3] >= 15
    check xSol[3] + 3 <= 2*zSol[2]
    check 50*tSol[4] - 50*tSol[3] + xSol[4] - 2*zSol[2] >= 4
    check xSol[4] + 2 <= 2*zSol[3]
    check 50*tSol[5] - 50*tSol[4] + xSol[2] - 2*zSol[3] >= 12
    check xSol[2] <= 2*zSol[4] + 1
    check 50*tSol[6] - 50*tSol[5] + xSol[5] - 2*zSol[4] >= 35
    check xSol[5] <= 2*zSol[5]
    check 50*tSol[7] - 50*tSol[6] + xSol[6] - 2*zSol[5] >= 3
    check 50*tSol[8] - 50*tSol[7] + xSol[4] - xSol[6] >= 10
    check xSol[4] <= 2*zSol[6] + 1
    check 50*tSol[9] - 50*tSol[8] + xSol[1] - 2*zSol[6] >= 8
    check 50*tSol[10] - 50*tSol[9] + xSol[6] - xSol[1] >= 3
    check xSol[6] <= 2*zSol[7] + 1
    check 50*tSol[11] - 50*tSol[10] + xSol[7] - 2*zSol[7] >= 7
    check 50*tSol[11] - 50*tSol[10] + xSol[7] + wSol[0] - 2*zSol[7] >= 21
    check xSol[7] + wSol[0] <= 2*zSol[8] + 1
    check 50*tSol[12] - 50*tSol[11] + xSol[3] - 2*zSol[8] >= 35
    check xSol[3] + 2 <= 2*zSol[9]
    check 50*tSol[13] - 50*tSol[12] + xSol[1] - 2*zSol[9] >= 34
    check 50*tSol[14] - 50*tSol[13] + xSol[3] - xSol[1] >= 6
    check 50*tSol[15] - 50*tSol[14] + xSol[7] - 2*zSol[2] >= 30
    check 50*tSol[16] - 50*tSol[15] + xSol[2] - 2*zSol[8] >= 8
    check 50*tSol[17] - 50*tSol[16] + xSol[1] - 2*zSol[4] >= 34
    check xSol[1] <= 2*zSol[10] + 1
    check 50*tSol[18] - 50*tSol[17] - 2*zSol[10] >= 9
    check 50*tSol[19] - 50*tSol[18] + xSol[0] >= 9
    check 50*tSol[20] - 50*tSol[7] + xSol[1] - xSol[6] >= 9
    check 50*tSol[21] - 50*tSol[20] + xSol[3] - 2*zSol[10] >= 8
    check 50*tSol[22] - 50*tSol[21] + xSol[2] - xSol[3] >= 6
    check 50*tSol[23] - 50*tSol[22] + xSol[4] - xSol[2] >= 6
    check 50*tSol[24] - 50*tSol[23] + xSol[6] - xSol[4] >= 3
    check 50*tSol[25] - 50*tSol[5] + xSol[5] - 2*zSol[4] >= 21
    check 50*tSol[11] - 50*tSol[10] + xSol[7] + wSol[1] - 2*zSol[7] >= 24
    check xSol[7] + wSol[1] <= 2*zSol[11] + 1
    check 50*tSol[6] - 50*tSol[11] - 50*tSol[25] + 50*tSol[26] + xSol[3] - 2*zSol[11] >= 35
    check 50*tSol[27] - 50*tSol[11] - 2*zSol[8] >= 15
    check 50*tSol[28] - 50*tSol[27] + xSol[0] >= 3

    let objVal = 44*xSol[0] + 2100*tSol[19] - 550*tSol[10] +
                 550*tSol[24] - 100*tSol[12] + 100*tSol[26] + 100*tSol[28]
    echo "Objective value: ", objVal
    echo "x = ", xSol
    echo "t = ", tSol
    echo "z = ", zSol
    echo "w = ", wSol
    check objVal > 0
