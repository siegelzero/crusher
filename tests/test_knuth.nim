import std/[sequtils, unittest]
import crusher

suite "Knuth 1960 IBM 650 Drum Latency":
  test "Knuth's integer programming problem":
    # Knuth's 1960 integer program for minimizing memory access latency
    # on the IBM 650 drum computer. 51 integer variables, 43 constraints.
    # The drum has 50 word positions; the problem arranges data/instructions
    # to minimize total rotational latency across multiple access patterns.
    # See: https://www-cs-faculty.stanford.edu/~knuth/papers/prob.tex

    var sys = initConstraintSystem[int]()

    # x_2..x_9: drum positions (8 vars)
    var x = sys.newConstrainedSequence(8)
    x.setDomain(toSeq 0..200)

    # t_2..t_30: cumulative rotation counts (29 vars)
    var t = sys.newConstrainedSequence(29)
    t.setDomain(toSeq 0..20)

    # z_1..z_12: auxiliary linking variables (12 vars)
    var z = sys.newConstrainedSequence(12)
    z.setDomain(toSeq 0..100)

    # w_1, w_2: auxiliary offset variables (2 vars)
    var w = sys.newConstrainedSequence(2)
    w.setDomain(toSeq 0..200)

    # Index mapping:
    #   x_i -> x[i-2]   (i = 2..9)
    #   t_i -> t[i-2]   (i = 2..30)
    #   z_i -> z[i-1]   (i = 1..12)
    #   w_i -> w[i-1]   (i = 1..2)

    # --- 43 Constraints from Knuth's MPS formulation ---

    # c1: x_2 + 2 <= 2*z_1
    sys.addConstraint(x[0] + 2 <= 2*z[0])
    # c2: 50*t_2 + x_3 - 2*z_1 >= 24
    sys.addConstraint(50*t[0] + x[1] - 2*z[0] >= 24)
    # c3: x_3 + 2 <= 2*z_2
    sys.addConstraint(x[1] + 2 <= 2*z[1])
    # c4: 50*(t_3 - t_2) + x_4 - 2*z_2 >= 5
    sys.addConstraint(50*t[1] - 50*t[0] + x[2] - 2*z[1] >= 5)
    # c5: 50*(t_4 - t_3) - x_4 >= 6
    sys.addConstraint(50*t[2] - 50*t[1] - x[2] >= 6)
    # c6: 50*(t_5 - t_4) + x_5 >= 15
    sys.addConstraint(50*t[3] - 50*t[2] + x[3] >= 15)
    # c7: x_5 + 3 <= 2*z_3
    sys.addConstraint(x[3] + 3 <= 2*z[2])
    # c8: 50*(t_6 - t_5) + x_6 - 2*z_3 >= 4
    sys.addConstraint(50*t[4] - 50*t[3] + x[4] - 2*z[2] >= 4)
    # c9: x_6 + 2 <= 2*z_4
    sys.addConstraint(x[4] + 2 <= 2*z[3])
    # c10: 50*(t_7 - t_6) + x_4 - 2*z_4 >= 12
    sys.addConstraint(50*t[5] - 50*t[4] + x[2] - 2*z[3] >= 12)
    # c11: x_4 <= 2*z_5 + 1
    sys.addConstraint(x[2] <= 2*z[4] + 1)
    # c12: 50*(t_8 - t_7) + x_7 - 2*z_5 >= 35
    sys.addConstraint(50*t[6] - 50*t[5] + x[5] - 2*z[4] >= 35)
    # c13: x_7 <= 2*z_6
    sys.addConstraint(x[5] <= 2*z[5])
    # c14: 50*(t_9 - t_8) + x_8 - 2*z_6 >= 3
    sys.addConstraint(50*t[7] - 50*t[6] + x[6] - 2*z[5] >= 3)
    # c15: 50*(t_10 - t_9) + x_6 - x_8 >= 10
    sys.addConstraint(50*t[8] - 50*t[7] + x[4] - x[6] >= 10)
    # c16: x_6 <= 2*z_7 + 1
    sys.addConstraint(x[4] <= 2*z[6] + 1)
    # c17: 50*(t_11 - t_10) + x_3 - 2*z_7 >= 8
    sys.addConstraint(50*t[9] - 50*t[8] + x[1] - 2*z[6] >= 8)
    # c18: 50*(t_12 - t_11) + x_8 - x_3 >= 3
    sys.addConstraint(50*t[10] - 50*t[9] + x[6] - x[1] >= 3)
    # c19: x_8 <= 2*z_8 + 1
    sys.addConstraint(x[6] <= 2*z[7] + 1)
    # c20: 50*(t_13 - t_12) + x_9 - 2*z_8 >= 7
    sys.addConstraint(50*t[11] - 50*t[10] + x[7] - 2*z[7] >= 7)
    # c21: 50*(t_13 - t_12) + x_9 + w_1 - 2*z_8 >= 21
    sys.addConstraint(50*t[11] - 50*t[10] + x[7] + w[0] - 2*z[7] >= 21)
    # c22: x_9 + w_1 <= 2*z_9 + 1
    sys.addConstraint(x[7] + w[0] <= 2*z[8] + 1)
    # c23: 50*(t_14 - t_13) + x_5 - 2*z_9 >= 35
    sys.addConstraint(50*t[12] - 50*t[11] + x[3] - 2*z[8] >= 35)
    # c24: x_5 + 2 <= 2*z_10
    sys.addConstraint(x[3] + 2 <= 2*z[9])
    # c25: 50*(t_15 - t_14) + x_3 - 2*z_10 >= 34
    sys.addConstraint(50*t[13] - 50*t[12] + x[1] - 2*z[9] >= 34)
    # c26: 50*(t_16 - t_15) + x_5 - x_3 >= 6
    sys.addConstraint(50*t[14] - 50*t[13] + x[3] - x[1] >= 6)
    # c27: 50*(t_17 - t_16) + x_9 - 2*z_3 >= 30
    sys.addConstraint(50*t[15] - 50*t[14] + x[7] - 2*z[2] >= 30)
    # c28: 50*(t_18 - t_17) + x_4 - 2*z_9 >= 8
    sys.addConstraint(50*t[16] - 50*t[15] + x[2] - 2*z[8] >= 8)
    # c29: 50*(t_19 - t_18) + x_3 - 2*z_5 >= 34
    sys.addConstraint(50*t[17] - 50*t[16] + x[1] - 2*z[4] >= 34)
    # c30: x_3 <= 2*z_11 + 1
    sys.addConstraint(x[1] <= 2*z[10] + 1)
    # c31: 50*(t_20 - t_19) - 2*z_11 >= 9
    sys.addConstraint(50*t[18] - 50*t[17] - 2*z[10] >= 9)
    # c32: 50*(t_21 - t_20) + x_2 >= 9
    sys.addConstraint(50*t[19] - 50*t[18] + x[0] >= 9)
    # c33: 50*(t_22 - t_9) + x_3 - x_8 >= 9
    sys.addConstraint(50*t[20] - 50*t[7] + x[1] - x[6] >= 9)
    # c34: 50*(t_23 - t_22) + x_5 - 2*z_11 >= 8
    sys.addConstraint(50*t[21] - 50*t[20] + x[3] - 2*z[10] >= 8)
    # c35: 50*(t_24 - t_23) + x_4 - x_5 >= 6
    sys.addConstraint(50*t[22] - 50*t[21] + x[2] - x[3] >= 6)
    # c36: 50*(t_25 - t_24) + x_6 - x_4 >= 6
    sys.addConstraint(50*t[23] - 50*t[22] + x[4] - x[2] >= 6)
    # c37: 50*(t_26 - t_25) + x_8 - x_6 >= 3
    sys.addConstraint(50*t[24] - 50*t[23] + x[6] - x[4] >= 3)
    # c38: 50*(t_27 - t_7) + x_7 - 2*z_5 >= 21
    sys.addConstraint(50*t[25] - 50*t[5] + x[5] - 2*z[4] >= 21)
    # c39: 50*(t_13 - t_12) + x_9 + w_2 - 2*z_8 >= 24
    sys.addConstraint(50*t[11] - 50*t[10] + x[7] + w[1] - 2*z[7] >= 24)
    # c40: x_9 + w_2 <= 2*z_12 + 1
    sys.addConstraint(x[7] + w[1] <= 2*z[11] + 1)
    # c41: 50*(t_8 - t_13 - t_27 + t_28) + x_5 - 2*z_12 >= 35
    sys.addConstraint(50*t[6] - 50*t[11] - 50*t[25] + 50*t[26] + x[3] - 2*z[11] >= 35)
    # c42: 50*(t_29 - t_13) - 2*z_9 >= 15
    sys.addConstraint(50*t[27] - 50*t[11] - 2*z[8] >= 15)
    # c43: 50*(t_30 - t_29) + x_2 >= 3
    sys.addConstraint(50*t[28] - 50*t[27] + x[0] >= 3)

    # Objective: minimize total drum access time
    # = 30(50*t_21 + x_2) + 10(50*(t_21+t_26-t_12) + x_2)
    #   + (50*(t_21+t_28-t_14) + x_2) + (50*(t_21+t_26-t_12+t_28-t_14) + x_2)
    #   + 2(50*t_30 + x_2)
    # Expanded: 44*x_2 + 2100*t_21 - 550*t_12 + 550*t_26 - 100*t_14
    #           + 100*t_28 + 100*t_30
    let obj = 44*x[0] + 2100*t[19] - 550*t[10] + 550*t[24] - 100*t[12] + 100*t[26] + 100*t[28]

    sys.minimize(obj, parallel=true, tabuThreshold=1000, verbose=true)

    # Extract solution
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
    check xSol[0] + 2 <= 2*zSol[0]                                                          # c1
    check 50*tSol[0] + xSol[1] - 2*zSol[0] >= 24                                           # c2
    check xSol[1] + 2 <= 2*zSol[1]                                                          # c3
    check 50*tSol[1] - 50*tSol[0] + xSol[2] - 2*zSol[1] >= 5                               # c4
    check 50*tSol[2] - 50*tSol[1] - xSol[2] >= 6                                           # c5
    check 50*tSol[3] - 50*tSol[2] + xSol[3] >= 15                                          # c6
    check xSol[3] + 3 <= 2*zSol[2]                                                          # c7
    check 50*tSol[4] - 50*tSol[3] + xSol[4] - 2*zSol[2] >= 4                               # c8
    check xSol[4] + 2 <= 2*zSol[3]                                                          # c9
    check 50*tSol[5] - 50*tSol[4] + xSol[2] - 2*zSol[3] >= 12                              # c10
    check xSol[2] <= 2*zSol[4] + 1                                                          # c11
    check 50*tSol[6] - 50*tSol[5] + xSol[5] - 2*zSol[4] >= 35                              # c12
    check xSol[5] <= 2*zSol[5]                                                              # c13
    check 50*tSol[7] - 50*tSol[6] + xSol[6] - 2*zSol[5] >= 3                               # c14
    check 50*tSol[8] - 50*tSol[7] + xSol[4] - xSol[6] >= 10                                # c15
    check xSol[4] <= 2*zSol[6] + 1                                                          # c16
    check 50*tSol[9] - 50*tSol[8] + xSol[1] - 2*zSol[6] >= 8                               # c17
    check 50*tSol[10] - 50*tSol[9] + xSol[6] - xSol[1] >= 3                                # c18
    check xSol[6] <= 2*zSol[7] + 1                                                          # c19
    check 50*tSol[11] - 50*tSol[10] + xSol[7] - 2*zSol[7] >= 7                             # c20
    check 50*tSol[11] - 50*tSol[10] + xSol[7] + wSol[0] - 2*zSol[7] >= 21                  # c21
    check xSol[7] + wSol[0] <= 2*zSol[8] + 1                                               # c22
    check 50*tSol[12] - 50*tSol[11] + xSol[3] - 2*zSol[8] >= 35                            # c23
    check xSol[3] + 2 <= 2*zSol[9]                                                          # c24
    check 50*tSol[13] - 50*tSol[12] + xSol[1] - 2*zSol[9] >= 34                            # c25
    check 50*tSol[14] - 50*tSol[13] + xSol[3] - xSol[1] >= 6                               # c26
    check 50*tSol[15] - 50*tSol[14] + xSol[7] - 2*zSol[2] >= 30                            # c27
    check 50*tSol[16] - 50*tSol[15] + xSol[2] - 2*zSol[8] >= 8                             # c28
    check 50*tSol[17] - 50*tSol[16] + xSol[1] - 2*zSol[4] >= 34                            # c29
    check xSol[1] <= 2*zSol[10] + 1                                                         # c30
    check 50*tSol[18] - 50*tSol[17] - 2*zSol[10] >= 9                                      # c31
    check 50*tSol[19] - 50*tSol[18] + xSol[0] >= 9                                         # c32
    check 50*tSol[20] - 50*tSol[7] + xSol[1] - xSol[6] >= 9                                # c33
    check 50*tSol[21] - 50*tSol[20] + xSol[3] - 2*zSol[10] >= 8                            # c34
    check 50*tSol[22] - 50*tSol[21] + xSol[2] - xSol[3] >= 6                               # c35
    check 50*tSol[23] - 50*tSol[22] + xSol[4] - xSol[2] >= 6                               # c36
    check 50*tSol[24] - 50*tSol[23] + xSol[6] - xSol[4] >= 3                               # c37
    check 50*tSol[25] - 50*tSol[5] + xSol[5] - 2*zSol[4] >= 21                             # c38
    check 50*tSol[11] - 50*tSol[10] + xSol[7] + wSol[1] - 2*zSol[7] >= 24                  # c39
    check xSol[7] + wSol[1] <= 2*zSol[11] + 1                                              # c40
    check 50*tSol[6] - 50*tSol[11] - 50*tSol[25] + 50*tSol[26] + xSol[3] - 2*zSol[11] >= 35  # c41
    check 50*tSol[27] - 50*tSol[11] - 2*zSol[8] >= 15                                      # c42
    check 50*tSol[28] - 50*tSol[27] + xSol[0] >= 3                                         # c43

    # Compute and report objective value
    let objVal = 44*xSol[0] + 2100*tSol[19] - 550*tSol[10] +
                 550*tSol[24] - 100*tSol[12] + 100*tSol[26] + 100*tSol[28]
    echo "Objective value: ", objVal
    echo "x = ", xSol
    echo "t = ", tSol
    echo "z = ", zSol
    echo "w = ", wSol
    check objVal > 0
