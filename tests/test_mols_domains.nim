import std/[packedsets, sequtils, unittest]
import crusher

proc buildMOLSSystem(n: int): (ConstraintSystem[int], ConstrainedMatrix[int],
                                ConstrainedMatrix[int], ConstrainedMatrix[int]) =
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    var Y = sys.newConstrainedMatrix(n, n)
    var Z = sys.newConstrainedMatrix(n, n)

    X.setDomain(toSeq(0..<n))
    Y.setDomain(toSeq(0..<n))
    Z.setDomain(toSeq(0..<n))

    for row in X.rows():
        sys.addConstraint(allDifferent(row))
    for row in Y.rows():
        sys.addConstraint(allDifferent(row))
    for row in Z.rows():
        sys.addConstraint(allDifferent(row))
    for col in X.columns():
        sys.addConstraint(allDifferent(col))
    for col in Y.columns():
        sys.addConstraint(allDifferent(col))
    for col in Z.columns():
        sys.addConstraint(allDifferent(col))

    for i in 0..<n:
        sys.addConstraint(X[0, i] == i)
        sys.addConstraint(X[i, 0] == i)
        sys.addConstraint(Y[0, i] == i)
    for i in 1..<n:
        sys.addConstraint(Y[i, 0] <= i + 1)
        sys.addConstraint(Y[i, 0] != i)

    for i in 0..<n:
        for j in 0..<n:
            sys.addConstraint(matrixElement(Z, i, X[i, j], Y[i, j]))

    return (sys, X, Y, Z)

proc pos(m: ConstrainedMatrix[int], i, j: int): int =
    m.offset + i * m.n + j

suite "MOLS Domain Reduction":
    test "Symmetry breaking fixes X first row and column":
        let (sys, X, _, _) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        for i in 0..<5:
            check reduced[X.pos(0, i)] == @[i]
            check reduced[X.pos(i, 0)] == @[i]

    test "Symmetry breaking fixes Y first row":
        let (sys, _, Y, _) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        for i in 0..<5:
            check reduced[Y.pos(0, i)] == @[i]

    test "MatrixElement propagation fixes Z first row":
        let (sys, _, _, Z) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        for i in 0..<5:
            check reduced[Z.pos(0, i)] == @[i]

    test "AllDifferent + inequality forces Y[1,0] = 2":
        let (sys, _, Y, _) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        check reduced[Y.pos(1, 0)] == @[2]

    test "MatrixElement propagates Y[1,0]=2 to Z[1,1]=2":
        let (sys, _, _, Z) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        check reduced[Z.pos(1, 1)] == @[2]

    test "Y first column reduced by allDifferent + bounds":
        let (sys, _, Y, _) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        check reduced[Y.pos(2, 0)].len == 2
        check 1 in reduced[Y.pos(2, 0)]
        check 3 in reduced[Y.pos(2, 0)]
        check reduced[Y.pos(3, 0)].len == 2
        check 1 in reduced[Y.pos(3, 0)]
        check 4 in reduced[Y.pos(3, 0)]

    test "Z diagonal mirrors Y first column":
        let (sys, _, _, Z) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        check reduced[Z.pos(2, 2)].len == 2
        check 1 in reduced[Z.pos(2, 2)]
        check 3 in reduced[Z.pos(2, 2)]
        check reduced[Z.pos(3, 3)].len == 2
        check 1 in reduced[Z.pos(3, 3)]
        check 4 in reduced[Z.pos(3, 3)]

    test "Overall reduction is significant":
        let (sys, _, _, _) = buildMOLSSystem(5)
        let reduced = reduceDomain(sys.baseArray)
        var totalOriginal, totalReduced: int
        for pos in sys.baseArray.allPositions():
            totalOriginal += sys.baseArray.domain[pos].len
            totalReduced += reduced[pos].len
        let pctReduction = 100 - totalReduced * 100 div totalOriginal
        check pctReduction >= 40

    test "Domain reduction works for n=4":
        let (sys, X, Y, Z) = buildMOLSSystem(4)
        let reduced = reduceDomain(sys.baseArray)
        for i in 0..<4:
            check reduced[X.pos(0, i)] == @[i]
            check reduced[X.pos(i, 0)] == @[i]
            check reduced[Y.pos(0, i)] == @[i]
            check reduced[Z.pos(0, i)] == @[i]
        check reduced[Y.pos(1, 0)] == @[2]
        check reduced[Z.pos(1, 1)] == @[2]

suite "MOLS Fixed Constraint Removal":
    test "Singleton positions excluded from search":
        var (sys, X, Y, Z) = buildMOLSSystem(5)
        sys.baseArray.reducedDomain = reduceDomain(sys.baseArray)
        sys.baseArray.removeFixedConstraints()

        # Known singletons: X[0,*], X[*,0], Y[0,*], Z[0,*], Y[1,0], Z[1,1]
        var searchPositions: PackedSet[int]
        for pos in sys.baseArray.allSearchPositions():
            searchPositions.incl(pos)

        # X first row and column are fixed
        for i in 0..<5:
            check X.pos(0, i) notin searchPositions
            check X.pos(i, 0) notin searchPositions
        # Y first row is fixed
        for i in 0..<5:
            check Y.pos(0, i) notin searchPositions
        # Z first row is fixed
        for i in 0..<5:
            check Z.pos(0, i) notin searchPositions
        # Y[1,0] and Z[1,1] are fixed
        check Y.pos(1, 0) notin searchPositions
        check Z.pos(1, 1) notin searchPositions

    test "All-singleton constraints removed":
        var (sys, _, _, _) = buildMOLSSystem(5)
        sys.baseArray.reducedDomain = reduceDomain(sys.baseArray)
        let constraintsBefore = sys.baseArray.constraints.len
        sys.baseArray.removeFixedConstraints()
        let constraintsAfter = sys.baseArray.constraints.len
        check constraintsAfter < constraintsBefore

    test "Mixed constraints preserved":
        var (sys, _, _, _) = buildMOLSSystem(5)
        sys.baseArray.reducedDomain = reduceDomain(sys.baseArray)
        sys.baseArray.removeFixedConstraints()
        # There should still be constraints left (mixed ones with non-fixed positions)
        check sys.baseArray.constraints.len > 0

    test "Fixed positions populated correctly":
        var (sys, _, _, _) = buildMOLSSystem(5)
        sys.baseArray.reducedDomain = reduceDomain(sys.baseArray)
        sys.baseArray.removeFixedConstraints()

        # Every fixed position should have a singleton domain
        for pos in sys.baseArray.fixedPositions.items:
            check sys.baseArray.reducedDomain[pos].len == 1
        # Should have at least the known 19 singletons for n=5
        check sys.baseArray.fixedPositions.len >= 19
