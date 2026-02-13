import std/[sequtils, unittest]
import crusher

proc validateLangfordSequence(sequence: seq[int], k: int): bool =
    let n = 2 * k
    if sequence.len != n: return false

    # Check separation constraint: the two occurrences of i are separated by exactly i positions
    for i in 1..k:
        var positions: seq[int] = @[]
        for j, val in sequence:
            if val == i:
                positions.add(j)

        if positions.len != 2: return false
        let separation = positions[1] - positions[0] - 1
        if separation != i: return false

    return true

suite "Langford Sequence Tests":
    test "Langford Sequence K=4":
        var sys = initConstraintSystem[int]()
        let k = 4
        let n = 2 * k  # sequence length = 8

        var solution = sys.newConstrainedSequence(n)
        solution.setDomain(toSeq(1..k))

        var position = sys.newConstrainedSequence(2 * k)
        position.setDomain(toSeq(0..<n))

        sys.addConstraint(allDifferent(position))

        for i in 1..k:
            sys.addConstraint(position[k + i - 1] == position[i - 1] + i + 1)
            sys.addConstraint(element(position[i - 1], solution, i))
            sys.addConstraint(element(position[k + i - 1], solution, i))

        sys.resolve()

        let result = solution.assignment
        echo "Langford sequence K=4: ", result
        echo "Position sequence K=4: ", position.assignment
        check validateLangfordSequence(result, k)

    test "Langford Sequence K=12 (Length 24)":
        var sys = initConstraintSystem[int]()
        let k = 12
        let n = 2 * k  # sequence length = 24

        var solution = sys.newConstrainedSequence(n)
        solution.setDomain(toSeq(1..k))

        var position = sys.newConstrainedSequence(2 * k)
        position.setDomain(toSeq(0..<n))

        sys.addConstraint(allDifferent(position))

        for i in 1..k:
            sys.addConstraint(position[k + i - 1] == position[i - 1] + i + 1)
            sys.addConstraint(element(position[i - 1], solution, i))
            sys.addConstraint(element(position[k + i - 1], solution, i))

        sys.resolve(tabuThreshold=10000, parallel=true)

        let result = solution.assignment
        echo "Langford sequence K=12: ", result
        echo "Position sequence K=12: ", position.assignment
        check validateLangfordSequence(result, k)

    test "Langford Sequence K=2 (Unsolvable)":
        # K=2 has no solution for Langford sequences (K ≡ 2 mod 4)
        var sys = initConstraintSystem[int]()
        let k = 2
        let n = 2 * k  # sequence length = 4

        var solution = sys.newConstrainedSequence(n)
        solution.setDomain(toSeq(1..k))

        var position = sys.newConstrainedSequence(2 * k)
        position.setDomain(toSeq(0..<n))

        sys.addConstraint(allDifferent(position))

        for i in 1..k:
            sys.addConstraint(position[k + i - 1] == position[i - 1] + i + 1)
            sys.addConstraint(element(position[i - 1], solution, i))
            sys.addConstraint(element(position[k + i - 1], solution, i))

        # For unsolvable cases, the system should throw NoSolutionFoundError
        expect(NoSolutionFoundError):
            sys.resolve()

        echo "Langford sequence K=2: correctly detected as unsolvable"
