import std/[sequtils, unittest]
import crusher

suite "LexOrder":

    test "lexLt - strict lexicographic ordering":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        var y = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(1..5))
        y.setDomain(toSeq(1..5))

        let xpos = toSeq(0..2)
        let ypos = toSeq(3..5)
        sys.addConstraint(lexLt[int](xpos, ypos))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let ax = x.assignment()
        let ay = y.assignment()

        # Verify x is lexicographically < y
        var isLess = false
        for i in 0..<3:
            if ax[i] < ay[i]:
                isLess = true
                break
            elif ax[i] > ay[i]:
                isLess = false
                break
        check isLess

    test "lexLe - non-strict allows equality":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        var y = sys.newConstrainedSequence(3)
        x.setDomain(@[3])
        y.setDomain(@[3])

        let xpos = toSeq(0..2)
        let ypos = toSeq(3..5)
        sys.addConstraint(lexLe[int](xpos, ypos))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let ax = x.assignment()
        let ay = y.assignment()

        # Equal sequences should satisfy lexLe
        check ax == ay
