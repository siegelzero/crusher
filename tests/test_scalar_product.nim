import std/[sequtils, unittest]
import crusher

suite "ScalarProduct":

    test "scalarProduct - weighted sum":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        # 2*x[0] + 3*x[1] + 5*x[2] == 20
        sys.addConstraint(scalarProduct(@[2, 3, 5], x) == 20)

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        check 2*a[0] + 3*a[1] + 5*a[2] == 20
