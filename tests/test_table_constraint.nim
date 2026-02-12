import std/[sequtils, unittest]
import crusher

suite "TableConstraint":

    test "tableIn - tuple membership":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(1..3))

        let allowed = @[@[1, 2, 3], @[3, 2, 1], @[2, 2, 2]]
        sys.addConstraint(tableIn[int](toSeq(0..2), allowed))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        check a in allowed

    test "tableNotIn - tuple exclusion":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(1..3))

        # Forbid all-same tuples
        let forbidden = @[@[1, 1, 1], @[2, 2, 2], @[3, 3, 3]]
        sys.addConstraint(tableNotIn[int](toSeq(0..2), forbidden))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        check a notin forbidden
