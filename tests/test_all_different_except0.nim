import std/[sequtils, unittest]
import crusher

suite "AllDifferentExcept0":

    test "allDifferentExcept0 - non-zero values distinct":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(5)
        x.setDomain(toSeq(0..4))

        sys.addConstraint(allDifferentExcept0(x))
        # Force at least two zeros so we test the "except 0" part
        sys.addConstraint(atLeast[int](toSeq(0..4), 0, 2))

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        # Check: all non-zero values are distinct
        var nonZero: seq[int] = @[]
        for v in a:
            if v != 0:
                nonZero.add(v)
        check nonZero.len == nonZero.deduplicate().len

        # Check: at least 2 zeros
        var zeroCount = 0
        for v in a:
            if v == 0:
                zeroCount += 1
        check zeroCount >= 2
