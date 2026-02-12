import std/[sequtils, unittest]
import crusher

suite "Magic Sequence":

    test "Magic Sequence (N=7)":
        const N = 7
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(N)
        x.setDomain(toSeq(0..(N-1)))

        # sum(x) == N
        sys.addConstraint(x.sum() == N)

        # scalarProduct(0..N-1, x) == N
        var coeffs = newSeq[int](N)
        for i in 0..<N:
            coeffs[i] = i
        sys.addConstraint(scalarProduct(coeffs, x) == N)

        # For each value v, the count of v must equal x[v].
        # Since atLeast/atMost need constant bounds, iterate over possible counts:
        var counts = newSeq[ConstrainedVariable[int]](N)
        for i in 0..<N:
            counts[i] = sys.newConstrainedVariable()
            counts[i].setDomain(toSeq(0..(N-1)))
            sys.addConstraint(counts[i] == x[i])

        for v in 0..<N:
            for c in 0..<N:
                # implies(x[v] == c, atLeast(x, v, c) AND atMost(x, v, c))
                let cond = (x[v] == c)
                let countConstraint = atLeast[int](toSeq(0..<N), v, c) and atMost[int](toSeq(0..<N), v, c)
                sys.addConstraint(cond -> countConstraint)

        sys.resolve(parallel=true, tabuThreshold=50000, populationSize=10)

        let a = x.assignment()

        # Verify magic sequence property
        check a.foldl(a + b) == N
        var weightedSum = 0
        for i in 0..<N:
            weightedSum += i * a[i]
        check weightedSum == N

        for v in 0..<N:
            var count = 0
            for j in 0..<N:
                if a[j] == v:
                    count += 1
            check count == a[v]
