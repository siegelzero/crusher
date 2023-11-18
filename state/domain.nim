import std/[packedsets, sequtils]

import ../constrainedArray
import ../constraints/constraint


proc domainFiltering*[T](carray: ConstrainedArray[T]) =
    var cStamp = newSeq[int](carray.constraints.len)
    var vStamp = newSeq[int](carray.len)
    var inQ = newSeq[int](carray.len)
    var Q = newSeq[int]([])
    var t = 1
    var v: int

    for i in 0..<carray.constraints.len:
        cStamp[i] = 0

    # Treat all variables as active
    for pos in carray.allPositions():
        Q.add(pos)
        inQ[pos] = 1
        vStamp[pos] = 1

    while Q.len() > 0:
        v = Q.pop()
        inQ[v] = 0

        # for cons in carray.constraintsAtPosition[v]:
            # if vStamp[v] cStamp[c]





proc reduceDomain*[T](carray: ConstrainedArray[T]): seq[seq[T]] =
    var pos: int
    var assignment = newSeq[T](carray.len)

    var reduced = newSeq[seq[T]](carray.len)
    var exclusions = newSeq[PackedSet[T]](carray.len)

    for cons in carray.constraints:
        # Simplest case is constraints involving one variable
        if cons.positions.len == 1:
            pos = toSeq(cons.positions)[0]

            # Check all values in the domain. If any don't satisfy this constraint, remove the value from the domain.
            for d in carray.domain[pos]:
                assignment[pos] = d
                if not cons.evaluate(assignment):
                    exclusions[pos].incl(d)
            
    for pos in carray.allPositions():
        for d in carray.domain[pos]:
            if not (d in exclusions[pos]):
                reduced[pos].add(d)

    return reduced