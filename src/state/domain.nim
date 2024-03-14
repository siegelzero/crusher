import std/[packedsets, sequtils]

import ../constrainedArray
import ../constraints/constraint


proc reduceDomain*[T](carray: ConstrainedArray[T]): seq[seq[T]] =
    var
        ok: bool
        pos1, pos2: int
        assignment = newSeq[T](carray.len)
        reduced = newSeq[seq[T]](carray.len)
        currentDomain = newSeq[PackedSet[T]](carray.len)

    for pos in carray.allPositions():
        currentDomain[pos] = toPackedSet[T](carray.domain[pos])

    # First examine any single-variable constraints to reduce domains
    for cons in carray.constraints:
        if cons.positions.len != 1:
            continue
        var pos = toSeq(cons.positions)[0]
        for d in carray.domain[pos]:
            cons.updatePosition(pos, d)
            if cons.penalty() > 0:
                # echo "Excluding ", d, " from ", pos
                currentDomain[pos].excl(d)
    
    # Now check two-variable constraints
    for cons in carray.constraints:
        if cons.positions.len != 2:
            continue

        var pos1 = toSeq(cons.positions)[0]
        var pos2 = toSeq(cons.positions)[1]

        for val1 in toSeq(currentDomain[pos1]):
            ok = false
            cons.updatePosition(pos1, val1)

            for val2 in currentDomain[pos2]:
                cons.updatePosition(pos2, val2)
                if cons.penalty() > 0:
                    ok = true
                    break

            if not ok:
                # echo "Excluding ", val1, " from ", pos1
                currentDomain[pos1].excl(val1)

        # echo "Checking reverse"

        for val2 in toSeq(currentDomain[pos2]):
            ok = false
            cons.updatePosition(pos2, val2)

            for val1 in currentDomain[pos1]:
                cons.updatePosition(pos1, val1)
                if cons.penalty() > 0:
                    ok = true
                    break

            if not ok:
                # echo "Excluding ", val2, " from ", pos2
                currentDomain[pos2].excl(val2)
    
    for pos in carray.allPositions():
        reduced[pos] = toSeq(currentDomain[pos])
    
    return reduced