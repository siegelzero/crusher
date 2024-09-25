import std/[packedsets, sequtils, strformat]

import constraints/stateful
import expressions

################################################################################
# Type definitions
################################################################################

type
    ConstrainedArray*[T] = object
        len*: int
        constraints*: seq[StatefulConstraint[T]]
        domain*: seq[seq[T]]
        entries*: seq[AlgebraicExpression[T]]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): AlgebraicExpression[T] {.inline.} = arr.entries[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield i

func `$`*[T](arr: ConstrainedArray[T]): string =
    return fmt"ConstrainedArray of size {arr.len}"


################################################################################
# ConstrainedArray Creation
################################################################################

func initConstrainedArray*[T](n: int): ConstrainedArray[T] =
    var entries: seq[AlgebraicExpression[T]] = @[]
    for pos in 0..<n:
        entries.add(
            newAlgebraicExpression[T](
                positions=toPackedSet[int](@[pos]),
                node=ExpressionNode[T](kind: RefNode, position: pos),
                linear=true
            )
        )
    return ConstrainedArray[T](
        len: n,
        constraints: newSeq[StatefulConstraint[T]](),
        domain: newSeq[seq[T]](n),
        entries: entries
    )

func extendArray*[T](arr: var ConstrainedArray[T], m: int) =
    # Extends the array by m elements.
    let n = arr.entries.len()
    for pos in n..<(n + m):
        arr.entries.add(
            newAlgebraicExpression[T](
                positions=toPackedSet[int]([pos]),
                node=ExpressionNode[T](kind: RefNode, position: pos),
                linear=true
            )
        )
        arr.domain.add(newSeq[T]())
    arr.len += m

################################################################################
# ConstrainedArray domains
################################################################################

func setDomain*[T](arr: var ConstrainedArray[T], domain: openArray[T]) =
    # Sets domain of all positions to the given values.
    for position in arr.allPositions():
        arr.domain[position] = toSeq[T](domain)

func setDomain*[T](arr: var ConstrainedArray[T], position: int, domain: openArray[T]) =
    # Sets domain of position to the given values.
    arr.domain[position] = toSeq[T](domain)

func allDifferent*[T](arr: ConstrainedArray[T]): StatefulConstraint[T] {.inline.} =
    allDifferent(toSeq arr.allPositions())

proc addBaseConstraint*[T](arr: var ConstrainedArray[T], cons: StatefulConstraint[T]) {.inline.} =
    # Adds the constraint to the 
    arr.constraints.add(cons)

################################################################################
# ConstrainedArray domain reduction
################################################################################

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
    
    # # Now check two-variable constraints
    # for cons in carray.constraints:
    #     if cons.positions.len != 2:
    #         continue

    #     var pos1 = toSeq(cons.positions)[0]
    #     var pos2 = toSeq(cons.positions)[1]

    #     for val1 in toSeq(currentDomain[pos1]):
    #         ok = false
    #         cons.updatePosition(pos1, val1)

    #         for val2 in currentDomain[pos2]:
    #             cons.updatePosition(pos2, val2)
    #             if cons.penalty() > 0:
    #                 ok = true
    #                 break

    #         if not ok:
    #             # echo "Excluding ", val1, " from ", pos1
    #             currentDomain[pos1].excl(val1)

    #     # echo "Checking reverse"

    #     for val2 in toSeq(currentDomain[pos2]):
    #         ok = false
    #         cons.updatePosition(pos2, val2)

    #         for val1 in currentDomain[pos1]:
    #             cons.updatePosition(pos1, val1)
    #             if cons.penalty() > 0:
    #                 ok = true
    #                 break

    #         if not ok:
    #             # echo "Excluding ", val2, " from ", pos2
    #             currentDomain[pos2].excl(val2)
    
    for pos in carray.allPositions():
        reduced[pos] = toSeq(currentDomain[pos])
    
    return reduced

