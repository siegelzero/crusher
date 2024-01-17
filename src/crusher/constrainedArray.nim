import std/[packedsets, sequtils]

import constraints/constraint
import expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    ConstrainedArray*[T] = object
        len*: int
        constraints*: seq[Constraint[T]]
        domain*: seq[seq[T]]
        entries*: seq[Expression[T]]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): Expression[T] {.inline.} = arr.entries[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield i

################################################################################
# ConstrainedArray Creation
################################################################################

func initConstrainedArray*[T](n: int): ConstrainedArray[T] =
    var entries: seq[Expression[T]] = @[]
    for pos in 0..<n:
        entries.add(
            Expression[T](
                positions: toPackedSet[int](@[pos]),
                node: ExpressionNode[T](kind: RefNode, position: pos)
            )
        )
    return ConstrainedArray[T](
        len: n,
        constraints: newSeq[Constraint[T]](),
        domain: newSeq[seq[T]](n),
        entries: entries
    )

func extendArray*[T](arr: var ConstrainedArray[T], m: int) =
    # Extends the array by m elements.
    let n = arr.entries.len()
    for pos in n..<(n + m):
        arr.entries.add(
            Expression[T](
                positions: toPackedSet[int]([pos]),
                node: ExpressionNode[T](kind: RefNode, position: pos)
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

func allDifferent*[T](arr: ConstrainedArray[T]): Constraint[T] {.inline.} =
    allDifferent(toSeq arr.allPositions())

func addConstraint*[T](arr: var ConstrainedArray[T], cons: Constraint[T]) {.inline.} =
    # Adds the constraint to the 
    arr.constraints.add(cons)
