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
        values*: seq[Expression[T]]

################################################################################
# Value Extraction
################################################################################

func `[]`*[T](arr: ConstrainedArray[T], idx: int): Expression[T] {.inline.} = arr.values[idx]

iterator allPositions*[T](arr: ConstrainedArray[T]): int =
    for i in 0..<arr.len: yield i

################################################################################
# ConstrainedArray Methods
################################################################################

func initConstrainedArray*[T](n: int): ConstrainedArray[T] =
    var values: seq[Expression[T]] = @[]
    for pos in 0..<n:
        values.add(
            Expression[T](
                positions: toPackedSet[int]([pos]),
                node: ExpressionNode[T](kind: RefNode, position: pos)
            )
        )
    return ConstrainedArray[T](
        len: n,
        constraints: newSeq[Constraint[T]](),
        domain: newSeq[seq[T]](n),
        values: values
    )

func setDomain*[T](arr: var ConstrainedArray[T], domain: openArray[T]) =
    # Sets domain of all positions to the given values.
    for position in arr.allPositions():
        arr.domain[position] = toSeq[T](domain)

func setDomain*[T](arr: var ConstrainedArray[T], position: int, domain: openArray[T]) =
    # Sets domain of position to the given values.
    arr.domain[position] = toSeq[T](domain)

func allDifferent*[T](arr: var ConstrainedArray[T]) =
    # Adds all-different constraints for the all positions in the array
    for i in 0..<arr.len:
        for j in 0..<i:
            arr.constraints.add(arr[i] != arr[j])

func allDifferent*[T](arr: var ConstrainedArray[T], positions: seq[int]) =
    # Adds all-different constraints for the given positions.
    for i in 0..<positions.len:
        for j in 0..<i:
            arr.constraints.add(arr[positions[i]] != arr[positions[j]])

func allDifferent*[T](arr: var ConstrainedArray[T], expressions: seq[Expression[T]]) =
    # Adds all-different constraints for the given expressions.
    for i in 0..<expressions.len:
        for j in 0..<i:
            arr.constraints.add(expressions[i] != expressions[j])

func addConstraint*[T](arr: var ConstrainedArray[T], cons: Constraint[T]) {.inline.} =
    # Adds the constraint to the 
    arr.constraints.add(cons)