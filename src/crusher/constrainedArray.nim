import std/[packedsets, sequtils, strformat]

import constraints/stateful
import constraints/algebraic
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
        arr.domain[position] = toSeq(domain)

func setDomain*[T](arr: var ConstrainedArray[T], position: int, domain: openArray[T]) =
    # Sets domain of position to the given values.
    arr.domain[position] = @domain

func allDifferent*[T](arr: ConstrainedArray[T]): StatefulConstraint[T] {.inline.} =
    allDifferent(toSeq arr.allPositions())

template OrderingArrayRel(relName: untyped) =
    func `relName`*[T](arr: ConstrainedArray[T]): seq[AlgebraicConstraint[T]] {.inline.} =
        var expressions: seq[AlgebraicExpression[T]] = @[]
        for pos in arr.allPositions():
            expressions.add(newAlgebraicExpression[T](
                toPackedSet[int]([pos]),
                ExpressionNode[T](kind: RefNode, position: pos),
                true
            ))
        return `relName`(expressions)

OrderingArrayRel(increasing)
OrderingArrayRel(strictlyIncreasing)
OrderingArrayRel(decreasing)
OrderingArrayRel(strictlyDecreasing)

proc addBaseConstraint*[T](arr: var ConstrainedArray[T], cons: StatefulConstraint[T]) {.inline.} =
    # Adds the constraint to the 
    arr.constraints.add(cons)

################################################################################
# ConstrainedArray domain reduction
################################################################################

proc reduceDomain*[T](carray: ConstrainedArray[T]): seq[seq[T]] =
    var
        reduced = newSeq[seq[T]](carray.len)
        currentDomain = newSeq[PackedSet[T]](carray.len)

    for pos in carray.allPositions():
        currentDomain[pos] = toPackedSet[T](carray.domain[pos])

    # First examine any single-variable constraints to reduce domains
    for cons in carray.constraints:
        if cons.positions.len != 1:
            continue
        var pos = toSeq(cons.positions)[0]
        
        # Initialize constraint with a dummy assignment
        var dummyAssignment = newSeq[T](carray.len)
        for i in 0..<carray.len:
            if carray.domain[i].len > 0:
                dummyAssignment[i] = carray.domain[i][0]
            else:
                # If domain is empty, use default value (this shouldn't happen in normal cases)
                dummyAssignment[i] = T.default
        
        # Only initialize and test single-position constraints to avoid interference
        cons.initialize(dummyAssignment)
        
        for d in carray.domain[pos]:
            cons.updatePosition(pos, d)
            if cons.penalty() > 0:
                currentDomain[pos].excl(d)
    
    for pos in carray.allPositions():
        reduced[pos] = toSeq(currentDomain[pos])
    
    return reduced

################################################################################
# Deep Copy for ConstrainedArray (for parallel processing)
################################################################################

proc deepCopy*[T](arr: ConstrainedArray[T]): ConstrainedArray[T] =
  ## Creates a deep copy of a ConstrainedArray for thread-safe parallel processing
  result.len = arr.len
  result.domain = arr.domain  # seq[seq[T]] - deep copy by assignment
  result.entries = arr.entries  # seq[AlgebraicExpression[T]] - should be immutable
  
  # Deep copy all stateful constraints
  result.constraints = newSeq[StatefulConstraint[T]](arr.constraints.len)
  for i, constraint in arr.constraints:
    result.constraints[i] = constraint.deepCopy()

