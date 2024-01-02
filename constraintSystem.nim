import std/[packedsets, sequtils]

import constrainedArray
import expressions/[expression, expressionNode]

################################################################################
# Type definitions
################################################################################

type
    ConstrainedVariable[T] = object
        system: ConstraintSystem[T]
        shape: (int, int)
        offset: int
        size: int

    ConstraintSystem*[T] = object
        size: int
        carray: ConstrainedArray[T]
        variables: seq[ConstrainedVariable[T]]


func `[]`*[T](cvar: ConstrainedVariable[T], i: int): Expression[T] {.inline.} =
    doAssert i < cvar.size
    cvar.system.carray.entries[cvar.offset + i]

func `[]`*[T](cvar: ConstrainedVariable[T], i, j: int): Expression[T] {.inline.} =
    doAssert i*j < cvar.size
    doAssert i < cvar.shape[0]
    doAssert j < cvar.shape[1]
    cvar.system.carray.entries[cvar.offset + i*j + j]

func initConstraintSystem*[T](): ConstraintSystem[T] =
    return ConstraintSystem[T](
        size: 0,
        carray: initConstrainedArray[T](0),
        variables: newSeq[ConstrainedVariable[T]]()
    )

func addVariable*[T](system: ConstraintSystem[T], m: int, n = 1): ConstrainedVariable[T] =
    result = ConstrainedVariable[T](
        system: system,
        shape: (m, n),
        offset: system.carray.len,
        size: m*n
    )
    system.carray.extendArray(m*n)
    system.variables.add(result)


func assignment*[T](cvar: ConstrainedVariable[T]): seq[T] =
    for pos in cvar.system.carray.allPositions():
        result.add(cvar.system.)
