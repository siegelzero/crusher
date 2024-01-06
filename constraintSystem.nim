import std/[packedsets, sequtils]

import constrainedArray
import constraints/constraint
import expressions/[expression, expressionNode]
import heuristics/tabuSearch

################################################################################
# Type definitions
################################################################################

type
    VariableShape = enum
        Sequence, Matrix

    ConstrainedVariable*[T] = object
        system*: ConstraintSystem[T]
        offset*: int
        size*: int
        n*: int
        case shape*: VariableShape
            of Matrix:
                m*: int
            of Sequence:
                discard

    ConstraintSystem*[T] = ref object
        size*: int
        variables*: seq[ConstrainedVariable[T]]
        carray*: ConstrainedArray[T]
        currentAssignment*: seq[T]


################################################################################
# ConstraintSystem creation
################################################################################

func initConstraintSystem*[T](): ConstraintSystem[T] =
    return ConstraintSystem[T](
        size: 0,
        carray: initConstrainedArray[T](0),
        variables: newSeq[ConstrainedVariable[T]](),
        currentAssignment: newSeq[T]()
    )

func newConstrainedMatrix*[T](system: ConstraintSystem[T], m, n: int): ConstrainedVariable[T] =
    result = ConstrainedVariable[T](
        shape: Matrix,
        m: m,
        n: n,
        system: system,
        offset: system.carray.len,
        size: m*n
    )
    system.carray.extendArray(m*n)
    system.variables.add(result)

proc newConstrainedSequence*[T](system: ConstraintSystem[T], n: int): ConstrainedVariable[T] =
    result = ConstrainedVariable[T](
        shape: Sequence,
        n: n,
        system: system,
        offset: system.carray.len,
        size: n
    )
    system.carray.extendArray(n)
    system.variables.add(result)

################################################################################
# ConstrainedVariable access
################################################################################

func `[]`*[T](cvar: ConstrainedVariable[T], i: int): Expression[T] {.inline.} =
    cvar.system.carray[cvar.offset + i]


func `[]`*[T](cvar: ConstrainedVariable[T], i, j: int): Expression[T] {.inline.} =
    cvar.system.carray[cvar.offset + cvar.m*i + j]


iterator columns*[T](cvar: ConstrainedVariable[T]): seq[Expression[T]] =
    case cvar.shape:
        of Matrix:
            var col: seq[Expression[T]]
            for i in 0..<cvar.n:
                col = @[]
                for j in 0..<cvar.m:
                    col.add(cvar[j, i])
                yield col
        of Sequence:
            discard

iterator rows*[T](cvar: ConstrainedVariable[T]): seq[Expression[T]] =
    case cvar.shape:
        of Matrix:
            var row: seq[Expression[T]]
            for i in 0..<cvar.m:
                row = @[]
                for j in 0..<cvar.n:
                    row.add(cvar[i, j])
                yield row
        of Sequence:
            discard


proc display*[T](cvar: ConstrainedVariable[T]) =
    case cvar.shape:
        of Sequence:
            echo cvar.getAssignment()
        of Matrix:
            let assignment = cvar.getAssignment()
            for i in 0..<cvar.m:
                echo assignment[cvar.m*i..<(cvar.m*i + cvar.n)]

################################################################################
# ConstrainedVariable domains
################################################################################

func setDomain*[T](cvar: ConstrainedVariable[T], domain: openArray[T]) =
    cvar.system.carray.setDomain(domain)

func setDomain*[T](cvar: var ConstrainedArray[T], position: int, domain: openArray[T]) =
    cvar.system.carray.setDomain(position, domain)

################################################################################
# ConstrainedVariable constraints
################################################################################

func addConstraint*[T](system: ConstraintSystem[T], constraint: Constraint[T]) {.inline.} =
    system.carray.addConstraint(constraint)

func getAssignment*[T](cvar: ConstrainedVariable[T]): seq[T] =
    cvar.system.currentAssignment[cvar.offset..<(cvar.offset + cvar.size)]

proc findAssignment*[T](system: ConstraintSystem[T], tenure, threshold: int) =
    system.currentAssignment = system.carray.findAssignment(tenure, threshold)