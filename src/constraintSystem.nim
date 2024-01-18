import std/[packedsets, sequtils]

import constrainedArray
import constraints/constraint
import expressions/expression
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
        baseArray*: ConstrainedArray[T]
        currentAssignment*: seq[T]


################################################################################
# ConstraintSystem creation
################################################################################

func initConstraintSystem*[T](): ConstraintSystem[T] =
    # Initializes empty ConstraintSystem
    return ConstraintSystem[T](
        size: 0,
        baseArray: initConstrainedArray[T](0),
        variables: newSeq[ConstrainedVariable[T]](),
        currentAssignment: newSeq[T]()
    )


func newConstrainedMatrix*[T](system: ConstraintSystem[T], m, n: int): ConstrainedVariable[T] =
    # Creates new ConstrainedVariable in the form of an mxn matrix, adding the variable to the system.
    result = ConstrainedVariable[T](
        shape: Matrix,
        m: m,
        n: n,
        system: system,
        offset: system.baseArray.len,
        size: m*n
    )
    system.baseArray.extendArray(m*n)
    system.variables.add(result)


proc newConstrainedSequence*[T](system: ConstraintSystem[T], n: int): ConstrainedVariable[T] =
    # Creates new ConstrainedVariable in the form of a length n seq, adding the variable to the system.
    result = ConstrainedVariable[T](
        shape: Sequence,
        n: n,
        system: system,
        offset: system.baseArray.len,
        size: n
    )
    system.baseArray.extendArray(n)
    system.variables.add(result)

################################################################################
# ConstrainedVariable access
################################################################################

func `[]`*[T](cvar: ConstrainedVariable[T], i: int): Expression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + i]


func `[]`*[T](cvar: ConstrainedVariable[T], i, j: int): Expression[T] {.inline.} =
    cvar.system.baseArray[cvar.offset + cvar.m*i + j]


func values*[T](cvar: ConstrainedVariable[T]): seq[Expression[T]] =
    case cvar.shape:
        of Matrix:
            for i in 0..<cvar.m:
                for j in 0..<cvar.n:
                    result.add(cvar[i, j])
        of Sequence:
            for i in 0..<cvar.n:
                result.add(cvar[i])


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
    cvar.system.baseArray.setDomain(domain)

func setDomain*[T](cvar: var ConstrainedArray[T], position: int, domain: openArray[T]) =
    cvar.system.baseArray.setDomain(position, domain)

################################################################################
# ConstrainedVariable constraints
################################################################################

proc allDifferent*[T](cvar: ConstrainedVariable[T]): Constraint[T] =
    # allDifferent on constrained variable
    allDifferent(cvar.basePositions())

func addConstraint*[T](system: ConstraintSystem[T], constraint: Constraint[T]) =
    system.baseArray.addConstraint(constraint)

func basePositions*[T](cvar: ConstrainedVariable[T]): seq[int] =
    toSeq cvar.offset..<(cvar.offset + cvar.size)

func getAssignment*[T](cvar: ConstrainedVariable[T]): seq[T] =
    cvar.system.currentAssignment[cvar.offset..<(cvar.offset + cvar.size)]

proc findAssignment*[T](system: ConstraintSystem[T], tenure, threshold: int) =
    system.currentAssignment = system.baseArray.findAssignment(tenure, threshold)

proc resolve*[T](system: ConstraintSystem[T], threshold = 10000) =
    for imp in system.baseArray.parallelSearch(threshold):
        if imp.cost == 0:
            system.currentAssignment = imp.currentAssignment