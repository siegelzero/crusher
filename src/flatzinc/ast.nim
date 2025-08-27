################################################################################
# Type definitions
################################################################################

type
    FlatZincType* = enum
        fzBool, fzInt, fzFloat, fzSetInt
        fzArrayBool, fzArrayInt, fzArrayFloat, fzArraySetInt

    FlatZincDomain* = object
        case domainType*: FlatZincType
        of fzInt:
            intRange*: tuple[min: int, max: int]
            intSet*: seq[int]
            hasRange*: bool
            hasSet*: bool
        of fzBool:
            discard
        of fzFloat:
            floatRange*: tuple[min: float, max: float]
        of fzSetInt:
            setIntRange*: tuple[min: int, max: int]
        else:
            discard

    FlatZincLiteral* = object
        case literalType*: FlatZincType
        of fzInt:
            intVal*: int
        of fzBool:
            boolVal*: bool
        of fzFloat:
            floatVal*: float
        of fzSetInt:
            setVal*: seq[int]
        else:
            discard

    ExprType* = enum
        feIdent, feLiteral, feArray

    FlatZincExpr* = ref object
        case exprType*: ExprType
        of feIdent:
            name*: string
        of feLiteral:
            literal*: FlatZincLiteral
        of feArray:
            elements*: seq[FlatZincExpr]

    FlatZincVarDecl* = object
        name*: string
        varType*: FlatZincType
        domain*: FlatZincDomain
        isVar*: bool
        annotations*: seq[string]
        annotationParams*: seq[seq[int]]  # Parameters for each annotation (e.g., output_array dimensions)
        arraySize*: seq[int]
        arrayValue*: seq[int]  # For parameter arrays like [1,1,1]
        arrayVarRefs*: seq[string]  # For arrays that reference other variables

    FlatZincConstraint* = object
        name*: string
        args*: seq[FlatZincExpr]
        annotations*: seq[string]

    SolveType* = enum
        fsSatisfy, fsMinimize, fsMaximize

    FlatZincSolve* = object
        case solveType*: SolveType
        of fsMinimize, fsMaximize:
            objective*: FlatZincExpr
        of fsSatisfy:
            discard
        annotations*: seq[string]

    FlatZincModel* = object
        predicates*: seq[string]
        varDecls*: seq[FlatZincVarDecl]
        constraints*: seq[FlatZincConstraint]
        solve*: FlatZincSolve
        output*: seq[string]

################################################################################
# String representation
################################################################################

proc `$`*(expr: FlatZincExpr): string =
    case expr.exprType:
        of feIdent:
            result = expr.name
        of feLiteral:
            case expr.literal.literalType:
                of fzInt: result = $expr.literal.intVal
                of fzBool: result = $expr.literal.boolVal
                of fzFloat: result = $expr.literal.floatVal
                of fzSetInt: result = "{" & $expr.literal.setVal & "}"
                else: result = "?"
        of feArray:
            result = "["
            for i, elem in expr.elements:
                if i > 0: result.add(", ")
                result.add($elem)
            result.add("]")