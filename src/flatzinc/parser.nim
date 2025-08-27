import std/strutils
import lexer, ast

################################################################################
# Type definitions
################################################################################

type
    Parser* = object
        tokens*: seq[Token]
        pos*: int

    ParseError* = object of CatchableError

################################################################################
# Parser initialization
################################################################################

proc initParser*(tokens: seq[Token]): Parser =
    Parser(tokens: tokens, pos: 0)

################################################################################
# Parser utility functions
################################################################################

proc current(p: Parser): Token =
    if p.pos >= p.tokens.len:
        Token(kind: tkEof)
    else:
        p.tokens[p.pos]

proc advance(p: var Parser): Token =
    result = p.current
    p.pos += 1

proc peek(p: Parser, offset: int = 1): Token =
    let peekPos = p.pos + offset
    if peekPos >= p.tokens.len:
        Token(kind: tkEof)
    else:
        p.tokens[peekPos]

proc expect(p: var Parser, kind: TokenKind): Token =
    let tok = p.current
    if tok.kind != kind:
        raise newException(ParseError, "Expected " & $kind & " but got " & $tok.kind & " at line " & $tok.line)
    result = p.advance()

proc match(p: Parser, kind: TokenKind): bool =
    p.current.kind == kind

proc matchAny(p: Parser, kinds: varargs[TokenKind]): bool =
    p.current.kind in kinds

################################################################################
# Type parsing
################################################################################

proc parseType(p: var Parser): FlatZincType =
    case p.current.kind:
        of tkBool1:
            discard p.advance()
            result = fzBool
        of tkInt1:
            discard p.advance()
            result = fzInt
        of tkFloat1:
            discard p.advance()
            result = fzFloat
        of tkInt, tkLBrace:
            # This is a domain specification like "1..25" or "{1,2,3}", assume int type
            result = fzInt
        of tkArray:
            discard p.advance()
            discard p.expect(tkLBracket)
            # Parse array indices - for now just skip to closing bracket
            while not p.match(tkRBracket) and not p.match(tkEof):
                discard p.advance()
            discard p.expect(tkRBracket)
            discard p.expect(tkOf)
            # Handle optional 'var' keyword in array element type
            if p.match(tkVar):
                discard p.advance()
            let baseType = p.parseType()
            case baseType:
                of fzBool: result = fzArrayBool
                of fzInt: result = fzArrayInt  
                of fzFloat: result = fzArrayFloat
                of fzSetInt: result = fzArraySetInt
                else: result = fzArrayInt
        else:
            raise newException(ParseError, "Expected type at line " & $p.current.line)

proc parseTypeWithDimensions(p: var Parser): (FlatZincType, seq[int]) =
    var dimensions: seq[int] = @[]
    case p.current.kind:
        of tkBool1:
            discard p.advance()
            result = (fzBool, dimensions)
        of tkInt1:
            discard p.advance()
            result = (fzInt, dimensions)
        of tkFloat1:
            discard p.advance()
            result = (fzFloat, dimensions)
        of tkInt, tkLBrace:
            # This is a domain specification like "1..25" or "{1,2,3}", assume int type
            result = (fzInt, dimensions)
        of tkArray:
            discard p.advance()
            discard p.expect(tkLBracket)
            # Parse array indices - extract dimensions
            while not p.match(tkRBracket) and not p.match(tkEof):
                if p.match(tkInt):
                    let minStr = p.current.value
                    discard p.advance()
                    if p.match(tkDotDot):
                        discard p.advance()
                        if p.match(tkInt):
                            let maxStr = p.current.value
                            discard p.advance()  # Advance past the max value token
                            try:
                                let minVal = parseInt(minStr)
                                let maxVal = parseInt(maxStr)
                                let dimSize = maxVal - minVal + 1
                                dimensions.add(dimSize)
                            except:
                                raise newException(ParseError, "Invalid array range '" & minStr & ".." & maxStr & "' at line " & $p.current.line)
                        else:
                            raise newException(ParseError, "Expected array range max value after '..' at line " & $p.current.line)
                    else:
                        try:
                            let dimSize = parseInt(minStr)
                            dimensions.add(dimSize)
                        except:
                            raise newException(ParseError, "Invalid array dimension '" & minStr & "' at line " & $p.current.line)
                else:
                    discard p.advance()
            discard p.expect(tkRBracket)
            discard p.expect(tkOf)
            # Handle optional 'var' keyword in array element type
            if p.match(tkVar):
                discard p.advance()
            let baseType = p.parseType()
            case baseType:
                of fzBool: result = (fzArrayBool, dimensions)
                of fzInt: result = (fzArrayInt, dimensions)  
                of fzFloat: result = (fzArrayFloat, dimensions)
                of fzSetInt: result = (fzArraySetInt, dimensions)
                else: result = (fzArrayInt, dimensions)
        else:
            raise newException(ParseError, "Expected type at line " & $p.current.line)

################################################################################
# Domain parsing
################################################################################

proc parseDomain(p: var Parser, varType: FlatZincType): FlatZincDomain =
    result = FlatZincDomain(domainType: varType)
    
    case varType:
        of fzInt:
            if p.match(tkLBrace):
                # Set of integers
                discard p.advance() # Skip {
                result.intSet = @[]
                while not p.match(tkRBrace) and not p.match(tkEof):
                    if p.match(tkInt):
                        result.intSet.add(parseInt(p.advance().value))
                    elif p.match(tkComma):
                        discard p.advance()
                    else:
                        break
                discard p.expect(tkRBrace)
                result.hasSet = true
            elif p.match(tkInt):
                # Parse range min..max or single integer
                let min = parseInt(p.advance().value)
                if p.match(tkDotDot):
                    discard p.advance()
                    let max = parseInt(p.expect(tkInt).value)
                    result.intRange = (min, max)
                    result.hasRange = true
                else:
                    # Single integer value
                    result.intSet = @[min]
                    result.hasSet = true
        of fzBool:
            discard # No domain constraints for bool
        of fzFloat:
            if p.match(tkFloat):
                let min = parseFloat(p.advance().value)
                if p.match(tkDotDot):
                    discard p.advance()
                    let max = parseFloat(p.expect(tkFloat).value)
                    result.floatRange = (min, max)
        else:
            discard

################################################################################
# Expression parsing
################################################################################

proc parseExpr(p: var Parser): FlatZincExpr =
    case p.current.kind:
        of tkIdent:
            let identName = p.advance().value
            # Check for array indexing like a[1]
            if p.match(tkLBracket):
                discard p.advance() # Skip [
                # For now, just include the index in the name
                var indexName = identName & "["
                while not p.match(tkRBracket) and not p.match(tkEof):
                    case p.current.kind:
                        of tkInt:
                            indexName.add(p.advance().value)
                        of tkComma:
                            indexName.add(p.advance().value)
                        of tkIdent:
                            indexName.add(p.advance().value)
                        else:
                            indexName.add("?")
                            discard p.advance()
                indexName.add("]")
                discard p.expect(tkRBracket)
                result = FlatZincExpr(exprType: feIdent, name: indexName)
            else:
                result = FlatZincExpr(exprType: feIdent, name: identName)
        of tkInt:
            let val = parseInt(p.advance().value)
            result = FlatZincExpr(
                exprType: feLiteral,
                literal: FlatZincLiteral(literalType: fzInt, intVal: val)
            )
        of tkBool:
            let val = p.advance().value == "true"
            result = FlatZincExpr(
                exprType: feLiteral,
                literal: FlatZincLiteral(literalType: fzBool, boolVal: val)
            )
        of tkFloat:
            let val = parseFloat(p.advance().value)
            result = FlatZincExpr(
                exprType: feLiteral,
                literal: FlatZincLiteral(literalType: fzFloat, floatVal: val)
            )
        of tkLBracket:
            discard p.advance() # Skip [
            result = FlatZincExpr(exprType: feArray, elements: @[])
            while not p.match(tkRBracket) and not p.match(tkEof):
                result.elements.add(p.parseExpr())
                if p.match(tkComma):
                    discard p.advance()
                else:
                    break
            discard p.expect(tkRBracket)
        of tkSet:
            # Parse set literal
            let setStr = p.advance().value
            # Simple parsing - extract numbers from set string
            var setVals: seq[int] = @[]
            let nums = setStr.replace("{", "").replace("}", "").split(",")
            for numStr in nums:
                try:
                    setVals.add(parseInt(numStr.strip()))
                except:
                    discard
            result = FlatZincExpr(
                exprType: feLiteral,
                literal: FlatZincLiteral(literalType: fzSetInt, setVal: setVals)
            )
        else:
            raise newException(ParseError, "Unexpected token in expression: " & $p.current.kind & " at line " & $p.current.line)

################################################################################
# Variable declaration parsing
################################################################################

proc parseVarDecl(p: var Parser): FlatZincVarDecl =
    var isVar = p.match(tkVar)
    if isVar:
        discard p.advance()
  
    # Parse type or domain first
    var varType: FlatZincType
    var domain: FlatZincDomain
    var arrayDimensions: seq[int] = @[]
    
    if p.matchAny(tkInt, tkLBrace):
        # This is a domain constraint like "1..10" or "{1,2,3}"
        varType = fzInt
        domain = p.parseDomain(varType)
    else:
        # This is a type declaration
        # For array types, check for var after 'of' keyword
        let startPos = p.pos
        (varType, arrayDimensions) = p.parseTypeWithDimensions()
        
        # Check if parseType consumed a 'var' keyword (for array declarations)
        if not isVar:
            # Look back at consumed tokens to see if there was a 'var' keyword
            for i in startPos..<p.pos:
                if i < p.tokens.len and p.tokens[i].kind == tkVar:
                    isVar = true
                    break
        
        domain = FlatZincDomain(domainType: varType)
        
        # Parse optional domain constraint
        if p.matchAny(tkInt, tkFloat, tkLBrace) or (varType == fzInt and p.match(tkInt)):
            # For array types, domain applies to elements
            let domainType = case varType:
                of fzArrayInt: fzInt
                of fzArrayBool: fzBool  
                of fzArrayFloat: fzFloat
                else: varType
            domain = p.parseDomain(domainType)
  
    discard p.expect(tkColon)
    let name = p.expect(tkIdent).value
    
    # Parse optional annotations
    var annotations: seq[string] = @[]
    var annotationParams: seq[seq[int]] = @[]
    while p.match(tkAnnotations):
        discard p.advance() # Skip ::
        # Collect identifiers and parse function parameters
        while p.match(tkIdent):
            let annotationName = p.advance().value
            annotations.add(annotationName)
            
            # Parse annotation parameters if present
            var params: seq[int] = @[]
            if p.match(tkLParen):
                discard p.advance() # Skip (
                # Parse array dimensions for output_array([1..4, 1..4])
                if annotationName == "output_array" and p.match(tkLBracket):
                    discard p.advance() # Skip [
                    # Parse dimension ranges
                    while not p.match(tkRBracket) and not p.match(tkEof):
                        if p.match(tkInt):
                            let minStr = p.current.value
                            discard p.advance()
                            if p.match(tkDotDot):
                                discard p.advance()
                                if p.match(tkInt):
                                    let maxStr = p.current.value
                                    discard p.advance()
                                    let minVal = parseInt(minStr)
                                    let maxVal = parseInt(maxStr)
                                    params.add(maxVal - minVal + 1)
                                else:
                                    raise newException(ParseError, "Expected range max value after '..' at line " & $p.current.line)
                            else:
                                params.add(parseInt(minStr))
                        elif p.match(tkComma):
                            discard p.advance() # Skip comma
                        else:
                            discard p.advance()
                    if p.match(tkRBracket):
                        discard p.advance() # Skip ]
                    if p.match(tkRParen):
                        discard p.advance() # Skip )
                else:
                    # Skip other annotation parameters we don't parse yet
                    var parenCount = 1
                    while parenCount > 0 and not p.match(tkEof):
                        case p.current.kind:
                            of tkLParen: parenCount += 1
                            of tkRParen: parenCount -= 1
                            else: discard
                        discard p.advance()
            annotationParams.add(params)
            # Break if we don't see another :: coming
            if not p.match(tkAnnotations):
                break
    
    # Parse optional assignment (for parameters)
    var arrayValue: seq[int] = @[]
    var arrayVarRefs: seq[string] = @[]
    if p.match(tkEq):
        discard p.advance()
        let expr = p.parseExpr()
        # Extract array values if this is an array assignment
        if expr.exprType == feArray:
            for elem in expr.elements:
                if elem.exprType == feLiteral and elem.literal.literalType == fzInt:
                    arrayValue.add(elem.literal.intVal)
                elif elem.exprType == feIdent:
                    arrayVarRefs.add(elem.name)
    
    discard p.expect(tkSemicolon)
    
    result = FlatZincVarDecl(
        name: name,
        varType: varType,
        domain: domain,
        isVar: isVar,
        annotations: annotations,
        annotationParams: annotationParams,
        arraySize: arrayDimensions,
        arrayValue: arrayValue,
        arrayVarRefs: arrayVarRefs
    )

################################################################################
# Constraint parsing
################################################################################

proc parseConstraint(p: var Parser): FlatZincConstraint =
    discard p.expect(tkConstraint)
    let name = p.expect(tkIdent).value
    discard p.expect(tkLParen)
    
    var args: seq[FlatZincExpr] = @[]
    while not p.match(tkRParen) and not p.match(tkEof):
        args.add(p.parseExpr())
        if p.match(tkComma):
            discard p.advance()
        else:
            break
    
    discard p.expect(tkRParen)
    
    # Parse optional annotations
    var annotations: seq[string] = @[]
    while p.match(tkAnnotations):
        discard p.advance() # Skip ::
        while p.match(tkIdent):
            annotations.add(p.advance().value)
            # Skip function call parentheses and contents
            if p.match(tkLParen):
                discard p.advance() # Skip (
                var parenCount = 1
                while parenCount > 0 and not p.match(tkEof):
                    case p.current.kind:
                        of tkLParen: parenCount += 1
                        of tkRParen: parenCount -= 1
                        else: discard
                    discard p.advance()
            # Break if we don't see another :: coming
            if not p.match(tkAnnotations):
                break
    
    discard p.expect(tkSemicolon)
    
    result = FlatZincConstraint(
        name: name,
        args: args,
        annotations: annotations
    )

################################################################################
# Solve statement parsing
################################################################################

proc parseSolve(p: var Parser): FlatZincSolve =
    discard p.expect(tkSolve)
    
    # Parse annotations that appear before the solve method
    var annotations: seq[string] = @[]
    while p.match(tkAnnotations):
        discard p.advance() # Skip ::
        while p.match(tkIdent):
            annotations.add(p.advance().value)
            # Skip function call parentheses and contents
            if p.match(tkLParen):
                discard p.advance() # Skip (
                var parenCount = 1
                while parenCount > 0 and not p.match(tkEof):
                    case p.current.kind:
                        of tkLParen: parenCount += 1
                        of tkRParen: parenCount -= 1
                        else: discard
                    discard p.advance()
            # Break if we don't see another :: coming
            if not p.match(tkAnnotations):
                break
    
    case p.current.kind:
        of tkSatisfy:
            discard p.advance()
            result = FlatZincSolve(solveType: fsSatisfy, annotations: annotations)
        of tkMinimize:
            discard p.advance()
            let obj = p.parseExpr()
            result = FlatZincSolve(solveType: fsMinimize, objective: obj, annotations: annotations)
        of tkMaximize:
            discard p.advance()
            let obj = p.parseExpr()
            result = FlatZincSolve(solveType: fsMaximize, objective: obj, annotations: annotations)
        else:
            raise newException(ParseError, "Expected satisfy, minimize, or maximize at line " & $p.current.line)
    
    discard p.expect(tkSemicolon)

################################################################################
# Output statement parsing
################################################################################

proc parseOutput(p: var Parser): seq[string] =
    discard p.expect(tkOutput)
    discard p.expect(tkLBracket)
    
    result = @[]
    while not p.match(tkRBracket) and not p.match(tkEof):
        if p.match(tkString):
            result.add(p.advance().value)
        elif p.match(tkIdent):
            let ident = p.advance().value
            if p.match(tkLParen):
                # Function call like show(x) - skip the function call for now
                discard p.advance() # Skip (
                while not p.match(tkRParen) and not p.match(tkEof):
                    discard p.advance() # Skip function arguments
                if p.match(tkRParen):
                    discard p.advance() # Skip )
                result.add(ident) # Just use the function name
            else:
                result.add(ident)
        else:
            # Skip unknown tokens
            discard p.advance()
        
        if p.match(tkComma):
            discard p.advance()
        else:
            break
    
    discard p.expect(tkRBracket)
    discard p.expect(tkSemicolon)

################################################################################
# Model parsing
################################################################################

proc parseModel*(p: var Parser): FlatZincModel =
    result = FlatZincModel(
        predicates: @[],
        varDecls: @[],
        constraints: @[],
        output: @[]
    )
    
    while not p.match(tkEof):
        case p.current.kind:
            of tkPredicate:
                # Skip predicate declarations for now
                discard p.advance()
                while not p.match(tkSemicolon) and not p.match(tkEof):
                    discard p.advance()
                if p.match(tkSemicolon):
                    discard p.advance()
            of tkVar, tkPar, tkArray, tkBool1, tkInt1, tkFloat1:
                result.varDecls.add(p.parseVarDecl())
            of tkConstraint:
                result.constraints.add(p.parseConstraint())
            of tkSolve:
                result.solve = p.parseSolve()
            of tkOutput:
                result.output = p.parseOutput()
            else:
                raise newException(ParseError, "Unexpected token at top level: " & $p.current.kind & " at line " & $p.current.line)

################################################################################
# Main parsing function
################################################################################

proc parseFlatZinc*(input: string): FlatZincModel =
    let tokens = tokenize(input)
    var parser = initParser(tokens)
    result = parser.parseModel()