import std/[strutils, tables]

################################################################################
# Type definitions
################################################################################

type
    TokenKind* = enum
        tkEof, tkError
        # Literals
        tkInt, tkFloat, tkString, tkBool, tkSet
        # Identifiers and keywords
        tkIdent
        tkVar, tkPar, tkArray, tkOf, tkInt1, tkBool1, tkFloat1
        tkConstraint, tkSolve, tkSatisfy, tkMinimize, tkMaximize
        tkPredicate, tkOutput
        # Operators and symbols
        tkLParen, tkRParen, tkLBracket, tkRBracket, tkLBrace, tkRBrace
        tkComma, tkSemicolon, tkColon, tkEq, tkDotDot, tkAnnotations
        # Special
        tkComment

    Token* = object
        kind*: TokenKind
        value*: string
        line*: int
        col*: int

    Lexer* = object
        input*: string
        pos*: int
        line*: int
        col*: int

################################################################################
# Constants
################################################################################

const Keywords = {
    "var": tkVar,
    "par": tkPar, 
    "array": tkArray,
    "of": tkOf,
    "int": tkInt1,
    "bool": tkBool1,
    "float": tkFloat1,
    "constraint": tkConstraint,
    "solve": tkSolve,
    "satisfy": tkSatisfy,
    "minimize": tkMinimize,
    "maximize": tkMaximize,
    "predicate": tkPredicate,
    "output": tkOutput,
    "true": tkBool,
    "false": tkBool
}.toTable

################################################################################
# Lexer initialization
################################################################################

proc initLexer*(input: string): Lexer =
    result = Lexer(input: input, pos: 0, line: 1, col: 1)

################################################################################
# Lexer utility functions
################################################################################

proc current(lex: Lexer): char =
    if lex.pos >= lex.input.len:
        '\0'
    else:
        lex.input[lex.pos]

proc advance(lex: var Lexer): char =
    result = lex.current
    if result == '\n':
        lex.line += 1
        lex.col = 1
    else:
        lex.col += 1
    lex.pos += 1

proc peek(lex: Lexer, offset: int = 1): char =
    let peekPos = lex.pos + offset
    if peekPos >= lex.input.len:
        '\0'
    else:
        lex.input[peekPos]

proc skipWhitespace(lex: var Lexer) =
    while lex.current in {' ', '\t', '\n', '\r'}:
        discard lex.advance()

################################################################################
# Token reading functions
################################################################################

proc readNumber(lex: var Lexer): Token =
    var value = ""
    let startLine = lex.line
    let startCol = lex.col
    var isFloat = false
    
    while lex.current.isDigit:
        value.add(lex.advance())
    
    # Only treat as float if we have a dot followed by digits
    if lex.current == '.' and lex.peek().isDigit:
        isFloat = true
        value.add(lex.advance())
        while lex.current.isDigit:
            value.add(lex.advance())
    
    result = Token(
        kind: if isFloat: tkFloat else: tkInt,
        value: value,
        line: startLine,
        col: startCol
    )

proc readIdentifier(lex: var Lexer): Token =
    var value = ""
    let startLine = lex.line
    let startCol = lex.col
    
    while lex.current.isAlphaNumeric or lex.current == '_':
        value.add(lex.advance())
    
    let kind = Keywords.getOrDefault(value, tkIdent)
    result = Token(
        kind: kind,
        value: value,
        line: startLine,
        col: startCol
    )

proc readString(lex: var Lexer): Token =
    var value = ""
    let startLine = lex.line
    let startCol = lex.col
    let quote = lex.advance() # Skip opening quote
    
    while lex.current != quote and lex.current != '\0':
        if lex.current == '\\':
            discard lex.advance()
            case lex.current:
                of 'n': value.add('\n')
                of 't': value.add('\t')
                of 'r': value.add('\r')
                of '\\': value.add('\\')
                of '"': value.add('"')
                of '\'': value.add('\'')
                else: value.add(lex.current)
        else:
            value.add(lex.current)
        discard lex.advance()
    
    if lex.current == quote:
        discard lex.advance() # Skip closing quote
    
    result = Token(
        kind: tkString,
        value: value,
        line: startLine,
        col: startCol
    )

proc readSet(lex: var Lexer): Token =
    var value = ""
    let startLine = lex.line
    let startCol = lex.col
    var braceCount = 1
    
    discard lex.advance() # Skip opening brace
    value.add('{')
    
    while braceCount > 0 and lex.current != '\0':
        let ch = lex.advance()
        value.add(ch)
        case ch:
            of '{': braceCount += 1
            of '}': braceCount -= 1
            else: discard
    
    result = Token(
        kind: tkSet,
        value: value,
        line: startLine,
        col: startCol
    )

proc readComment(lex: var Lexer): Token =
    var value = ""
    let startLine = lex.line
    let startCol = lex.col
    
    discard lex.advance() # Skip %
    while lex.current != '\n' and lex.current != '\0':
        value.add(lex.advance())
    
    result = Token(
        kind: tkComment,
        value: value,
        line: startLine,
        col: startCol
    )

################################################################################
# Main tokenization
################################################################################

proc nextToken*(lex: var Lexer): Token =
    lex.skipWhitespace()
    
    if lex.pos >= lex.input.len:
        return Token(kind: tkEof, line: lex.line, col: lex.col)
    
    let startLine = lex.line
    let startCol = lex.col
    
    case lex.current:
        of '0'..'9':
            result = lex.readNumber()
        of 'a'..'z', 'A'..'Z':
            result = lex.readIdentifier()
        of '"', '\'':
            result = lex.readString()
        of '{':
            result = lex.readSet()
        of '%':
            result = lex.readComment()
        of '(':
            discard lex.advance()
            result = Token(kind: tkLParen, value: "(", line: startLine, col: startCol)
        of ')':
            discard lex.advance()
            result = Token(kind: tkRParen, value: ")", line: startLine, col: startCol)
        of '[':
            discard lex.advance()
            result = Token(kind: tkLBracket, value: "[", line: startLine, col: startCol)
        of ']':
            discard lex.advance()
            result = Token(kind: tkRBracket, value: "]", line: startLine, col: startCol)
        of '}':
            discard lex.advance()
            result = Token(kind: tkRBrace, value: "}", line: startLine, col: startCol)
        of ',':
            discard lex.advance()
            result = Token(kind: tkComma, value: ",", line: startLine, col: startCol)
        of ';':
            discard lex.advance()
            result = Token(kind: tkSemicolon, value: ";", line: startLine, col: startCol)
        of ':':
            if lex.peek() == ':':
                discard lex.advance()
                discard lex.advance()
                result = Token(kind: tkAnnotations, value: "::", line: startLine, col: startCol)
            else:
                discard lex.advance()
                result = Token(kind: tkColon, value: ":", line: startLine, col: startCol)
        of '=':
            discard lex.advance()
            result = Token(kind: tkEq, value: "=", line: startLine, col: startCol)
        of '.':
            if lex.peek() == '.':
                discard lex.advance()
                discard lex.advance()
                result = Token(kind: tkDotDot, value: "..", line: startLine, col: startCol)
            else:
                discard lex.advance()
                result = Token(kind: tkError, value: ".", line: startLine, col: startCol)
        of '-':
            # Check if this is a negative number
            if lex.peek().isDigit:
                discard lex.advance() # Skip the '-'
                result = lex.readNumber()
                result.value = "-" & result.value
            else:
                discard lex.advance()
                result = Token(kind: tkError, value: "-", line: startLine, col: startCol)
        else:
            discard lex.advance()
            result = Token(kind: tkError, value: $lex.input[lex.pos-1], line: startLine, col: startCol)

proc tokenize*(input: string): seq[Token] =
    var lex = initLexer(input)
    result = @[]
    
    while true:
        let tok = lex.nextToken()
        if tok.kind == tkComment:
            continue # Skip comments
        result.add(tok)
        if tok.kind == tkEof:
            break