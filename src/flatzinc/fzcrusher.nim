################################################################################
# FlatZinc parser and translator for Crusher constraint solver
################################################################################
# 
# This module provides functionality to parse FlatZinc files and translate
# them into Crusher constraint systems for solving.

import std/[os, strformat, tables]
import parser, ast, translator

################################################################################
# Main solving function
################################################################################

proc solveFlatZincFile*(filename: string): bool =
    ## Parse and solve a FlatZinc file
    ## Returns true if a solution was found
    
    if not fileExists(filename):
        echo fmt"Error: File '{filename}' not found"
        return false
    
    let content = readFile(filename)
    
    try:
        # Parse the FlatZinc model
        let model = parseFlatZinc(content)
        echo fmt"Parsed FlatZinc model with {model.varDecls.len} variables and {model.constraints.len} constraints"
        
        # Translate to Crusher constraint system
        var translator = translateModel(model)
        echo fmt"Translated to Crusher system with {translator.system.baseArray.len} variables and {translator.system.baseArray.constraints.len} constraints"
        
        # Solve the constraint system
        let solved = translator.solve(model)
        
        if solved:
            echo "Solution found:"
            let solution = translator.getSolution()
            for varName, value in solution:
                echo fmt"  {varName} = {value}"
            return true
        else:
            echo "No solution found"
            return false
            
    except ParseError as e:
        echo fmt"Parse error: {e.msg}"
        return false
    except Exception as e:
        echo fmt"Error: {e.msg}"
        return false

################################################################################
# File parsing function
################################################################################

proc parseFlatZincFile*(filename: string): FlatZincModel =
    ## Parse a FlatZinc file and return the model
    let content = readFile(filename)
    result = parseFlatZinc(content)

################################################################################
# Main module execution
################################################################################

when isMainModule:
    import std/parseopt
    
    var filename = ""
    
    for kind, key, val in getopt():
        case kind:
            of cmdArgument:
                filename = key
            of cmdLongOption, cmdShortOption:
                case key:
                    of "h", "help":
                        echo "Usage: flatzinc [file.fzn]"
                        echo "Parse and solve FlatZinc constraint problems"
                        quit(0)
            of cmdEnd:
                discard
    
    if filename == "":
        echo "Usage: flatzinc [file.fzn]"
        quit(1)
    
    discard solveFlatZincFile(filename)