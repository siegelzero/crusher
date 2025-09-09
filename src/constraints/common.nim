import std/[tables, packedsets]
import ../expressions/expressions

################################################################################
# Common constraint infrastructure
################################################################################

################################################################################
# Count table operations
################################################################################

proc incrementCount*[T](countTable: var Table[T, int], value: T) {.inline.} =
    ## Increments the count for a value in the count table
    if value in countTable:
        countTable[value] += 1
    else:
        countTable[value] = 1

proc decrementCount*[T](countTable: var Table[T, int], value: T) {.inline.} =
    ## Decrements the count for a value, removing zero entries for memory efficiency
    if value in countTable:
        countTable[value] -= 1
        if countTable[value] <= 0:
            countTable.del(value)

proc getCount*[T](countTable: Table[T, int], value: T): int {.inline.} =
    ## Gets the count for a value, returning 0 if not present
    countTable.getOrDefault(value, 0)


################################################################################
# Expression position mapping
################################################################################



################################################################################
# Position-based constraint utilities
################################################################################

proc collectAllPositions*[T](expressions: seq[AlgebraicExpression[T]]): PackedSet[int] =
    ## Collects all positions referenced by a sequence of expressions
    result = toPackedSet[int]([])
    for exp in expressions:
        result.incl(exp.positions)

################################################################################
# Expression evaluation utilities
################################################################################

proc evaluateWithTempAssignment*[T](exp: AlgebraicExpression[T],
                                   currentAssignment: Table[int, T],
                                   position: int,
                                   tempValue: T): T =
    ## Evaluates an expression with a temporary value assignment
    var tempAssignment = currentAssignment
    tempAssignment[position] = tempValue
    return exp.evaluate(tempAssignment)