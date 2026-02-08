# Search for an odd IRDCS of length 83
# According to the paper, the shortest odd IRDCS has length 83 and uses
# odd moduli from 9 to 65 (excluding 57 and 63)

import std/[sequtils, tables, algorithm, times]
import ../src/crusher

proc validateIrdcsSolution(assignment: seq[int], n: int): bool =
    ## Validate that an assignment forms a valid IRDCS
    var indicesByModulus: Table[int, seq[int]]
    for i in 0..<n:
        let modulus = assignment[i]
        let idx = i + 1
        if modulus notin indicesByModulus:
            indicesByModulus[modulus] = @[]
        indicesByModulus[modulus].add(idx)

    for modulus, indices in indicesByModulus.pairs:
        if indices.len < 2:
            echo "  Invalid: Modulus ", modulus, " has only ", indices.len, " position(s)"
            return false
        let expectedResidue = indices[0] mod modulus
        for idx in indices:
            if idx mod modulus != expectedResidue:
                echo "  Invalid: Modulus ", modulus, " has inconsistent residues"
                return false
    return true

proc printSolution(assignment: seq[int], n: int) =
    echo "\nAlternate notation (modulus for each position):"
    echo assignment

    # Extract congruence classes
    var indicesByModulus: Table[int, seq[int]]
    for i in 0..<n:
        let modulus = assignment[i]
        let idx = i + 1
        if modulus notin indicesByModulus:
            indicesByModulus[modulus] = @[]
        indicesByModulus[modulus].add(idx)

    echo "\nCongruence classes:"
    var moduli: seq[int] = @[]
    for m in indicesByModulus.keys:
        moduli.add(m)
    moduli.sort()

    for m in moduli:
        let indices = indicesByModulus[m]
        let residue = indices[0] mod m
        echo "  ", residue, " (mod ", m, ") covers ", indices.len, " positions"

    # Compact notation
    var compactNotation: seq[int] = @[]
    var seen: seq[int] = @[]
    for m in assignment:
        if m notin seen:
            seen.add(m)
            compactNotation.add(m)

    echo "\nCompact notation:"
    echo compactNotation

    # Statistics
    echo "\nStatistics:"
    echo "  Length: ", n
    echo "  Order (number of moduli): ", moduli.len
    var heft = 0.0
    for m in moduli:
        heft += 1.0 / m.float
    echo "  Heft: ", heft

    # Check if all odd
    var allOdd = true
    for m in moduli:
        if m mod 2 == 0:
            allOdd = false
            break
    echo "  All odd: ", allOdd

proc main() =
    let n = 83
    echo "Searching for odd IRDCS of length ", n

    # Domain: odd numbers from 9 to 65 (the range used in the paper's solution)
    # Excluding 57 and 63 based on the paper's known solution
    var domain: seq[int] = @[]
    for m in countup(9, 65, 2):  # Odd numbers from 9 to 65
        domain.add(m)

    echo "Domain size: ", domain.len, " moduli"
    echo "Domain: ", domain

    var sys = initConstraintSystem[int]()

    # Create n variables
    var vars = sys.newConstrainedSequence(n)
    vars.setDomain(domain)

    # Add IRDCS constraint
    let positions = toSeq(0..<n)
    sys.addConstraint(irdcs[int](positions))

    echo "\nStarting search..."
    let startTime = cpuTime()

    # Solve with verbose output
    sys.resolve(parallel = true, verbose = true, tabuThreshold=1000)

    let elapsed = cpuTime() - startTime
    echo "\nSearch completed in ", elapsed, " seconds"

    # Get solution
    let assignment = vars.assignment

    # Validate
    echo "\nValidating solution..."
    if validateIrdcsSolution(assignment, n):
        echo "Solution is VALID!"
        printSolution(assignment, n)
    else:
        echo "Solution is INVALID"
        echo "Assignment: ", assignment

when isMainModule:
    main()
