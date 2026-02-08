import std/[sequtils, tables, unittest, algorithm]
import crusher

# Test the IRDCS constraint implementation
# Based on "Odd Incongruent Restricted Disjoint Covering Systems" by Paul Robert Emanuel

proc validateIrdcsSolution(assignment: seq[int], n: int): bool =
    ## Validate that an assignment forms a valid IRDCS of length n
    ## Returns true if valid, false otherwise

    # Group positions by modulus
    var indicesByModulus: Table[int, seq[int]]
    for i in 0..<n:
        let modulus = assignment[i]
        let idx = i + 1  # 1-indexed interval position
        if modulus notin indicesByModulus:
            indicesByModulus[modulus] = @[]
        indicesByModulus[modulus].add(idx)

    # Check each modulus
    for modulus, indices in indicesByModulus.pairs:
        # Must have at least 2 positions (restricted)
        if indices.len < 2:
            echo "Modulus ", modulus, " has only ", indices.len, " positions (need >= 2)"
            return false

        # All positions must have same residue mod modulus
        let expectedResidue = indices[0] mod modulus
        for idx in indices:
            if idx mod modulus != expectedResidue:
                echo "Modulus ", modulus, ": index ", idx, " has residue ", idx mod modulus,
                     " but expected ", expectedResidue
                return false

    return true

proc getCongruenceClasses(assignment: seq[int], n: int): seq[(int, int)] =
    ## Extract (modulus, residue) pairs from an assignment
    var indicesByModulus: Table[int, seq[int]]
    for i in 0..<n:
        let modulus = assignment[i]
        let idx = i + 1
        if modulus notin indicesByModulus:
            indicesByModulus[modulus] = @[]
        indicesByModulus[modulus].add(idx)

    result = @[]
    for modulus, indices in indicesByModulus.pairs:
        if indices.len > 0:
            result.add((modulus, indices[0] mod modulus))
    result.sort()

suite "IRDCS Constraint Tests":

    test "Validate length 11 example from paper":
        # Example from the paper: {0 (mod 3), 0 (mod 4), 0 (mod 5), 1 (mod 6), 2 (mod 9)}
        # Alternate notation: 6,9,3,4,5,3,6,4,3,5,9
        let assignment = @[6, 9, 3, 4, 5, 3, 6, 4, 3, 5, 9]
        check validateIrdcsSolution(assignment, 11)

        # Verify the congruence classes
        let classes = getCongruenceClasses(assignment, 11)
        # Should have: (3,0), (4,0), (5,0), (6,1), (9,2)
        check classes.len == 5

    test "Length 11 IRDCS constraint - valid solution has cost 0":
        # Test constraint directly with known valid solution
        let knownSolution = @[6, 9, 3, 4, 5, 3, 6, 4, 3, 5, 9]
        let n = 11

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(knownSolution)

        check constraint.cost == 0
        check constraint.isValid()

    test "Length 11 IRDCS constraint - invalid solution has cost > 0":
        # All same modulus but different residues
        let invalidSolution = @[3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
        let n = 11

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(invalidSolution)

        # Positions have residues: 1,2,0,1,2,0,1,2,0,1,2 (mod 3)
        # Group sizes: residue 0 has 3 positions (3,6,9), residue 1 has 4 (1,4,7,10), residue 2 has 4 (2,5,8,11)
        # This creates many conflict pairs
        check constraint.cost > 0
        check not constraint.isValid()

    test "Length 11 IRDCS - solve via constraint system":
        var sys = initConstraintSystem[int]()

        # Create 11 variables (positions 0-10)
        var vars: seq[ConstrainedVariable[int]] = @[]
        for i in 0..<11:
            var v = sys.newConstrainedVariable()
            # Domain: moduli from the known solution
            v.setDomain(@[3, 4, 5, 6, 9])
            vars.add(v)

        # Add IRDCS constraint
        let positions = toSeq(0..<11)
        sys.addConstraint(irdcs[int](positions))

        # Try to solve
        sys.resolve()

        # Check if solution is valid
        var assignment: seq[int] = @[]
        for v in vars:
            assignment.add(v.assignment)

        check validateIrdcsSolution(assignment, 11)

    test "Length 83 odd IRDCS - validate known solution":
        # The unique shortest odd IRDCS from the paper (length 83)
        let assignment = @[
            61, 41, 21, 65, 9, 43, 53, 59, 11, 15, 37, 17, 13, 9, 23, 19, 27, 33, 55, 11, 35,
            25, 9, 21, 15, 13, 31, 29, 17, 51, 11, 9, 49, 45, 19, 47, 39, 23, 13, 15, 9, 11,
            41, 27, 21, 17, 25, 37, 43, 9, 33, 13, 11, 19, 15, 35, 29, 31, 9, 53, 23, 61, 17,
            11, 13, 21, 59, 9, 65, 15, 27, 25, 19, 55, 11, 39, 9, 13, 45, 17, 51, 49, 47
        ]
        check assignment.len == 83
        check validateIrdcsSolution(assignment, 83)

        # Verify all moduli are odd
        for m in assignment:
            check m mod 2 == 1

    test "Length 83 odd IRDCS constraint - valid solution has cost 0":
        let n = 83
        let knownSolution = @[
            61, 41, 21, 65, 9, 43, 53, 59, 11, 15, 37, 17, 13, 9, 23, 19, 27, 33, 55, 11, 35,
            25, 9, 21, 15, 13, 31, 29, 17, 51, 11, 9, 49, 45, 19, 47, 39, 23, 13, 15, 9, 11,
            41, 27, 21, 17, 25, 37, 43, 9, 33, 13, 11, 19, 15, 35, 29, 31, 9, 53, 23, 61, 17,
            11, 13, 21, 59, 9, 65, 15, 27, 25, 19, 55, 11, 39, 9, 13, 45, 17, 51, 49, 47
        ]

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(knownSolution)

        check constraint.cost == 0
        check constraint.isValid()

    test "Length 84 odd IRDCS - validate first example":
        # First length 84 odd IRDCS from the paper
        let assignment = @[
            57, 13, 59, 47, 17, 21, 9, 29, 11, 39, 49, 35, 37, 15, 13, 9, 23, 27, 19, 11, 25, 17, 45,
            31, 9, 55, 21, 13, 15, 53, 11, 33, 51, 9, 43, 41, 29, 19, 17, 23, 13, 11, 9, 15, 27, 25,
            35, 21, 39, 37, 47, 9, 11, 13, 31, 17, 19, 57, 15, 49, 9, 59, 23, 11, 33, 29, 13, 45, 21,
            9, 25, 27, 17, 15, 11, 19, 41, 43, 9, 13, 55, 35, 53, 51
        ]
        check assignment.len == 84
        check validateIrdcsSolution(assignment, 84)

        # Verify all moduli are odd
        for m in assignment:
            check m mod 2 == 1

        # Test constraint
        let constraint = newIrdcsConstraint[int](84)
        constraint.initialize(assignment)
        check constraint.cost == 0

    test "moveDelta correctness":
        let n = 11
        let initialAssignment = @[3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6]

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(initialAssignment)

        let initialCost = constraint.cost

        # Test moveDelta for a specific move: change position 0 from 3 to 9
        let pos = 0
        let oldVal = 3
        let newVal = 9

        let delta = constraint.moveDelta(pos, oldVal, newVal)

        # Actually make the move and check
        constraint.updatePosition(pos, newVal)
        let newCost = constraint.cost

        check newCost - initialCost == delta

    test "moveDelta correctness - multiple moves":
        let n = 11
        let assignment = @[6, 9, 3, 4, 5, 3, 6, 4, 3, 5, 9]  # Valid solution

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(assignment)

        check constraint.cost == 0

        # Make a move that should increase cost
        let pos = 0
        let oldVal = 6
        let newVal = 3  # Change from 6 to 3

        let delta = constraint.moveDelta(pos, oldVal, newVal)
        constraint.updatePosition(pos, newVal)

        # Position 1 (index 1) with modulus 3 has residue 1 mod 3
        # Existing positions with modulus 3: indices 3, 6, 9 (residues 0, 0, 0)
        # So adding index 1 with residue 1 creates conflicts
        check constraint.cost > 0
        check constraint.cost == delta  # Since initial cost was 0

    test "Singleton penalty":
        # Test that using a modulus for only 1 position incurs penalty
        let n = 5

        # Modulus 7 used only once (position 0, index 1)
        # Modulus 3 used twice (positions 1,2 -> indices 2,3 -> residues 2,0) - conflict!
        # Modulus 5 used twice (positions 3,4 -> indices 4,5 -> residues 4,0) - conflict!
        let assignment = @[7, 3, 3, 5, 5]

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(assignment)

        # Should have singleton penalty for modulus 7
        # Plus conflict penalties for modulus 3 and 5
        check constraint.cost > 0

    test "Valid small IRDCS":
        # Create a small valid IRDCS manually
        # For n=6: positions 1,2,3,4,5,6
        # Use modulus 3 for positions 3,6 (indices 3,6 have residues 0,0 mod 3) - OK
        # Use modulus 4 for positions 4 (residue 0 mod 4) - singleton!
        # Use modulus 2 for positions 2,4,6 (residues 0,0,0 mod 2) - but 2 is too small

        # Let's try: n=4, modulus 2 for positions 2,4 (indices with residue 0 mod 2)
        #            modulus 3 for positions 1,3 - wait, 1 mod 3 = 1, 3 mod 3 = 0, conflict!

        # Actually valid small IRDCS are hard to construct. The paper shows length 11 is minimal for general case.
        # Let's just verify the length 11 solution works through the constraint system.
        var sys = initConstraintSystem[int]()

        var vars = sys.newConstrainedSequence(11)
        vars.setDomain(@[3, 4, 5, 6, 9])

        let positions = toSeq(0..<11)
        sys.addConstraint(irdcs[int](positions))

        sys.resolve()

        var assignment: seq[int] = vars.assignment
        check validateIrdcsSolution(assignment, 11)

    test "Deep copy preserves state":
        let n = 11
        let assignment = @[6, 9, 3, 4, 5, 3, 6, 4, 3, 5, 9]

        let constraint = newIrdcsConstraint[int](n)
        constraint.initialize(assignment)

        let copy = constraint.deepCopy()

        check copy.cost == constraint.cost
        check copy.n == constraint.n

        # Modify original
        constraint.updatePosition(0, 3)

        # Copy should be unchanged
        check copy.cost == 0  # Original valid solution cost
        check constraint.cost > 0  # Modified has violations
