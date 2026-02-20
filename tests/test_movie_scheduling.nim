## Movie Scheduling Test
## =====================
##
## Port of hakank's movie scheduling problem from Picat.
## From Steven Skiena "The Algorithm Design Manual", page 9ff.
##
## This demonstrates:
## - Boolean indicator variables (0/1)
## - Reification with boolean constraints
## - Implication constraints (->)
## - Optimization with maximize()
##
## Optimal solution: Z = 4 (4 movies can be watched without overlap)

import std/[sequtils, unittest]
import crusher

type
    Movie = object
        name: string
        start: int
        endTime: int

const
    Movies = [
        Movie(name: "Tarjan of the Jungle", start: 4, endTime: 13),
        Movie(name: "The Four Volume Problem", start: 17, endTime: 27),
        Movie(name: "The President's Algorist", start: 1, endTime: 10),
        Movie(name: "Steiner's Tree", start: 12, endTime: 18),
        Movie(name: "Process Terminated", start: 23, endTime: 30),
        Movie(name: "Halting State", start: 9, endTime: 16),
        Movie(name: "Programming Challenges", start: 19, endTime: 25),
        Movie(name: "'Discrete' Mathematics", start: 2, endTime: 7),
        Movie(name: "Calculated Bets", start: 26, endTime: 31),
    ]
    NumMovies = Movies.len

proc moviesOverlap(m1, m2: Movie): bool =
    ## Two movies overlap if neither starts after the other ends
    not (m1.start > m2.endTime or m2.start > m1.endTime)

proc solveMovieScheduling(): tuple[z: int, selected: seq[int]] =
    ## Solve the movie scheduling problem
    ## Returns the optimal count and indices of selected movies
    var sys = initConstraintSystem[int]()

    # X[i] = 1 if movie i is selected, 0 otherwise
    var X = sys.newConstrainedSequence(NumMovies)
    X.setDomain(@[0, 1])

    # For each pair of overlapping movies, at most one can be selected
    # This uses reification: (X[i] == 1 and X[j] == 1) -> not_overlap
    # Since overlap is constant, for overlapping pairs: not(X[i] == 1 and X[j] == 1)
    for i in 0..<NumMovies:
        for j in (i+1)..<NumMovies:
            if moviesOverlap(Movies[i], Movies[j]):
                # If movies overlap, can't select both
                # Using boolean constraint: not(both selected)
                sys.addConstraint(not ((X[i] == 1) and (X[j] == 1)))

    # Objective: maximize sum of X (number of selected movies)
    let objective = X.sum()

    sys.maximize(objective, verbose=false, parallel=true, populationSize=16, tabuThreshold=10000)

    let assignment = X.assignment()
    var selected: seq[int] = @[]
    for i in 0..<NumMovies:
        if assignment[i] == 1:
            selected.add(i)

    return (selected.len, selected)

proc solveMovieSchedulingWithExplicitReification(): tuple[z: int, selected: seq[int]] =
    ## Alternative approach using explicit reified boolean variables (B)
    ## This more closely mirrors the Picat model's reification pattern
    var sys = initConstraintSystem[int]()

    # X[i] = 1 if movie i is selected, 0 otherwise
    var X = sys.newConstrainedSequence(NumMovies)
    X.setDomain(@[0, 1])

    # B[i][j] = 1 iff movies i and j don't overlap (reified variable)
    # Since overlap is constant, B[i][j] is constant and we model it directly
    for i in 0..<NumMovies:
        for j in (i+1)..<NumMovies:
            let noOverlap = not moviesOverlap(Movies[i], Movies[j])

            # Picat pattern: (X[i] == 1 /\ X[j] == 1) => B == 1
            # When B = 0 (movies overlap): (X[i] == 1 and X[j] == 1) => false
            # This means: not(X[i] == 1 and X[j] == 1)
            if not noOverlap:
                # Movies overlap - can't select both
                # Using implication: (X[i] == 1 and X[j] == 1) -> <false condition>
                # Equivalent to: not(X[i] == 1 and X[j] == 1)
                sys.addConstraint(not ((X[i] == 1) and (X[j] == 1)))
            # else: movies don't overlap, no constraint needed (B = 1, implication trivially true)

    let objective = X.sum()
    sys.maximize(objective, verbose=false, parallel=true, populationSize=16, tabuThreshold=10000)

    let assignment = X.assignment()
    var selected: seq[int] = @[]
    for i in 0..<NumMovies:
        if assignment[i] == 1:
            selected.add(i)

    return (selected.len, selected)

proc verifySolution(selected: seq[int]): bool =
    ## Verify that selected movies don't overlap
    for i in 0..<selected.len:
        for j in (i+1)..<selected.len:
            if moviesOverlap(Movies[selected[i]], Movies[selected[j]]):
                return false
    return true

suite "Movie Scheduling Tests":

    test "Find optimal schedule (Z=4) - basic approach":
        let (z, selected) = solveMovieScheduling()

        echo "Optimal Z = ", z
        echo "Selected movies:"
        for idx in selected:
            echo "  ", Movies[idx].name, " [", Movies[idx].start, "-", Movies[idx].endTime, "]"

        # Verify optimal value matches Picat
        check z == 4

        # Verify no overlaps
        check verifySolution(selected)

    test "Find optimal schedule - explicit reification approach":
        let (z, selected) = solveMovieSchedulingWithExplicitReification()

        echo "Optimal Z = ", z
        echo "Selected movies:"
        for idx in selected:
            echo "  ", Movies[idx].name, " [", Movies[idx].start, "-", Movies[idx].endTime, "]"

        # Verify optimal value matches Picat
        check z == 4

        # Verify no overlaps
        check verifySolution(selected)

    test "Boolean NOT constraint for overlap prevention":
        ## Test that NOT(A and B) correctly prevents selection of overlapping pairs
        var sys = initConstraintSystem[int]()

        # Two movies that overlap: Tarjan [4-13] and Halting State [9-16]
        var x1 = sys.newConstrainedVariable()
        var x2 = sys.newConstrainedVariable()
        x1.setDomain(@[0, 1])
        x2.setDomain(@[0, 1])

        # Constraint: can't select both (they overlap)
        sys.addConstraint(not ((x1 == 1) and (x2 == 1)))

        # Try to select both - should fail, solver picks one
        sys.addConstraint(x1 + x2 >= 1)  # At least one must be selected
        sys.resolve(verbose=false)

        let v1 = x1.assignment()
        let v2 = x2.assignment()

        echo "x1 = ", v1, ", x2 = ", v2

        # At most one should be 1
        check (v1 == 1 and v2 == 0) or (v1 == 0 and v2 == 1) or (v1 == 0 and v2 == 0)
        # At least one should be 1
        check v1 + v2 >= 1
        # Combined: exactly one should be 1
        check v1 + v2 == 1

    test "Implication constraint equivalent to NOT(A and B)":
        ## Demonstrate that (A and B) -> false is equivalent to not(A and B)
        var sys = initConstraintSystem[int]()

        var x1 = sys.newConstrainedVariable()
        var x2 = sys.newConstrainedVariable()
        var dummy = sys.newConstrainedVariable()

        x1.setDomain(@[0, 1])
        x2.setDomain(@[0, 1])
        dummy.setDomain(@[0])  # Always 0, used for false condition

        # (x1 == 1 and x2 == 1) -> (dummy == 1)
        # Since dummy can only be 0, this is equivalent to: not(x1 == 1 and x2 == 1)
        sys.addConstraint(((x1 == 1) and (x2 == 1)) -> (dummy == 1))

        # Force both to try to be 1
        sys.addConstraint(x1 + x2 >= 1)

        sys.resolve(verbose=false)

        let v1 = x1.assignment()
        let v2 = x2.assignment()

        echo "Implication test: x1 = ", v1, ", x2 = ", v2

        # Both cannot be 1 due to the constraint
        check not (v1 == 1 and v2 == 1)

    test "Sum constraint for counting selected items":
        ## Test sum of boolean indicators
        var sys = initConstraintSystem[int]()

        var X = sys.newConstrainedSequence(5)
        X.setDomain(@[0, 1])

        # Select exactly 2
        sys.addConstraint(X.sum() == 2)
        sys.resolve(verbose=false)

        let assignment = X.assignment()
        var count = 0
        for v in assignment:
            if v == 1:
                count += 1

        check count == 2
