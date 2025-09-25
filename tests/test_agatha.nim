import std/[sequtils, unittest]
import crusher

suite "Complex Reification Test":
    test "Who Killed":
        # agatha, the butler, and charles live in the mansion, and are the only ones there
        let
            N = 3
            agatha = 0
            butler = 1
            charles = 2

        var sys = initConstraintSystem[int]()

        # the killer is one of the three
        var killer = sys.newConstrainedVariable()
        killer.setDomain([agatha, butler, charles])

        # define hates and richer boolean matrices
        var hates = sys.newConstrainedMatrix(N, N)
        hates.setDomain([0, 1])

        var richer = sys.newConstrainedMatrix(N, N)
        richer.setDomain([0, 1])

        for i in 0..<N:
            # the killer hates the victim
            sys.addConstraint(
                (killer == i) -> (hates[i, agatha] == 1)
            )
            # the killer is no richer than the victim
            sys.addConstraint(
                (killer == i) -> (richer[i, agatha] == 0)
            )

        # no one is richer than themselves
        for i in 0..<N:
            sys.addConstraint(richer[i, i] == 0)

        # if i is richer than n, then j is not richer than i
        for i in 0..<N:
            for j in 0..<N:
                if i != j:
                    sys.addConstraint(
                        (richer[i, j] == 1) <-> (richer[j, i] == 0)
                    )

        # charles hates nobody that agatha hates
        for i in 0..<N:
            sys.addConstraint(
                (hates[agatha, i] == 1) -> (hates[charles, i] == 0)
            )

        # agatha hates everyone except the butler
        sys.addConstraint(hates[agatha, agatha] == 1)
        sys.addConstraint(hates[agatha, butler] == 0)
        sys.addConstraint(hates[agatha, charles] == 1)

        # the butler hates everyone not richer than aunt agatha
        for i in 0..<N:
            sys.addConstraint(
                (richer[i, agatha] == 0) -> (hates[butler, i] == 1)
            )

        # the butler hates everyone whome agatha hates
        for i in 0..<N:
            sys.addConstraint(
                (hates[agatha, i] == 1) -> (hates[butler, i] == 1)
            )

        # nobody hates everyone
        for row in hates.rows():
            sys.addConstraint(sum(row) <= 2)

        sys.resolve()

        echo "Solution found!"
        echo "Killer: ", killer.assignment()
        let killerName = case killer.assignment():
            of 0: "Agatha"
            of 1: "Butler"
            of 2: "Charles"
            else: "Unknown"
        echo "The killer is: ", killerName

        echo "\nHates matrix:"
        let hatesAssignment = hates.assignment
        for i in 0..<N:
            let personName = case i:
                of 0: "Agatha"
                of 1: "Butler"
                of 2: "Charles"
                else: "Unknown"
            echo personName, " hates: ",
                (if hatesAssignment[i][agatha] == 1: "Agatha " else: ""),
                (if hatesAssignment[i][butler] == 1: "Butler " else: ""),
                (if hatesAssignment[i][charles] == 1: "Charles " else: "")

        echo "\nRicher matrix:"
        let richerAssignment = richer.assignment
        for i in 0..<N:
            let personName = case i:
                of 0: "Agatha"
                of 1: "Butler"
                of 2: "Charles"
                else: "Unknown"
            echo personName, " is richer than: ",
                (if richerAssignment[i][agatha] == 1: "Agatha " else: ""),
                (if richerAssignment[i][butler] == 1: "Butler " else: ""),
                (if richerAssignment[i][charles] == 1: "Charles " else: "")

        # Verify the solution
        check killer.assignment() == agatha  # Agatha killed herself
