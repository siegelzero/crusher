import std/[sequtils, unittest]
import ../src/crusher

suite "Constant Element Composition":
    test "Element constraint with constant array":
        ## Tests the constant element composition optimization foundation.
        ## The optimization detects element(y, constArray, x) constraints where
        ## constArray is constant, and enables downstream checks on x to be
        ## composed directly from y, eliminating the intermediate x channel variable
        ## from the penalty computation graph.

        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(2)  # index, value
        variables.setDomain([0, 1, 10, 12])

        let constArray = @[10, 12]
        system.addConstraint(element(variables[0], constArray, variables[1]))

        system.resolve()

        let solution = variables.assignment
        let index = solution[0]
        let value = solution[1]

        # Verify the element constraint is satisfied
        check value == constArray[index]
        echo "Element: index=", index, ", value=", value, " (expected constArray[", index, "]=", constArray[index], ")"

    test "Element constraint with larger constant array":
        ## Tests element constraint with a bigger constant array

        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(2)
        variables.setDomain(toSeq(0..4) & toSeq(100..104))

        let constArray = @[100, 101, 102, 103, 104]
        system.addConstraint(element(variables[0], constArray, variables[1]))

        system.resolve()

        let solution = variables.assignment
        let index = solution[0]
        let value = solution[1]

        # Verify the element constraint is satisfied
        check index in [0, 1, 2, 3, 4]
        check value == constArray[index]
        echo "Extended: index=", index, ", value=", value, " (expected ", constArray[index], ")"

    test "Multiple element constraints with same array":
        ## Tests two independent element constraints using the same constant array

        let system = initConstraintSystem[int]()
        let v1 = system.newConstrainedSequence(2)
        let v2 = system.newConstrainedSequence(2)

        v1.setDomain([0, 1, 20, 22])
        v2.setDomain([0, 1, 20, 22])

        let constArray = @[20, 22]
        system.addConstraint(element(v1[0], constArray, v1[1]))
        system.addConstraint(element(v2[0], constArray, v2[1]))

        system.resolve()

        let sol1 = v1.assignment
        let sol2 = v2.assignment

        let index1 = sol1[0]
        let value1 = sol1[1]
        let index2 = sol2[0]
        let value2 = sol2[1]

        check value1 == constArray[index1]
        check value2 == constArray[index2]
        echo "Multi-element: v1=", value1, " (index ", index1, "), v2=", value2, " (index ", index2, ")"
