import unittest
import ../src/crusher

suite "Simple Element Test":
    test "Single element constraint with constant array":
        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(2)  # index, value

        variables.setDomain([0, 1, 10, 20])

        let values = @[10, 20]

        # Debug: check what positions we're getting
        echo "variables[0] node position: ", variables[0].node.position
        echo "variables[1] node position: ", variables[1].node.position

        # Constraint: values[variables[0]] = variables[1]
        # If variables[0] = 0, then variables[1] should be 10 (values[0])
        # If variables[0] = 1, then variables[1] should be 20 (values[1])
        let constraint = element(variables[0], values, variables[1])
        system.addConstraint(constraint)

        system.resolve()

        let solution = variables.assignment
        let index = solution[0]
        let value = solution[1]

        # Check that the constraint is satisfied
        let expectedValue = values[index]
        check value == expectedValue

        echo "Solution: index=", index, ", value=", value, " (expected ", expectedValue, ")"
