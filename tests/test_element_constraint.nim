import unittest
import std/[sequtils, random]

import ../src/crusher

################################################################################
# Test Element Constraint (based on Global Constraint Catalog)
################################################################################

suite "Element Constraint Tests":

    test "Basic element constraint - GCC example":
        # Based on Global Constraint Catalog example: element(3, 〈6,9,2,9,2〉, 2)
        # Note: We use 0-based indexing, so index 3 becomes 2, value at index 2 is 2
        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(2)  # index, value

        variables.setDomain([0, 1, 2, 3, 4, 6, 9])

        # Table from GCC: 〈6,9,2,9,2〉 (with duplicates)
        let table = @[6, 9, 2, 9, 2]
        let elementConstraint = element(variables[0], table, variables[1])
        system.addConstraint(elementConstraint)

        # Fix index to 2 (0-based equivalent of GCC's index 3)
        system.addConstraint(variables[0] == 2)

        system.resolve()

        let assignment = variables.assignment
        check assignment[0] == 2  # index
        check assignment[1] == 2  # value at table[2]
        echo "GCC Example - Index: ", assignment[0], ", Value: ", assignment[1]

    test "Element constraint with duplicate values in table":
        # Test that duplicates in table work correctly
        let table = @[10, 20, 10, 30, 20]

        # Test each index position
        for testIndex in 0..<table.len:
            # Create new system for each test
            let testSystem = initConstraintSystem[int]()
            let testVars = testSystem.newConstrainedSequence(2)
            testVars.setDomain([0, 1, 2, 3, 4, 5, 10, 20, 30])

            let testConstraint = element(testVars[0], table, testVars[1])
            testSystem.addConstraint(testConstraint)
            testSystem.addConstraint(testVars[0] == testIndex)

            testSystem.resolve()

            let assignment = testVars.assignment
            check assignment[1] == table[testIndex]
            echo "Duplicate test - Index: ", testIndex, ", Expected: ", table[testIndex], ", Got: ", assignment[1]

    test "Element constraint bounds checking":
        let table = @[10, 20, 30]  # Valid indices: 0, 1, 2

        # Test valid indices work
        for validIndex in 0..<table.len:
            let testSystem = initConstraintSystem[int]()
            let testVars = testSystem.newConstrainedSequence(2)
            testVars.setDomain([0, 1, 2, 3, 4, 10, 20, 30])

            let testConstraint = element(testVars[0], table, testVars[1])
            testSystem.addConstraint(testConstraint)
            testSystem.addConstraint(testVars[0] == validIndex)

            testSystem.resolve()

            let assignment = testVars.assignment
            check assignment[1] == table[validIndex]

        # Test invalid index fails - index out of bounds should cause constraint violation
        let invalidSystem = initConstraintSystem[int]()
        let invalidVars = invalidSystem.newConstrainedSequence(2)
        # Domain includes out-of-bounds index
        invalidVars.setDomain([0, 1, 2, 3, 4, 10, 20, 30])

        let invalidConstraint = element(invalidVars[0], table, invalidVars[1])
        invalidSystem.addConstraint(invalidConstraint)
        invalidSystem.addConstraint(invalidVars[0] == 3)  # Out of bounds for table[3]

        # Try to resolve - this should fail for invalid constraints
        try:
            invalidSystem.resolve()
            check false  # Should not reach here
        except:
            check true   # Expected to fail
        echo "Bounds test - Out of bounds correctly failed"

    test "Element constraint with variable array":
        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(5)  # index, array[0], array[1], array[2], value

        variables.setDomain([0, 1, 2, 10, 20, 30])

        # Variable array constraint
        let variableArray = @[variables[1], variables[2], variables[3]]
        let elementConstraint = element(variables[0], variableArray, variables[4])
        system.addConstraint(elementConstraint)

        # Set up the array to match GCC-style example
        system.addConstraint(variables[1] == 10)  # array[0] = 10
        system.addConstraint(variables[2] == 20)  # array[1] = 20
        system.addConstraint(variables[3] == 30)  # array[2] = 30

        system.resolve()

        let assignment = variables.assignment
        let index = assignment[0]
        let value = assignment[4]
        let expectedValue = assignment[1 + index]  # array[index]

        check value == expectedValue
        echo "Variable array - Index: ", index, ", Value: ", value, ", Expected: ", expectedValue

    test "Element constraint mixed constant/variable array":
        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(3)  # index, array_var, value

        variables.setDomain([0, 1, 2, 10, 20, 30])

        # Mixed array: [10, variables[1], 30] - matches pattern from GCC examples
        let mixedArray = @[
            ArrayElement[int](isConstant: true, constantValue: 10),
            ArrayElement[int](isConstant: false, variablePosition: int(variables[1].node.position)),
            ArrayElement[int](isConstant: true, constantValue: 30)
        ]

        let elementConstraint = element(variables[0], mixedArray, variables[2])
        system.addConstraint(elementConstraint)
        system.addConstraint(variables[1] == 20)  # Set middle value

        system.resolve()

        let assignment = variables.assignment
        let index = assignment[0]
        let arrayVar = assignment[1]
        let value = assignment[2]

        check arrayVar == 20
        let expectedValue = case index:
            of 0: 10
            of 1: 20
            of 2: 30
            else: -1
        check value == expectedValue
        echo "Mixed array - Index: ", index, ", Array var: ", arrayVar, ", Value: ", value

    test "Element constraint functional dependency":
        # Test that VALUE is completely determined by INDEX and TABLE
        let table = @[100, 200, 300]

        # For each possible index, there should be exactly one valid value
        for testIndex in 0..<table.len:
            let testSystem = initConstraintSystem[int]()
            let testVars = testSystem.newConstrainedSequence(2)
            testVars.setDomain([0, 1, 2, 100, 200, 300])

            let testConstraint = element(testVars[0], table, testVars[1])
            testSystem.addConstraint(testConstraint)
            testSystem.addConstraint(testVars[0] == testIndex)

            testSystem.resolve()

            let assignment = testVars.assignment
            # Functional dependency: given index, value is uniquely determined
            check assignment[1] == table[testIndex]

        echo "Functional dependency test passed"

    test "Element constraint with incompatible domain (should fail)":
        let system = initConstraintSystem[int]()
        let variables = system.newConstrainedSequence(2)

        # Set conflicting domains - value domain doesn't contain table values
        variables.setDomain([0, 1, 2])  # Domain only has 0,1,2 but table has 10,20,30

        let table = @[10, 20, 30]
        let elementConstraint = element(variables[0], table, variables[1])
        system.addConstraint(elementConstraint)
        system.addConstraint(variables[0] == 0)  # Force index to 0 (table[0] = 10)

        # Try to resolve - this should fail because value 10 is not in domain [0,1,2]
        try:
            system.resolve()
            check false  # Should not reach here
        except:
            check true   # Expected to fail
        echo "Incompatible domain test - correctly failed to solve"

when isMainModule:
    echo "Running Element Constraint Tests based on Global Constraint Catalog..."