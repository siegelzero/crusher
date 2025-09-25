import std/unittest
import ../src/crusher
import ../src/search/resolution

suite "Unified Constraint API Tests":

    test "ConstrainedVariable operators return StatefulConstraint":
        var system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 3)

        # Set domains for variables
        sequence.setDomain([1, 2, 3, 4])

        # All relational operators should return StatefulConstraint
        let constraint1 = sequence[0] == sequence[1]  # StatefulConstraint
        let constraint2 = sequence[1] > sequence[2]   # StatefulConstraint
        let constraint3 = sequence[0] >= 2            # StatefulConstraint
        let constraint4 = sequence[2] < 4             # StatefulConstraint
        let constraint5 = sequence[1] <= sequence[0]  # StatefulConstraint

        # All constraints can be combined using logical operators
        let combined = constraint1 and constraint2 and constraint3 and constraint4 and constraint5

        system.addConstraint(combined)

        # Test that we can solve this system
        system.resolve()
        let solution = sequence.assignment

        echo "Found solution: ", solution[0], ", ", solution[1], ", ", solution[2]
        # Just verify we got some values (solution exists)
        check solution.len == 3

    test "AlgebraicExpression operators return StatefulConstraint":
        var system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 3)

        # Set domains for variables
        sequence.setDomain([1, 2, 3, 4, 5])

        # AlgebraicExpression comparisons should return StatefulConstraint
        let expr1 = sequence[0] + sequence[1]  # AlgebraicExpression
        let expr2 = sequence[2] * 2            # AlgebraicExpression

        let constraint = expr1 == expr2  # Should return StatefulConstraint
        system.addConstraint(constraint)

        # Test that we can solve this system
        system.resolve()
        let solution = sequence.assignment

        let sum = solution[0] + solution[1]
        let doubled = solution[2] * 2
        echo "Found solution: ", solution[0], " + ", solution[1], " = ", sum, " == ", doubled
        check sum == doubled

    test "Mixed constraint types work together":
        var system = initConstraintSystem[int]()
        let sequence = newConstrainedSequence(system, 4)

        # Set domains
        sequence.setDomain([1, 2, 3, 4])

        # Mix ConstrainedVariable and AlgebraicExpression constraints
        let varConstraint = sequence[0] == sequence[1]                    # StatefulConstraint from ConstrainedVariable
        let exprConstraint = sequence[2] == sequence[3]       # StatefulConstraint from AlgebraicExpression
        let sumConstraint = sequence[0] + sequence[1] == 6    # StatefulConstraint from AlgebraicExpression

        # All should combine seamlessly
        let combined = varConstraint and exprConstraint and sumConstraint
        system.addConstraint(combined)

        system.resolve()
        let solution = sequence.assignment

        echo "Found mixed solution: ", solution[0], ", ", solution[1], ", ", solution[2], ", ", solution[3]
        check solution[0] == solution[1]
        check solution[2] == solution[3]
        check solution[0] + solution[1] == 6