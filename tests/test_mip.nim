import std/[sequtils, unittest]
import crusher

suite "Mixed Integer Programming Tests":
    test "Binary Integer Programming - Standard MIP Example":
        # Binary integer programming problem with 5 variables
        # Variables: x0, x1, x2, x3, x4 ∈ {0, 1}
        # Constraints:
        # -x0 + 3*x1 - 5*x2 - x3 + 4*x4 <= -2
        # 2*x0 - 6*x1 + 3*x2 + 2*x3 - 2*x4 <= 0
        # x1 - 2*x2 + x3 + x4 <= -1
        # Minimize: 5*x0 + 7*x1 + 10*x2 + 3*x3 + x4
        # Expected solution: [0, 1, 1, 0, 0] with objective value 17

        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..1))  # Binary variables

        # Add constraints using algebraic expressions
        sys.addConstraint(-x[0] + 3*x[1] - 5*x[2] - x[3] + 4*x[4] <= -2)
        sys.addConstraint(2*x[0] - 6*x[1] + 3*x[2] + 2*x[3] - 2*x[4] <= 0)
        sys.addConstraint(x[1] - 2*x[2] + x[3] + x[4] <= -1)

        # Define objective function
        let objective = 5*x[0] + 7*x[1] + 10*x[2] + 3*x[3] + x[4]

        # Solve using minimization
        sys.minimize(objective)

        # Verify the solution
        let solution = x.assignment
        check solution == @[0, 1, 1, 0, 0]

        # Verify objective value
        let objectiveValue = objective.evaluate(solution)
        check objectiveValue == 17

        # Verify constraints are satisfied
        check (-solution[0] + 3*solution[1] - 5*solution[2] - solution[3] + 4*solution[4]) <= -2
        check (2*solution[0] - 6*solution[1] + 3*solution[2] + 2*solution[3] - 2*solution[4]) <= 0
        check (solution[1] - 2*solution[2] + solution[3] + solution[4]) <= -1

    test "Binary Integer Programming - Using Linearized Constraints":
        # Same problem but using linearize() for constraints
        # This tests the SumExpression path explicitly
        let n = 5
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..1))

        # Add constraints using linearized expressions
        sys.addConstraint(linearize(-x[0] + 3*x[1] - 5*x[2] - x[3] + 4*x[4]) <= -2)
        sys.addConstraint(linearize(2*x[0] - 6*x[1] + 3*x[2] + 2*x[3] - 2*x[4]) <= 0)
        sys.addConstraint(linearize(x[1] - 2*x[2] + x[3] + x[4]) <= -1)

        # Define linearized objective
        let objective = linearize(5*x[0] + 7*x[1] + 10*x[2] + 3*x[3] + x[4])

        # Solve using minimization (disable parallel for deterministic results)
        sys.minimize(objective, parallel=false)

        # Verify the solution
        let solution = x.assignment
        check solution == @[0, 1, 1, 0, 0]

        # Verify objective value (both from state and evaluation)
        # After minimize(), objective.value should be consistent with the final solution
        check objective.value == 17
        check objective.evaluate(solution) == 17

    test "Small Binary Programming Problem":
        # Smaller test case for quick verification
        # Variables: x0, x1, x2 ∈ {0, 1}
        # Constraint: x0 + x1 + x2 >= 2 (at least 2 variables must be 1)
        # Minimize: x0 + 2*x1 + 3*x2
        # Expected solution: [1, 1, 0] with objective value 3

        let n = 3
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..1))

        # At least 2 variables must be 1
        sys.addConstraint(x[0] + x[1] + x[2] >= 2)

        # Minimize cost (x2 has highest cost, so should be avoided)
        let objective = x[0] + 2*x[1] + 3*x[2]
        sys.minimize(objective)

        let solution = x.assignment
        let objectiveValue = objective.evaluate(solution)

        # Should pick the two cheapest variables: x0=1, x1=1, x2=0
        check solution == @[1, 1, 0]
        check objectiveValue == 3

        # Verify constraint satisfaction
        check (solution[0] + solution[1] + solution[2]) >= 2