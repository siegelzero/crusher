import std/[sequtils, unittest]
import crusher

suite "Knapsack Problem Tests":
    test "0/1 Knapsack - 15 items with capacity 750":
        # Table 5.2: An instance of the Knapsack problem with 15 items
        # Maximize profit subject to weight constraint
        # Variables: x[i] ∈ {0, 1} (1 = item selected, 0 = item not selected)
        # Constraint: sum(weights[i] * x[i]) <= 750
        # Objective: maximize sum(profits[i] * x[i])
        # Expected optimal solution: profit = 1458

        let n = 15
        let profits = @[135, 139, 149, 150, 156, 163, 173, 184, 192, 201, 210, 214, 221, 229, 240]
        let weights = @[70, 73, 77, 80, 82, 87, 90, 94, 98, 106, 110, 113, 115, 118, 120]
        let capacity = 750

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..1))  # Binary variables

        # Weight constraint: sum of selected item weights <= capacity
        var weightSum: AlgebraicExpression[int] = weights[0] * x[0]
        for i in 1..<n:
            weightSum = weightSum + weights[i] * x[i]
        sys.addConstraint(weightSum <= capacity)

        # Objective function: maximize total profit
        var profitSum: AlgebraicExpression[int] = profits[0] * x[0]
        for i in 1..<n:
            profitSum = profitSum + profits[i] * x[i]

        # Solve using maximization
        sys.maximize(profitSum, parallel=true, verbose=true)

        # Verify the solution
        let solution = x.assignment

        # Calculate total weight and profit
        var totalWeight = 0
        var totalProfit = 0
        for i in 0..<n:
            if solution[i] == 1:
                totalWeight += weights[i]
                totalProfit += profits[i]

        # Verify weight constraint is satisfied
        check totalWeight <= capacity

        # Verify objective value matches expected optimal
        let objectiveValue = profitSum.evaluate(solution)
        check objectiveValue == totalProfit
        check totalProfit == 1458  # Optimal solution

        echo "Solution: ", solution
        echo "Total weight: ", totalWeight, " / ", capacity
        echo "Total profit: ", totalProfit

        # List selected items
        echo "Selected items:"
        for i in 0..<n:
            if solution[i] == 1:
                echo "  Item ", i, ": profit=", profits[i], ", weight=", weights[i]

    test "0/1 Knapsack - 24 items with capacity 6404180":
        # Table 5.5: An instance of the Knapsack problem with 24 items
        # Maximize profit subject to weight constraint
        # Variables: x[i] ∈ {0, 1} (1 = item selected, 0 = item not selected)
        # Constraint: sum(weights[i] * x[i]) <= 6404180
        # Objective: maximize sum(profits[i] * x[i])

        let n = 24
        let profits = @[825594, 1677009, 1676628, 1523970, 943972, 97426,
                        69666, 1296457, 1678693, 1902996, 1844992, 1049289,
                        1252836, 1319836, 953277, 2067538, 675367, 853655,
                        1826027, 65731, 901489, 577243, 466257, 369261]
        let weights = @[382745, 799601, 909247, 729069, 467902, 44328,
                        34610, 698150, 823460, 903959, 853665, 551830,
                        610856, 670702, 488960, 951111, 323046, 446298,
                        931161, 31385, 496951, 264724, 224916, 169684]
        let capacity = 6404180

        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(n)
        x.setDomain(toSeq(0..1))  # Binary variables

        # Weight constraint: sum of selected item weights <= capacity (using linear expression)
        var weightSum: AlgebraicExpression[int] = weights[0] * x[0]
        for i in 1..<n:
            weightSum = weightSum + weights[i] * x[i]
        sys.addConstraint(linearize(weightSum) <= capacity)

        # Objective function: maximize total profit (using linear expression)
        var profitSum: AlgebraicExpression[int] = profits[0] * x[0]
        for i in 1..<n:
            profitSum = profitSum + profits[i] * x[i]
        let linearObjective = linearize(profitSum)

        # Solve using maximization
        sys.maximize(linearObjective, parallel=true, tabuThreshold=1000, verbose=false)

        # Verify the solution
        let solution = x.assignment

        # Calculate total weight and profit
        var totalWeight = 0
        var totalProfit = 0
        for i in 0..<n:
            if solution[i] == 1:
                totalWeight += weights[i]
                totalProfit += profits[i]

        # Verify weight constraint is satisfied
        check totalWeight <= capacity

        # Verify objective value (both from linear expression and evaluation)
        check linearObjective.value == totalProfit
        check linearObjective.evaluate(solution) == totalProfit

        echo "Solution: ", solution
        echo "Total weight: ", totalWeight, " / ", capacity
        echo "Total profit: ", totalProfit

        # List selected items
        echo "Selected items:"
        for i in 0..<n:
            if solution[i] == 1:
                echo "  Item ", i, ": profit=", profits[i], ", weight=", weights[i]
