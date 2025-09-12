import std/[unittest, sequtils, tables]
import "../src/crusher"

suite "Simple Deep Copy Tests":
    test "DeepCopy AlgebraicExpression - simple variable":
        let system = initConstraintSystem[int]()
        let variable = system.newConstrainedVariable()

        let original = variable.value
        let copied = original.deepCopy()

        # Should have same structure but be different objects
        check original.positions == copied.positions
        check original.linear == copied.linear
        check original.node.kind == copied.node.kind
        check original.node.position == copied.node.position

        # Should be different object references
        check cast[pointer](original) != cast[pointer](copied)
        check cast[pointer](original.node) != cast[pointer](copied.node)

    test "DeepCopy AlgebraicExpression - complex expression":
        let system = initConstraintSystem[int]()
        let var1 = system.newConstrainedVariable()
        let var2 = system.newConstrainedVariable()

        let original = var1.value + var2.value * 3 - 5
        let copied = original.deepCopy()

        # Should have same structure
        check original.positions == copied.positions
        check original.linear == copied.linear
        check original.node.kind == copied.node.kind
        check original.node.binaryOp == copied.node.binaryOp

        # Should be different object references
        check cast[pointer](original) != cast[pointer](copied)
        check cast[pointer](original.node) != cast[pointer](copied.node)
        check cast[pointer](original.node.left) != cast[pointer](copied.node.left)
        check cast[pointer](original.node.right) != cast[pointer](copied.node.right)

    test "DeepCopy SumExpression - position-based":
        let system = initConstraintSystem[int]()
        let sequence = system.newConstrainedSequence(3)

        let original = sequence.sum()
        original.initialize(@[1, 2, 3])

        let copied = original.deepCopy()

        # Should have same structure and state
        check original.positions == copied.positions
        check original.value == copied.value
        check original.constant == copied.constant
        check original.evalMethod == copied.evalMethod
        check original.currentAssignment == copied.currentAssignment

        # Should be different object references
        check cast[pointer](original) != cast[pointer](copied)

        # Verify they work independently
        original.updatePosition(0, 5)
        check original.value != copied.value

    test "DeepCopy ExpressionNode - all node types":
        # Test LiteralNode
        let literalNode = ExpressionNode[int](kind: LiteralNode, value: 42)
        let literalCopy = literalNode.deepCopy()
        check literalNode.kind == literalCopy.kind
        check literalNode.value == literalCopy.value
        check cast[pointer](literalNode) != cast[pointer](literalCopy)

        # Test RefNode
        let refNode = ExpressionNode[int](kind: RefNode, position: 5)
        let refCopy = refNode.deepCopy()
        check refNode.kind == refCopy.kind
        check refNode.position == refCopy.position
        check cast[pointer](refNode) != cast[pointer](refCopy)

        # Test UnaryOpNode
        let unaryNode = ExpressionNode[int](
            kind: UnaryOpNode,
            unaryOp: Negation,
            target: refNode
        )
        let unaryCopy = unaryNode.deepCopy()
        check unaryNode.kind == unaryCopy.kind
        check unaryNode.unaryOp == unaryCopy.unaryOp
        check unaryNode.target.position == unaryCopy.target.position
        check cast[pointer](unaryNode) != cast[pointer](unaryCopy)
        check cast[pointer](unaryNode.target) != cast[pointer](unaryCopy.target)

        # Test BinaryOpNode
        let binaryNode = ExpressionNode[int](
            kind: BinaryOpNode,
            binaryOp: Addition,
            left: refNode,
            right: literalNode
        )
        let binaryCopy = binaryNode.deepCopy()
        check binaryNode.kind == binaryCopy.kind
        check binaryNode.binaryOp == binaryCopy.binaryOp
        check binaryNode.left.position == binaryCopy.left.position
        check binaryNode.right.value == binaryCopy.right.value
        check cast[pointer](binaryNode) != cast[pointer](binaryCopy)
        check cast[pointer](binaryNode.left) != cast[pointer](binaryCopy.left)
        check cast[pointer](binaryNode.right) != cast[pointer](binaryCopy.right)

    test "DeepCopy MaxExpression and MinExpression":
        let system = initConstraintSystem[int]()
        let sequence = system.newConstrainedSequence(3)

        let originalMax = sequence.max()
        originalMax.initialize(@[1, 5, 3])
        let copiedMax = originalMax.deepCopy()

        check originalMax.positions == copiedMax.positions
        check originalMax.value == copiedMax.value
        check originalMax.evalMethod == copiedMax.evalMethod
        check cast[pointer](originalMax) != cast[pointer](copiedMax)

        let originalMin = sequence.min()
        originalMin.initialize(@[1, 5, 3])
        let copiedMin = originalMin.deepCopy()

        check originalMin.positions == copiedMin.positions
        check originalMin.value == copiedMin.value
        check originalMin.evalMethod == copiedMin.evalMethod
        check cast[pointer](originalMin) != cast[pointer](copiedMin)

suite "StatefulConstraint Deep Copy Tests":
    test "DeepCopy RelationalConstraint with StatefulAlgebraicExpressions":
        let system = initConstraintSystem[int]()
        let var1 = system.newConstrainedVariable()
        let var2 = system.newConstrainedVariable()

        # Create expressions and initialize them
        let leftExpr = newExpression(var1.value + 5)
        let rightExpr = newExpression(var2.value * 2)
        leftExpr.initialize(@[3, 7])
        rightExpr.initialize(@[3, 7])

        # Create relational constraint and initialize it
        let constraint = newRelationalConstraint[int](leftExpr, rightExpr, EqualTo)
        constraint.initialize(@[3, 7])

        # Create StatefulConstraint wrapper
        let statefulConstraint = StatefulConstraint[int](
            positions: constraint.positions,
            stateType: RelationalType,
            relationalState: constraint
        )

        # Deep copy the stateful constraint
        let copied = statefulConstraint.deepCopy()

        # Verify structure is preserved
        check statefulConstraint.positions == copied.positions
        check statefulConstraint.stateType == copied.stateType
        check statefulConstraint.relationalState.relation == copied.relationalState.relation
        check statefulConstraint.relationalState.cost == copied.relationalState.cost
        check statefulConstraint.relationalState.leftValue == copied.relationalState.leftValue
        check statefulConstraint.relationalState.rightValue == copied.relationalState.rightValue

        # Verify they are different objects
        check cast[pointer](statefulConstraint.relationalState) != cast[pointer](copied.relationalState)

        # Verify they work independently - modify original and re-evaluate
        statefulConstraint.relationalState.leftExpr.updatePosition(0, 10)
        # Update cached values after changing expression state
        statefulConstraint.relationalState.leftValue = statefulConstraint.relationalState.leftExpr.getValue()
        check statefulConstraint.relationalState.leftValue != copied.relationalState.leftValue

    test "DeepCopy OrderingConstraint PositionBased - preserves all state":
        let system = initConstraintSystem[int]()
        let sequence = system.newConstrainedSequence(4)

        # Create ordering constraint
        let positions = [0, 1, 2, 3]
        let constraint = newIncreasingConstraint[int](positions)
        constraint.initialize(@[1, 3, 2, 4])  # One violation: 3 > 2, cost should be 1

        # Wrap in StatefulConstraint
        let statefulConstraint = StatefulConstraint[int](
            positions: toPackedSet(positions),
            stateType: OrderingType,
            orderingState: constraint
        )

        # Deep copy
        let copied = statefulConstraint.deepCopy()

        # Verify structure and state preservation
        check statefulConstraint.orderingState.orderingType == copied.orderingState.orderingType
        check statefulConstraint.orderingState.cost == copied.orderingState.cost
        check statefulConstraint.orderingState.evalMethod == copied.orderingState.evalMethod
        check statefulConstraint.orderingState.currentAssignment == copied.orderingState.currentAssignment
        check statefulConstraint.orderingState.positions == copied.orderingState.positions
        check statefulConstraint.orderingState.sortedPositions == copied.orderingState.sortedPositions

        # Verify different objects
        check cast[pointer](statefulConstraint.orderingState) != cast[pointer](copied.orderingState)

        # Verify independent operation - change position 1 from 3 to 5
        # This should not change violations (1 < 5, 5 > 2, 2 < 4) - still 1 violation
        # But change position 1 from 3 to 1 should change violations (1 < 1 is false, so cost increases)
        let copiedCost = copied.orderingState.cost
        statefulConstraint.orderingState.updatePosition(1, 1)  # Change to 1 to create more violations
        # The updatePosition should have automatically updated the cost
        check statefulConstraint.orderingState.cost != copiedCost

    test "DeepCopy MultiknapsackConstraint PositionBased - preserves all state":
        let system = initConstraintSystem[int]()

        let positions = [0, 1, 2]
        let weights = [2, 3, 1]
        let capacities = @[(1, 5), (2, 3)]  # value 1 has capacity 5, value 2 has capacity 3

        # Create multiknapsack constraint
        let constraint = newMultiknapsackConstraint[int](positions, weights, capacities)
        constraint.initialize(@[1, 2, 1])  # assignments: pos0->val1(weight2), pos1->val2(weight3), pos2->val1(weight1)

        # Wrap in StatefulConstraint
        let statefulConstraint = StatefulConstraint[int](
            positions: toPackedSet(positions),
            stateType: MultiknapsackType,
            multiknapsackState: constraint
        )

        # Deep copy
        let copied = statefulConstraint.deepCopy()

        # Verify all state is preserved
        check statefulConstraint.multiknapsackState.cost == copied.multiknapsackState.cost
        check statefulConstraint.multiknapsackState.evalMethod == copied.multiknapsackState.evalMethod
        check statefulConstraint.multiknapsackState.currentAssignment == copied.multiknapsackState.currentAssignment
        check statefulConstraint.multiknapsackState.weights == copied.multiknapsackState.weights
        check statefulConstraint.multiknapsackState.capacities == copied.multiknapsackState.capacities
        check statefulConstraint.multiknapsackState.loadTable == copied.multiknapsackState.loadTable
        check statefulConstraint.multiknapsackState.positions == copied.multiknapsackState.positions

        # Verify different objects
        check cast[pointer](statefulConstraint.multiknapsackState) != cast[pointer](copied.multiknapsackState)

        # Verify independent operation
        statefulConstraint.multiknapsackState.updatePosition(0, 2)
        check statefulConstraint.multiknapsackState.cost != copied.multiknapsackState.cost
        check statefulConstraint.multiknapsackState.loadTable != copied.multiknapsackState.loadTable