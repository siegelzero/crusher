import std/[unittest, sequtils, tables, packedsets]
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


suite "ConstrainedArray deepCopy - all constraint types":
    ## Tests ConstrainedArray.deepCopy() for every constraint type.
    ## This is the path used by parallel search: deepCopy the array, then
    ## create independent TabuStates from original and copy.
    ## For each type: create system, add constraint, deepCopy baseArray,
    ## initialize both, verify same penalty, mutate original, verify copy unchanged.

    test "AllDifferent":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..4))
        sys.addConstraint(allDifferent(s))

        let assignment = @[1, 2, 3, 2]  # duplicate 2
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        # Mutate original — fix the duplicate
        sys.baseArray.constraints[0].updatePosition(3, 4)
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "AtLeast":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..3))
        sys.addConstraint(atLeast[int]([0, 1, 2, 3], 1, 3))  # at least 3 ones

        let assignment = @[1, 2, 1, 3]  # only 2 ones, need 3
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(1, 1)  # now 3 ones
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "AtMost":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..3))
        sys.addConstraint(atMost[int]([0, 1, 2, 3], 1, 1))  # at most 1 one

        let assignment = @[1, 1, 2, 3]  # 2 ones, max 1
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(0, 2)  # now 1 one
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "Element (constant array)":
        var sys = initConstraintSystem[int]()
        let idx = sys.newConstrainedVariable()
        let val = sys.newConstrainedVariable()
        idx.setDomain(toSeq(0..2))
        val.setDomain(toSeq(1..10))
        # array[idx] == val, array = [10, 20, 30]
        sys.addConstraint(element(idx.value, @[10, 20, 30], val.value))

        let assignment = @[1, 5]  # idx=1, val=5, but array[1]=20, so violated
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(1, 20)  # fix: val=20=array[1]
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "Relational (sum == target)":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(1..5))
        sys.addConstraint(s.sum() == 6)

        let assignment = @[1, 2, 5]  # sum=8, target=6
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        # Verify constraint ref is independent
        check cast[pointer](sys.baseArray.constraints[0]) !=
              cast[pointer](copied.constraints[0])

        sys.baseArray.constraints[0].updatePosition(2, 3)  # sum=1+2+3=6
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "Ordering (increasing)":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..4))
        sys.addConstraint(increasing[int]([0, 1, 2, 3]))

        let assignment = @[1, 3, 2, 4]  # violation: 3 > 2
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        # Verify state preservation (ordering preserves full runtime state)
        check sys.baseArray.constraints[0].orderingState.cost ==
              copied.constraints[0].orderingState.cost
        check sys.baseArray.constraints[0].orderingState.currentAssignment ==
              copied.constraints[0].orderingState.currentAssignment

        sys.baseArray.constraints[0].updatePosition(1, 2)  # fix: 1,2,2,4 — still valid
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "GlobalCardinality (exact)":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..3))
        # Value 1 appears exactly 2 times, value 2 exactly 1 time, value 3 exactly 1 time
        sys.addConstraint(globalCardinality[int]([0, 1, 2, 3], [1, 2, 3], [2, 1, 1]))

        let assignment = @[1, 1, 1, 2]  # val1 appears 3 times (want 2), val3 appears 0 (want 1)
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(2, 3)  # now [1,1,3,2] — correct!
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "GlobalCardinality (bounded)":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..3))
        # Value 1: [1,2], value 2: [1,2], value 3: [0,1]
        sys.addConstraint(globalCardinalityBounded[int]([0, 1, 2, 3], [1, 2, 3], [1, 1, 0], [2, 2, 1]))

        let assignment = @[1, 1, 1, 1]  # val1=4 (max 2), val2=0 (min 1)
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(2, 2)
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "Sequence":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(6)
        s.setDomain(toSeq(1..3))
        # In each window of 3, at least 1 and at most 2 values from {1}
        sys.addConstraint(sequence[int]([0, 1, 2, 3, 4, 5], 1, 2, 3, [1]))

        let assignment = @[1, 1, 1, 2, 3, 3]  # window [1,1,1] has 3 ones (max 2)
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        # Verify windowCounts state is preserved
        check sys.baseArray.constraints[0].sequenceState.windowCounts ==
              copied.constraints[0].sequenceState.windowCounts

        sys.baseArray.constraints[0].updatePosition(0, 2)  # [2,1,1,2,3,3] — all windows ok
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "Cumulative":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(0..5))
        # 3 tasks: durations [2,2,2], heights [3,3,3], limit 5, maxTime 10
        sys.addConstraint(cumulative[int]([0, 1, 2], [2, 2, 2], [3, 3, 3], 5))

        let assignment = @[0, 0, 0]  # all start at 0: height=9 at t=0,1 (limit 5)
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        # Verify resource profile state preserved
        check sys.baseArray.constraints[0].cumulativeState.resourceProfile ==
              copied.constraints[0].cumulativeState.resourceProfile

        sys.baseArray.constraints[0].updatePosition(2, 4)  # spread out tasks
        check sys.baseArray.constraints[0].penalty() < origPenalty
        check copied.constraints[0].penalty() == origPenalty

    test "Circuit":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..4))  # 1-indexed successor
        sys.addConstraint(circuit(s))

        let assignment = @[2, 1, 4, 3]  # two 2-cycles: 1→2→1, 3→4→3 (not a single circuit)
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        # Ref independence
        check cast[pointer](sys.baseArray.constraints[0].circuitState) !=
              cast[pointer](copied.constraints[0].circuitState)

        sys.baseArray.constraints[0].updatePosition(0, 3)  # 1→3→4→3... still broken but different
        check copied.constraints[0].penalty() == origPenalty

    test "Subcircuit":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..4))
        sys.addConstraint(subcircuit(s))

        let assignment = @[2, 3, 1, 4]  # subcircuit 1→2→3→1, node 4 self-loop ✓
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check copied.constraints[0].penalty() == origPenalty

        check cast[pointer](sys.baseArray.constraints[0].subcircuitState) !=
              cast[pointer](copied.constraints[0].subcircuitState)

        # Mutate — break the subcircuit
        sys.baseArray.constraints[0].updatePosition(0, 1)  # self-loop at 1, breaks chain
        check copied.constraints[0].penalty() == origPenalty

    test "AllDifferentExcept0":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(0..3))
        sys.addConstraint(allDifferentExcept0(s))

        let assignment = @[1, 2, 2, 0]  # duplicate 2 (non-zero), violated
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(2, 3)  # fix: [1,2,3,0]
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "LexOrder (lexLe)":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(6)
        s.setDomain(toSeq(1..5))
        # positions 0,1,2 <= positions 3,4,5 lexicographically
        sys.addConstraint(lexLe[int]([0, 1, 2], [3, 4, 5]))

        let assignment = @[3, 2, 1, 2, 2, 1]  # [3,2,1] > [2,2,1] lexicographically
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(0, 1)  # [1,2,1] <= [2,2,1]
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "TableIn":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(1..3))
        let tuples = @[@[1, 2, 3], @[3, 2, 1], @[2, 2, 2]]
        sys.addConstraint(tableIn[int]([0, 1, 2], tuples))

        let assignment = @[1, 1, 1]  # not in table
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(0, 2)  # [2,1,1] still not in table
        check copied.constraints[0].penalty() == origPenalty

    test "TableNotIn":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(1..3))
        let forbidden = @[@[1, 1, 1], @[2, 2, 2], @[3, 3, 3]]
        sys.addConstraint(tableNotIn[int]([0, 1, 2], forbidden))

        let assignment = @[1, 1, 1]  # forbidden
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(0, 2)  # [2,1,1] not forbidden
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "CountEq":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(5)  # 4 array positions + 1 target
        s.setDomain(toSeq(0..4))
        # count(positions 0..3, value=1) == position 4
        sys.addConstraint(countEq[int]([0, 1, 2, 3], 1, 4))

        let assignment = @[1, 2, 1, 3, 0]  # count of 1s = 2, target = 0
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(4, 2)  # target=2 matches count
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "Regular (DFA)":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(1..2))
        # Simple DFA: accepts sequences that end with value 2
        # States: 1 (start), 2 (seen 2)
        # Transitions: state 1 + input 1 -> state 1, state 1 + input 2 -> state 2
        #              state 2 + input 1 -> state 1, state 2 + input 2 -> state 2
        let transition = @[@[1, 2], @[1, 2]]  # [state][input-1] -> next_state
        sys.addConstraint(regular[int]([0, 1, 2], 2, 1, 2, transition, 1, [2]))

        let assignment = @[1, 2, 1]  # ends in state 1, not accepting
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check origPenalty > 0
        check copied.constraints[0].penalty() == origPenalty

        sys.baseArray.constraints[0].updatePosition(2, 2)  # ends with 2 — accepted
        check sys.baseArray.constraints[0].penalty() == 0
        check copied.constraints[0].penalty() == origPenalty

    test "IRDCS":
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(4)
        s.setDomain(toSeq(1..8))
        sys.addConstraint(irdcs[int]([0, 1, 2, 3]))

        let assignment = @[1, 1, 1, 1]  # bad interval representation
        var copied = sys.baseArray.deepCopy()

        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        let origPenalty = sys.baseArray.constraints[0].penalty()
        check copied.constraints[0].penalty() == origPenalty

        check cast[pointer](sys.baseArray.constraints[0].irdcsState) !=
              cast[pointer](copied.constraints[0].irdcsState)

        sys.baseArray.constraints[0].updatePosition(0, 3)
        check copied.constraints[0].penalty() == origPenalty

    test "ConstrainedArray deepCopy with multiple constraint types":
        ## Integration test: system with diverse constraints, deepCopy preserves all
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(5)
        s.setDomain(toSeq(1..5))

        sys.addConstraint(allDifferent(s))
        sys.addConstraint(s.sum() == 15)
        sys.addConstraint(increasing[int]([0, 1, 2, 3, 4]))

        let assignment = @[3, 1, 4, 2, 5]  # sum=15, not sorted, allDiff
        var copied = sys.baseArray.deepCopy()

        # Initialize all constraints in both
        for c in sys.baseArray.constraints: c.initialize(assignment)
        for c in copied.constraints: c.initialize(assignment)

        # All penalties match after init
        var origPenalties = newSeq[int](sys.baseArray.constraints.len)
        for i in 0..<sys.baseArray.constraints.len:
            origPenalties[i] = sys.baseArray.constraints[i].penalty()
            check sys.baseArray.constraints[i].penalty() == copied.constraints[i].penalty()
            # All constraint refs are independent
            check cast[pointer](sys.baseArray.constraints[i]) !=
                  cast[pointer](copied.constraints[i])

        # Mutate original
        for i in 0..<sys.baseArray.constraints.len:
            sys.baseArray.constraints[i].updatePosition(0, 1)

        # Copy unchanged — each constraint's penalty is still the original value
        for i in 0..<copied.constraints.len:
            check copied.constraints[i].penalty() == origPenalties[i]

    test "ConstrainedArray deepCopy - domain independence":
        ## Verify domain seqs are independent (not shared refs)
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(1..5))
        sys.addConstraint(allDifferent(s))

        var copied = sys.baseArray.deepCopy()

        # Domains should have same content
        check sys.baseArray.domain == copied.domain

        # But modifying original domain shouldn't affect copy
        sys.baseArray.domain[0].add(99)
        check 99 notin copied.domain[0]

    test "ConstrainedArray deepCopy - channel binding independence":
        ## Verify channel bindings (expression refs) are independent
        var sys = initConstraintSystem[int]()
        var s = sys.newConstrainedSequence(3)
        s.setDomain(toSeq(1..5))
        sys.addConstraint(allDifferent(s))

        var copied = sys.baseArray.deepCopy()

        # Channel bindings should be independent
        for i in 0..<sys.baseArray.channelBindings.len:
            if sys.baseArray.channelBindings.len > 0:
                check cast[pointer](sys.baseArray.channelBindings[i].indexExpression) !=
                      cast[pointer](copied.channelBindings[i].indexExpression)

    test "ConstrainedArray deepCopy - expression entry independence":
        ## Verify AlgebraicExpression entries (ref objects) are independent
        var sys = initConstraintSystem[int]()
        var v1 = sys.newConstrainedVariable()
        var v2 = sys.newConstrainedVariable()
        v1.setDomain(toSeq(1..5))
        v2.setDomain(toSeq(1..5))
        sys.addConstraint(v1.value + v2.value == 6)

        var copied = sys.baseArray.deepCopy()

        # Expression entries should be independent refs
        for i in 0..<sys.baseArray.entries.len:
            if not sys.baseArray.entries[i].isNil:
                check cast[pointer](sys.baseArray.entries[i]) !=
                      cast[pointer](copied.entries[i])
