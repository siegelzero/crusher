## Tests for linear expression merging in sum() and scalarProduct().
##
## When all sub-expressions are linear (but not simple RefNodes), sum() and
## scalarProduct() should merge them into a single PositionBased SumExpression
## rather than falling through to ExpressionBased evaluation.

import std/[sequtils, tables, unittest]
import crusher

suite "Linear Sum Merge":

    test "sum of linear expressions uses PositionBased":
        ## sum([x[0]+x[1], x[1]-x[2], 2*x[0]]) should merge to PositionBased
        ## Merged: 3*x[0] + 2*x[1] - x[2]
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])   # x0 + x1
        terms.add(x[1] - x[2])   # x1 - x2
        terms.add(2 * x[0])      # 2*x0

        let s = sum(terms)
        # Should be PositionBased since all terms are linear
        check s.evalMethod == PositionBased
        # Merged coefficients: x0=3, x1=2, x2=-1
        check s.coefficient[x[0].node.position] == 3
        check s.coefficient[x[1].node.position] == 2
        check s.coefficient[x[2].node.position] == -1

    test "sum of linear expressions with constants":
        ## sum([x[0]+5, x[1]-3]) => x[0]+x[1]+2 (constant=2)
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(2)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + 5)
        terms.add(x[1] - 3)

        let s = sum(terms)
        check s.evalMethod == PositionBased
        check s.constant == 2
        check s.coefficient[x[0].node.position] == 1
        check s.coefficient[x[1].node.position] == 1

    test "sum of linear expressions cancelling coefficients":
        ## sum([x[0]+x[1], -x[1]]) => x[0] (x[1] cancels to zero)
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(2)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])
        terms.add(0 - x[1])  # -x[1]

        let s = sum(terms)
        check s.evalMethod == PositionBased
        check s.coefficient[x[0].node.position] == 1
        # x[1] should have been removed (zero coefficient)
        check x[1].node.position notin s.coefficient

    test "sum with non-linear expression falls back to ExpressionBased":
        ## sum([x[0]*x[1], x[2]]) should use ExpressionBased because x[0]*x[1] is non-linear
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] * x[1])  # non-linear
        terms.add(x[2])

        let s = sum(terms)
        check s.evalMethod == ExpressionBased

    test "scalarProduct of linear expressions uses PositionBased":
        ## scalarProduct([2, 3], [x[0]+x[1], x[1]-x[2]])
        ## = 2*(x0+x1) + 3*(x1-x2) = 2*x0 + 5*x1 - 3*x2
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])   # x0 + x1
        terms.add(x[1] - x[2])   # x1 - x2

        let s = scalarProduct(@[2, 3], terms)
        check s.evalMethod == PositionBased
        check s.coefficient[x[0].node.position] == 2
        check s.coefficient[x[1].node.position] == 5
        check s.coefficient[x[2].node.position] == -3

    test "scalarProduct of linear expressions with constants":
        ## scalarProduct([2, 3], [x[0]+1, x[1]+2])
        ## = 2*(x0+1) + 3*(x1+2) = 2*x0 + 3*x1 + 8 (constant=2+6=8)
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(2)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + 1)
        terms.add(x[1] + 2)

        let s = scalarProduct(@[2, 3], terms)
        check s.evalMethod == PositionBased
        check s.constant == 8
        check s.coefficient[x[0].node.position] == 2
        check s.coefficient[x[1].node.position] == 3

    test "scalarProduct with non-linear expression falls back":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(2)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] * x[1])  # non-linear
        terms.add(x[0])

        let s = scalarProduct(@[1, 1], terms)
        check s.evalMethod == ExpressionBased

    test "merged linear sum solves correctly":
        ## End-to-end: 3*x[0] + 2*x[1] - x[2] == 10
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])   # x0 + x1
        terms.add(x[1] - x[2])   # x1 - x2
        terms.add(2 * x[0])      # 2*x0
        # Merged: 3*x0 + 2*x1 - x2 == 10
        sys.addConstraint(sum(terms) == 10)

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        check 3*a[0] + 2*a[1] - a[2] == 10

    test "merged linear scalarProduct solves correctly":
        ## End-to-end: 2*(x0+x1) + 3*(x1-x2) == 15
        ## = 2*x0 + 5*x1 - 3*x2 == 15
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedSequence(3)
        x.setDomain(toSeq(0..10))

        var terms: seq[AlgebraicExpression[int]] = @[]
        terms.add(x[0] + x[1])
        terms.add(x[1] - x[2])
        sys.addConstraint(scalarProduct(@[2, 3], terms) == 15)

        sys.resolve(parallel=true, tabuThreshold=10000)

        let a = x.assignment()
        check 2*a[0] + 5*a[1] - 3*a[2] == 15
