import std/[sequtils, unittest]
import crusher

suite "ConstrainedVariable Tests":
    test "Basic ConstrainedVariable functionality":
        # Create constraint system
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3, 4, 5])
        y.setDomain([1, 2, 3, 4, 5])

        # Add a simple constraint
        sys.addConstraint(x + y == 5)
        sys.addConstraint(x > y)

        # Solve the constraint system
        sys.resolve()

        check x.assignment() + y.assignment() == 5
        check x.assignment() > y.assignment()

    test "All comparison operators":
        var sys = initConstraintSystem[int]()

        var a = sys.newConstrainedVariable()
        var b = sys.newConstrainedVariable()
        var c = sys.newConstrainedVariable()

        a.setDomain([1, 5, 10])
        b.setDomain([1, 5, 10])
        c.setDomain([1, 5, 10])

        # Test all comparison operators
        sys.addConstraint(a < b)
        sys.addConstraint(b <= c)
        sys.addConstraint(a >= 1)
        sys.addConstraint(c <= 10)

        sys.resolve()

        check a.assignment() < b.assignment()
        check b.assignment() <= c.assignment()
        check a.assignment() >= 1
        check c.assignment() <= 10

    test "Arithmetic expressions with constants":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3, 4, 5])
        y.setDomain([1, 2, 3, 4, 5])

        # Test mixed arithmetic with constants
        sys.addConstraint(x + 2 == y)
        sys.addConstraint(x > 1)

        sys.resolve()

        check x.assignment() + 2 == y.assignment()
        check x.assignment() > 1

    test "Multiple variables with complex constraints":
        var sys = initConstraintSystem[int]()
        var w = sys.newConstrainedVariable()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()
        var z = sys.newConstrainedVariable()

        w.setDomain([1, 2, 3, 4])
        x.setDomain([1, 2, 3, 4])
        y.setDomain([1, 2, 3, 4])
        z.setDomain([1, 2, 3, 4])

        # Chain of constraints
        sys.addConstraint(w < x)
        sys.addConstraint(x < y)
        sys.addConstraint(y < z)
        sys.addConstraint(w + x + y + z == 10)

        sys.resolve()

        check w.assignment() < x.assignment()
        check x.assignment() < y.assignment()
        check y.assignment() < z.assignment()
        check w.assignment() + x.assignment() + y.assignment() + z.assignment() == 10

    test "Domain constraints":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()

        # Test setting different domain ranges
        x.setDomain([10, 20, 30, 40, 50])
        sys.addConstraint(x > 25)

        sys.resolve()

        check x.assignment() > 25
        check x.assignment() in [30, 40, 50]

    test "Negative domain values":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([-5, -3, -1, 1, 3, 5])
        y.setDomain([-5, -3, -1, 1, 3, 5])

        sys.addConstraint(x + y == 0)
        sys.addConstraint(x < 0)

        sys.resolve()

        check x.assignment() + y.assignment() == 0
        check x.assignment() < 0
        check y.assignment() > 0

    test "Equality constraints with multiple solutions":
        var sys = initConstraintSystem[int]()
        var x = sys.newConstrainedVariable()
        var y = sys.newConstrainedVariable()

        x.setDomain([1, 2, 3])
        y.setDomain([1, 2, 3])

        sys.addConstraint(x == y)

        sys.resolve()

        check x.assignment() == y.assignment()
        check x.assignment() in [1, 2, 3]

