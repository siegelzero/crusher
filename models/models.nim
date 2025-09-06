import std/[sequtils, strformat]

import constraints/constraint
import expressions/expression
import constrainedArray
import constraintSystem


proc sendMoreMoney*(): ConstraintSystem[int] =
    let
        S = 0
        E = 1
        N = 2
        D = 3
        M = 4
        O = 5
        R = 6
        Y = 7

    var sys = initConstraintSystem[int]()
    var value = sys.newConstrainedSequence(8)
    value.setDomain(toSeq 0..9)
    sys.addConstraint(allDifferent(value))

    var
        send = 1000*value[S] + 100*value[E] + 10*value[N] + value[D]
        more = 1000*value[M] + 100*value[O] + 10*value[R] + value[E]
        money = 10000*value[M] + 1000*value[O] + 100*value[N] + 10*value[E] + value[Y]

    sys.addConstraint(send + more == money)
    sys.addConstraint(value[S] > 0)
    sys.addConstraint(value[M] > 0)

    return sys


proc ageProblem*(): ConstrainedArray[int] =
    # John is twice as old as Jim; the sum of their ages is that of
    # Jerry's, while the ages of the three of them add up to 36.
    # How old is each?
    var age = initConstrainedArray[int](3)
    age.setDomain(toSeq 0..36)

    let
        john = 0
        jim = 1
        jerry = 2

    # John is twice as old as Jim
    age.addConstraint(age[john] == 2*age[jim])

    # The sum of their ages is that of Jerry
    age.addConstraint(age[john] + age[jim] == age[jerry])

    # The ages of the three of them add up to 36
    age.addConstraint(age[john] + age[jim] + age[jerry] == 36)

    return age


proc magicSquareLC*(n: int): ConstraintSystem[int] =
    # Magic Squares
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)

    let target = n*(n*n + 1) div 2
    echo fmt"Target: {target}"

    # Row sums == target
    for row in X.rows():
        sys.addConstraint(linearCombinationEq(row, target))

    # Col sums == target
    for col in X.columns():
        sys.addConstraint(linearCombinationEq(col, target))

    # Diagonals
    var terms: seq[Expression[int]] = @[]
    for i in 0..<n:
        terms.add(X[i, i])
    sys.addConstraint(linearCombinationEq(terms, target))

    terms = @[]
    for i in 0..<n:
        terms.add(X[i, n - i - 1])
    sys.addConstraint(linearCombinationEq(terms, target))

    # All entries in square must be distinct
    sys.addConstraint(allDifferent(X))
    X.setDomain(toSeq(1..n*n))

    return sys