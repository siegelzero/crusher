import std/sequtils

import constraints/constraint
import expressions/expression
import constrainedArray
import constraintSystem


proc sendMoreMoney*(): ConstrainedArray[int] =
    let
        S = 0
        E = 1
        N = 2
        D = 3
        M = 4
        O = 5
        R = 6
        Y = 7
    
    var value = initConstrainedArray[int](8)
    value.setDomain(toSeq 0..9)
    value.allDifferent()

    var 
        send = 1000*value[S] + 100*value[E] + 10*value[N] + value[D]
        more = 1000*value[M] + 100*value[O] + 10*value[R] + value[E]
        money = 10000*value[M] + 1000*value[O] + 100*value[N] + 10*value[E] + value[Y]
    
    value.addConstraint(send + more == money)
    value.addConstraint(value[S] > 0)
    value.addConstraint(value[M] > 0)

    return value


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


proc latinSquareSystem*(n: int): ConstraintSystem[int] =
    # Latin Squares
    var system = initConstraintSystem[int]()
    var x = system.newConstrainedMatrix(n, n)
    x.setDomain(toSeq(0..<n))

    var locations: seq[Expression[int]] = @[]
    # Set rows to be distinct
    for i in 0..<n:
        locations = @[]
        for j in 0..<n:
            locations.add(x[i, j])
        system.addConstraint(allDifferent(locations))

    # Set all columns to be distinct
    for j in 0..<n:
        locations = @[]
        for i in 0..<n:
            locations.add(x[i, j])
        system.addConstraint(allDifferent(locations))
        
    # First row in order 0 1 2...
    for i in 0..<n:
        system.addConstraint(x[0, i] == i)

    # First col in order 0 1 2...
    for i in 0..<n:
        system.addConstraint(x[i, 0] == i)

    return system


proc MOLSSystem*(n: int): ConstraintSystem[int] =
    # Mutually Orthogonal Latin Squares
    var sys = initConstraintSystem[int]()
    var X = sys.newConstrainedMatrix(n, n)
    var Y = sys.newConstrainedMatrix(n, n)

    # Set up each of X and Y to be latin squares
    # Set domain of each entry to 0..<n
    X.setDomain(toSeq(0..<n))
    Y.setDomain(toSeq(0..<n))

    # Each row has to be a permutation of 0, 1, .., n
    for row in X.rows():
        sys.addConstraint(allDifferent(row))

    for row in Y.rows():
        sys.addConstraint(allDifferent(row))

    # Each col has to be a permutation of 0, 1, .., n
    for col in X.columns():
        sys.addConstraint(allDifferent(col))

    for col in Y.columns():
        sys.addConstraint(allDifferent(col))
        
    # First row in order 0 1 2... in first square
    for i in 0..<n:
        sys.addConstraint(X[0, i] == i)

    # First col in order 0 1 2... in both squares
    for i in 0..<n:
        sys.addConstraint(X[i, 0] == i)
        sys.addConstraint(Y[i, 0] == i)
    
    # Mutual orthogonality condition
    var pairs: seq[Expression[int]] = @[]
    for i in 0..<n:
        for j in 0..<n:
            pairs.add(X[i, j] + n*Y[i, j])
    sys.addConstraint(allDifferent(pairs))

    return sys


proc nQueens*(n: int): ConstrainedArray[int] =
    var x = initConstrainedArray[int](n)
    x.setDomain(toSeq 0..<n)

    for i in 0..<n:
        for j in (i + 1)..<n:
            x.addConstraint(x[i] != x[j])
            x.addConstraint(x[i] - x[j] != i - j)
            x.addConstraint(x[i] - x[j] != j - i)

    return x


proc nQueens2*(n: int): ConstrainedArray[int] =
    var x = initConstrainedArray[int](n)
    x.setDomain(toSeq 0..<n)

    var terms: seq[Expression[int]] = @[]
    for i in 0..<n:
        terms.add(x[i])
    x.addConstraint(allDifferent(terms))

    terms.reset()
    for i in 0..<n:
        terms.add(x[i] - i)
    x.addConstraint(allDifferent(terms))

    terms.reset()
    for i in 0..<n:
        terms.add(x[i] + i)
    x.addConstraint(allDifferent(terms))

    return x


proc magicSquare*(n: int): ConstrainedArray[int] = 
    # Magic Squares

    var
        x = initConstrainedArray[int](n*n)
        terms: seq[Expression[int]]

    let target = n*(n*n + 1) div 2

    # Row sums == target
    for p in 0..<n:
        terms = @[]
        for q in 0..<n:
            terms.add(x[p*n + q])
        x.addConstraint(terms.foldl(a + b) == target)

    # Col sums == target
    for q in 0..<n:
        terms = @[]
        for p in 0..<n:
            terms.add(x[p*n + q])
        x.addConstraint(terms.foldl(a + b) == target)
        
    # Diagonals
    terms = @[]
    for p in countup(0, n*n, n + 1):
        terms.add(x[p])
    x.addConstraint(terms.foldl(a + b) == target)

    terms = @[]
    for p in countup(n - 1, n*(n - 1), n - 1):
        terms.add(x[p])
    x.addConstraint(terms.foldl(a + b) == target)

    # All entries in square must be distinct
    x.allDifferent()

    x.setDomain(toSeq(1..n*n))
    return x


proc fooProblem*(): ConstraintSystem[int] =
    var system = initConstraintSystem[int]()
    var value = system.newConstrainedSequence(6)

    value.setDomain(toSeq(0..<5))

    system.addConstraint(value[0] + value[1] + value[2] == 3)
    system.addConstraint(value[3] + value[4] + value[5] == 3)
    system.addConstraint(value[2] + value[3] == 2)

    return system


proc fooGrid*(): ConstraintSystem[int] =
    var system = initConstraintSystem[int]()
    var value = system.newConstrainedMatrix(3, 3)

    value.setDomain(toSeq(0..<3))

    system.addConstraint(value[0, 0] + value[0, 1] + value[0, 2] == 2)
    system.addConstraint(value[1, 0] + value[1, 1] + value[1, 2] == 2)
    system.addConstraint(value[2, 0] + value[2, 1] + value[2, 2] == 2)

    return system
