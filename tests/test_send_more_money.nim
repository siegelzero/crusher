import std/[sequtils, unittest]
import crusher

suite "SEND + MORE == MONEY Tests":
    test "Cryptarithmetic puzzle solution":
        # Create the SEND + MORE == MONEY model
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

        # Solve the constraint system
        sys.resolve(10000, parallel=true, verbose=true)

        # Extract the solution
        let solution = value.assignment()

        # Validate the solution
        check solution.len == 8

        let
            sVal = solution[S]
            eVal = solution[E]
            nVal = solution[N]
            dVal = solution[D]
            mVal = solution[M]
            oVal = solution[O]
            rVal = solution[R]
            yVal = solution[Y]

        # Check that all values are digits (0-9)
        for val in solution:
            check val >= 0 and val <= 9

        # Check that all digits are different
        check solution.deduplicate().len == 8

        # Check that S and M are not 0 (leading digits)
        check sVal > 0
        check mVal > 0

        # Calculate and verify the equation
        let
            sendVal = 1000*sVal + 100*eVal + 10*nVal + dVal
            moreVal = 1000*mVal + 100*oVal + 10*rVal + eVal
            moneyVal = 10000*mVal + 1000*oVal + 100*nVal + 10*eVal + yVal

        echo "Solution: SEND=", sendVal, ", MORE=", moreVal, ", MONEY=", moneyVal

        # Check the main constraint
        check sendVal + moreVal == moneyVal

        # Verify against known solution: 9567 + 1085 = 10652
        check sVal == 9 and eVal == 5 and nVal == 6 and dVal == 7
        check mVal == 1 and oVal == 0 and rVal == 8 and yVal == 2
