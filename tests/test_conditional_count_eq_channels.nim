## Tests for conditional count-equals channel bindings.
##
## These test the ConditionalCountEqChannelBinding feature:
## 1. API-level: addConditionalCountEqChannelBinding with paired + direct positions
## 2. FZN-level: detectConditionalCountPatterns pattern detection and translation
## 3. Channel propagation correctness through solve/optimize

import std/[sequtils, sets, unittest, tables, algorithm]
import crusher
import flatzinc/[parser, translator, output]

suite "Conditional Count-Equals Channel Bindings (API)":

    test "Basic conditional count: paired positions only":
        ## 3 primary positions (domain {1,2,3}), 3 filter positions (domain {0,1}).
        ## Channel counts: #{primary[i]==2 AND filter[i]==1}.
        ## Fix filter[0..2] = 1, constrain count == 2.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            # 3 primary search vars (positions 0-2), domain {1,2,3}
            var primary = sys.newConstrainedSequence(3)
            primary.setDomain(@[1, 2, 3])

            # 3 filter search vars (positions 3-5), domain {0,1}
            var filter = sys.newConstrainedSequence(3)
            filter.setDomain(@[0, 1])

            # Channel: count of (primary[i]==2 AND filter[i]==1) at position 6
            let countPos = sys.baseArray.len
            var countVar = sys.newConstrainedVariable()
            countVar.setDomain(toSeq(0..3))
            sys.baseArray.addConditionalCountEqChannelBinding(
                countPos, targetValue = 2,
                primaryPositions = @[0, 1, 2],
                filterPositions = @[3, 4, 5],
                filterValue = 1)

            # Fix all filters to 1 so the count depends only on primary values
            sys.addConstraint(filter[0] == 1)
            sys.addConstraint(filter[1] == 1)
            sys.addConstraint(filter[2] == 1)

            # Require count == 2
            sys.addConstraint(sys.baseArray[countPos] == 2)

            sys.resolve(tabuThreshold = 5000)

            # Verify channel value
            var actual = 0
            for i in 0..2:
                if sys.assignment[i] == 2 and sys.assignment[i + 3] == 1:
                    inc actual
            check actual == 2
            check sys.assignment[countPos] == 2

    test "Conditional count: filter blocks counting":
        ## When filter[i] != filterValue, primary[i] doesn't count even if it matches.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            var primary = sys.newConstrainedSequence(3)
            primary.setDomain(@[1, 2])

            var filter = sys.newConstrainedSequence(3)
            filter.setDomain(@[0, 1])

            let countPos = sys.baseArray.len
            var countVar = sys.newConstrainedVariable()
            countVar.setDomain(toSeq(0..3))
            sys.baseArray.addConditionalCountEqChannelBinding(
                countPos, targetValue = 2,
                primaryPositions = @[0, 1, 2],
                filterPositions = @[3, 4, 5],
                filterValue = 1)

            # All primaries are 2, but only filter[0]=1, rest=0
            sys.addConstraint(primary[0] == 2)
            sys.addConstraint(primary[1] == 2)
            sys.addConstraint(primary[2] == 2)
            sys.addConstraint(filter[0] == 1)
            sys.addConstraint(filter[1] == 0)
            sys.addConstraint(filter[2] == 0)

            # Count should be exactly 1 (only position 0 passes both checks)
            sys.addConstraint(sys.baseArray[countPos] == 1)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[countPos] == 1

    test "Conditional count with primaryOnly positions":
        ## Mix of paired (primary+filter) and primaryOnly (no filter check) positions.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            # 2 paired primary positions (0-1)
            var pairedPrimary = sys.newConstrainedSequence(2)
            pairedPrimary.setDomain(@[1, 2, 3])

            # 2 filter positions (2-3)
            var filter = sys.newConstrainedSequence(2)
            filter.setDomain(@[0, 1])

            # 1 primaryOnly position (4)
            var directVar = sys.newConstrainedVariable()
            directVar.setDomain(@[1, 2, 3])

            let countPos = sys.baseArray.len
            var countVar = sys.newConstrainedVariable()
            countVar.setDomain(toSeq(0..3))
            sys.baseArray.addConditionalCountEqChannelBinding(
                countPos, targetValue = 2,
                primaryPositions = @[0, 1],
                filterPositions = @[2, 3],
                filterValue = 1,
                primaryOnlyPositions = @[4])

            # Set up: paired[0]=2 with filter[0]=1 → counts
            #         paired[1]=2 with filter[1]=0 → blocked
            #         direct[0]=2 → counts (no filter check)
            sys.addConstraint(pairedPrimary[0] == 2)
            sys.addConstraint(filter[0] == 1)
            sys.addConstraint(pairedPrimary[1] == 2)
            sys.addConstraint(filter[1] == 0)
            sys.addConstraint(directVar == 2)

            sys.addConstraint(sys.baseArray[countPos] == 2)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[countPos] == 2

    test "Conditional count with constantOffset":
        ## Channel = constantOffset + paired count.
        for trial in 0..<5:
            var sys = initConstraintSystem[int]()

            var primary = sys.newConstrainedSequence(2)
            primary.setDomain(@[1, 2])

            var filter = sys.newConstrainedSequence(2)
            filter.setDomain(@[0, 1])

            let countPos = sys.baseArray.len
            var countVar = sys.newConstrainedVariable()
            countVar.setDomain(toSeq(0..5))
            sys.baseArray.addConditionalCountEqChannelBinding(
                countPos, targetValue = 1,
                primaryPositions = @[0, 1],
                filterPositions = @[2, 3],
                filterValue = 1,
                constantOffset = 3)

            # Both primary=1, both filter=1 → paired count = 2, total = 3 + 2 = 5
            sys.addConstraint(primary[0] == 1)
            sys.addConstraint(primary[1] == 1)
            sys.addConstraint(filter[0] == 1)
            sys.addConstraint(filter[1] == 1)
            sys.addConstraint(sys.baseArray[countPos] == 5)

            sys.resolve(tabuThreshold = 5000)

            check sys.assignment[countPos] == 5

    test "Conditional count used in optimization":
        ## Minimize a conditional count channel value.
        ## 4 primary vars, 4 filter vars. Minimize count where primary==1 AND filter==1.
        var sys = initConstraintSystem[int]()

        var primary = sys.newConstrainedSequence(4)
        primary.setDomain(@[1, 2])

        var filter = sys.newConstrainedSequence(4)
        filter.setDomain(@[0, 1])

        let countPos = sys.baseArray.len
        var countVar = sys.newConstrainedVariable()
        countVar.setDomain(toSeq(0..4))
        sys.baseArray.addConditionalCountEqChannelBinding(
            countPos, targetValue = 1,
            primaryPositions = @[0, 1, 2, 3],
            filterPositions = @[4, 5, 6, 7],
            filterValue = 1)

        # At least 2 filters must be 1
        sys.addConstraint(filter[0] + filter[1] + filter[2] + filter[3] >= 2)

        # Minimize the conditional count
        sys.minimize(sys.baseArray[countPos], parallel = true,
                    tabuThreshold = 2000, lowerBound = 0)

        # Optimal: set all primary != 1 (i.e., primary = 2), then count = 0
        check sys.assignment[countPos] == 0

    test "Multiple conditional count channels for different target values":
        ## Two conditional count channels over the same positions but different target values.
        for trial in 0..<3:
            var sys = initConstraintSystem[int]()

            var primary = sys.newConstrainedSequence(4)
            primary.setDomain(@[1, 2, 3])

            var filter = sys.newConstrainedSequence(4)
            filter.setDomain(@[0, 1])

            let countPos1 = sys.baseArray.len
            var count1 = sys.newConstrainedVariable()
            count1.setDomain(toSeq(0..4))
            sys.baseArray.addConditionalCountEqChannelBinding(
                countPos1, targetValue = 1,
                primaryPositions = @[0, 1, 2, 3],
                filterPositions = @[4, 5, 6, 7],
                filterValue = 1)

            let countPos2 = sys.baseArray.len
            var count2 = sys.newConstrainedVariable()
            count2.setDomain(toSeq(0..4))
            sys.baseArray.addConditionalCountEqChannelBinding(
                countPos2, targetValue = 2,
                primaryPositions = @[0, 1, 2, 3],
                filterPositions = @[4, 5, 6, 7],
                filterValue = 1)

            # Fix filters to 1
            for i in 0..3:
                sys.addConstraint(filter[i] == 1)

            # Require: count(primary==1 AND filter==1) == 2
            #          count(primary==2 AND filter==1) == 1
            sys.addConstraint(sys.baseArray[countPos1] == 2)
            sys.addConstraint(sys.baseArray[countPos2] == 1)

            sys.resolve(tabuThreshold = 5000)

            let a = primary.assignment
            var c1, c2 = 0
            for v in a:
                if v == 1: inc c1
                if v == 2: inc c2
            check c1 == 2
            check c2 == 1
            check sys.assignment[countPos1] == 2
            check sys.assignment[countPos2] == 1

suite "Conditional Count-Equals FZN Pattern Detection":

    test "Detect conditional count: paired + direct indicators":
        ## Full decomposition: 2 conditional (paired via array_bool_and) + 1 direct.
        ## Pattern: count_if(x[i]==2 AND y[i]==1) for i=1..2, plus direct x3==2.
        ## Target = count + 1 (constantOffset from rhs).
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 0..1: y1 :: output_var;
var 0..1: y2 :: output_var;
var 0..4: target :: output_var;
var bool: bp1 :: var_is_introduced :: is_defined_var;
var bool: bp2 :: var_is_introduced :: is_defined_var;
var bool: bf1 :: var_is_introduced :: is_defined_var;
var bool: bf2 :: var_is_introduced :: is_defined_var;
var bool: ba1 :: var_is_introduced :: is_defined_var;
var bool: ba2 :: var_is_introduced :: is_defined_var;
var 0..1: n1 :: var_is_introduced :: is_defined_var;
var 0..1: n2 :: var_is_introduced :: is_defined_var;
var bool: bd3 :: var_is_introduced :: is_defined_var;
var 0..1: n3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 2, bp1) :: defines_var(bp1);
constraint int_eq_reif(y1, 1, bf1) :: defines_var(bf1);
constraint array_bool_and([bp1, bf1], ba1) :: defines_var(ba1);
constraint bool2int(ba1, n1) :: defines_var(n1);
constraint int_eq_reif(x2, 2, bp2) :: defines_var(bp2);
constraint int_eq_reif(y2, 1, bf2) :: defines_var(bf2);
constraint array_bool_and([bp2, bf2], ba2) :: defines_var(ba2);
constraint bool2int(ba2, n2) :: defines_var(n2);
constraint int_eq_reif(x3, 2, bd3) :: defines_var(bd3);
constraint bool2int(bd3, n3) :: defines_var(n3);
constraint int_lin_eq([1, -1, -1, -1], [target, n1, n2, n3], -1) :: defines_var(target);
constraint int_le(target, 3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Pattern detected
        check tr.conditionalCountEqPatterns.len == 1
        for _, pat in tr.conditionalCountEqPatterns:
            check pat.targetValue == 2
            check pat.filterValue == 1
            check pat.primaryVarNames.len == 2   # x1, x2 (paired)
            check pat.filterVarNames.len == 2    # y1, y2 (paired)
            check pat.primaryOnlyVarNames.len == 1  # x3 (direct)
            check pat.constantOffset == -1       # rhs=-1, targetCoeff=1 → -1*1 = -1... wait
            # rhs=-1, targetCoeff=1 → constantOffset = rhs * targetCoeff = -1
            # Actual: target = constantOffset + count = -1 + count
            # So target = count - 1... But int_lin_eq is: 1*target - n1 - n2 - n3 = -1
            # → target = n1+n2+n3 - 1, so constantOffset = -1. Correct.

        # Solve and verify
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal >= 0
        check targetVal <= 3

        # Manually compute expected count
        var count = 0
        let x1 = tr.sys.assignment[tr.varPositions["x1"]]
        let y1 = tr.sys.assignment[tr.varPositions["y1"]]
        let x2 = tr.sys.assignment[tr.varPositions["x2"]]
        let y2 = tr.sys.assignment[tr.varPositions["y2"]]
        let x3 = tr.sys.assignment[tr.varPositions["x3"]]
        if x1 == 2 and y1 == 1: inc count
        if x2 == 2 and y2 == 1: inc count
        if x3 == 2: inc count
        # target = count + constantOffset = count - 1
        check targetVal == count - 1

    test "Detect conditional count: all paired, no direct":
        ## All indicators go through array_bool_and (no direct path).
        ## count_if(x[i]==1 AND y[i]==1) for i=1..3.
        let src = """
var 1..2: x1 :: output_var;
var 1..2: x2 :: output_var;
var 1..2: x3 :: output_var;
var 0..1: y1 :: output_var;
var 0..1: y2 :: output_var;
var 0..1: y3 :: output_var;
var 0..3: target :: output_var;
var bool: bp1 :: var_is_introduced :: is_defined_var;
var bool: bp2 :: var_is_introduced :: is_defined_var;
var bool: bp3 :: var_is_introduced :: is_defined_var;
var bool: bf1 :: var_is_introduced :: is_defined_var;
var bool: bf2 :: var_is_introduced :: is_defined_var;
var bool: bf3 :: var_is_introduced :: is_defined_var;
var bool: ba1 :: var_is_introduced :: is_defined_var;
var bool: ba2 :: var_is_introduced :: is_defined_var;
var bool: ba3 :: var_is_introduced :: is_defined_var;
var 0..1: n1 :: var_is_introduced :: is_defined_var;
var 0..1: n2 :: var_is_introduced :: is_defined_var;
var 0..1: n3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 1, bp1) :: defines_var(bp1);
constraint int_eq_reif(y1, 1, bf1) :: defines_var(bf1);
constraint array_bool_and([bp1, bf1], ba1) :: defines_var(ba1);
constraint bool2int(ba1, n1) :: defines_var(n1);
constraint int_eq_reif(x2, 1, bp2) :: defines_var(bp2);
constraint int_eq_reif(y2, 1, bf2) :: defines_var(bf2);
constraint array_bool_and([bp2, bf2], ba2) :: defines_var(ba2);
constraint bool2int(ba2, n2) :: defines_var(n2);
constraint int_eq_reif(x3, 1, bp3) :: defines_var(bp3);
constraint int_eq_reif(y3, 1, bf3) :: defines_var(bf3);
constraint array_bool_and([bp3, bf3], ba3) :: defines_var(ba3);
constraint bool2int(ba3, n3) :: defines_var(n3);
constraint int_lin_eq([-1, 1, 1, 1], [target, n1, n2, n3], 0) :: defines_var(target);
constraint int_eq(target, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.conditionalCountEqPatterns.len == 1
        for _, pat in tr.conditionalCountEqPatterns:
            check pat.targetValue == 1
            check pat.filterValue == 1
            check pat.primaryVarNames.len == 3
            check pat.filterVarNames.len == 3
            check pat.primaryOnlyVarNames.len == 0
            check pat.constantOffset == 0  # rhs=0, targetCoeff=-1 → 0*(-1) = 0

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal == 2

        # Verify: exactly 2 positions have x[i]==1 AND y[i]==1
        var count = 0
        for name in ["1", "2", "3"]:
            let xv = tr.sys.assignment[tr.varPositions["x" & name]]
            let yv = tr.sys.assignment[tr.varPositions["y" & name]]
            if xv == 1 and yv == 1: inc count
        check count == 2

    test "Conditional count with shared reif boolVars (not consumed)":
        ## The int_eq_reif output boolVars are also used in a bool_clause.
        ## The pattern detector must NOT consume them so reification channels get built.
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 0..1: y1 :: output_var;
var 0..1: y2 :: output_var;
var 0..2: target :: output_var;
var bool: bp1 :: var_is_introduced :: is_defined_var;
var bool: bp2 :: var_is_introduced :: is_defined_var;
var bool: bf1 :: var_is_introduced :: is_defined_var;
var bool: bf2 :: var_is_introduced :: is_defined_var;
var bool: ba1 :: var_is_introduced :: is_defined_var;
var bool: ba2 :: var_is_introduced :: is_defined_var;
var 0..1: n1 :: var_is_introduced :: is_defined_var;
var 0..1: n2 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 2, bp1) :: defines_var(bp1);
constraint int_eq_reif(y1, 1, bf1) :: defines_var(bf1);
constraint array_bool_and([bp1, bf1], ba1) :: defines_var(ba1);
constraint bool2int(ba1, n1) :: defines_var(n1);
constraint int_eq_reif(x2, 2, bp2) :: defines_var(bp2);
constraint int_eq_reif(y2, 1, bf2) :: defines_var(bf2);
constraint array_bool_and([bp2, bf2], ba2) :: defines_var(ba2);
constraint bool2int(ba2, n2) :: defines_var(n2);
constraint int_lin_eq([-1, 1, 1], [target, n1, n2], 0) :: defines_var(target);
constraint bool_clause([bp1, bp2], []);
constraint int_eq(target, 1);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Pattern should be detected
        check tr.conditionalCountEqPatterns.len == 1

        # bp1, bp2 must NOT be consumed (they're in bool_clause)
        check "bp1" notin tr.definedVarNames or "bp1" in tr.channelVarNames
        check "bp2" notin tr.definedVarNames or "bp2" in tr.channelVarNames

        # Should solve without KeyError
        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        let targetVal = tr.sys.assignment[tr.varPositions["target"]]
        check targetVal == 1

    test "No false detection on plain count_eq (no array_bool_and)":
        ## A simple count_eq pattern (no paired conditions) should NOT trigger
        ## conditional count detection (requires hasConditional).
        let src = """
var 1..3: x1 :: output_var;
var 1..3: x2 :: output_var;
var 1..3: x3 :: output_var;
var 0..3: target :: output_var;
var bool: b1 :: var_is_introduced :: is_defined_var;
var bool: b2 :: var_is_introduced :: is_defined_var;
var bool: b3 :: var_is_introduced :: is_defined_var;
var 0..1: n1 :: var_is_introduced :: is_defined_var;
var 0..1: n2 :: var_is_introduced :: is_defined_var;
var 0..1: n3 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(x1, 2, b1) :: defines_var(b1);
constraint int_eq_reif(x2, 2, b2) :: defines_var(b2);
constraint int_eq_reif(x3, 2, b3) :: defines_var(b3);
constraint bool2int(b1, n1) :: defines_var(n1);
constraint bool2int(b2, n2) :: defines_var(n2);
constraint bool2int(b3, n3) :: defines_var(n3);
constraint int_lin_eq([-1, 1, 1, 1], [target, n1, n2, n3], 0) :: defines_var(target);
constraint int_eq(target, 2);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        # Should NOT be detected as conditional (no array_bool_and → hasConditional=false)
        check tr.conditionalCountEqPatterns.len == 0

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        # Verify: exactly 2 of x1..x3 equal 2
        var count = 0
        for name in ["x1", "x2", "x3"]:
            if tr.sys.assignment[tr.varPositions[name]] == 2:
                inc count
        check count == 2

    test "Conditional count solves constrained problem":
        ## A small but meaningful problem: 4 items, each with a type (1..3) and an active
        ## flag (0..1). Count how many active items have type==2. Require exactly 2.
        ## Also require at least 3 items to be active.
        let src = """
var 1..3: type1 :: output_var;
var 1..3: type2 :: output_var;
var 1..3: type3 :: output_var;
var 1..3: type4 :: output_var;
var 0..1: active1 :: output_var;
var 0..1: active2 :: output_var;
var 0..1: active3 :: output_var;
var 0..1: active4 :: output_var;
var 0..4: count_active_type2 :: output_var;
var bool: bp1 :: var_is_introduced :: is_defined_var;
var bool: bp2 :: var_is_introduced :: is_defined_var;
var bool: bp3 :: var_is_introduced :: is_defined_var;
var bool: bp4 :: var_is_introduced :: is_defined_var;
var bool: bf1 :: var_is_introduced :: is_defined_var;
var bool: bf2 :: var_is_introduced :: is_defined_var;
var bool: bf3 :: var_is_introduced :: is_defined_var;
var bool: bf4 :: var_is_introduced :: is_defined_var;
var bool: ba1 :: var_is_introduced :: is_defined_var;
var bool: ba2 :: var_is_introduced :: is_defined_var;
var bool: ba3 :: var_is_introduced :: is_defined_var;
var bool: ba4 :: var_is_introduced :: is_defined_var;
var 0..1: n1 :: var_is_introduced :: is_defined_var;
var 0..1: n2 :: var_is_introduced :: is_defined_var;
var 0..1: n3 :: var_is_introduced :: is_defined_var;
var 0..1: n4 :: var_is_introduced :: is_defined_var;
constraint int_eq_reif(type1, 2, bp1) :: defines_var(bp1);
constraint int_eq_reif(active1, 1, bf1) :: defines_var(bf1);
constraint array_bool_and([bp1, bf1], ba1) :: defines_var(ba1);
constraint bool2int(ba1, n1) :: defines_var(n1);
constraint int_eq_reif(type2, 2, bp2) :: defines_var(bp2);
constraint int_eq_reif(active2, 1, bf2) :: defines_var(bf2);
constraint array_bool_and([bp2, bf2], ba2) :: defines_var(ba2);
constraint bool2int(ba2, n2) :: defines_var(n2);
constraint int_eq_reif(type3, 2, bp3) :: defines_var(bp3);
constraint int_eq_reif(active3, 1, bf3) :: defines_var(bf3);
constraint array_bool_and([bp3, bf3], ba3) :: defines_var(ba3);
constraint bool2int(ba3, n3) :: defines_var(n3);
constraint int_eq_reif(type4, 2, bp4) :: defines_var(bp4);
constraint int_eq_reif(active4, 1, bf4) :: defines_var(bf4);
constraint array_bool_and([bp4, bf4], ba4) :: defines_var(ba4);
constraint bool2int(ba4, n4) :: defines_var(n4);
constraint int_lin_eq([-1, 1, 1, 1, 1], [count_active_type2, n1, n2, n3, n4], 0) :: defines_var(count_active_type2);
constraint int_eq(count_active_type2, 2);
constraint int_lin_le([-1, -1, -1, -1], [active1, active2, active3, active4], -3);
solve satisfy;
"""
        let model = parseFzn(src)
        var tr = translate(model)

        check tr.conditionalCountEqPatterns.len == 1

        tr.sys.resolve(parallel = true, tabuThreshold = 5000, verbose = false)

        # Verify solution
        let a = tr.sys.assignment
        let countVal = a[tr.varPositions["count_active_type2"]]
        check countVal == 2

        # Verify: at least 3 active
        var totalActive = 0
        for name in ["active1", "active2", "active3", "active4"]:
            totalActive += a[tr.varPositions[name]]
        check totalActive >= 3

        # Verify: exactly 2 items have type==2 AND active==1
        var actualCount = 0
        for i in 1..4:
            let t = a[tr.varPositions["type" & $i]]
            let act = a[tr.varPositions["active" & $i]]
            if t == 2 and act == 1: inc actualCount
        check actualCount == 2
