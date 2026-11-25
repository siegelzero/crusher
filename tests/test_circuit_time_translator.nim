## Unit tests for the circuit-time translator passes:
##   - detectCircuitTimePropagation: successor-form (inequality) and legacy
##     predecessor-form (equality) matching, multi-instance, service-time
##     folding, fixed links, unconstrained arcs, depot anchoring
##   - verifyCircuitTimeCandidates: projection-soundness rejection cases and
##     objective linkage extraction (direct max, weighted sum of maxima,
##     direct sum of times -> weighted-sum metric)
##   - tryMatchSuccFormAccumulators: equality accumulator chains (CVRP load /
##     vehicle painting), forward/backward anchoring guards, one instance per
##     value array across mirror circuits
##   - objective bound delegation (circuitTimeObjectiveExact)
##   - dropImpliedInverseCircuits: circuit over the channel side of an inverse
##     pair is consumed when the forward side is circuit-enforced
##   - deterministic mutual-inverse suppression (annotated side stays searchable)
##   - rewriteInverseChannelIndexedElements: channel-index elements rewritten
##     to forward-side elements, with subsumption (including circuit-time-
##     consumed witnesses) and tautology elimination
##   - split time chains (VRP with location congestion): chain intermediates
##     without bindings, linked pickup/delivery pairs started on one vehicle

import unittest
import std/[strutils, tables, sets, packedsets, random]
import crusher
import flatzinc/[parser, translator]
import constraints/[types, circuitTimeProp]
import search/tabu

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

proc countType(tr: FznTranslator, st: StatefulConstraintType): int =
    for c in tr.sys.baseArray.constraints:
        if c.stateType == st:
            inc result

proc pos(tr: FznTranslator, name: string): int =
    tr.varPositions[name]

proc val(tr: FznTranslator, name: string): int =
    tr.sys.assignment[tr.varPositions[name]]

## Successor-form base model: 4 nodes = 2 customers (1, 2), start depot (3,
## time fixed 0), end depot (4, succ fixed to 3 = giant-tour wrap, no time
## triple). Services: node1=2, node2=3, node3=0.
##   row_n[j] = dist from n to j (1-based by successor value)
const SuccBase = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 0..50: t1;
var 0..50: t2;
var 0..50: t4;
var 0..20: d1;
var 0..20: d2;
var 0..20: d3;
var 0..50: a1;
var 0..50: a2;
var 0..50: a3;
var 0..50: m;
constraint crusher_circuit([s1, s2, s3, 3]);
constraint array_int_element(s1, [0, 3, 9, 4], d1) :: defines_var(d1);
constraint array_var_int_element(s1, [t1, t2, 0, t4], a1) :: defines_var(a1);
constraint int_lin_le([1, 1, -1], [t1, d1, a1], -2);
constraint array_int_element(s2, [3, 0, 9, 6], d2) :: defines_var(d2);
constraint array_var_int_element(s2, [t1, t2, 0, t4], a2) :: defines_var(a2);
constraint int_lin_le([1, 1, -1], [t2, d2, a2], -3);
constraint array_int_element(s3, [2, 5, 0, 9], d3) :: defines_var(d3);
constraint array_var_int_element(s3, [t1, t2, 0, t4], a3) :: defines_var(a3);
constraint int_lin_le([1, -1], [d3, a3], 0);
constraint array_int_maximum(m, [t1, t2, 0, t4]) :: defines_var(m);
"""

# ---------------------------------------------------------------------------
# Successor-form detection
# ---------------------------------------------------------------------------

suite "Circuit-time successor-form detection":

    test "basic detection: structure, service folding, depot, fixed link":
        let tr = translate(parseFzn(SuccBase & "solve minimize m;\n"))
        check tr.circuitTimeCandidates.len == 1
        let cand = tr.circuitTimeCandidates[0]
        check cand.forward == true
        check cand.linkVarNames == @["s1", "s2", "s3", ""]
        check cand.rawFixedLinks[3] == 3
        check cand.depotIdx == 2          # node 3 (0-based), first fixed-time node
        check cand.depotDep == 0
        check cand.outConstrained == @[true, true, true, false]
        # Service folded into the matrix: dist[to][from] = row_from[to] + service_from
        check cand.distMatrix[1][0] == 3 + 2   # 1 -> 2
        check cand.distMatrix[3][0] == 4 + 2   # 1 -> 4
        check cand.distMatrix[3][1] == 6 + 3   # 2 -> 4
        check cand.distMatrix[0][2] == 2 + 0   # 3 -> 1
        check cand.distMatrix[0][3] == 0       # node 4 unconstrained: zero row
        # Time windows: fixed node pinned, others from (presolve-tightened)
        # domains — t1 <= 48 and t2 <= 47 follow from the lin_le chains
        check cand.earlyTimes == @[0, 0, 0, 0]
        check cand.lateTimes == @[48, 47, 0, 50]
        # Emitted as the only global constraint; the circuit was consumed
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0

    test "direct objective linkage: minimize the covering max":
        let tr = translate(parseFzn(SuccBase & "solve minimize m;\n"))
        let cand = tr.circuitTimeCandidates[0]
        check cand.useMaxMetric == true
        check cand.objectiveWeight == 1
        check cand.objectiveConstOffset == 0
        check cand.objectiveMetricLo == 0

    test "satisfy with unobserved times: kept with no objective linkage":
        # Times feed nothing (no maximum at all): projection is sound, weight 0
        var src = ""
        for line in SuccBase.splitLines():
            if "array_int_maximum" notin line and not line.startsWith("var 0..50: m"):
                src.add(line & "\n")
        let tr = translate(parseFzn(src & "solve satisfy;\n"))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].objectiveWeight == 0
        check tr.countType(CircuitTimePropType) == 1

    test "round-trip: solution is a circuit with exact earliest times":
        # minimize m so the inequality->earliest projection applies (under
        # plain satisfy with an observed max the verifier rejects, by design)
        var tr = translate(parseFzn(SuccBase & "solve minimize m;\n"))
        check tr.circuitTimeCandidates.len == 1
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        let s = @[tr.val("s1"), tr.val("s2"), tr.val("s3"), 3]
        # Hamiltonian circuit over 4 nodes
        var seen: HashSet[int]
        var cur = 1
        for i in 0..<4:
            check cur notin seen
            seen.incl(cur)
            cur = s[cur-1]
        check cur == 1
        check seen.len == 4
        # Earliest-time equality along constrained arcs (node 3's time is the
        # fixed 0; nothing but the unconstrained node 4 may point at it)
        let t = @[tr.val("t1"), tr.val("t2"), 0, tr.val("t4")]
        let rows = @[@[0, 3, 9, 4], @[3, 0, 9, 6], @[2, 5, 0, 9]]
        let service = @[2, 3, 0]
        for n in 0..<3:
            let target = s[n] - 1
            check target != 2            # only node 4 (wrap) enters the depot
            check t[target] == t[n] + service[n] + rows[n][target]

# ---------------------------------------------------------------------------
# Weighted multi-instance objective linkage
# ---------------------------------------------------------------------------

proc twoScenarioSrc(objLinEq: string): string =
    ## Two independent 3-node circuits (1 customer, start depot 2, end depot 3
    ## with fixed wrap), maxima mA/mB, plus the given objective definition.
    result = """
var 1..3: sa1;
var 1..3: sa2;
var 0..40: ta1;
var 0..40: ta3;
var 0..20: da1;
var 0..20: da2;
var 0..40: aa1;
var 0..40: aa2;
var 0..40: ma;
var 1..3: sb1;
var 1..3: sb2;
var 0..40: tb1;
var 0..40: tb3;
var 0..20: db1;
var 0..20: db2;
var 0..40: ab1;
var 0..40: ab2;
var 0..40: mb;
var 0..200: obj;
constraint crusher_circuit([sa1, sa2, 2]);
constraint array_int_element(sa1, [0, 9, 4], da1) :: defines_var(da1);
constraint array_var_int_element(sa1, [ta1, 0, ta3], aa1) :: defines_var(aa1);
constraint int_lin_le([1, 1, -1], [ta1, da1, aa1], -2);
constraint array_int_element(sa2, [3, 0, 9], da2) :: defines_var(da2);
constraint array_var_int_element(sa2, [ta1, 0, ta3], aa2) :: defines_var(aa2);
constraint int_lin_le([1, -1], [da2, aa2], 0);
constraint array_int_maximum(ma, [ta1, 0, ta3]) :: defines_var(ma);
constraint crusher_circuit([sb1, sb2, 2]);
constraint array_int_element(sb1, [0, 9, 5], db1) :: defines_var(db1);
constraint array_var_int_element(sb1, [tb1, 0, tb3], ab1) :: defines_var(ab1);
constraint int_lin_le([1, 1, -1], [tb1, db1, ab1], -1);
constraint array_int_element(sb2, [2, 0, 9], db2) :: defines_var(db2);
constraint array_var_int_element(sb2, [tb1, 0, tb3], ab2) :: defines_var(ab2);
constraint int_lin_le([1, -1], [db2, ab2], 0);
constraint array_int_maximum(mb, [tb1, 0, tb3]) :: defines_var(mb);
""" & objLinEq

suite "Circuit-time objective linkage and soundness verification":

    test "weighted sum of maxima: per-instance weights extracted":
        let src = twoScenarioSrc(
            "constraint int_lin_eq([1, -3, -2], [obj, ma, mb], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")
        let tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 2
        var weights: seq[int]
        for cand in tr.circuitTimeCandidates:
            check cand.forward == true
            check cand.objectiveConstOffset == 0
            weights.add(cand.objectiveWeight)
        check weights == @[3, 2]
        check tr.countType(CircuitTimePropType) == 2
        check tr.countType(CircuitType) == 0

    test "negative weight (minimize pushes max up): candidates rejected":
        # obj = 3*ma - 2*mb: minimizing obj wants mb LARGE -> projection of
        # scenario B's times to their minima is unsound; B must be dropped.
        # A's weight remains sign-sound, but bound distribution needs the
        # full clean form, so A keeps weight 0.
        let src = twoScenarioSrc(
            "constraint int_lin_eq([1, -3, 2], [obj, ma, mb], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")
        let tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].objectiveWeight == 0
        # The dropped scenario translates normally: its circuit survives
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 1

    test "maximize over observed times: candidate rejected":
        let tr = translate(parseFzn(SuccBase & "solve maximize m;\n"))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitTimePropType) == 0
        check tr.countType(CircuitType) == 1

    test "satisfy with observed max: candidate rejected":
        # No objective direction justifies projecting times to their minima
        # while a max over them is observable.
        let tr = translate(parseFzn(SuccBase & "solve satisfy;\n"))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitTimePropType) == 0
        check tr.countType(CircuitType) == 1

    test "time variable observed by a foreign constraint: rejected":
        let src = SuccBase & "constraint int_lin_le([1, -1], [t1, t2], 0);\n" &
                  "solve minimize m;\n"
        let tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitTimePropType) == 0
        check tr.countType(CircuitType) == 1

    test "partial max coverage: kept but no bound distribution":
        # Max over a strict subset of the times: sound for projection, but the
        # instance metric (max over ALL nodes) would over-prune as a bound.
        var src = ""
        for line in SuccBase.splitLines():
            if "array_int_maximum" in line:
                src.add("constraint array_int_maximum(m, [t1, t2]) :: defines_var(m);\n")
            else:
                src.add(line & "\n")
        let tr = translate(parseFzn(src & "solve minimize m;\n"))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].objectiveWeight == 0
        check tr.countType(CircuitTimePropType) == 1

# ---------------------------------------------------------------------------
# Legacy predecessor form
# ---------------------------------------------------------------------------

suite "Circuit-time predecessor-form (legacy TSPTW)":

    ## 4 nodes, depot 1 (constant departure 0 in the departures array).
    ## row_l[k] = dist from k to l. Ring distances 1, diagonals 5.
    const PredSrc = """
var 1..4: p1;
var 1..4: p2;
var 1..4: p3;
var 1..4: p4;
var 0..100: dep2;
var 0..100: dep3;
var 0..100: dep4;
var 0..100: arr1;
var 0..100: arr2;
var 0..100: arr3;
var 0..100: arr4;
var 0..100: dpp1;
var 0..100: dpp2;
var 0..100: dpp3;
var 0..100: dpp4;
var 0..20: dur1;
var 0..20: dur2;
var 0..20: dur3;
var 0..20: dur4;
constraint crusher_circuit([p1, p2, p3, p4]);
constraint array_int_element(p1, [0, 1, 5, 1], dur1) :: defines_var(dur1);
constraint array_var_int_element(p1, [0, dep2, dep3, dep4], dpp1) :: defines_var(dpp1);
constraint int_lin_eq([1, -1, -1], [arr1, dpp1, dur1], 0) :: defines_var(arr1);
constraint array_int_element(p2, [1, 0, 1, 5], dur2) :: defines_var(dur2);
constraint array_var_int_element(p2, [0, dep2, dep3, dep4], dpp2) :: defines_var(dpp2);
constraint int_lin_eq([1, -1, -1], [arr2, dpp2, dur2], 0) :: defines_var(arr2);
constraint int_max(arr2, 0, dep2);
constraint array_int_element(p3, [5, 1, 0, 1], dur3) :: defines_var(dur3);
constraint array_var_int_element(p3, [0, dep2, dep3, dep4], dpp3) :: defines_var(dpp3);
constraint int_lin_eq([1, -1, -1], [arr3, dpp3, dur3], 0) :: defines_var(arr3);
constraint int_max(arr3, 0, dep3);
constraint array_int_element(p4, [1, 5, 1, 0], dur4) :: defines_var(dur4);
constraint array_var_int_element(p4, [0, dep2, dep3, dep4], dpp4) :: defines_var(dpp4);
constraint int_lin_eq([1, -1, -1], [arr4, dpp4, dur4], 0) :: defines_var(arr4);
constraint int_max(arr4, 0, dep4);
solve minimize arr1;
"""

    test "detection: pred orientation, depot, legacy objective behavior":
        let tr = translate(parseFzn(PredSrc))
        check tr.circuitTimeCandidates.len == 1
        let cand = tr.circuitTimeCandidates[0]
        check cand.forward == false
        check cand.linkVarNames == @["p1", "p2", "p3", "p4"]
        check cand.depotIdx == 0
        check cand.depotDep == 0
        check cand.outConstrained.len == 0      # all arcs constrained
        check cand.useMaxMetric == false
        check cand.objectiveWeight == 1          # legacy: bound = target
        # Legacy linkage is heuristic, not exact: no bound delegation
        check tr.sys.circuitTimeObjectiveExact == false
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0

    test "round-trip: valid circuit with consistent equality times":
        var tr = translate(parseFzn(PredSrc))
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        let p = @[tr.val("p1"), tr.val("p2"), tr.val("p3"), tr.val("p4")]
        var seen: HashSet[int]
        var cur = 1
        for i in 0..<4:
            check cur notin seen
            seen.incl(cur)
            # follow successor: the node whose predecessor is cur
            for l in 1..4:
                if p[l-1] == cur:
                    cur = l
                    break
        check cur == 1
        check seen.len == 4
        # arrival[l] = departure[pred_l] + dist[l][pred_l]; departures = max(arr, 0)
        let rows = @[@[0, 1, 5, 1], @[1, 0, 1, 5], @[5, 1, 0, 1], @[1, 5, 1, 0]]
        let arr = @[tr.val("arr1"), tr.val("arr2"), tr.val("arr3"), tr.val("arr4")]
        for l in 0..<4:
            let k = p[l] - 1
            let dep = if k == 0: 0 else: max(arr[k], 0)
            check arr[l] == dep + rows[l][k]

# ---------------------------------------------------------------------------
# Inverse-channel passes
# ---------------------------------------------------------------------------

## Mutual inverse pair: S (annotated, stays searchable) and P (channelized).
## Both carry circuit constraints; P's is implied and must be dropped.
const InverseBase = """
var 1..4: sv1;
var 1..4: sv2;
var 1..4: sv3;
var 1..4: sv4;
var 1..4: pv1;
var 1..4: pv2;
var 1..4: pv3;
var 1..4: pv4;
array [1..4] of var int: S = [sv1, sv2, sv3, sv4];
array [1..4] of var int: P = [pv1, pv2, pv3, pv4];
constraint crusher_circuit(S);
constraint crusher_circuit(P);
constraint array_var_int_element(sv1, P, 1);
constraint array_var_int_element(sv2, P, 2);
constraint array_var_int_element(sv3, P, 3);
constraint array_var_int_element(sv4, P, 4);
constraint array_var_int_element(pv1, S, 1);
constraint array_var_int_element(pv2, S, 2);
constraint array_var_int_element(pv3, S, 3);
constraint array_var_int_element(pv4, S, 4);
"""
const InverseSolve = """
solve :: int_search([sv1, sv2, sv3, sv4], input_order, indomain_min, complete) satisfy;
"""

suite "Implied inverse circuits and deterministic direction":

    test "circuit on the channelized side is dropped; annotated side searchable":
        let tr = translate(parseFzn(InverseBase & InverseSolve))
        # Exactly one circuit survives (the forward side's)
        check tr.countType(CircuitType) == 1
        # Deterministic direction: the non-annotated P side became channels
        for name in ["pv1", "pv2", "pv3", "pv4"]:
            check tr.pos(name) in tr.sys.baseArray.channelPositions
        for name in ["sv1", "sv2", "sv3", "sv4"]:
            check tr.pos(name) notin tr.sys.baseArray.channelPositions

    test "round-trip: P is maintained as the exact inverse of S":
        var tr = translate(parseFzn(InverseBase & InverseSolve))
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        var s, p: seq[int]
        for name in ["sv1", "sv2", "sv3", "sv4"]: s.add(tr.val(name))
        for name in ["pv1", "pv2", "pv3", "pv4"]: p.add(tr.val(name))
        for k in 0..<4:
            check s[p[k] - 1] == k + 1
            check p[s[k] - 1] == k + 1

suite "Inverse-indexed element rewrite":

    ## VRP vehicle-coherence shape on top of the mutual-inverse pair:
    ## V[P[k]] = v_k and V[S[k]] = v_k for the "customers" k in {1, 2}.
    const VehicleSrc = InverseBase & """
var 0..1: v1;
var 0..1: v2;
var 0..1: v3;
var 0..1: v4;
array [1..4] of var int: V = [v1, v2, v3, v4];
constraint array_var_int_element(pv1, V, v1);
constraint array_var_int_element(pv2, V, v2);
constraint array_var_int_element(sv1, V, v1);
constraint array_var_int_element(sv2, V, v2);
""" & InverseSolve

    test "channel-index elements rewritten; subsumption and tautologies":
        let tr = translate(parseFzn(VehicleSrc))
        # The pred-indexed V elements are consumed (rewritten); the consistency
        # elements on the suppressed side rewrite to tautologies and vanish.
        # Survivors: 2 original succ-form coherence elements + 2 emitted
        # forward-side rewrites (for forward vars whose self-target has no
        # subsuming original).
        check tr.countType(ElementType) == 4
        check tr.countType(CircuitType) == 1
        # Original channel-index elements are marked consumed
        var consumedPredElems = 0
        for ci, con in tr.model.constraints:
            if con.name == "array_var_int_element" and
               con.args[0].kind == FznIdent and
               con.args[0].ident in ["pv1", "pv2"] and
               con.args[1].kind == FznIdent and con.args[1].ident == "V":
                check ci in tr.definingConstraints
                inc consumedPredElems
        check consumedPredElems == 2

    test "round-trip: coherence semantics preserved (all on one route)":
        # On a 4-cycle with coherence into/out of nodes 1 and 2, all vehicle
        # values are transitively equal; pinning v1 pins everything.
        var tr = translate(parseFzn(VehicleSrc & "constraint int_eq(v1, 1);\n"))
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        check tr.val("v1") == 1
        check tr.val("v2") == 1
        check tr.val("v3") == 1
        check tr.val("v4") == 1

# ---------------------------------------------------------------------------
# Successor form + inverse arrays together (stochastic-vrp shape)
# ---------------------------------------------------------------------------

suite "Successor-form circuit-time with inverse channel arrays":

    ## The full interaction: time chain on S (consumes circuit(S)), pred array
    ## P with literal entry (pred of the start depot is the end depot), mutual
    ## inverse elements. Circuit-time link vars must stay searchable, P becomes
    ## channels, and circuit(P) is dropped because CircuitTimeProp enforces S.
    const ComboSrc = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 1..4: q1;
var 1..4: q2;
var 1..4: q4;
var 0..50: t1;
var 0..50: t2;
var 0..50: t4;
var 0..20: d1;
var 0..20: d2;
var 0..20: d3;
var 0..50: a1;
var 0..50: a2;
var 0..50: a3;
var 0..50: m;
array [1..4] of var int: S = [s1, s2, s3, 3];
array [1..4] of var int: P = [q1, q2, 4, q4];
constraint crusher_circuit(S);
constraint crusher_circuit(P);
constraint array_var_int_element(s1, P, 1);
constraint array_var_int_element(s2, P, 2);
constraint array_var_int_element(s3, P, 3);
constraint array_int_element(s1, [0, 3, 9, 4], d1) :: defines_var(d1);
constraint array_var_int_element(s1, [t1, t2, 0, t4], a1) :: defines_var(a1);
constraint int_lin_le([1, 1, -1], [t1, d1, a1], -2);
constraint array_int_element(s2, [3, 0, 9, 6], d2) :: defines_var(d2);
constraint array_var_int_element(s2, [t1, t2, 0, t4], a2) :: defines_var(a2);
constraint int_lin_le([1, 1, -1], [t2, d2, a2], -3);
constraint array_int_element(s3, [2, 5, 0, 9], d3) :: defines_var(d3);
constraint array_var_int_element(s3, [t1, t2, 0, t4], a3) :: defines_var(a3);
constraint int_lin_le([1, -1], [d3, a3], 0);
constraint array_int_maximum(m, [t1, t2, 0, t4]) :: defines_var(m);
solve :: int_search([s1, s2, s3], input_order, indomain_min, complete) minimize m;
"""

    test "link vars stay searchable, pred channels, implied circuit dropped":
        let tr = translate(parseFzn(ComboSrc))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].objectiveWeight == 1
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0     # S's consumed, P's implied-dropped
        for name in ["s1", "s2", "s3"]:
            check tr.pos(name) notin tr.sys.baseArray.channelPositions
        for name in ["q1", "q2", "q4"]:
            check tr.pos(name) in tr.sys.baseArray.channelPositions

# ---------------------------------------------------------------------------
# Direct linear objective observer (sum of times -> weighted-sum metric)
# ---------------------------------------------------------------------------

proc succSumSrc(objDef: string): string =
    ## SuccBase without the array_int_maximum observer, plus an objective var
    ## and the given objective definition / solve item.
    for line in SuccBase.splitLines():
        if "array_int_maximum" notin line and not line.startsWith("var 0..50: m"):
            result.add(line & "\n")
    result.add("var 0..200: obj;\n")
    result.add(objDef)

suite "Circuit-time direct sum-of-times objective":

    test "objective = sum of times: accepted with per-node sum weights":
        # obj = t1 + t2 + t4 (node 3's time is the fixed literal 0)
        let tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -1, -1, -1], [obj, t1, t2, t4], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 1
        let cand = tr.circuitTimeCandidates[0]
        check cand.useSumMetric == true
        check cand.sumMetricWeights == @[1, 1, 0, 1]
        check cand.objectiveWeight == 1
        check cand.objectiveConstOffset == 0
        check cand.objectiveMetricLo == 0
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0

    test "weighted partial sum: only observed times carry weights":
        # obj = 2*t1 + t4; t2 is unobserved (projection still sound)
        let tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -2, -1], [obj, t1, t4], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 1
        let cand = tr.circuitTimeCandidates[0]
        check cand.useSumMetric == true
        check cand.sumMetricWeights == @[2, 0, 0, 1]
        check cand.objectiveWeight == 1

    test "constant offset extracted from the rhs":
        # obj - t1 - t2 - t4 = 5  =>  obj = sum + 5
        let tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -1, -1, -1], [obj, t1, t2, t4], 5) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].objectiveConstOffset == 5
        check tr.circuitTimeCandidates[0].useSumMetric == true

    test "named coefficient/variable arrays (FZN flattener output shape)":
        let tr = translate(parseFzn(succSumSrc(
            "array [1..4] of int: oc = [1, -1, -1, -1];\n" &
            "array [1..4] of var int: ov = [obj, t1, t2, t4];\n" &
            "constraint int_lin_eq(oc, ov, 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].useSumMetric == true
        check tr.circuitTimeCandidates[0].sumMetricWeights == @[1, 1, 0, 1]

    test "negative effective weight: candidate rejected":
        # obj = t1 + t2 - t4: minimizing presses t4 UP -> projection unsound
        let tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -1, -1, 1], [obj, t1, t2, t4], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitTimePropType) == 0
        check tr.countType(CircuitType) == 1

    test "maximize over a direct sum: candidate rejected":
        let tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -1, -1, -1], [obj, t1, t2, t4], 0) :: defines_var(obj);\n" &
            "solve maximize obj;\n")))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitType) == 1

    test "lin_eq over times not defining the objective: rejected":
        # Same shape but defines an unrelated var -> foreign observer
        let tr = translate(parseFzn(succSumSrc(
            "var 0..200: other;\n" &
            "constraint int_lin_eq([1, -1, -1, -1], [other, t1, t2, t4], 0) :: defines_var(other);\n" &
            "constraint int_lin_le([1], [obj], 200);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitType) == 1

    test "round-trip: earliest times hold under a sum objective":
        # (obj itself is expression-defined and has no search position)
        var tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -1, -1, -1], [obj, t1, t2, t4], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.circuitTimeCandidates.len == 1
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        let s = @[tr.val("s1"), tr.val("s2"), tr.val("s3"), 3]
        let t = @[tr.val("t1"), tr.val("t2"), 0, tr.val("t4")]
        let rows = @[@[0, 3, 9, 4], @[3, 0, 9, 6], @[2, 5, 0, 9]]
        let service = @[2, 3, 0]
        for n in 0..<3:
            check t[s[n] - 1] == t[n] + service[n] + rows[n][s[n] - 1]

# ---------------------------------------------------------------------------
# Equality accumulator chains (CVRP load / vehicle painting)
# ---------------------------------------------------------------------------

## Load chain: 2 customers with demands 2 and 3, start depot 3 (load literal
## 0), end depot 4 (free load = route load, capacity via domain 0..6). The
## start-depot arc uses the constant-result element form (L[s3] = 0); the
## customer arcs use defines_var elements + offset lin_eqs.
const AccumLoadSrc = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 0..6: l1;
var 0..6: l2;
var 0..6: l4;
var 0..6: r1;
var 0..6: r2;
array [1..4] of var int: L = [l1, l2, 0, l4];
constraint crusher_circuit([s1, s2, s3, 3]);
constraint array_var_int_element(s1, L, r1) :: defines_var(r1);
constraint int_lin_eq([1, -1], [l1, r1], -2);
constraint array_var_int_element(s2, L, r2) :: defines_var(r2);
constraint int_lin_eq([1, -1], [l2, r2], -3);
constraint array_var_int_element(s3, L, 0);
"""

## Vehicle painting: customer values free, depot values fixed by literals;
## only customer arcs are chained (zero offset, unified result = own var), so
## the anchors sit at segment ENDS (backward anchoring).
const AccumVehSrc = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 1..3: v1;
var 1..3: v2;
array [1..4] of var int: V = [v1, v2, 1, 1];
constraint crusher_circuit([s1, s2, s3, 3]);
constraint array_var_int_element(s1, V, v1);
constraint array_var_int_element(s2, V, v2);
"""

suite "Circuit accumulator chains (equality form)":

    test "load chain: forward-anchored accumulator detected and consumed":
        let tr = translate(parseFzn(AccumLoadSrc & "solve satisfy;\n"))
        check tr.circuitTimeCandidates.len == 1
        let cand = tr.circuitTimeCandidates[0]
        check cand.equalityChain == true
        check cand.forward == true
        check cand.linkVarNames == @["s1", "s2", "s3", ""]
        check cand.depotIdx == 2                 # node 3, the fixed literal 0
        check cand.depotDep == 0
        check cand.outConstrained == @[true, true, true, false]
        # Offset matrix: uniform rows dist[to][from] = demand_from
        for toN in 0..<4:
            check cand.distMatrix[toN][0] == 2
            check cand.distMatrix[toN][1] == 3
            check cand.distMatrix[toN][2] == 0   # depot arc: offset 0
            check cand.distMatrix[toN][3] == 0   # unconstrained
        # Capacity becomes the two-sided window (presolve tightens the
        # customer loads through the offset equations: l1 <= 6-2, l2 <= 6-3)
        check cand.earlyTimes == @[0, 0, 0, 0]
        check cand.lateTimes == @[4, 3, 0, 6]
        check cand.departureVars == @["l1", "l2", "", "l4"]
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0
        # Value vars and element results are channels; links stay searchable
        for name in ["l1", "l2", "l4", "r1", "r2"]:
            check tr.pos(name) in tr.sys.baseArray.channelPositions
        for name in ["s1", "s2", "s3"]:
            check tr.pos(name) notin tr.sys.baseArray.channelPositions

    test "load chain round-trip: exact prefix-sum loads along the tour":
        var tr = translate(parseFzn(AccumLoadSrc & "solve satisfy;\n"))
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        let s = @[tr.val("s1"), tr.val("s2"), tr.val("s3"), 3]
        let load = @[tr.val("l1"), tr.val("l2"), 0, tr.val("l4")]
        let demand = @[2, 3, 0]
        for n in 0..<3:
            check load[s[n] - 1] == load[n] + demand[n]
        check load[3] == 5                       # route load at the end depot

    test "vehicle painting: backward-anchored zero-offset chain":
        let tr = translate(parseFzn(AccumVehSrc & "solve satisfy;\n"))
        check tr.circuitTimeCandidates.len == 1
        let cand = tr.circuitTimeCandidates[0]
        check cand.equalityChain == true
        check cand.outConstrained == @[true, true, false, false]
        check cand.departureVars == @["v1", "v2", "", ""]
        for toN in 0..<4:
            for fromN in 0..<4:
                check cand.distMatrix[toN][fromN] == 0
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0
        check tr.countType(ElementType) == 0     # both elements consumed

    test "vehicle painting round-trip: values painted from the anchors":
        var tr = translate(parseFzn(AccumVehSrc & "solve satisfy;\n"))
        tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
        check tr.val("v1") == 1
        check tr.val("v2") == 1

    test "shared value variable: alias group penalizes split routes":
        # Two vehicles; customers 1 and 2 share ONE vehicle variable (the
        # flattener unifies veh[i] and veh[P+i] for same-vehicle pickup and
        # delivery). Start depots 3 (veh 1) and 4 (veh 2), end depots 5 and 6
        # wrap to the next start. Splitting the customers across vehicles
        # must cost: the walk paints them differently but writes one variable.
        let src = """
var 1..6: s1;
var 1..6: s2;
var 1..6: s3;
var 1..6: s4;
var 1..2: v;
array [1..6] of var int: V = [v, v, 1, 2, 1, 2];
constraint crusher_circuit([s1, s2, s3, s4, 4, 3]);
constraint array_var_int_element(s1, V, v);
constraint array_var_int_element(s2, V, v);
constraint array_var_int_element(s3, V, 1);
constraint array_var_int_element(s4, V, 2);
solve satisfy;
"""
        var tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].aliasGroups == @[@[0, 1]]
        var ctp: CircuitTimePropConstraint[int]
        for c in tr.sys.baseArray.constraints:
            if c.stateType == CircuitTimePropType: ctp = c.circuitTimePropState
        check ctp != nil
        var a = newSeq[int](tr.sys.baseArray.len)
        # 3 -> 1 -> 5 -> 4 -> 2 -> 6 -> 3: customers on different vehicles
        a[tr.pos("s3")] = 1; a[tr.pos("s1")] = 5; a[tr.pos("s4")] = 2; a[tr.pos("s2")] = 6
        ctp.initialize(a)
        check ctp.cost == 1
        # Customer 2 on vehicle 1 too (3 -> 1 -> 2 -> 5, 4 -> 6): consistent
        a[tr.pos("s1")] = 2; a[tr.pos("s2")] = 5; a[tr.pos("s4")] = 6
        ctp.initialize(a)
        check ctp.cost == 0
        for seed in 0..<10:
            randomize(seed)
            var tr2 = translate(parseFzn(src))
            tr2.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
            let s = @[tr2.val("s1"), tr2.val("s2"), tr2.val("s3"), tr2.val("s4"), 4, 3]
            let vv = @[tr2.val("v"), tr2.val("v"), 1, 2, 1, 2]
            for n in 0..<4:
                check vv[s[n] - 1] == vv[n]

    test "no anchored end (both guards fail): family rejected":
        # End depot value free AND segment starts free -> neither forward nor
        # backward anchoring is sound; elements must translate normally.
        let src = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 1..3: v1;
var 1..3: v2;
var 1..3: v4;
array [1..4] of var int: V = [v1, v2, 1, v4];
constraint crusher_circuit([s1, s2, s3, 3]);
constraint array_var_int_element(s1, V, v1);
constraint array_var_int_element(s2, V, v2);
solve satisfy;
"""
        let tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 0
        check tr.countType(CircuitTimePropType) == 0
        check tr.countType(CircuitType) == 1
        check tr.countType(ElementType) == 2

    test "time chain and load chain coexist on one circuit (CVRP shape)":
        let tr = translate(parseFzn(SuccBase & """
var 0..6: l1;
var 0..6: l2;
var 0..6: l4;
var 0..6: r1;
var 0..6: r2;
array [1..4] of var int: L = [l1, l2, 0, l4];
constraint array_var_int_element(s1, L, r1) :: defines_var(r1);
constraint int_lin_eq([1, -1], [l1, r1], -2);
constraint array_var_int_element(s2, L, r2) :: defines_var(r2);
constraint int_lin_eq([1, -1], [l2, r2], -3);
constraint array_var_int_element(s3, L, 0);
solve minimize m;
"""))
        check tr.circuitTimeCandidates.len == 2
        var nEquality, nTime: int
        for cand in tr.circuitTimeCandidates:
            if cand.equalityChain: inc nEquality
            else: inc nTime
        check nEquality == 1
        check nTime == 1
        check tr.countType(CircuitTimePropType) == 2
        check tr.countType(CircuitType) == 0

    test "mirror circuit: one instance per value array, rewrite subsumed":
        # Mutual-inverse pair S/P with vehicle painting expressed on BOTH
        # sides. The S-side accumulator wins; the P-side family is skipped
        # (one instance per array), and the pred-indexed elements are
        # subsumed by the circuit-time-consumed forward elements instead of
        # being re-emitted.
        let src = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 1..4: q1;
var 1..4: q2;
var 1..4: q4;
var 1..3: v1;
var 1..3: v2;
array [1..4] of var int: S = [s1, s2, s3, 3];
array [1..4] of var int: P = [q1, q2, 4, q4];
array [1..4] of var int: V = [v1, v2, 1, 1];
constraint crusher_circuit(S);
constraint crusher_circuit(P);
constraint array_var_int_element(s1, P, 1);
constraint array_var_int_element(s2, P, 2);
constraint array_var_int_element(s3, P, 3);
constraint array_var_int_element(s1, V, v1);
constraint array_var_int_element(s2, V, v2);
constraint array_var_int_element(q1, V, v1);
constraint array_var_int_element(q2, V, v2);
solve :: int_search([s1, s2, s3], input_order, indomain_min, complete) satisfy;
"""
        let tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 1
        check tr.circuitTimeCandidates[0].equalityChain == true
        check tr.countType(CircuitTimePropType) == 1
        check tr.countType(CircuitType) == 0     # S consumed, P implied-dropped
        # The q1/q2-indexed V elements are subsumed by the circuit-time-
        # consumed forward elements. One rewrite IS emitted: the s3 slot
        # (pred-of-customer = depot 3 => vehicle = V[3]) has no forward twin.
        check tr.countType(ElementType) == 1
        var consumedPredElems = 0
        for ci, con in tr.model.constraints:
            if con.name == "array_var_int_element" and
               con.args[0].kind == FznIdent and
               con.args[0].ident in ["q1", "q2"] and
               con.args[1].kind == FznIdent and con.args[1].ident == "V":
                check ci in tr.definingConstraints
                inc consumedPredElems
        check consumedPredElems == 2
        for name in ["q1", "q2", "q4"]:
            check tr.pos(name) in tr.sys.baseArray.channelPositions

# ---------------------------------------------------------------------------
# Objective bound delegation
# ---------------------------------------------------------------------------

suite "Objective bound delegation (circuitTimeObjectiveExact)":

    test "single sum-linked successor instance: delegation enabled":
        let tr = translate(parseFzn(succSumSrc(
            "constraint int_lin_eq([1, -1, -1, -1], [obj, t1, t2, t4], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")))
        check tr.sys.circuitTimeObjectiveExact == true

    test "single max-linked successor instance: delegation enabled":
        let tr = translate(parseFzn(SuccBase & "solve minimize m;\n"))
        check tr.sys.circuitTimeObjectiveExact == true

    test "two linked instances: no delegation (joint bound needed)":
        let src = twoScenarioSrc(
            "constraint int_lin_eq([1, -3, -2], [obj, ma, mb], 0) :: defines_var(obj);\n" &
            "solve minimize obj;\n")
        let tr = translate(parseFzn(src))
        check tr.circuitTimeCandidates.len == 2
        check tr.sys.circuitTimeObjectiveExact == false

    test "unlinked accumulator instance: no delegation":
        let tr = translate(parseFzn(AccumLoadSrc & "solve satisfy;\n"))
        check tr.sys.circuitTimeObjectiveExact == false

# ---------------------------------------------------------------------------
# Position-encoded tours with time-dependent travel (tdtsp)
# ---------------------------------------------------------------------------

suite "Position-chain circuits and time-dependent travel (tdtsp)":
    ## tests/data/tdtsp/tiny.fzn: the challenge model on 3 visits + end node,
    ## buckets of 10. No circuit: the tour is next/prev (inverse) plus
    ## position[next[i]] = position[i] + 1; travel is T[i, next[i], t div 10],
    ## stated over successors and again over predecessors, plus two redundant
    ## sum bounds. The optimum, 24, needs waiting at visit 2 (Gecode: tvar =
    ## [0, 10, 15, 24]).
    let src = readFile("tests/data/tdtsp/tiny.fzn")

    test "implied circuit; time chain with buckets, mirrors and sums consumed":
        let tr = translate(parseFzn(src))
        var nTd, nAcc: int
        for cand in tr.circuitTimeCandidates:
            if cand.equalityChain: inc nAcc
            elif cand.tdBucket == 10: inc nTd
        check nTd == 1
        check nAcc == 1                      # the position chain
        check tr.countType(CircuitTimePropType) == 2
        check tr.countType(CircuitType) == 1  # the inferred circuit stays: tour moves
        # Every arc (both statements) and both redundant sums are consumed
        var nLe = 0
        for ci, con in tr.model.constraints:
            if con.name == "int_lin_le":
                inc nLe
                check ci in tr.definingConstraints
        check nLe > 0

    test "round-trip: optimum through waiting":
        var tr = translate(parseFzn(src))
        let objExpr = tr.getExpr(tr.objectivePos)
        minimize(tr.sys, objExpr, parallel = false, tabuThreshold = 1000,
                 lowerBound = tr.objectiveLoBound, upperBound = tr.objectiveHiBound)
        check tr.sys.hasFeasibleSolution
        let tv = @[0, tr.val("X_INTRODUCED_13_"), tr.val("X_INTRODUCED_14_"), tr.val("objective")]
        check tv[3] == 24
        check tv[1] == 10

    test "implied tour relations consumed, premises kept":
        # next = [X17, X5, X6, 1], prev = R = [4, X9, X10, X18],
        # atposition = A = [1, X17, X18, 4] with X18 = next[X17].
        let tr = translate(parseFzn(src))
        proc idx(tr: FznTranslator, text: string): int =
            ## constraint index whose args print as `text` (a, b, c)
            result = -1
            for ci, con in tr.model.constraints:
                var parts: seq[string]
                for a in con.args:
                    parts.add(if a.kind == FznIdent: a.ident.replace("X_INTRODUCED_", "X").replace("_", "")
                              elif a.kind == FznIntLit: $a.intVal else: "?")
                if con.name & "(" & parts.join(",") & ")" == text:
                    return ci
        # position[i] = position[prev[i]] + 1, its intermediates, and the walk
        # relations position[A[k]] = k, A[position[i]] = i, prev[A[k]] = A[k-1]
        for t in ["array_var_int_element(X9,position,X37)", "array_var_int_element(X10,position,X39)",
                  "array_var_int_element(X1,atposition,2)", "array_var_int_element(X2,atposition,3)",
                  "array_var_int_element(X18,prev,X17)"]:
            let ci = tr.idx(t)
            check ci >= 0
            check ci in tr.definingConstraints
        var nLinEqLeft = 0
        for ci, con in tr.model.constraints:
            if con.name == "int_lin_eq" and ci notin tr.definingConstraints: inc nLinEqLeft
        check nLinEqLeft == 0
        # Nothing over the walk or the predecessor positions is left to evaluate
        check tr.countType(ElementType) <= 1        # at most a duplicate premise
        check tr.countType(RelationalType) == 0     # no bucket bounds either

    test "no walk relations without the walk chain":
        # Without X18 = next[X17], atposition[3] is not provably the node at
        # position 3: the walk relations stay (the prev-side chain still goes).
        let broken = src.replace("constraint array_var_int_element(X_INTRODUCED_17_,next,X_INTRODUCED_18_):: defines_var(X_INTRODUCED_18_);\n", "")
        check broken.len < src.len
        let tr = translate(parseFzn(broken))
        var walkLeft = 0
        for ci, con in tr.model.constraints:
            if con.name == "array_var_int_element" and con.args[1].kind == FznIdent and
               con.args[1].ident == "atposition" and ci notin tr.definingConstraints:
                inc walkLeft
        check walkLeft == 2

    test "travel intermediates keep their bindings when something reads them":
        let tr = translate(parseFzn(src))
        # mirror t[p_2] and its bucket: consumed, read by nobody
        check "X_INTRODUCED_45_" in tr.deadChannelVars
        check "X_INTRODUCED_46_" in tr.deadChannelVars
        # An output bucket keeps its binding and (through its consumed
        # definition) the time it divides. (A live constraint reading it fails
        # projection-soundness verification before this point.)
        let withOut = src.replace("var 0..2: X_INTRODUCED_46_ ::var_is_introduced",
                                  "var 0..2: X_INTRODUCED_46_ :: output_var ::var_is_introduced")
        check withOut != src
        let tr2 = translate(parseFzn(withOut))
        check tr2.circuitTimeCandidates.len == 2
        check "X_INTRODUCED_46_" notin tr2.deadChannelVars
        check "X_INTRODUCED_45_" notin tr2.deadChannelVars
        check "X_INTRODUCED_57_" in tr2.deadChannelVars

    test "no implied circuit unless the closing node's position is N":
        # With P[4] free, S = [2, 4, 2, 1], P = [1, 2, 1, 3] satisfies every
        # chain equation (cycle 1 -> 2 -> 4 -> 1, node 3 hanging off 2), so
        # circuit(S) is not implied.
        let mk = proc(p4: string): string = """
var 1..4: s1;
var 1..4: s2;
var 1..4: s3;
var 1..4: p2;
var 1..4: p3;
""" & p4 & """
var 1..4: r2;
var 1..4: r3;
array [1..4] of var int: S :: output_array([1..4]) = [s1, s2, s3, 1];
array [1..4] of var int: P :: output_array([1..4]) = [1, p2, p3, P4];
constraint array_var_int_element(s1, P, 2);
constraint array_var_int_element(s2, P, r2) :: defines_var(r2);
constraint int_lin_eq([1, -1], [r2, p2], 1);
constraint array_var_int_element(s3, P, r3) :: defines_var(r3);
constraint int_lin_eq([1, -1], [r3, p3], 1);
solve satisfy;
"""
        proc nCircuits(src: string): int =
            let tr = translate(parseFzn(src))
            for con in tr.model.constraints:
                if con.name == "crusher_circuit": inc result
        check nCircuits(mk("var 4..4: P4;\n")) == 1
        check nCircuits(mk("var 1..4: P4;\n")) == 0


## vrplc_service.mzn flattened with crusher's mznlib on a tiny instance: one
## request (pickup 1, delivery 2), two vehicles (start depots 3, 4; end depots
## 5, 6; succ[5] = 4 and succ[6] = 3 close the giant tour). The pickup and
## delivery share one vehicle variable (X39); X73 / X76 are the start depots'
## demand lookups qq[succ[3]] / qq[succ[4]], whose row (2, -2, 0, ...) leaves
## their declared 0..5: they forbid driving from a start depot to the delivery.
const TinyVrplc = """
predicate crusher_circuit(array [int] of var int: x);
array [1..2] of int: X_INTRODUCED_42_ = [1,-1];
array [1..6] of int: X_INTRODUCED_48_ = [0,4,3,3,3,3];
array [1..3] of int: X_INTRODUCED_52_ = [1,1,-1];
array [1..6] of int: X_INTRODUCED_53_ = [4,0,5,5,5,5];
array [1..6] of int: X_INTRODUCED_57_ = [3,5,0,0,0,0];
array [1..6] of int: X_INTRODUCED_65_ = [2,-2,0,0,0,0];
array [1..5] of int: X_INTRODUCED_83_ = [1,-1,-1,-1,-1];
var 0..19: objective:: output_var:: is_defined_var;
var 1..6: X_INTRODUCED_6_;
var 1..6: X_INTRODUCED_7_;
var 1..6: X_INTRODUCED_8_;
var 1..6: X_INTRODUCED_9_;
var 0..5: X_INTRODUCED_12_;
var 0..5: X_INTRODUCED_13_;
var 0..40: X_INTRODUCED_18_;
var 0..40: X_INTRODUCED_19_;
var 2..20: X_INTRODUCED_24_;
var 6..30: X_INTRODUCED_25_;
var 0..40: X_INTRODUCED_30_;
var 0..40: X_INTRODUCED_31_;
var 0..40: X_INTRODUCED_32_;
var 0..40: X_INTRODUCED_33_;
var 0..40: X_INTRODUCED_34_;
var 0..40: X_INTRODUCED_35_;
var 1..2: X_INTRODUCED_39_ ::var_is_introduced ;
var 1..1: X_INTRODUCED_40_ ::var_is_introduced ;
var 2..2: X_INTRODUCED_41_ ::var_is_introduced ;
var 0..4: X_INTRODUCED_49_ ::var_is_introduced :: is_defined_var;
var 0..40: X_INTRODUCED_51_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_54_ ::var_is_introduced :: is_defined_var;
var 0..40: X_INTRODUCED_56_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_58_ ::var_is_introduced :: is_defined_var;
var 0..40: X_INTRODUCED_60_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_61_ ::var_is_introduced :: is_defined_var;
var 0..40: X_INTRODUCED_63_ ::var_is_introduced :: is_defined_var;
var -5..5: X_INTRODUCED_64_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_67_ ::var_is_introduced :: is_defined_var;
var -5..5: X_INTRODUCED_68_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_70_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_73_ ::var_is_introduced :: is_defined_var;
var 0..5: X_INTRODUCED_76_ ::var_is_introduced :: is_defined_var;
array [1..6] of var int: veh:: output_array([1..6]) = [X_INTRODUCED_39_,X_INTRODUCED_39_,1,2,1,2];
array [1..6] of var int: succ:: output_array([1..6]) = [X_INTRODUCED_6_,X_INTRODUCED_7_,X_INTRODUCED_8_,X_INTRODUCED_9_,4,3];
array [1..6] of var int: load:: output_array([1..6]) = [X_INTRODUCED_12_,X_INTRODUCED_13_,0,0,0,0];
array [1..6] of var int: arr:: output_array([1..6]) = [X_INTRODUCED_18_,X_INTRODUCED_19_,X_INTRODUCED_32_,X_INTRODUCED_33_,X_INTRODUCED_34_,X_INTRODUCED_35_];
array [1..6] of var int: ser:: output_array([1..6]) = [X_INTRODUCED_24_,X_INTRODUCED_25_,X_INTRODUCED_32_,X_INTRODUCED_33_,X_INTRODUCED_34_,X_INTRODUCED_35_];
array [1..6] of var int: dep:: output_array([1..6]) = [X_INTRODUCED_30_,X_INTRODUCED_31_,X_INTRODUCED_32_,X_INTRODUCED_33_,X_INTRODUCED_34_,X_INTRODUCED_35_];
constraint crusher_circuit(succ);
constraint array_var_int_element(X_INTRODUCED_6_,veh,X_INTRODUCED_39_);
constraint array_var_int_element(X_INTRODUCED_7_,veh,X_INTRODUCED_39_);
constraint array_var_int_element(X_INTRODUCED_8_,veh,1);
constraint array_var_int_element(X_INTRODUCED_9_,veh,2);
constraint int_lin_le(X_INTRODUCED_42_,[X_INTRODUCED_18_,X_INTRODUCED_24_],0);
constraint int_lin_le(X_INTRODUCED_42_,[X_INTRODUCED_19_,X_INTRODUCED_25_],0);
constraint int_lin_le(X_INTRODUCED_42_,[X_INTRODUCED_24_,X_INTRODUCED_30_],-2);
constraint int_lin_le(X_INTRODUCED_42_,[X_INTRODUCED_25_,X_INTRODUCED_31_],-3);
constraint array_int_element(X_INTRODUCED_6_,X_INTRODUCED_48_,X_INTRODUCED_49_):: defines_var(X_INTRODUCED_49_);
constraint array_var_int_element(X_INTRODUCED_6_,arr,X_INTRODUCED_51_):: defines_var(X_INTRODUCED_51_);
constraint int_lin_eq(X_INTRODUCED_52_,[X_INTRODUCED_30_,X_INTRODUCED_49_,X_INTRODUCED_51_],0);
constraint array_int_element(X_INTRODUCED_7_,X_INTRODUCED_53_,X_INTRODUCED_54_):: defines_var(X_INTRODUCED_54_);
constraint array_var_int_element(X_INTRODUCED_7_,arr,X_INTRODUCED_56_):: defines_var(X_INTRODUCED_56_);
constraint int_lin_eq(X_INTRODUCED_52_,[X_INTRODUCED_31_,X_INTRODUCED_54_,X_INTRODUCED_56_],0);
constraint array_int_element(X_INTRODUCED_8_,X_INTRODUCED_57_,X_INTRODUCED_58_):: defines_var(X_INTRODUCED_58_);
constraint array_var_int_element(X_INTRODUCED_8_,arr,X_INTRODUCED_60_):: defines_var(X_INTRODUCED_60_);
constraint int_lin_eq(X_INTRODUCED_52_,[X_INTRODUCED_32_,X_INTRODUCED_58_,X_INTRODUCED_60_],0);
constraint array_int_element(X_INTRODUCED_9_,X_INTRODUCED_57_,X_INTRODUCED_61_):: defines_var(X_INTRODUCED_61_);
constraint array_var_int_element(X_INTRODUCED_9_,arr,X_INTRODUCED_63_):: defines_var(X_INTRODUCED_63_);
constraint int_lin_eq(X_INTRODUCED_52_,[X_INTRODUCED_33_,X_INTRODUCED_61_,X_INTRODUCED_63_],0);
constraint array_int_element(X_INTRODUCED_6_,X_INTRODUCED_65_,X_INTRODUCED_64_):: defines_var(X_INTRODUCED_64_);
constraint array_var_int_element(X_INTRODUCED_6_,load,X_INTRODUCED_67_):: defines_var(X_INTRODUCED_67_);
constraint int_lin_eq(X_INTRODUCED_52_,[X_INTRODUCED_12_,X_INTRODUCED_64_,X_INTRODUCED_67_],0);
constraint array_int_element(X_INTRODUCED_7_,X_INTRODUCED_65_,X_INTRODUCED_68_):: defines_var(X_INTRODUCED_68_);
constraint array_var_int_element(X_INTRODUCED_7_,load,X_INTRODUCED_70_):: defines_var(X_INTRODUCED_70_);
constraint int_lin_eq(X_INTRODUCED_52_,[X_INTRODUCED_13_,X_INTRODUCED_68_,X_INTRODUCED_70_],0);
constraint array_int_element(X_INTRODUCED_8_,X_INTRODUCED_65_,X_INTRODUCED_73_):: defines_var(X_INTRODUCED_73_);
constraint array_var_int_element(X_INTRODUCED_8_,load,X_INTRODUCED_73_);
constraint array_int_element(X_INTRODUCED_9_,X_INTRODUCED_65_,X_INTRODUCED_76_):: defines_var(X_INTRODUCED_76_);
constraint array_var_int_element(X_INTRODUCED_9_,load,X_INTRODUCED_76_);
constraint int_lin_le(X_INTRODUCED_42_,[X_INTRODUCED_30_,X_INTRODUCED_19_],-4);
constraint int_lin_eq(X_INTRODUCED_83_,[objective,X_INTRODUCED_49_,X_INTRODUCED_54_,X_INTRODUCED_58_,X_INTRODUCED_61_],0):: defines_var(objective);
solve :: seq_search([int_search(succ,first_fail,indomain_min,complete),int_search(ser,smallest,indomain_min,complete),int_search(arr,smallest,indomain_min,complete),int_search(dep,smallest,indomain_min,complete),int_search(load,smallest,indomain_min,complete),int_search(veh,first_fail,indomain_min,complete)]) minimize objective;
"""

suite "Split time chains (VRP with location congestion)":

    test "chain intermediates need no binding; objective lookups and narrowing rows keep theirs":
        let tr = translate(parseFzn(TinyVrplc))
        check tr.circuitTimeCandidates.len == 3
        check tr.countType(CircuitTimePropType) == 3
        # arr[succ[i]] (time chain), load[succ[i]] and the customers' demand lookups
        for name in ["X_INTRODUCED_51_", "X_INTRODUCED_56_", "X_INTRODUCED_60_",
                     "X_INTRODUCED_63_", "X_INTRODUCED_67_", "X_INTRODUCED_70_",
                     "X_INTRODUCED_64_", "X_INTRODUCED_68_"]:
            check name in tr.deadChannelVars
        # travel lookups read by the objective
        for name in ["X_INTRODUCED_49_", "X_INTRODUCED_54_", "X_INTRODUCED_58_", "X_INTRODUCED_61_"]:
            check name notin tr.deadChannelVars
        # declared domain narrower than the row: the binding still restricts succ
        check "X_INTRODUCED_73_" notin tr.deadChannelVars
        check "X_INTRODUCED_76_" notin tr.deadChannelVars

    test "an output intermediate keeps its binding":
        let src = TinyVrplc.replace("var 0..5: X_INTRODUCED_67_ ::var_is_introduced",
                                    "var 0..5: X_INTRODUCED_67_ :: output_var ::var_is_introduced")
        check src != TinyVrplc
        let tr = translate(parseFzn(src))
        check "X_INTRODUCED_67_" notin tr.deadChannelVars
        check "X_INTRODUCED_70_" in tr.deadChannelVars

    test "initial tours keep each linked pair on one empty vehicle":
        var tr = translate(parseFzn(TinyVrplc))
        tr.sys.baseArray.reducedDomain = reduceDomain(tr.sys.baseArray)
        tr.sys.baseArray.sharedDomainPtr = addr tr.sys.baseArray.reducedDomain
        for seed in 0..<10:
            randomize(seed)
            let st = newTabuState[int](tr.sys.baseArray)
            template succOf(name: string): int = st.assignment[tr.pos(name)]
            # pickup (earlier window) directly before its delivery
            check succOf("X_INTRODUCED_6_") == 2
            # start depot -> pickup, delivery -> that vehicle's end depot
            if succOf("X_INTRODUCED_8_") == 1:
                check succOf("X_INTRODUCED_7_") == 5
            else:
                check succOf("X_INTRODUCED_9_") == 1
                check succOf("X_INTRODUCED_7_") == 6

    test "round-trip: solutions satisfy the original model":
        let time = @[@[0, 4, 3, 3, 3, 3], @[4, 0, 5, 5, 5, 5], @[3, 5, 0, 0, 0, 0],
                     @[3, 5, 0, 0, 0, 0], @[3, 5, 0, 0, 0, 0], @[3, 5, 0, 0, 0, 0]]
        let qq = @[2, -2, 0, 0, 0, 0]
        for seed in 0..<5:
            randomize(seed)
            var tr = translate(parseFzn(TinyVrplc))
            tr.sys.resolve(parallel = false, tabuThreshold = 10000, verbose = false)
            check tr.sys.hasFeasibleSolution
            let succ = @[tr.val("X_INTRODUCED_6_"), tr.val("X_INTRODUCED_7_"),
                         tr.val("X_INTRODUCED_8_"), tr.val("X_INTRODUCED_9_"), 4, 3]
            let veh = @[tr.val("X_INTRODUCED_39_"), tr.val("X_INTRODUCED_39_"), 1, 2, 1, 2]
            let load = @[tr.val("X_INTRODUCED_12_"), tr.val("X_INTRODUCED_13_"), 0, 0, 0, 0]
            let starts = @[tr.val("X_INTRODUCED_32_"), tr.val("X_INTRODUCED_33_"),
                           tr.val("X_INTRODUCED_34_"), tr.val("X_INTRODUCED_35_")]
            let arr = @[tr.val("X_INTRODUCED_18_"), tr.val("X_INTRODUCED_19_")] & starts
            let ser = @[tr.val("X_INTRODUCED_24_"), tr.val("X_INTRODUCED_25_")] & starts
            let dep = @[tr.val("X_INTRODUCED_30_"), tr.val("X_INTRODUCED_31_")] & starts
            var seen: set[0..5]
            var c = 0
            for _ in 0..<6:
                seen.incl(c)
                c = succ[c] - 1
            check card(seen) == 6
            for i in 0..<4:                    # requests and start depots
                let j = succ[i] - 1
                check veh[j] == veh[i]
                check dep[i] + time[i][j] == arr[j]
                check load[i] + qq[j] == load[j]
                check load[j] in 0..5
            check arr[0] <= ser[0] and ser[0] + 2 <= dep[0] and ser[0] in 2..20
            check arr[1] <= ser[1] and ser[1] + 3 <= dep[1] and ser[1] in 6..30
            check dep[0] + 4 <= arr[1]
            for t in arr & ser & dep: check t in 0..40

suite "Ruin-and-recreate on a pickup-and-delivery giant tour":

    ## vrplc_service.mzn on two requests (pickups 1, 2; deliveries 3, 4), two
    ## vehicles, one service slot per location; optimum 16.
    test "rounds keep the tour valid, never worsen the key, and commit exactly":
        let src = readFile("tests/data/vrplc/two_requests.fzn")
        for seed in 0..<8:
            randomize(seed)
            var tr = translate(parseFzn(src))
            tr.sys.baseArray.reducedDomain = reduceDomain(tr.sys.baseArray)
            tr.sys.baseArray.sharedDomainPtr = addr tr.sys.baseArray.reducedDomain
            let st = newTabuState[int](tr.sys.baseArray)
            st.buildRuinRecreate()
            check st.rrUnits.len == 2
            for u in st.rrUnits: check u.len == 2
            var nMovable = 0
            for m in st.rrMovable:
                if m: inc nMovable
            check nMovable == 4
            let cc = st.circuitConstraints[st.rrCirc]
            if cc.cost != 0: continue
            var improved = 0
            for round in 0..<200:
                let before = st.rrKey()
                let r = st.rrRound()
                let after = st.rrKey()
                check cc.cost == 0
                check after <= before
                if r > 0:
                    inc improved
                    check after < before
                if r < 0: check after == before
            # the incremental state matches a fresh evaluation of its assignment
            var fresh = TabuState[int]()
            fresh.init(tr.sys.baseArray, initialAssignment = st.assignment)
            check fresh.cost == st.cost
            check st.rrRounds > 0
