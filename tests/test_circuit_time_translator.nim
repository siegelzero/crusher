## Unit tests for the circuit-time translator passes:
##   - detectCircuitTimePropagation: successor-form (inequality) and legacy
##     predecessor-form (equality) matching, multi-instance, service-time
##     folding, fixed links, unconstrained arcs, depot anchoring
##   - verifyCircuitTimeCandidates: projection-soundness rejection cases and
##     objective linkage extraction (direct max, weighted sum of maxima)
##   - dropImpliedInverseCircuits: circuit over the channel side of an inverse
##     pair is consumed when the forward side is circuit-enforced
##   - deterministic mutual-inverse suppression (annotated side stays searchable)
##   - rewriteInverseChannelIndexedElements: channel-index elements rewritten
##     to forward-side elements, with subsumption and tautology elimination

import unittest
import std/[strutils, tables, sets, packedsets]
import crusher
import flatzinc/[parser, translator]
import constraints/types

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
        # Time windows: fixed node pinned, others from domains
        check cand.earlyTimes == @[0, 0, 0, 0]
        check cand.lateTimes == @[50, 50, 0, 50]
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
        var tr = translate(parseFzn(SuccBase & "solve satisfy;\n"))
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
