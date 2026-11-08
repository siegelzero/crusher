
import resolution
from std/times import epochTime
import std/[algorithm, packedsets]
import std/tables
from std/os import getEnv
from std/strutils import parseInt
import ../constraints/[types, circuitTimeProp, stateful]
import ../expressions/expressions

when compileOption("threads"):
    import parallelResolution

proc copyPackedSet(src: PackedSet[int]): PackedSet[int] =
    ## Force a deep copy of a PackedSet to avoid shared Trunk refs under ARC.
    ## Nim 2.2.6's PackedSet.=copy is buggy: it doesn't clear dest.head before
    ## rebuilding the linked list, causing old and new trunks to chain together.
    result = initPackedSet[int]()
    for item in src.items:
        result.incl(item)

const BoundFloor = low(int) div 2
const BoundCeil = high(int) div 2

proc safeLowerBound(v: int): int {.inline.} =
    ## Compute a heuristic lower bound well below v, without overflow.
    if v <= BoundFloor: v
    else: min(0, v - abs(v) - 1)

proc safeUpperBound(v: int): int {.inline.} =
    ## Compute a heuristic upper bound well above v, without overflow.
    if v >= BoundCeil: v
    else: max(0, v + abs(v) + 1)
import ../expressions/expressions
import ../expressions/stateful
import ../expressions/sumExpression
import ../expressions/weightedSameValue
import ../constraintSystem
import ../constrainedArray

type
    OptimizationDirection* = enum
        Minimize, Maximize

proc applyCircuitTimeObjectiveBounds[T](system: ConstraintSystem[T],
                                        target: T, minimize: bool) =
    ## Distribute a global objective upper bound across CircuitTimeProp
    ## instances. The translator links instances to the objective as
    ##   objective = sum_i w_i * metric_i + constOffset   (all w_i > 0)
    ## so any solution with objective <= target satisfies, for each instance i:
    ##   metric_i <= (target - constOffset - sum_{j != i} w_j * metricLo_j) / w_i
    ## Instances with objectiveWeight == 0 are not linked to the objective and
    ## get no bound. The single-instance TSPTW case (weight 1, offset 0,
    ## metricLo 0) reduces to the plain bound metric <= target.
    var linked: seq[CircuitTimePropConstraint[T]]
    for c in system.baseArray.constraints:
        if c.stateType == CircuitTimePropType:
            if minimize and c.circuitTimePropState.objectiveWeight > 0:
                linked.add(c.circuitTimePropState)
            else:
                c.circuitTimePropState.clearObjectiveBound()
    if linked.len == 0: return
    # All linked instances must agree on the objective's constant offset (they
    # were extracted from the same linear definition). If they don't (e.g. a
    # legacy pred-form instance mixed with weighted successor-form instances),
    # fall back to the plain bound metric <= target, which is looser and
    # therefore sound for weights >= 1 and non-negative metric lower bounds.
    var offsetsAgree = true
    for c in linked:
        if c.objectiveConstOffset != linked[0].objectiveConstOffset:
            offsetsAgree = false
            break
    if not offsetsAgree:
        for c in linked:
            c.setObjectiveBound(target)
        return
    var weightedLoSum: T = linked[0].objectiveConstOffset
    for c in linked:
        weightedLoSum += T(c.objectiveWeight) * c.objectiveMetricLo
    for c in linked:
        let slack = target - (weightedLoSum - T(c.objectiveWeight) * c.objectiveMetricLo)
        var bound = slack div T(c.objectiveWeight)
        if slack < 0 and (slack mod T(c.objectiveWeight)) != 0:
            dec bound   # floor division for a negative numerator
        c.setObjectiveBound(bound)

proc applyObjectiveStaging[T](system: ConstraintSystem[T], targetBound: int, verbose: bool) =
    ## When the objective upper bound `targetBound` implies the dominant gating
    ## variable `v <= k`, apply the precomputed staged-presolve fixings (singleton
    ## domain + fixedPositions) so the gated blocks collapse before local search runs.
    ## Sound: each fixing was derived by presolve under `v <= k`, and is applied only
    ## when `objective <= targetBound` requires `v <= k`. Minimize / weight>0 only.
    let st = system.objectiveStaging
    if not st.active or st.weight <= 0: return
    # objective >= weight*v + minRest and objective <= targetBound
    #   => v <= floor((targetBound - minRest) / weight)
    let num = targetBound - st.minRest
    var kB = num div st.weight
    if num < 0 and (num mod st.weight) != 0:
        dec kB   # floor division for a negative numerator
    if kB >= st.vHi: return    # bound does not constrain v
    if kB < st.vLo: return     # implies v below its domain: subproblem infeasible — let search report it
    if kB notin st.fixingsByBound: return
    let fixes = st.fixingsByBound[kB]
    if fixes.len == 0: return
    for (pos, val) in fixes:
        system.baseArray.reducedDomain[pos] = @[val]
        system.baseArray.fixedPositions.incl(pos)
    system.baseArray.tightenReducedDomain()
    if verbose:
        echo "[Opt] Staging: objective<=", targetBound, " implies v<=", kB,
             " (fixed ", fixes.len, " gated positions)"
        flushFile(stdout)



template optimizeImpl(ObjectiveType: typedesc, direction: OptimizationDirection, procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: ObjectiveType[T],
                      parallel=true,
                      tabuThreshold=1000,
                      scatterThreshold=1,
                      populationSize=0,  # 0 = auto: 2 * worker threads
                      numWorkers=0,
                      scatterStrategy: ScatterStrategy = PathRelinking,
                      verbose=false,
                      multiplier=2,  # deprecated, ignored
                      lowerBound=low(int),
                      upperBound=high(int),
                      deadline: float = 0.0,
                      onSolution: proc(assignment: seq[T]) {.closure.} = nil,
                      ) =
        # onSolution, if supplied, is invoked on the main thread immediately after
        # each new incumbent is stored (initial + every improvement). It is used to
        # stream intermediate FlatZinc solutions for the MiniZinc Challenge `-i` mode.
        # Compute effective population size: 0 means auto-detect (2 * worker threads)
        let effectivePopSize = when compileOption("threads"):
            if populationSize > 0: populationSize
            else:
                let workers = if numWorkers > 0: numWorkers else: getOptimalWorkerCount()
                workers * 2
        else:
            if populationSize > 0: populationSize else: 8

        # Find initial feasible solution: single unified resolve with tabu + scatter fallback.
        # Tabu probe runs first; if it fails, scatter search continues from the tabu pool
        # without re-initialization.
        let initSolveStart = epochTime()
        system.resolve(parallel=parallel, tabuThreshold=min(tabuThreshold, 1000),
                      scatterThreshold=max(scatterThreshold, 3),
                      populationSize=effectivePopSize, numWorkers=numWorkers,
                      scatterStrategy=scatterStrategy, verbose=verbose,
                      deadline=deadline)
        let initSolveElapsed = max(0.001, epochTime() - initSolveStart)
        let initIters = system.lastIterations
        objective.initialize(system.assignment)
        var currentCost = objective.value
        var hasBoundConstraint = false

        # The initial resolve ignores the objective variable's declared domain
        # bounds — they are deferred to the optimizer (see translator.nim). So
        # the assignment found here can satisfy every hard constraint yet still
        # have an objective value outside [lowerBound..upperBound]. Such an
        # assignment is NOT a valid solution of the original model, so we must
        # not record it as an incumbent or stream it via onSolution; doing so
        # would emit an out-of-domain "solution" (e.g. objective=51 for a
        # `var 1..20` objective) that the MiniZinc checker rejects as incorrect.
        var boundsViolated = false
        if upperBound != high(int) and currentCost > upperBound:
            boundsViolated = true
        if lowerBound != low(int) and currentCost < lowerBound:
            boundsViolated = true

        if not boundsViolated:
            system.hasFeasibleSolution = true
            system.bestAssignmentValid = false
            system.bestFeasibleAssignment = system.assignment
            system.bestAssignmentValid = true
            if onSolution != nil: onSolution(system.bestFeasibleAssignment)
        else:
            system.hasFeasibleSolution = false

        # Detect "low iteration rate" workloads. When the per-move cost is so
        # high that tabu only manages a few iterations per second (typically
        # huge global constraints with O(n²)+ per-move work), a binary-search
        # bisection wastes most of the budget chasing a target so far above
        # the true optimum that no resolve attempt can reach it. For such
        # workloads we skip the bisection phase entirely and go straight to
        # the retry-improvement loop, which only ever ratchets the bound by
        # one step at a time. The threshold is empirical: anything below
        # ~100 iters/sec means even a single bisection probe consumes a
        # significant chunk of the deadline.
        const LowIterRateThreshold = 100.0  # iters/sec
        let initIterRate =
            if initIters > 0: initIters.float / initSolveElapsed
            else: 0.0
        let lowIterRate = initIters > 0 and initIterRate < LowIterRateThreshold

        echo "[Opt] Initial solution: ", currentCost
        flushFile(stdout)
        # Objective of the first feasible solution: while nothing (bisection
        # or ladder) has beaten it, the search may be stuck in a trivial
        # attractor (kitchen: the empty layout) — see stuckAtStart below.
        var firstCost = currentCost
        if lowIterRate and verbose:
            echo "[Opt] Low iter rate detected (", initIterRate.int, "/s) — skipping binary search bisection, going straight to retry-improvement"
            flushFile(stdout)

        # Add domain bounds as permanent constraints only when the initial solution
        # violates them. Adding trivially-satisfied bounds wastes per-iteration work
        # (full penalty map rebuilds at all positions on every move).
        if boundsViolated:
            if upperBound != high(int):
                system.addConstraint(objective <= upperBound)
            if lowerBound != low(int):
                system.addConstraint(objective >= lowerBound)
            echo "[Opt] Objective ", currentCost, " outside domain [", lowerBound, "..", upperBound, "], constraining..."
            flushFile(stdout)
            system.hasFeasibleSolution = false
            let savedAssignment = system.assignment
            var domainResolved = false
            # Try parallel resolve with scatter search, retrying with fresh seeds.
            for attempt in 1..5:
                if deadline > 0 and epochTime() > deadline:
                    raise newException(TimeLimitExceededError, "Time limit exceeded")
                system.baseArray.reducedDomain = @[]  # Force recomputation
                system.adaptedTabuThreshold = 0  # Use full threshold
                try:
                    system.resolve(parallel=parallel, tabuThreshold=tabuThreshold,
                                  scatterThreshold=max(scatterThreshold, 3),
                                  populationSize=effectivePopSize, numWorkers=numWorkers,
                                  scatterStrategy=scatterStrategy, verbose=verbose,
                                  deadline=deadline)
                    domainResolved = true
                    break
                except NoSolutionFoundError:
                    if verbose:
                        echo "[Opt] Domain bound resolve attempt ", attempt, " failed"
                    flushFile(stdout)
                except InfeasibleError:
                    raise
            if not domainResolved:
                if verbose:
                    echo "[Opt] Trying sequential from saved assignment"
                    flushFile(stdout)
                # Raises NoSolutionFoundError if no in-bounds assignment is found,
                # which propagates to the caller as UNKNOWN. This is correct: we
                # must never fall through and report the out-of-domain initial
                # assignment as a solution.
                system.resolveFromAssignment(savedAssignment, tabuThreshold, verbose, deadline)
            # Reaching here means an in-bounds assignment was found (resolve only
            # returns on a zero-penalty solution, which now includes the objective
            # bound constraints). Record it as the first valid incumbent.
            objective.initialize(system.assignment)
            currentCost = objective.value
            system.hasFeasibleSolution = true
            system.bestAssignmentValid = false
            system.bestFeasibleAssignment = system.assignment
            system.bestAssignmentValid = true
            if onSolution != nil: onSolution(system.bestFeasibleAssignment)
            echo "[Opt] Resolved within domain bounds: ", currentCost
            flushFile(stdout)
            firstCost = currentCost

        # Cache the base reduced domain and fixed positions (after any domain bound constraints).
        # Subsequent iterations only change the search bound — no need to recompute.
        # Use copyPackedSet for PackedSet to work around Nim 2.2.6 =copy bug under ARC.
        let baseReducedDomain = system.baseArray.reducedDomain
        let baseFixedPositions = copyPackedSet(system.baseArray.fixedPositions)

        # Stall cap for probes and speculative asks (see nearStallSecs): stop a
        # state after CRUSHER_PROBE_CAP_PCT percent of the remaining time
        # without any improvement, at least 5 s (default 10; 100 disables it).
        # Only for budgets of at least StallCapMinBudget seconds: on a 10 s
        # budget community detection reaches its exact optimum only through
        # the far bisection probe running the whole time (its near-feasible
        # states ARE the search; cutting the probe after 2-5 quiet seconds
        # left it at 701048 instead of 715070 in half the runs), and no cap
        # can be both long enough for that and short enough to matter. On a
        # 60 s kitchen run the hopeless probe at 560 of [1..1120] otherwise
        # eats the budget (0 instead of 200-370).
        const StallCapMinBudget = 30.0
        var probeCapPct = 10
        try: probeCapPct = parseInt(getEnv("CRUSHER_PROBE_CAP_PCT", "10"))
        except ValueError: discard
        let totalBudget = if deadline > 0: deadline - initSolveStart else: 0.0
        proc stallCap(deadline: float): float =
            if deadline <= 0 or probeCapPct >= 100 or totalBudget < StallCapMinBudget:
                return 0.0
            max(5.0, probeCapPct.float / 100.0 * (deadline - epochTime()))

        # Binary search bounds
        when direction == Minimize:
            var lo = if lowerBound != low(int): lowerBound else: safeLowerBound(currentCost)
            var hi = currentCost - 1
            # loProven is ONLY set by InfeasibleError from domain reduction — the sole
            # mechanism by which a local search solver can prove a lower bound. Domain
            # bounds from variable declarations are hints, not proofs.
            var loProven = false
            let domainLoBound = if lowerBound != low(int): lowerBound else: low(int)
        else:
            var lo = currentCost + 1
            var hi = if upperBound != high(int): upperBound else: safeUpperBound(currentCost)
            var hiProven = false
            let domainHiBound = if upperBound != high(int): upperBound else: high(int)

        # A probe state where only the objective-bound constraint is violated
        # is a feasible solution of the original problem (TabuState tracks the
        # best such state as nearBest*, collected into system.nearFeasible*).
        # Adopt it when it beats the incumbent instead of throwing the probe
        # away — whether the probe stagnated or ran out of time (warehouse: a
        # 102k incumbent kept while the timed-out probe held an 88k state).
        template adoptNearFeasible(): bool =
            var adopted = false
            if system.nearFeasibleAssignment.len > 0:
                system.initialize(system.nearFeasibleAssignment)
                objective.initialize(system.assignment)
                let nearObj = objective.value
                var feasible = true
                for c in system.baseArray.constraints:
                    if not c.isObjectiveBound and c.penalty() > 0:
                        feasible = false
                        break
                when direction == Minimize:
                    let better = nearObj < currentCost and
                        (lowerBound == low(int) or nearObj >= domainLoBound)
                else:
                    let better = nearObj > currentCost and
                        (upperBound == high(int) or nearObj <= domainHiBound)
                if verbose:
                    echo "[Opt] Near-feasible probe state: objective=", nearObj, " feasible=", feasible,
                         " incumbent=", currentCost, " (raw bound violation ", system.nearFeasibleCost, ")"
                    flushFile(stdout)
                if feasible and better:
                    currentCost = nearObj
                    system.bestAssignmentValid = false
                    system.bestFeasibleAssignment = system.assignment
                    system.bestAssignmentValid = true
                    if onSolution != nil: onSolution(system.bestFeasibleAssignment)
                    echo "[Opt] Improved (near-feasible probe state): ", nearObj
                    flushFile(stdout)
                    adopted = true
            adopted

        # Phase 1: Binary search — fast tabu-only probes (no scatter)
        if verbose:
            echo "[Opt] Binary search [", lo, "..", hi, "]"
            flushFile(stdout)

        # Product objectives skip bisection: a midpoint product bound has no
        # gradient and no factor decomposition — the retry loop's factor
        # staging ratchets the shape down directly instead.
        let skipBisection = lowIterRate or
            (direction == Minimize and system.objectiveProduct.active)
        while lo <= hi and not skipBisection:
            if deadline > 0 and epochTime() > deadline:
                system.searchCompleted = false
                break

            let bestSolution = system.assignment
            # Binary search: try the midpoint
            let target = lo + (hi - lo) div 2

            if hasBoundConstraint:
                system.removeLastConstraint()
                hasBoundConstraint = false

            when direction == Minimize:
                # With an exact single-instance circuit-time linkage the metric
                # bound (applied below) is equivalent to objective <= target;
                # the explicit relational over the objective's channel terms
                # only duplicates the pressure at much higher per-move cost.
                if not system.circuitTimeObjectiveExact:
                    system.addConstraint(objective <= target)
                    system.baseArray.constraints[^1].isObjectiveBound = true
                    hasBoundConstraint = true
            else:
                system.addConstraint(objective >= target)
                system.baseArray.constraints[^1].isObjectiveBound = true
                hasBoundConstraint = true
            # Reset near-feasible tracking for this probe (see TabuState.boundConstraint)
            system.nearFeasibleCost = high(int)
            system.nearFeasibleAssignment = @[]
            # Set objective bound on CircuitTimeProp constraints (if any)
            system.applyCircuitTimeObjectiveBounds(target, direction == Minimize)
            system.baseArray.reducedDomain = baseReducedDomain
            system.baseArray.fixedPositions = copyPackedSet(baseFixedPositions)
            system.baseArray.tightenReducedDomain()
            when direction == Minimize:
                applyObjectiveStaging(system, target, verbose)

            if verbose:
                echo "[Opt] Trying ", target, " [", lo, "..", hi, "]"
                flushFile(stdout)

            if deadline > 0 and deadline - epochTime() < 5.0:
                system.searchCompleted = false
                break

            # Save constraints/fixedPositions before resolve (which may mutate them
            # via removeFixedConstraints) so the optimizer can still add/remove bounds
            let savedConstraints = system.baseArray.constraints
            let savedFixed = copyPackedSet(system.baseArray.fixedPositions)

            # Local search cannot prove a midpoint infeasible, so a probe far
            # above the true optimum (kitchen: midpoint 575 of [31..1120],
            # optimum 516) otherwise runs until the global deadline and the
            # whole budget is spent on one hopeless ask. Stall cap: a probe
            # state stops once its near-feasible incumbent has not improved
            # for a quarter of the remaining time (at least 2 s). A fixed
            # wall-clock cap instead cut productive probes short (warehouse
            # wlp02: 236650 capped vs 143590 uncapped — each restart costs 5 s
            # of state creation and the search momentum).
            system.baseArray.nearStallSecs = stallCap(deadline)

            try:
                system.resolve(
                    parallel=parallel,
                    tabuThreshold=tabuThreshold,
                    scatterThreshold=0,
                    populationSize=effectivePopSize,
                    numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy,
                    verbose=verbose,
                    deadline=deadline,
                    seedAssignment=bestSolution,
                )
                objective.initialize(system.assignment)
                currentCost = objective.value
                # Validate: reject solutions that violate the original domain bound.
                # This catches cases where disconnected variable arrays allow the
                # solver to find zero-penalty assignments with infeasible objectives.
                # Only checks against the ORIGINAL domain bound (immutable), not the
                # dynamic binary search lo/hi which ratchets during no-solution rounds.
                when direction == Minimize:
                    if lowerBound != low(int) and currentCost < domainLoBound:
                        if verbose:
                            echo "[Opt] Rejected infeasible solution: ", currentCost, " < domain lower bound ", domainLoBound
                            flushFile(stdout)
                        system.initialize(bestSolution)
                        objective.initialize(system.assignment)
                        currentCost = objective.value
                        lo = target + 1
                        continue
                else:
                    if upperBound != high(int) and currentCost > domainHiBound:
                        if verbose:
                            echo "[Opt] Rejected infeasible solution: ", currentCost, " > domain upper bound ", domainHiBound
                            flushFile(stdout)
                        system.initialize(bestSolution)
                        objective.initialize(system.assignment)
                        currentCost = objective.value
                        hi = target - 1
                        continue
                system.bestAssignmentValid = false
                system.bestFeasibleAssignment = system.assignment
                system.bestAssignmentValid = true
                if onSolution != nil: onSolution(system.bestFeasibleAssignment)
                echo "[Opt] Improved: ", objective.value
                flushFile(stdout)
                if verbose:
                    echo "[Opt] iters=", system.lastIterations
                    flushFile(stdout)
                # Found solution at value currentCost — narrow toward better
                when direction == Minimize:
                    hi = currentCost - 1
                else:
                    lo = currentCost + 1
            except TimeLimitExceededError:
                if not adoptNearFeasible():
                    system.initialize(bestSolution)
                    objective.initialize(system.assignment)
                system.searchCompleted = false
                break
            except InfeasibleError:
                # Domain reduction proved no solution at this bound — narrow range
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                when direction == Minimize:
                    lo = target + 1
                    loProven = true
                else:
                    hi = target - 1
                    hiProven = true
            except NoSolutionFoundError:
                # The probe missed its target, but a state where only the bound
                # constraint was violated is a feasible solution of the original
                # problem; keep it when it beats the incumbent instead of throwing
                # the whole probe away (warehouse: 102k incumbent, probe reached 56k).
                if adoptNearFeasible():
                    when direction == Minimize:
                        hi = currentCost - 1
                    else:
                        lo = currentCost + 1
                    continue
                system.initialize(bestSolution)
                objective.initialize(system.assignment)
                # If staging fixed gated blocks at this target (i.e. the target forced
                # the dominant variable v into a stage), a failure means that stage is
                # too tight at this bound — narrow UP and keep bisecting toward the
                # feasible stage rather than abandoning to the retry phase. Without
                # staging (full model), keep the original behaviour: break to scatter.
                var stagedTarget = false
                when direction == Minimize:
                    let st = system.objectiveStaging
                    if st.active and st.weight > 0:
                        let num = target - st.minRest
                        var kB = num div st.weight
                        if num < 0 and (num mod st.weight) != 0: dec kB
                        if kB >= st.vLo and kB < st.vHi: stagedTarget = true
                if stagedTarget:
                    when direction == Minimize:
                        lo = target + 1
                    else:
                        hi = target - 1
                else:
                    # Tabu-only couldn't find — break to retry with scatter search
                    break
            finally:
                system.baseArray.nearStallSecs = 0.0
                system.baseArray.constraints = savedConstraints
                system.baseArray.fixedPositions = copyPackedSet(savedFixed)

        # Retry: binary search used fast tabu-only probes until first failure.
        # Now try to beat the current best with full scatter search, deepening threshold on each failure.
        var retryThreshold = tabuThreshold
        # Ask step. Two regimes (see the retry-ladder notes): in the
        # target-limited regime every successful ask lands exactly on the
        # asked bound and a ±1 ladder pays a full resolve per unit (kitchen:
        # ~30 asks → 30 points in 40 s), so the step doubles on each exact
        # hit; in the overshoot regime a ±1 ask already lands far past the
        # target (community detection, wordpress), where speculative steps
        # only add failures, so a success that overshoots by more than
        # StepResetGain steps resets the step to 1. Failed or rejected asks
        # quarter the step; speculative (step > 1) asks run tabu-only so they
        # fail fast and never consume the scatter/LNS budget.
        var retryStep = 1
        const StepResetGain = 8
        # When the incumbent is still the very first feasible solution, the
        # seeded ask keeps restarting inside the same attractor: alternate
        # seeded and fresh-population asks, and time-box them (a tall_complex
        # ask for objective 1 otherwise ran 43 s of a 60 s budget).
        var askUnseeded = false
        block retryLoop:
            while true:
                # Check if current cost is already at the known bound.
                # Only claim proven optimal if the bound was established by
                # InfeasibleError (domain reduction proof) or user-provided.
                when direction == Minimize:
                    # Proven optimal if: (a) domain reduction proved lo, or
                    # (b) current cost matches the domain lower bound (no feasible
                    # solution can exist below it by definition of the variable domain).
                    if currentCost <= lo and loProven:
                        system.optimalityProven = true
                        break retryLoop
                    elif domainLoBound != low(int) and currentCost <= domainLoBound:
                        system.optimalityProven = true
                        break retryLoop
                    elif currentCost <= lo:
                        lo = min(safeLowerBound(currentCost), safeLowerBound(lo))
                else:
                    if currentCost >= hi and hiProven:
                        system.optimalityProven = true
                        break retryLoop
                    elif domainHiBound != high(int) and currentCost >= domainHiBound:
                        system.optimalityProven = true
                        break retryLoop
                    elif currentCost >= hi:
                        hi = max(safeUpperBound(currentCost), safeUpperBound(hi))

                if deadline > 0 and epochTime() > deadline:
                    system.searchCompleted = false
                    break retryLoop

                let bestSolution = system.assignment
                if hasBoundConstraint:
                    system.removeLastConstraint()
                    hasBoundConstraint = false

                let askFrom = currentCost
                when direction == Minimize:
                    var askTarget = currentCost - retryStep
                    if domainLoBound != low(int): askTarget = max(askTarget, domainLoBound)
                    askTarget = min(askTarget, currentCost - 1)
                else:
                    var askTarget = currentCost + retryStep
                    if domainHiBound != high(int): askTarget = min(askTarget, domainHiBound)
                    askTarget = max(askTarget, currentCost + 1)
                let effStep = abs(currentCost - askTarget)
                let stuckAtStart = currentCost == firstCost

                when direction == Minimize:
                    # See the binary-search phase: an exact circuit-time
                    # linkage replaces the explicit objective bound.
                    if not system.circuitTimeObjectiveExact:
                        system.addConstraint(objective <= askTarget)
                        system.baseArray.constraints[^1].isObjectiveBound = true
                        hasBoundConstraint = true
                else:
                    system.addConstraint(objective >= askTarget)
                    system.baseArray.constraints[^1].isObjectiveBound = true
                    hasBoundConstraint = true
                system.nearFeasibleCost = high(int)
                system.nearFeasibleAssignment = @[]
                # Set objective bound on CircuitTimeProp constraints (retry loop)
                system.applyCircuitTimeObjectiveBounds(askTarget, direction == Minimize)
                system.baseArray.reducedDomain = baseReducedDomain
                system.baseArray.fixedPositions = copyPackedSet(baseFixedPositions)
                system.baseArray.tightenReducedDomain()
                when direction == Minimize:
                    applyObjectiveStaging(system, askTarget, verbose)

                # Product-objective factor staging: try bounding the factors
                # directly before the plain composite retry. `obj ≤ T` alone is
                # a flat ±1 penalty with no direction; `a ≤ wa` propagates into
                # the factor's defining structure (typically a max over
                # placements) and penalises each offending element, giving
                # local search a gradient toward the smaller shape.
                when direction == Minimize:
                    if system.objectiveProduct.active and not system.circuitTimeObjectiveExact:
                        let op = system.objectiveProduct
                        let target = askTarget
                        let curA = int(op.aExpr.evaluate(system.assignment))
                        let curB = int(op.bExpr.evaluate(system.assignment))
                        # Pareto-maximal splits (wa, hb): wa·hb ≤ target, no split
                        # dominated by another. Iterate wa descending; hb is then
                        # forced, and only strictly increasing hb survive.
                        var splits: seq[(int, int)]
                        var bestHb = low(int)
                        for wa in countdown(op.aHi, max(op.aLo, 1)):
                            let hb = min(op.bHi, target div wa)
                            if hb < op.bLo: continue
                            if hb > bestHb:
                                splits.add((wa, hb))
                                bestHb = hb
                                if hb == op.bHi: break
                        # Closest-to-incumbent shapes first: least repacking work
                        splits.sort(proc(x, y: (int, int)): int =
                            cmp(abs(x[0]-curA) + abs(x[1]-curB), abs(y[0]-curA) + abs(y[1]-curB)))
                        if splits.len > 3: splits.setLen(3)

                        var stagedImproved = false
                        for (wa, hb) in splits:
                            if deadline > 0 and epochTime() > deadline:
                                break
                            system.baseArray.reducedDomain = baseReducedDomain
                            system.baseArray.fixedPositions = copyPackedSet(baseFixedPositions)
                            let savedConstraintsP = system.baseArray.constraints
                            let savedFixedP = copyPackedSet(system.baseArray.fixedPositions)
                            # Per-input bounds when the factor is a max channel:
                            # each protruding element contributes its own
                            # graduated violation (gradient), unlike a single
                            # flat bound on the max.
                            if op.aInputs.len > 0:
                                for ie in op.aInputs:
                                    system.addConstraint(ie <= T(wa - op.aShift))
                            else:
                                system.addConstraint(op.aExpr <= T(wa))
                            if op.bInputs.len > 0:
                                for ie in op.bInputs:
                                    system.addConstraint(ie <= T(hb - op.bShift))
                            else:
                                system.addConstraint(op.bExpr <= T(hb))
                            system.baseArray.tightenReducedDomain()
                            try:
                                if verbose:
                                    echo "[Opt] Retry targeting ", target, " via factor bounds ", wa, "x", hb
                                    flushFile(stdout)
                                system.resolve(
                                    parallel=parallel,
                                    tabuThreshold=retryThreshold,
                                    scatterThreshold=scatterThreshold,
                                    populationSize=effectivePopSize,
                                    numWorkers=numWorkers,
                                    scatterStrategy=scatterStrategy,
                                    verbose=verbose,
                                    deadline=deadline,
                                    seedAssignment=bestSolution,
                                )
                                objective.initialize(system.assignment)
                                currentCost = objective.value
                                if domainLoBound != low(int) and currentCost < domainLoBound:
                                    system.initialize(bestSolution)
                                    objective.initialize(system.assignment)
                                    currentCost = objective.value
                                else:
                                    stagedImproved = true
                            except TimeLimitExceededError:
                                system.initialize(bestSolution)
                                objective.initialize(system.assignment)
                                system.searchCompleted = false
                            except InfeasibleError:
                                # Only this split's box is proven empty — other
                                # splits at the same target may still work.
                                system.initialize(bestSolution)
                                objective.initialize(system.assignment)
                            except NoSolutionFoundError:
                                system.initialize(bestSolution)
                                objective.initialize(system.assignment)
                            finally:
                                system.baseArray.constraints = savedConstraintsP
                                system.baseArray.fixedPositions = copyPackedSet(savedFixedP)
                            if stagedImproved:
                                break

                        if stagedImproved:
                            system.bestAssignmentValid = false
                            system.bestFeasibleAssignment = system.assignment
                            system.bestAssignmentValid = true
                            if onSolution != nil: onSolution(system.bestFeasibleAssignment)
                            echo "[Opt] Retry improved (factor bounds): ", currentCost
                            flushFile(stdout)
                            retryThreshold = tabuThreshold
                            continue
                        if deadline > 0 and epochTime() > deadline:
                            system.searchCompleted = false
                            break retryLoop

                let savedConstraints2 = system.baseArray.constraints
                let savedFixed2 = copyPackedSet(system.baseArray.fixedPositions)

                let thisUnseeded = askUnseeded
                askUnseeded = false
                # Speculative (step > 1) asks and asks that have not yet left
                # the first solution get the probes' stall cap and run
                # tabu-only, so they fail fast (a stalled ask surfaces as
                # NoSolutionFoundError and is handled like a failed one).
                let fastAsk = effStep > 1 or stuckAtStart
                system.baseArray.nearStallSecs = if fastAsk: stallCap(deadline) else: 0.0

                try:
                    if verbose:
                        if effStep > 1:
                            echo "[Opt] Retry targeting ", askTarget, " (step ", effStep, ")"
                        else:
                            echo "[Opt] Retry targeting ", askTarget
                        flushFile(stdout)

                    if verbose and thisUnseeded:
                        echo "[Opt] Retry from a fresh population"
                        flushFile(stdout)
                    system.resolve(
                        parallel=parallel,
                        tabuThreshold=retryThreshold,
                        scatterThreshold=(if fastAsk: 0 else: scatterThreshold),
                        populationSize=effectivePopSize,
                        numWorkers=numWorkers,
                        scatterStrategy=scatterStrategy,
                        verbose=verbose,
                        deadline=deadline,
                        seedAssignment=(if thisUnseeded: newSeq[T]() else: bestSolution),
                    )
                    objective.initialize(system.assignment)
                    currentCost = objective.value
                    # Reject solutions that violate the domain bound
                    # Reject solutions that violate the domain bound.
                    # Note: constraint/fixedPositions restore is handled by the finally block.
                    when direction == Minimize:
                        if domainLoBound != low(int) and currentCost < domainLoBound:
                            if verbose:
                                echo "[Opt] Rejected infeasible retry solution: ", currentCost, " < domain bound ", domainLoBound
                                flushFile(stdout)
                            system.initialize(bestSolution)
                            objective.initialize(system.assignment)
                            currentCost = objective.value
                            retryStep = max(1, effStep div 4)
                            if effStep == 1:
                                retryThreshold = min(retryThreshold + retryThreshold div 2, 100_000)
                            continue
                    else:
                        if domainHiBound != high(int) and currentCost > domainHiBound:
                            if verbose:
                                echo "[Opt] Rejected infeasible retry solution: ", currentCost, " > domain bound ", domainHiBound
                                flushFile(stdout)
                            system.initialize(bestSolution)
                            objective.initialize(system.assignment)
                            currentCost = objective.value
                            retryStep = max(1, effStep div 4)
                            if effStep == 1:
                                retryThreshold = min(retryThreshold + retryThreshold div 2, 100_000)
                            continue
                    system.bestAssignmentValid = false
                    system.bestFeasibleAssignment = system.assignment
                    system.bestAssignmentValid = true
                    if onSolution != nil: onSolution(system.bestFeasibleAssignment)
                    echo "[Opt] Retry improved: ", currentCost
                    flushFile(stdout)
                    retryThreshold = tabuThreshold  # reset on success
                    let gain = abs(currentCost - askFrom)
                    if gain > StepResetGain * effStep:
                        retryStep = 1          # overshoot regime: ±1 lands far anyway
                    else:
                        retryStep = effStep * 2 # exact hit: target-limited, grow
                except TimeLimitExceededError:
                    if not adoptNearFeasible():
                        system.initialize(bestSolution)
                        objective.initialize(system.assignment)
                    system.searchCompleted = false
                    break retryLoop
                except InfeasibleError:
                    # Domain reduction proved no better solution exists — provably optimal
                    system.optimalityProven = true
                    system.initialize(bestSolution)
                    objective.initialize(system.assignment)
                    break retryLoop
                except NoSolutionFoundError:
                    if adoptNearFeasible():
                        # Progress was made: keep asking, as after a retry success
                        # (with no deadline the loop is bounded by its own caps).
                        retryThreshold = tabuThreshold
                        retryStep = max(1, effStep div 4)
                        continue
                    system.initialize(bestSolution)
                    objective.initialize(system.assignment)
                    if effStep > 1:
                        # A speculative ask missed: shrink and re-ask at the same
                        # threshold. Must continue even without a deadline, or the
                        # first over-aggressive ask would abort the whole ladder.
                        retryStep = max(1, effStep div 4)
                        if verbose:
                            echo "[Opt] Retry step shrinks to ", retryStep
                            flushFile(stdout)
                        continue
                    retryThreshold = retryThreshold * 2
                    system.adaptedTabuThreshold = 0  # force using bumped threshold
                    if stuckAtStart:
                        askUnseeded = not thisUnseeded
                    if verbose:
                        echo "[Opt] Retry deepening threshold to ", retryThreshold
                        flushFile(stdout)
                    if deadline > 0 and epochTime() < deadline:
                        continue
                    break retryLoop
                finally:
                    system.baseArray.nearStallSecs = 0.0
                    system.baseArray.constraints = savedConstraints2
                    system.baseArray.fixedPositions = copyPackedSet(savedFixed2)

        # Clean up the bound constraint and restore best solution
        if hasBoundConstraint:
            system.removeLastConstraint()
        system.initialize(system.assignment)
        objective.initialize(system.assignment)
        if system.optimalityProven:
            echo "[Opt] Proven optimal: ", objective.value
        else:
            echo "[Opt] Done: ", objective.value
        flushFile(stdout)

# Generate minimize and maximize procedures for all stateful expression types
optimizeImpl(SumExpression, Minimize, minimize)
optimizeImpl(MinExpression, Minimize, minimize)
optimizeImpl(MaxExpression, Minimize, minimize)
optimizeImpl(StatefulAlgebraicExpression, Minimize, minimize)

optimizeImpl(SumExpression, Maximize, maximize)
optimizeImpl(MinExpression, Maximize, maximize)
optimizeImpl(MaxExpression, Maximize, maximize)
optimizeImpl(StatefulAlgebraicExpression, Maximize, maximize)

optimizeImpl(WeightedSameValueExpression, Minimize, minimize)
optimizeImpl(WeightedSameValueExpression, Maximize, maximize)

optimizeImpl(BinaryPairwiseSumExpression, Minimize, minimize)
optimizeImpl(BinaryPairwiseSumExpression, Maximize, maximize)

# Template for AlgebraicExpression wrappers - convert to StatefulAlgebraicExpression
template algebraicWrapper(procName: untyped) =
    proc procName*[T](system: ConstraintSystem[T],
                      objective: AlgebraicExpression[T],
                      parallel=true,
                      tabuThreshold=1000,
                      scatterThreshold=1,
                      populationSize=0,  # 0 = auto: 2 * worker threads
                      numWorkers=0,
                      scatterStrategy: ScatterStrategy = PathRelinking,
                      verbose=false,
                      multiplier=6,  # deprecated, ignored
                      lowerBound=low(int),
                      upperBound=high(int),
                      deadline: float = 0.0,
                      onSolution: proc(assignment: seq[T]) {.closure.} = nil,
                      ) =
        if objective.linear:
            # Automatically linearize for O(1) incremental updates
            let linearizedObjective = linearize(objective)
            procName(system, linearizedObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                    scatterThreshold=scatterThreshold,
                    populationSize=populationSize, numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy, verbose=verbose,
                    lowerBound=lowerBound, upperBound=upperBound,
                    deadline=deadline, onSolution=onSolution)
        else:
            let statefulObjective = newStatefulAlgebraicExpression(objective)
            procName(system, statefulObjective, parallel=parallel, tabuThreshold=tabuThreshold,
                    scatterThreshold=scatterThreshold,
                    populationSize=populationSize, numWorkers=numWorkers,
                    scatterStrategy=scatterStrategy, verbose=verbose,
                    lowerBound=lowerBound, upperBound=upperBound,
                    deadline=deadline, onSolution=onSolution)

# Generate AlgebraicExpression wrappers
algebraicWrapper(minimize)
algebraicWrapper(maximize)
