import ../expressions
import constraintNode

################################################################################
# Type definitions
################################################################################

type
    CumulativeConstraint*[T] = ref object
        cumulativeExpr*: CumulativeExpression[T]
        relation*: BinaryRelation
        target*: T      # Usually the capacity limit
        cost*: int

################################################################################
# CumulativeConstraint creation
################################################################################

func init*[T](state: CumulativeConstraint[T],
              cumulativeExpr: CumulativeExpression[T],
              relation: BinaryRelation,
              target: T) =
    state.cost = 0
    state.cumulativeExpr = cumulativeExpr
    state.relation = relation
    state.target = target

func newCumulativeConstraint*[T](cumulativeExpr: CumulativeExpression[T],
                                relation: BinaryRelation,
                                target: T): CumulativeConstraint[T] =
    new(result)
    result.init(cumulativeExpr, relation, target)

################################################################################
# CumulativeConstraint initialization and updates
################################################################################

func initialize*[T](state: CumulativeConstraint[T], assignment: seq[T]) =
    state.cumulativeExpr.initialize(assignment)
    state.cost = state.relation.penalty(state.cumulativeExpr.currentMaxUsage, state.target)

func updatePosition*[T](state: CumulativeConstraint[T], position: int, newValue: T) {.inline.} =
    state.cumulativeExpr.updatePosition(position, newValue)
    state.cost = state.relation.penalty(state.cumulativeExpr.currentMaxUsage, state.target)

proc moveDelta*[T](state: CumulativeConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let usageDelta = state.cumulativeExpr.moveDelta(position, oldValue, newValue)
    let newMaxUsage = state.cumulativeExpr.currentMaxUsage + usageDelta
    let newCost = int(state.relation.penalty(newMaxUsage, state.target))
    return newCost - oldCost

################################################################################
# Helper functions for constraint creation
################################################################################

func cumulativeConstraint*[T](
    startPositions, durationPositions, demandPositions: seq[int], 
    capacity: T
): CumulativeConstraint[T] =
    # Create constraint from variable positions (all variable parameters)
    var startParams: seq[TaskParam[T]] = @[]
    var durationParams: seq[TaskParam[T]] = @[]
    var demandParams: seq[TaskParam[T]] = @[]
    
    for pos in startPositions:
        startParams.add(TaskParam[T](isConstant: false, variablePosition: pos))
    for pos in durationPositions:
        durationParams.add(TaskParam[T](isConstant: false, variablePosition: pos))
    for pos in demandPositions:
        demandParams.add(TaskParam[T](isConstant: false, variablePosition: pos))
    
    let capacityParam = TaskParam[T](isConstant: true, constantValue: capacity)
    let cumulExpr = newCumulativeExpression[T](startParams, durationParams, demandParams, capacityParam)
    
    return newCumulativeConstraint[T](cumulExpr, LessThanEq, capacity)

func cumulativeConstraintFromParams*[T](
    startParams, durationParams, demandParams: seq[TaskParam[T]], 
    capacityParam: TaskParam[T]
): CumulativeConstraint[T] =
    # Create constraint from mixed constant/variable parameters
    let cumulExpr = newCumulativeExpression[T](startParams, durationParams, demandParams, capacityParam)
    let targetValue = if capacityParam.isConstant: capacityParam.constantValue else: T(0)
    
    return newCumulativeConstraint[T](cumulExpr, LessThanEq, targetValue)

func cumulativeConstraintConstants*[T](
    startTimes, durations, demands: seq[int],  # Constant values
    capacity: T
): CumulativeConstraint[T] =
    # Create constraint from all constant parameters
    var startParams: seq[TaskParam[T]] = @[]
    var durationParams: seq[TaskParam[T]] = @[]
    var demandParams: seq[TaskParam[T]] = @[]
    
    for val in startTimes:
        startParams.add(TaskParam[T](isConstant: true, constantValue: T(val)))
    for val in durations:
        durationParams.add(TaskParam[T](isConstant: true, constantValue: T(val)))
    for val in demands:
        demandParams.add(TaskParam[T](isConstant: true, constantValue: T(val)))
    
    let capacityParam = TaskParam[T](isConstant: true, constantValue: capacity)
    let cumulExpr = newCumulativeExpression[T](startParams, durationParams, demandParams, capacityParam)
    
    return newCumulativeConstraint[T](cumulExpr, LessThanEq, capacity)