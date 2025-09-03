import ../expressions

################################################################################
# Type definitions
################################################################################

type
    DiffnConstraint*[T] = ref object
        diffnExpr*: DiffnExpression[T]
        cost*: int

################################################################################
# DiffnConstraint creation
################################################################################

func init*[T](state: DiffnConstraint[T], diffnExpr: DiffnExpression[T]) =
    state.cost = 0
    state.diffnExpr = diffnExpr

func newDiffnConstraint*[T](diffnExpr: DiffnExpression[T]): DiffnConstraint[T] =
    new(result)
    result.init(diffnExpr)

################################################################################
# DiffnConstraint initialization and updates
################################################################################

func initialize*[T](state: DiffnConstraint[T], assignment: seq[T]) =
    state.diffnExpr.initialize(assignment)
    state.cost = state.diffnExpr.overlapCount

func updatePosition*[T](state: DiffnConstraint[T], position: int, newValue: T) {.inline.} =
    state.diffnExpr.updatePosition(position, newValue)
    state.cost = state.diffnExpr.overlapCount

proc moveDelta*[T](state: DiffnConstraint[T], position: int, oldValue, newValue: T): int {.inline.} =
    # Returns cost delta for changing position from oldValue to newValue.
    let oldCost = state.cost
    let overlapDelta = state.diffnExpr.moveDelta(position, oldValue, newValue)
    let newOverlapCount = state.diffnExpr.overlapCount + overlapDelta
    return newOverlapCount - oldCost

################################################################################
# Helper functions for constraint creation
################################################################################

func diffnConstraint*[T](
    xPositions, widthPositions, yPositions, heightPositions: seq[int]
): DiffnConstraint[T] =
    # Create constraint from variable positions (all variable parameters)
    var xParams: seq[RectangleParam[T]] = @[]
    var wParams: seq[RectangleParam[T]] = @[]
    var yParams: seq[RectangleParam[T]] = @[]
    var hParams: seq[RectangleParam[T]] = @[]
    
    for pos in xPositions:
        xParams.add(RectangleParam[T](isConstant: false, variablePosition: pos))
    for pos in widthPositions:
        wParams.add(RectangleParam[T](isConstant: false, variablePosition: pos))
    for pos in yPositions:
        yParams.add(RectangleParam[T](isConstant: false, variablePosition: pos))
    for pos in heightPositions:
        hParams.add(RectangleParam[T](isConstant: false, variablePosition: pos))
    
    let diffnExpr = newDiffnExpression[T](xParams, wParams, yParams, hParams)
    return newDiffnConstraint[T](diffnExpr)

func diffnConstraintMixed*[T](
    xParams, wParams, yParams, hParams: seq[RectangleParam[T]]
): DiffnConstraint[T] =
    # Create constraint from mixed constant/variable parameters
    let diffnExpr = newDiffnExpression[T](xParams, wParams, yParams, hParams)
    return newDiffnConstraint[T](diffnExpr)

func diffnConstraintConstants*[T](
    xCoords, widths, yCoords, heights: seq[int]
): DiffnConstraint[T] =
    # Create constraint from all constant parameters (mainly for testing)
    var xParams: seq[RectangleParam[T]] = @[]
    var wParams: seq[RectangleParam[T]] = @[]
    var yParams: seq[RectangleParam[T]] = @[]
    var hParams: seq[RectangleParam[T]] = @[]
    
    for val in xCoords:
        xParams.add(RectangleParam[T](isConstant: true, constantValue: T(val)))
    for val in widths:
        wParams.add(RectangleParam[T](isConstant: true, constantValue: T(val)))
    for val in yCoords:
        yParams.add(RectangleParam[T](isConstant: true, constantValue: T(val)))
    for val in heights:
        hParams.add(RectangleParam[T](isConstant: true, constantValue: T(val)))
    
    let diffnExpr = newDiffnExpression[T](xParams, wParams, yParams, hParams)
    return newDiffnConstraint[T](diffnExpr)
