import std/[sequtils, algorithm, math, random, packedsets, strformat]
import ../constraintSystem
import ../constraints/stateful
import populationManager

type
  RelinkingStats* = object
    pairsProcessed*: int
    intermediateStatesGenerated*: int
    statesImproved*: int
    successRate*: float

  RelinkingParams* = object
    baseStepFraction*: float  # Base fraction for step size (default: 0.1 = 1/10)
    adaptiveStepSize*: bool   # Whether to use adaptive step sizing
    constraintGuided*: bool   # Whether to prioritize constraint-violating positions
    maxIntermediateStates*: int  # Maximum states to generate per path

proc newRelinkingParams*(): RelinkingParams =
  RelinkingParams(
    baseStepFraction: 0.1,
    adaptiveStepSize: true,
    constraintGuided: true,
    maxIntermediateStates: 10
  )

proc getConstraintPositions*[T](system: ConstraintSystem[T], constraintIndex: int): seq[int] =
  if constraintIndex < 0 or constraintIndex >= system.baseArray.constraints.len:
    return @[]
  
  let constraint = system.baseArray.constraints[constraintIndex]
  result = @[]
  for position in constraint.positions:
    result.add(position)

proc selectPositionsToChange*[T](currentState, targetState: seq[T], 
                                system: ConstraintSystem[T],
                                violatedConstraints: seq[int],
                                currentCost, previousCost: int,
                                params: RelinkingParams): seq[int] =
  # Find positions where current and target differ
  var diffPositions: seq[int]
  for i in 0..<currentState.len:
    if currentState[i] != targetState[i]:
      diffPositions.add(i)
  
  if diffPositions.len == 0:
    return @[]
  
  # Calculate base step size
  let baseStepSize = max(1, int(diffPositions.len.float * params.baseStepFraction))
  
  # Adaptive step size based on cost improvement
  let adaptiveStepSize = if params.adaptiveStepSize:
                          if currentCost < previousCost:
                            max(1, baseStepSize div 2)  # Smaller steps if improving
                          elif currentCost > previousCost:
                            min(diffPositions.len, baseStepSize * 2)  # Larger steps if worsening
                          else:
                            baseStepSize  # Same if no change
                        else:
                          baseStepSize
  
  if not params.constraintGuided:
    # Simple random selection of positions to change
    diffPositions.shuffle()
    return diffPositions[0..<min(adaptiveStepSize, diffPositions.len)]
  
  # Constraint-guided selection: prioritize positions involved in violated constraints
  var priorityPositions: seq[int]
  var positionPriority: seq[(int, int)] # (position, priority_count)
  
  for pos in diffPositions:
    var priorityCount = 0
    for violatedIdx in violatedConstraints:
      let constraintPositions = getConstraintPositions(system, violatedIdx)
      if pos in constraintPositions:
        priorityCount += 1
    positionPriority.add((pos, priorityCount))
  
  # Sort by priority (most constrained first), then by value difference magnitude
  positionPriority.sort do (a, b: (int, int)) -> int:
    if a[1] != b[1]:
      return cmp(b[1], a[1])  # Higher priority first
    else:
      # If same priority, prefer larger value differences
      let diffA = abs(currentState[a[0]] - targetState[a[0]])
      let diffB = abs(currentState[b[0]] - targetState[b[0]])
      return cmp(diffB, diffA)
  
  # Select top positions up to adaptive step size
  result = @[]
  for i in 0..<min(adaptiveStepSize, positionPriority.len):
    result.add(positionPriority[i][0])

proc generateIntermediateStates*[T](startState, endState: seq[T],
                                   system: ConstraintSystem[T],
                                   params: RelinkingParams): seq[seq[T]] =
  result = @[]
  
  # Validate inputs
  if startState.len != endState.len or startState.len == 0:
    return result
  
  var currentState = startState
  var previousCost = calculateCost(system)
  var step = 0
  
  while currentState != endState and step < params.maxIntermediateStates:
    # Get violated constraints for current state
    system.assignment = currentState
    let violatedConstraints = getViolatedConstraints(system)
    let currentCost = calculateCost(system)
    
    # Select positions to change
    let positionsToChange = selectPositionsToChange(
      currentState, endState, system, violatedConstraints, 
      currentCost, previousCost, params
    )
    
    if positionsToChange.len == 0:
      break
    
    # Create next intermediate state
    var nextState = currentState
    for pos in positionsToChange:
      nextState[pos] = endState[pos]
    
    result.add(nextState)
    currentState = nextState
    previousCost = currentCost
    step += 1

proc pathRelink*[T](memberA, memberB: PopulationMember[T], 
                   system: ConstraintSystem[T],
                   params: RelinkingParams = newRelinkingParams()): seq[seq[T]] =
  if memberA.assignment == memberB.assignment:
    return @[]
  
  # Generate intermediate states from A to B
  let intermediateStates = generateIntermediateStates(
    memberA.assignment, memberB.assignment, system, params
  )
  
  result = intermediateStates

proc performPathRelinking*[T](pop: Population[T], 
                             systemTemplate: ConstraintSystem[T],
                             pairs: seq[(int, int)],
                             params: RelinkingParams = newRelinkingParams()): (seq[seq[T]], RelinkingStats) =
  var allIntermediateStates: seq[seq[T]] = @[]
  var stats = RelinkingStats()
  
  for (i, j) in pairs:
    let memberA = pop.getMember(i)
    let memberB = pop.getMember(j)
    
    # Create a working copy of the system for cost calculations
    var workingSystem = systemTemplate.deepCopy()
    
    # Generate intermediate states for this pair
    let intermediateStates = pathRelink(memberA, memberB, workingSystem, params)
    
    stats.pairsProcessed += 1
    stats.intermediateStatesGenerated += intermediateStates.len
    
    for state in intermediateStates:
      allIntermediateStates.add(state)
  
  # Calculate success rate (will be updated after batch improvement)
  stats.successRate = 0.0  # Will be calculated by caller after batch improve
  
  return (allIntermediateStates, stats)


proc createBalancedIntermediates*[T](startState, endState: seq[T], 
                                    numSteps: int): seq[seq[T]] =
  # Alternative method: create intermediates that maintain balanced distance to both endpoints
  result = @[]
  
  if startState == endState or numSteps <= 0:
    return result
  
  let totalDistance = hammingDistance(startState, endState)
  if totalDistance == 0:
    return result
  
  # Find all differing positions
  var diffPositions: seq[int]
  for i in 0..<startState.len:
    if startState[i] != endState[i]:
      diffPositions.add(i)
  
  # Create intermediate states by gradually changing positions
  let positionsPerStep = max(1, diffPositions.len div numSteps)
  var currentState = startState
  
  for step in 1..numSteps:
    if diffPositions.len == 0:
      break
    
    var nextState = currentState
    let endIdx = min(step * positionsPerStep, diffPositions.len)
    let startIdx = (step - 1) * positionsPerStep
    
    for idx in startIdx..<endIdx:
      if idx < diffPositions.len:
        let pos = diffPositions[idx]
        nextState[pos] = endState[pos]
    
    if nextState != currentState:
      result.add(nextState)
      currentState = nextState
    
    if currentState == endState:
      break

proc printRelinkingStats*(stats: RelinkingStats) =
  echo fmt"└─ Relinking: {stats.pairsProcessed} pairs → {stats.intermediateStatesGenerated} states → {stats.statesImproved} improved ({stats.successRate:.1f}%)"