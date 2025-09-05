import std/[strformat, random, sequtils, algorithm, times, strutils]
import ../constraintSystem
import ../constrainedArray
import ../constraints/stateful
import tabu
import populationManager
import pathRelinking
import heuristics

type
  PopulationSearchParams* = object
    populationSize*: int
    maxGenerations*: int
    minDiversityThreshold*: int
    elitePercentage*: float
    qualityWeight*: float
    maxPairsPerGeneration*: int
    relinkingParams*: RelinkingParams
    tabuThreshold*: int
    verbose*: bool
    earlyTermination*: bool  # Stop when solution found (cost = 0)

  SearchResult*[T] = object
    solved*: bool
    bestCost*: int
    bestAssignment*: seq[T]
    generations*: int
    totalEvaluations*: int
    elapsedTime*: float

proc newPopulationSearchParams*(): PopulationSearchParams =
  PopulationSearchParams(
    populationSize: 20,
    maxGenerations: 100,
    minDiversityThreshold: 5,
    elitePercentage: 0.2,
    qualityWeight: 0.7,
    maxPairsPerGeneration: 50,
    relinkingParams: newRelinkingParams(),
    tabuThreshold: 1000,
    verbose: false,
    earlyTermination: true
  )

proc generateInitialPopulation*[T](system: ConstraintSystem[T], 
                                  populationSize: int,
                                  maxAttempts: int = 100): seq[ConstraintSystem[T]] =
  result = @[]
  var attempts = 0
  
  while result.len < populationSize and attempts < maxAttempts:
    # Create a new system copy for each population member
    var newSystem = system.deepCopy()
    
    # Quick local improvement to get a reasonable starting point
    var tabuState = newTabuState(newSystem.baseArray, false)  # Disable timing for initialization
    
    # Short tabu search to improve the random assignment
    let shortTabuThreshold = 100
    let improvedState = tabuState.tabuImprove(shortTabuThreshold)
    
    # Update the system with the improved assignment
    newSystem.assignment = improvedState.assignment
    result.add(newSystem)
    attempts += 1

proc populationSearch*[T](system: ConstraintSystem[T], 
                         params: PopulationSearchParams = newPopulationSearchParams()): SearchResult[T] =
  let startTime = epochTime()
  
  if params.verbose:
    echo "Starting Population-based Path Relinking Search"
    echo fmt"Parameters: pop={params.populationSize}, gens={params.maxGenerations}, diversity≥{params.minDiversityThreshold}"
    echo fmt"Elite={params.elitePercentage * 100.0:.1f}%, quality_weight={params.qualityWeight:.2f}, tabu_threshold={params.tabuThreshold}"
    echo ""
  
  # Initialize population with diverse solutions
  if params.verbose:
    echo "Generating initial population..."
  
  let initialSystems = generateInitialPopulation(system, params.populationSize)
  var population = newPopulation[T](params.populationSize, system.assignment.len, params.minDiversityThreshold)
  
  # Add initial systems to population
  population.initializePopulation(initialSystems)
  
  if params.verbose:
    echo fmt"Initial population created: {population.members.len} members"
    let initialStats = population.calculateStats()
    initialStats.printStats()
    echo ""
  
  # Main search loop
  var generation = 0
  var bestEverFound = false
  
  while generation < params.maxGenerations:
    generation += 1
    population.generation = generation
    
    # Select pairs for path relinking (most diverse first)
    let pairs = population.selectPairsForRelinking(params.maxPairsPerGeneration)
    
    if pairs.len == 0:
      if params.verbose:
        echo "No suitable pairs for relinking - terminating"
      break
    
    # Perform path relinking to generate intermediate states
    let (intermediateStates, relinkingStats) = performPathRelinking(
      population, system, pairs, params.relinkingParams
    )
    
    if intermediateStates.len == 0:
      if params.verbose:
        echo "No intermediate states generated - continuing"
      continue
    
    # Create systems for batch improvement
    var systemsForImprovement: seq[ConstraintSystem[T]] = @[]
    for state in intermediateStates:
      var newSystem = system.deepCopy()
      newSystem.assignment = state
      systemsForImprovement.add(newSystem)
    
    # Batch improve all intermediate states using existing tabu search
    let improvedStates = batchImprove(systemsForImprovement, params.tabuThreshold, false)
    
    # Convert improved states back to population members
    var newCandidates: seq[PopulationMember[T]] = @[]
    var statesImproved = 0
    
    for i, tabuState in improvedStates:
      let cost = tabuState.cost
      
      # Calculate violations using constraint initialization
      var workingSystem = system.deepCopy()
      workingSystem.assignment = tabuState.assignment
      
      # Initialize all constraints with the new assignment
      for constraint in workingSystem.baseArray.constraints:
        constraint.initialize(workingSystem.assignment)
      
      let violations = getViolatedConstraints(workingSystem)
      
      if cost == 0 and params.earlyTermination:
        # Solution found!
        let elapsedTime = epochTime() - startTime
        if params.verbose:
          echo fmt"✓ SOLUTION FOUND in generation {generation}!"
          echo fmt"  Cost: {cost}, Time: {elapsedTime:.2f}s"
        
        return SearchResult[T](
          solved: true,
          bestCost: cost,
          bestAssignment: tabuState.assignment,
          generations: generation,
          totalEvaluations: population.totalEvaluations,
          elapsedTime: elapsedTime
        )
      
      # Check if this state improved from its starting point
      # Calculate original cost of the intermediate state before improvement
      if i < intermediateStates.len:
        var originalSystem = system.deepCopy()
        originalSystem.assignment = intermediateStates[i]
        
        # Initialize constraints with original intermediate state
        for constraint in originalSystem.baseArray.constraints:
          constraint.initialize(originalSystem.assignment)
        
        let originalCost = calculateCost(originalSystem)
        if cost < originalCost:
          statesImproved += 1
      else:
        # Fallback: consider it improved if better than population average
        let avgCost = if population.members.len > 0:
                       population.members.mapIt(it.cost).foldl(a + b, 0).float / population.members.len.float
                     else: float.high
        if cost.float < avgCost:
          statesImproved += 1
      
      let member = PopulationMember[T](
        assignment: tabuState.assignment,
        cost: cost,
        age: 0,
        constraintViolations: violations
      )
      newCandidates.add(member)
    
    # Update population with new candidates
    let improvementCount = population.updatePopulation(newCandidates, params.elitePercentage, params.qualityWeight)
    
    # Calculate and display statistics
    if params.verbose:
      var stats = population.calculateStats()
      stats.improvementCount = improvementCount
      stats.printStats()
      
      # Print relinking stats with updated success rate
      var updatedRelinkingStats = relinkingStats
      updatedRelinkingStats.statesImproved = statesImproved
      updatedRelinkingStats.successRate = if relinkingStats.intermediateStatesGenerated > 0:
                                           (statesImproved.float / relinkingStats.intermediateStatesGenerated.float) * 100.0
                                         else: 0.0
      updatedRelinkingStats.printRelinkingStats()
      echo ""
      
      # Check for convergence warnings
      if stats.diversityPercentage < 5.0:
        echo "⚠  Population critically converged - may need restart"
      elif stats.generationsSinceImprovement > params.maxGenerations div 4:
        echo "⚠  Search appears to be stagnating"
    
    # Check for early termination conditions
    if population.getBest().cost == 0 and params.earlyTermination:
      bestEverFound = true
      break
  
  # Search completed
  let elapsedTime = epochTime() - startTime
  let best = population.getBest()
  
  if params.verbose:
    echo fmt"Search completed after {generation} generations"
    echo fmt"Best cost: {best.cost}, Time: {elapsedTime:.2f}s"
    echo fmt"Total evaluations: {population.totalEvaluations}"
    
    if best.cost == 0:
      echo "✓ SOLUTION FOUND!"
    else:
      echo "Search terminated without finding optimal solution"
  
  return SearchResult[T](
    solved: best.cost == 0,
    bestCost: best.cost,
    bestAssignment: best.assignment,
    generations: generation,
    totalEvaluations: population.totalEvaluations,
    elapsedTime: elapsedTime
  )

proc resolvePopulationBased*[T](system: ConstraintSystem[T],
                               populationSize: int = 20,
                               maxGenerations: int = 100,
                               tabuThreshold: int = 1000,
                               verbose: bool = false) =
  var params = newPopulationSearchParams()
  params.populationSize = populationSize
  params.maxGenerations = maxGenerations
  params.tabuThreshold = tabuThreshold
  params.verbose = verbose
  
  let result = populationSearch(system, params)
  
  # Update the original system with the best solution found
  system.assignment = result.bestAssignment
  
  if verbose:
    if result.solved:
      echo "Population search succeeded!"
    else:
      echo fmt"Population search completed with best cost: {result.bestCost}"