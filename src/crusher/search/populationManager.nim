import std/[sequtils, algorithm, random, math, strformat, sugar]
import ../constraintSystem
import ../constraints/stateful

type
  PopulationMember*[T] = object
    assignment*: seq[T]
    cost*: int
    age*: int
    constraintViolations*: seq[int]

  PopulationStats*[T] = object
    generation*: int
    totalEvaluations*: int
    size*: int
    minCost*: int
    maxCost*: int
    meanCost*: float
    medianCost*: int
    bestEverCost*: int
    avgHammingDistance*: float
    diversityPercentage*: float
    minDiversity*: int
    maxDiversity*: int
    improvementCount*: int
    generationsSinceImprovement*: int
    avgAge*: float

  Population*[T] = ref object
    members*: seq[PopulationMember[T]]
    maxSize*: int
    minDiversityThreshold*: int
    assignmentLength*: int
    bestEverCost*: int
    generation*: int
    generationsSinceImprovement*: int
    totalEvaluations*: int

proc newPopulation*[T](maxSize: int, assignmentLength: int, minDiversityThreshold: int = 10): Population[T] =
  Population[T](
    members: newSeq[PopulationMember[T]](),
    maxSize: maxSize,
    assignmentLength: assignmentLength,
    minDiversityThreshold: minDiversityThreshold,
    bestEverCost: int.high,
    generation: 0,
    generationsSinceImprovement: 0,
    totalEvaluations: 0
  )

proc hammingDistance*[T](assign1, assign2: seq[T]): int =
  result = 0
  for i in 0..<assign1.len:
    if assign1[i] != assign2[i]:
      result += 1

proc diversityScore*[T](candidate: seq[T], population: seq[PopulationMember[T]]): float =
  if population.len == 0:
    return float.high
  
  var totalDistance = 0
  for member in population:
    totalDistance += hammingDistance(candidate, member.assignment)
  return totalDistance.float / population.len.float

proc isTooSimilar*[T](pop: Population[T], candidate: seq[T]): bool =
  for member in pop.members:
    if hammingDistance(candidate, member.assignment) < pop.minDiversityThreshold:
      return true
  return false

proc calculateStats*[T](pop: Population[T]): PopulationStats[T] =
  if pop.members.len == 0:
    return PopulationStats[T]()
  
  let costs = pop.members.mapIt(it.cost)
  let ages = pop.members.mapIt(it.age.float)
  
  # Optimize: Only calculate diversity if we have multiple members
  var avgHammingDistance = 0.0
  if pop.members.len > 1:
    var totalHammingDistance = 0
    var pairCount = 0
    for i in 0..<pop.members.len:
      for j in i+1..<pop.members.len:
        totalHammingDistance += hammingDistance(pop.members[i].assignment, pop.members[j].assignment)
        pairCount += 1
    
    avgHammingDistance = if pairCount > 0: totalHammingDistance.float / pairCount.float else: 0.0
  let diversityPercentage = (avgHammingDistance / pop.assignmentLength.float) * 100.0
  
  var sortedCosts = costs
  sortedCosts.sort()
  
  var minDist = 0
  var maxDist = 0
  if pop.members.len > 1:
    minDist = int.high
    for i in 0..<pop.members.len:
      for j in i+1..<pop.members.len:
        let dist = hammingDistance(pop.members[i].assignment, pop.members[j].assignment)
        minDist = min(minDist, dist)
        maxDist = max(maxDist, dist)
    
    if minDist == int.high:
      minDist = 0
  
  PopulationStats[T](
    generation: pop.generation,
    totalEvaluations: pop.totalEvaluations,
    size: pop.members.len,
    minCost: costs.min(),
    maxCost: costs.max(),
    meanCost: costs.foldl(a + b, 0).float / costs.len.float,
    medianCost: sortedCosts[sortedCosts.len div 2],
    bestEverCost: pop.bestEverCost,
    avgHammingDistance: avgHammingDistance,
    diversityPercentage: diversityPercentage,
    minDiversity: minDist,
    maxDiversity: maxDist,
    improvementCount: 0, # Will be set by caller
    generationsSinceImprovement: pop.generationsSinceImprovement,
    avgAge: ages.foldl(a + b, 0.0) / ages.len.float
  )

proc printStats*[T](stats: PopulationStats[T]) =
  echo fmt"Generation {stats.generation} [Evals: {stats.totalEvaluations}]"
  echo fmt"├─ Population: Cost=[{stats.minCost}-{stats.maxCost}] μ={stats.meanCost:.1f} med={stats.medianCost} | Best: {stats.bestEverCost}"
  echo fmt"├─ Diversity: μ={stats.avgHammingDistance:.1f} ({stats.diversityPercentage:.1f}%) range=[{stats.minDiversity}-{stats.maxDiversity}]"
  echo fmt"└─ Progress: +{stats.improvementCount} improved, {stats.generationsSinceImprovement} gens since best, avg age {stats.avgAge:.1f}"
  
  if stats.diversityPercentage < 10.0:
    echo "⚠  Population converging - diversity critically low"
  elif stats.generationsSinceImprovement > 10:
    echo "⚠  Search stagnating - consider restart"

proc addMember*[T](pop: Population[T], assignment: seq[T], cost: int, constraintViolations: seq[int] = @[]): bool =
  if pop.isTooSimilar(assignment):
    return false
  
  let member = PopulationMember[T](
    assignment: assignment,
    cost: cost,
    age: 0,
    constraintViolations: constraintViolations
  )
  
  pop.members.add(member)
  pop.totalEvaluations += 1
  
  if cost < pop.bestEverCost:
    pop.bestEverCost = cost
    pop.generationsSinceImprovement = 0
  
  return true

proc selectionScore*[T](pop: Population[T], member: PopulationMember[T], qualityWeight: float = 0.7): float =
  # Protect against division by zero
  let normalizedCost = if pop.bestEverCost > 0: 
                        member.cost.float / pop.bestEverCost.float 
                      else: 
                        if member.cost == 0: 0.0 else: 1.0
  
  let memberDiversityScore = diversityScore(member.assignment, pop.members)
  let normalizedDiversity = if pop.assignmentLength > 0: 
                             memberDiversityScore / pop.assignmentLength.float 
                           else: 
                             0.0
  
  return qualityWeight * (1.0 - normalizedCost) + (1.0 - qualityWeight) * normalizedDiversity

proc updatePopulation*[T](pop: Population[T], newCandidates: seq[PopulationMember[T]], 
                         elitePercentage: float = 0.2, qualityWeight: float = 0.7): int =
  var improvementCount = 0
  
  # Age existing members
  for i in 0..<pop.members.len:
    pop.members[i].age += 1
  
  # Combine all candidates (existing + new)
  var allCandidates = pop.members & newCandidates
  
  for candidate in newCandidates:
    pop.totalEvaluations += 1
    if candidate.cost < pop.bestEverCost:
      pop.bestEverCost = candidate.cost
      pop.generationsSinceImprovement = 0
      improvementCount += 1
    elif candidate.cost <= pop.members.mapIt(it.cost).min():
      improvementCount += 1
  
  allCandidates.sort(proc(a, b: PopulationMember[T]): int = cmp(a.cost, b.cost))
  
  let eliteCount = max(1, int(pop.maxSize.float * elitePercentage))
  var newPopulation = allCandidates[0..<min(eliteCount, allCandidates.len)]
  
  if newPopulation.len < pop.maxSize:
    var remaining = allCandidates[newPopulation.len..^1]
    remaining.sort(proc(a, b: PopulationMember[T]): int = 
      cmp(pop.selectionScore(b, qualityWeight), pop.selectionScore(a, qualityWeight)))
    
    let needed = pop.maxSize - newPopulation.len
    for i in 0..<min(needed, remaining.len):
      if not pop.isTooSimilar(remaining[i].assignment) or newPopulation.len < pop.maxSize div 2:
        newPopulation.add(remaining[i])
  
  pop.members = newPopulation[0..<min(pop.maxSize, newPopulation.len)]
  pop.generation += 1
  
  if improvementCount == 0:
    pop.generationsSinceImprovement += 1
  
  return improvementCount

proc selectPairsForRelinking*[T](pop: Population[T], maxPairs: int = -1): seq[(int, int)] =
  if pop.members.len < 2:
    return @[]
  
  var pairs: seq[(int, int, int)] # (i, j, distance)
  
  for i in 0..<pop.members.len:
    for j in i+1..<pop.members.len:
      let distance = hammingDistance(pop.members[i].assignment, pop.members[j].assignment)
      pairs.add((i, j, distance))
  
  pairs.sort(proc(a, b: (int, int, int)): int = cmp(b[2], a[2]))
  
  let numPairs = if maxPairs > 0: min(maxPairs, pairs.len) else: pairs.len
  result = newSeq[(int, int)](numPairs)
  
  for i in 0..<numPairs:
    result[i] = (pairs[i][0], pairs[i][1])

proc calculateCost*[T](system: ConstraintSystem[T]): int =
  result = 0
  for constraint in system.baseArray.constraints:
    result += constraint.penalty()

proc getViolatedConstraints*[T](system: ConstraintSystem[T]): seq[int] =
  result = @[]
  for i, constraint in system.baseArray.constraints:
    if constraint.penalty() > 0:
      result.add(i)

proc initializePopulation*[T](pop: Population[T], systems: seq[ConstraintSystem[T]]) =
  for system in systems:
    if pop.members.len >= pop.maxSize:
      break
    
    if not pop.isTooSimilar(system.assignment):
      let cost = calculateCost(system)
      let violations = getViolatedConstraints(system)
      discard pop.addMember(system.assignment, cost, violations)

proc getBest*[T](pop: Population[T]): PopulationMember[T] =
  result = pop.members[0]
  for member in pop.members:
    if member.cost < result.cost:
      result = member

proc size*[T](pop: Population[T]): int =
  pop.members.len

proc getMember*[T](pop: Population[T], index: int): PopulationMember[T] =
  pop.members[index]

proc isEmpty*[T](pop: Population[T]): bool =
  pop.members.len == 0

proc getCurrentBestCost*[T](pop: Population[T]): int =
  if pop.isEmpty():
    return int.high
  return pop.getBest().cost