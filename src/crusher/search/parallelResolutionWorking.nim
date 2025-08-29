import std/[os, strformat, atomics]
import std/typedthreads

import heuristics, tabuSearch
import ../constraintSystem

type 
  SharedResult*[T] = object
    solved*: Atomic[bool]
    solutionFound*: Atomic[bool] 
    bestCost*: Atomic[int]
    solutionWorkerId*: Atomic[int]
    assignment*: seq[T]  # Protected by solved flag

  WorkerParams*[T] = object
    systemCopy*: ConstraintSystem[T]
    threshold*: int
    result*: ptr SharedResult[T]
    workerId*: int

proc tabuSearchWorker*[T](params: WorkerParams[T]) {.thread.} =
  ## Worker thread that performs tabu search and updates shared result
  try:
    echo fmt"Worker {params.workerId} starting tabu search"
    
    # DEBUGGING: Verify each worker has independent constraint instances
    when defined(debugCostCalculation):
      echo fmt"Worker {params.workerId} has {params.systemCopy.baseArray.constraints.len} constraints"
      for i, constraint in params.systemCopy.baseArray.constraints:
        echo fmt"Worker {params.workerId} constraint {i} address: {cast[int](constraint.unsafeAddr)}"
    
    # Create termination check function
    proc shouldTerminate(): bool {.gcsafe.} = params.result.solutionFound.load()
    
    let improved = params.systemCopy.baseArray.tabuImproveWithTermination(params.threshold, shouldTerminate)
    
    echo fmt"Worker {params.workerId} completed with cost {improved.cost}"
    
    # Check if we found a perfect solution
    if improved.cost == 0:
      # DEBUGGING: Double-check the cost by re-evaluating the assignment
      params.systemCopy.assignment = improved.assignment
      
      # Recalculate total cost by summing all constraint penalties
      var actualCost = 0
      for constraint in params.systemCopy.baseArray.constraints:
        actualCost += constraint.penalty()
      
      echo fmt"Worker {params.workerId} reports cost 0, actual re-evaluated cost: {actualCost}"
      
      if actualCost != 0:
        echo fmt"Worker {params.workerId} ERROR: Cost mismatch! Reported 0 but actual is {actualCost}"
        # Don't claim this as a perfect solution
        return
      
      # Try to claim the solution using solutionFound flag
      let wasAlreadyFound = params.result.solutionFound.exchange(true)
      if not wasAlreadyFound:  # We're the first to find a perfect solution
        echo fmt"Worker {params.workerId} found verified perfect solution!"
        
        # We have exclusive access to update the assignment
        # Create a temporary copy to ensure atomic assignment update
        var tempAssignment = newSeq[T](improved.assignment.len)
        for i in 0..<improved.assignment.len:
          tempAssignment[i] = improved.assignment[i]
        
        # Atomically replace the assignment (single pointer operation)
        params.result.assignment = tempAssignment
        
        # Set remaining atomic flags
        params.result.bestCost.store(0)
        params.result.solutionWorkerId.store(params.workerId)
        params.result.solved.store(true)  # Mark as solved
        
        echo fmt"Worker {params.workerId} successfully stored verified perfect solution!"
        return
      else:
        echo fmt"Worker {params.workerId} found perfect solution but another worker already claimed it"
        return
    
    # Update best cost if we found an improvement
    var currentBest = params.result.bestCost.load()
    while improved.cost < currentBest:
      let swapped = params.result.bestCost.compareExchange(currentBest, improved.cost)
      if swapped:
        echo fmt"Worker {params.workerId} found new best cost: {improved.cost}"
        # Don't update assignment for non-perfect solutions to avoid race conditions
        break
      currentBest = params.result.bestCost.load()
        
  except Exception as e:
    echo fmt"Worker {params.workerId} failed: {e.msg}"

proc resolveParallelWorking*[T](system: ConstraintSystem[T],
                               initialTabuThreshold=32,
                               maxAttempts=10,
                               attemptThreshold=10,
                               numWorkers=4) = 
  ## Working parallel resolution using typedthreads and shared memory
  
  var lastImprovement = 0
  var bestAttempt = high(int)
  var bestSolution: seq[T]
  var attempt = 0
  var currentTabuThreshold = initialTabuThreshold

  # Use the same sequential search structure as the original, but parallelize each attempt
  for improved in system.baseArray.sequentialSearch(currentTabuThreshold, maxAttempts):
    attempt += 1
    echo fmt"Parallel attempt {attempt} starting with {numWorkers} workers"

    if improved.cost == 0:
      system.assignment = improved.assignment
      return

    # Create shared result structure
    var sharedResult = SharedResult[T](assignment: @[])
    sharedResult.solved.store(false)
    sharedResult.solutionFound.store(false)
    sharedResult.bestCost.store(high(int))
    sharedResult.solutionWorkerId.store(-1)
    
    # Create worker parameters and launch threads
    var threads: seq[Thread[WorkerParams[T]]]
    threads.setLen(numWorkers)
    
    for i in 0..<numWorkers:
      var systemCopy = system.deepCopy()  # Deep copy the constraint system for thread safety
      systemCopy.assignment = improved.assignment  # Start from current best
      
      let params = WorkerParams[T](
        systemCopy: systemCopy,
        threshold: currentTabuThreshold,
        result: sharedResult.addr,
        workerId: i
      )
      createThread(threads[i], tabuSearchWorker, params)
    
    # Wait for perfect solution or all workers to complete
    var solutionFound = false
    while not solutionFound:
      if sharedResult.solutionFound.load():
        let workerId = sharedResult.solutionWorkerId.load()
        echo fmt"Perfect solution found by worker {workerId}!"
        system.assignment = sharedResult.assignment
        solutionFound = true
        break
      
      # Check if all threads are done
      var allDone = true
      for thread in threads:
        if running(thread):
          allDone = false
          break
      
      if allDone:
        break
      else:
        sleep(50)  # Check every 50ms
    
    # Clean up threads
    for thread in threads:
      joinThread(thread)
    
    if solutionFound:
      return
    
    # Track best result from this parallel attempt
    let finalBestCost = sharedResult.bestCost.load()
    if finalBestCost < bestAttempt:
      bestAttempt = finalBestCost
      bestSolution = improved.assignment  # Use the input assignment as base
      lastImprovement = attempt
      #echo fmt"Found better solution with cost {finalBestCost}"

    # Increase tabu threshold if no improvement for a while  
    if attempt - lastImprovement > attemptThreshold:
      currentTabuThreshold += currentTabuThreshold div 4  # Increase by 25%
      echo fmt"No improvement for {attemptThreshold} batches, increasing threshold to {currentTabuThreshold}"
      lastImprovement = attempt  # Reset counter
    
    # Continue searching - don't give up until perfect solution found

proc resolveParallelSimple*[T](system: ConstraintSystem[T],
                              tabuThreshold=1000,
                              numWorkers=4) = 
  ## Parallel version that runs multiple batches until solution found
  
  echo fmt"Starting parallel resolution with {numWorkers} workers"
  
  var attempt = 0
  var bestAttempt = high(int)
  var bestSolution: seq[T]
  var lastImprovement = 0
  var currentTabuThreshold = tabuThreshold
  
  # Keep running parallel batches until we find a solution
  while true:
    attempt += 1
    echo fmt"Parallel batch {attempt} starting with {numWorkers} workers"
    
    # Create shared result structure for this batch
    var sharedResult = SharedResult[T](assignment: @[])
    sharedResult.solved.store(false)
    sharedResult.solutionFound.store(false)
    sharedResult.bestCost.store(high(int))
    sharedResult.solutionWorkerId.store(-1)
    
    # Launch worker threads for this batch
    var threads: seq[Thread[WorkerParams[T]]]
    threads.setLen(numWorkers)
    
    for i in 0..<numWorkers:
      var systemCopy = system.deepCopy()  # Each worker gets a deep copy for thread safety
      
      let params = WorkerParams[T](
        systemCopy: systemCopy,
        threshold: currentTabuThreshold,
        result: sharedResult.addr,
        workerId: i
      )
      createThread(threads[i], tabuSearchWorker, params)
    
    # Wait for first solution or all workers to complete
    while not sharedResult.solutionFound.load():
      # Check if all threads are done
      var allDone = true
      for thread in threads:
        if running(thread):
          allDone = false
          break
      
      if allDone:
        break
      else:
        sleep(50)  # Check every 50ms
    
    # Clean up threads
    for thread in threads:
      joinThread(thread)
    
    # Check if we found a perfect solution
    if sharedResult.solutionFound.load():
      let solutionWorkerId = sharedResult.solutionWorkerId.load()
      echo fmt"Perfect solution found by worker {solutionWorkerId} in batch {attempt}!"
      system.assignment = sharedResult.assignment
      return
    
    # Track best result from this batch
    let batchBestCost = sharedResult.bestCost.load()
    if batchBestCost < bestAttempt:
      bestAttempt = batchBestCost  
      if bestSolution.len == 0:
        bestSolution = system.assignment  # Use current system assignment as fallback
      lastImprovement = attempt
      echo fmt"Batch {attempt} found better solution with cost {batchBestCost}"
    
    # Adaptive tabu threshold - increase if no improvement for several attempts
    if attempt - lastImprovement > 5:
      currentTabuThreshold = currentTabuThreshold + (currentTabuThreshold div 4)  # Increase by 25%
      echo fmt"No improvement for 5 batches, increasing threshold to {currentTabuThreshold}"
      lastImprovement = attempt  # Reset counter
    
    # Continue to next batch - no limit, keep trying until solution found
