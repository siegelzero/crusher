import unittest, times, sequtils, algorithm
import ../src/crusher
import ../src/search/parallelResolution
import ../src/search/tabu

proc testParallelMagicSquare() =
    # Test parallel search on a 3x3 magic square
    var system = initConstraintSystem[int]()
    let magic_square = newConstrainedMatrix[int](system, 3, 3)

    # Set domain to 1-9 for all cells
    system.baseArray.setDomain([1, 2, 3, 4, 5, 6, 7, 8, 9])

    # All cells must be different
    system.addConstraint(magic_square.allDifferent())

    # All rows sum to 15
    for row in magic_square.rows:
        system.addConstraint(sum(row) == 15)

    # All columns sum to 15
    for col in magic_square.columns:
        system.addConstraint(sum(col) == 15)

    # Test parallel resolution using resolve with parallel=true and verbose=true
    let start_time = cpuTime()
    resolve(system, tabuThreshold=5000, parallel=true, populationSize=8, numWorkers=2, verbose=true)
    let parallel_time = cpuTime() - start_time
    let solution = system.assignment

    # Verify solution is valid
    check(solution.len == 9)

    # Verify all different
    let unique_values = toSeq(1..9)
    check(sorted(solution) == unique_values)

    # Verify magic square properties
    let matrix = @[
        @[solution[0], solution[1], solution[2]],
        @[solution[3], solution[4], solution[5]],
        @[solution[6], solution[7], solution[8]]
    ]

    # Check rows sum to 15
    for row in matrix:
        let rowSum = row[0] + row[1] + row[2]
        check(rowSum == 15)

    # Check columns sum to 15
    for col in 0..2:
        check(matrix[0][col] + matrix[1][col] + matrix[2][col] == 15)

    echo "Parallel magic square solution found in ", parallel_time, " seconds"
    echo "Solution: ", solution

proc testParallelResolve() =
    # Test parallelResolve directly with a simple problem
    var system = initConstraintSystem[int]()
    let sequence = newConstrainedSequence[int](system, 4)
    sequence.setDomain([1, 2, 3, 4])
    system.addConstraint(sequence.allDifferent())

    # Test parallelResolve directly
    echo "Testing parallelResolve with verbose logging:"
    parallelResolve(system, populationSize=8, numWorkers=2, tabuThreshold=1000, verbose=true)

    # Check that a solution was found
    check(system.assignment.len == 4)

    # Verify the solution is valid (all different values 1-4)
    let sortedSolution = sorted(system.assignment)
    check(sortedSolution == @[1, 2, 3, 4])

    echo "ParallelResolve test passed"

proc testWorkerCountDetection() =
    # Test automatic worker count detection
    let optimal = getOptimalWorkerCount()
    check(optimal >= 1)
    check(optimal <= 8)  # Capped at 8
    echo "Detected optimal worker count: ", optimal

proc testParallelVsSequential() =
    # Compare parallel vs sequential on a harder problem
    var system = initConstraintSystem[int]()
    let sequence = newConstrainedSequence[int](system, 6)
    sequence.setDomain([1, 2, 3, 4, 5, 6])
    system.addConstraint(sequence.allDifferent())

    # Sequential test
    if system.baseArray.reducedDomain.len == 0:
        system.baseArray.reducedDomain = reduceDomain(system.baseArray)

    let start_seq = cpuTime()
    let sequential_result = system.baseArray.tabuImprove(5000)
    let seq_time = cpuTime() - start_seq

    # Parallel test with verbose logging
    let system2 = system.deepCopy()
    let start_par = cpuTime()
    echo "Testing parallel vs sequential with verbose logging:"
    resolve(system2, tabuThreshold=5000, parallel=true, populationSize=4, numWorkers=2, verbose=true)
    let par_time = cpuTime() - start_par

    check(sequential_result.bestCost == 0)
    check(system2.assignment.len == 6)

    echo "Sequential time: ", seq_time, " seconds"
    echo "Parallel time: ", par_time, " seconds"

suite "Parallel Search Tests":
    test "Magic Square Parallel Resolution":
        testParallelMagicSquare()

    test "Parallel Resolve Functionality":
        testParallelResolve()

    test "Worker Count Detection":
        testWorkerCountDetection()

    test "Parallel vs Sequential Comparison":
        testParallelVsSequential()

when isMainModule:
    echo "Running parallel search tests..."
    # Note: These tests require --threads:on --mm:arc compilation flags
    echo "Compile with: nim c -r --threads:on --mm:arc -d:release test_parallel_search.nim"