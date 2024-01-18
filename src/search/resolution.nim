import heuristics
import ../constraintSystem


proc resolve*[T](system: ConstraintSystem[T], threshold = 1000) =
    # for improved in system.baseArray.parallelSearch(threshold):
    #     doAssert improved.cost == 0
    #     system.assignment = improved.assignment

    var improved = system.baseArray.hybrid(threshold)
    doAssert improved.cost == 0
    system.assignment = improved.assignment