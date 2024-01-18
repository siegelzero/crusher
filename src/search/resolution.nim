import heuristics
import ../constraintSystem


proc resolve*[T](system: ConstraintSystem[T], threshold = 10000) =
    for improved in system.baseArray.parallelSearch(threshold):
        if improved.cost == 0:
            system.assignment = improved.assignment