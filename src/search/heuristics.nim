import std/[cpuinfo, strformat, threadpool]

import ../constrainedArray
import ../state/arrayState
import tabuSearch


iterator parallelSearch*[T](carray: ConstrainedArray[T], tabuThreshold: int): ArrayState[T] =
    let N = countProcessors()
    var jobs = newSeq[FlowVarBase](N)
    var idx: int
    var res: ArrayState[T]

    for i in 0..<N:
        jobs[i] = spawn carray.tabuImprove(tabuThreshold)
    
    while jobs.len > 0:
        idx = blockUntilAny(jobs)
        res = ^FlowVar[ArrayState[T]](jobs[idx])
        yield res
        jobs.del(idx)
        if res.cost == 0:
            break


proc hybrid*[T](carray: ConstrainedArray[T], tabuThreshold: int): ArrayState[T] =
    var initial: seq[ArrayState[T]]

    for improved in carray.parallelSearch(tabuThreshold):
        if improved.cost == 0:
            return improved
        initial.add(improved)

    doAssert initial.len >= 2
    echo fmt"initial population: {initial.len}"

    var A, B: ArrayState[T]
    A = initial.pop()
    B = initial.pop()

    echo fmt"Found {A.cost} -- {B.cost}"

    return A