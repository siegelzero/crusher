import std/[packedsets, sequtils]
import constrainedArray


proc enumerate2[T](arr: var ConstrainedArray[T]) =
    var constraintMap: seq[seq[Constraint[T]]]
    for i in 0..<arr.len:
        constraintMap.add(@[])

    for cons in arr.constraints:
        constraintMap[max(toSeq cons.positions)].add(cons)
    
    var solutions: seq[seq[T]]

    proc backtrack(idx: int, arr: var ConstrainedArray[T]) =
        if idx == arr.len:
            solutions.add(arr.currentAssignment())
            echo arr.currentAssignment()
        else:
            for d in arr.domain[idx]:
                arr.assignValue(idx, d)

                var ok = true
                for cons in constraintMap[idx]:
                    if not cons.satisfied():
                        ok = false
                        break
                
                if ok:
                    backtrack(idx + 1, arr)

    backtrack(0, arr)
    echo len(solutions)


proc sendMoreMoney() =
    let
        S = 0
        E = 1
        N = 2
        D = 3
        M = 4
        O = 5
        R = 6
        Y = 7

        n = 8
    
    var value = initConstrainedArray[int](n)
    value.setDomain(toSeq 0..9)
    value.allDifferent()

    var 
        send = 1000*value[S] + 100*value[E] + 10*value[N] + value[D]
        more = 1000*value[M] + 100*value[O] + 10*value[R] + value[E]
        money = 10000*value[M] + 1000*value[O] + 100*value[N] + 10*value[E] + value[Y]
    
    value.addConstraint(send + more == money)
    value.addConstraint(value[S] > 0)
    value.addConstraint(value[M] > 0)

    value.enumerate2()

when isMainModule:
    sendMoreMoney()