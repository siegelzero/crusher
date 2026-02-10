import std/strformat

type
    PoolEntry*[T] = object
        assignment*: seq[T]
        cost*: int

    CandidatePool*[T] = object
        entries*: seq[PoolEntry[T]]
        minCost*: int
        maxCost*: int

proc distance*[T](a, b: PoolEntry[T]): int =
    ## Hamming distance between two assignments
    for i in 0..<a.assignment.len:
        if a.assignment[i] != b.assignment[i]:
            inc result

proc minDistance*[T](pool: CandidatePool[T], entry: PoolEntry[T]): int =
    ## Minimum Hamming distance from entry to any pool member
    result = high(int)
    for e in pool.entries:
        let d = distance(entry, e)
        if d < result:
            result = d

proc meanDistance*[T](pool: CandidatePool[T]): float =
    ## Mean pairwise Hamming distance across the pool
    if pool.entries.len < 2: return 0.0
    var total = 0
    var count = 0
    for i in 0..<pool.entries.len:
        for j in 0..<i:
            total += distance(pool.entries[i], pool.entries[j])
            inc count
    result = total.float / count.float

proc updateBounds*[T](pool: var CandidatePool[T]) =
    if pool.entries.len == 0:
        pool.minCost = 0
        pool.maxCost = 0
        return
    pool.minCost = high(int)
    pool.maxCost = 0
    for entry in pool.entries:
        if entry.cost < pool.minCost:
            pool.minCost = entry.cost
        if entry.cost > pool.maxCost:
            pool.maxCost = entry.cost

proc replaceMostSimilar*[T](pool: var CandidatePool[T], entry: PoolEntry[T]) =
    ## Replace the most similar entry with worse-or-equal cost (diversity-preserving)
    var
        minDist = high(int)
        minIndex = -1

    for i in 0..<pool.entries.len:
        if entry.cost <= pool.entries[i].cost:
            let d = distance(entry, pool.entries[i])
            if d < minDist:
                minDist = d
                minIndex = i

    if minIndex >= 0:
        pool.entries[minIndex] = entry
        pool.updateBounds()

proc replaceMaxCost*[T](pool: var CandidatePool[T], entry: PoolEntry[T]) =
    ## Replace the worst entry in the pool
    var maxIndex = 0
    for i in 1..<pool.entries.len:
        if pool.entries[i].cost > pool.entries[maxIndex].cost:
            maxIndex = i

    if entry.cost < pool.entries[maxIndex].cost:
        pool.entries[maxIndex] = entry
        pool.updateBounds()

proc update*[T](pool: var CandidatePool[T], entries: seq[PoolEntry[T]]) =
    ## Batch diversity-preserving replacement
    for e in entries:
        pool.replaceMostSimilar(e)

iterator pairs*[T](pool: CandidatePool[T]): (int, int) =
    ## Iterator over all unique (i, j) index pairs
    for i in 0..<pool.entries.len:
        for j in 0..<i:
            yield (i, j)

proc poolStatistics*[T](pool: CandidatePool[T], verbose: bool = true) =
    if not verbose or pool.entries.len == 0:
        return
    var poolSum = 0
    for e in pool.entries:
        poolSum += e.cost
    let avgDist = pool.meanDistance()
    echo &"[Pool] size={pool.entries.len} min={pool.minCost} mean={float(poolSum) / float(pool.entries.len):.1f} max={pool.maxCost} diversity={avgDist:.1f}"
