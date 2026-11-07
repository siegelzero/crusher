## Shared immutable element arrays for channel bindings (see SharedElems).
## Re-exported by constrainedArray: generic `for` loops resolve the implicit
## `items` at the instantiation site, so the accessors must be visible wherever
## ConstrainedArray is used.

import elementState

type
    SharedElems*[T] = object
        ## Immutable, process-lifetime array of ArrayElements shared by every
        ## copy of a channel binding. Element tables (e.g. flattened distance
        ## matrices) can total tens of millions of entries; as a plain seq each
        ## per-worker ConstrainedArray copy duplicated them (716MiB per copy on
        ## surface-based-tsp ch130). A raw pointer is copied for free and, unlike
        ## a ref, involves no (non-atomic) refcounting across worker threads.
        ## Never freed: bindings live until process exit.
        data: ptr UncheckedArray[ArrayElement[T]]
        n: int


################################################################################
# SharedElems accessors (seq-like, read-only)
################################################################################

proc toSharedElems*[T](s: openArray[ArrayElement[T]]): SharedElems[T] =
    result.n = s.len
    if s.len > 0:
        result.data = cast[ptr UncheckedArray[ArrayElement[T]]](
            allocShared0(sizeof(ArrayElement[T]) * s.len))
        for i in 0..<s.len: result.data[i] = s[i]

func len*[T](a: SharedElems[T]): int {.inline.} = a.n
func high*[T](a: SharedElems[T]): int {.inline.} = a.n - 1
func `[]`*[T](a: SharedElems[T], i: int): ArrayElement[T] {.inline.} =
    when compileOption("boundChecks"):
        if i < 0 or i >= a.n:
            raise newException(IndexDefect, "SharedElems index " & $i & " out of 0.." & $(a.n - 1))
    a.data[i]
func `[]`*[T](a: SharedElems[T], i: BackwardsIndex): ArrayElement[T] {.inline.} =
    a[a.n - int(i)]
iterator items*[T](a: SharedElems[T]): ArrayElement[T] =
    for i in 0..<a.n: yield a.data[i]
iterator pairs*[T](a: SharedElems[T]): (int, ArrayElement[T]) =
    for i in 0..<a.n: yield (i, a.data[i])
proc toElemSeq*[T](a: SharedElems[T]): seq[ArrayElement[T]] =
    result = newSeq[ArrayElement[T]](a.n)
    for i in 0..<a.n: result[i] = a.data[i]

