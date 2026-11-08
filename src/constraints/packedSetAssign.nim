## Safe reassignment of PackedSet fields.
##
## This Nim stdlib's `PackedSet.=copy` rebuilds the destination's trunk table
## without clearing `dest.head` first, so copying into a set that already holds
## trunks chains the old trunks onto the new list. A field reassigned on every
## move (regular/table constraints: `lastAffected = positions`) accumulates
## trunks until a later copy of it overflows the hash table and
## `while dest.data[h] != nil` probes forever (work-task-variation stalled in
## `getAffectedPositions` until the watchdog killed the solver).
## Resetting the destination first makes the copy start from an empty chain.

import std/packedsets

proc assignSet*[A](dest: var PackedSet[A], src: PackedSet[A]) {.inline.} =
    dest = initPackedSet[A]()
    dest = src
