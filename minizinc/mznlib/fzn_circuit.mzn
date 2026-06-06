% Crusher implements circuit as a native global (crusher_circuit). The standard
% `circuit` predicate calls fzn_circuit(index2int(enum2int(x))), which reindexes
% the array to 1-based but leaves the successor *values* in the original index
% set. For a non-1-based index set (e.g. an array indexed 2..5 whose successors
% are also in 2..5) that value offset would otherwise be invisible to the
% backend, which would mis-read the constraint as a 1-based circuit. Tightening
% each successor to index_set(x) pins its domain to the node set, so the backend
% recovers the offset from the variable domains.
predicate crusher_circuit(array [int] of var int: x);

predicate fzn_circuit(array [int] of var int: x) =
  forall (i in index_set(x)) (x[i] in index_set(x))
  /\ crusher_circuit(x);
