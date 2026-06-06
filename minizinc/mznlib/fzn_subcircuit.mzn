% See fzn_circuit.mzn for why the successor values are tightened to the index
% set before delegating to the native global: it makes the value offset of a
% non-1-based index set recoverable from the variable domains. For subcircuit a
% node that is not on the circuit maps to itself (x[i] = i), which is still
% within index_set(x), so the same tightening is valid.
predicate crusher_subcircuit(array [int] of var int: x);

predicate fzn_subcircuit(array [int] of var int: x) =
  forall (i in index_set(x)) (x[i] in index_set(x))
  /\ crusher_subcircuit(x);
