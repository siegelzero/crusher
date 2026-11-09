% Native optional-task disjunctive: task i (start s[i], duration d[i]) takes
% part only when o[i] holds; present tasks with d[i] > 0 must not overlap.
% Zero-duration tasks are unconstrained (non-strict semantics).
predicate crusher_disjunctive_opt(array [int] of var int: s,
                                  array [int] of var bool: o,
                                  array [int] of var int: d);
