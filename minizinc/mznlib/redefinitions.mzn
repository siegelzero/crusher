% Crusher solver redefinitions
% This file tells MiniZinc which global constraints Crusher supports natively.
% Native constraints are used directly instead of being decomposed.

% Override standard decomposition of minimum/maximum into int_min/int_max chains.
% Crusher handles these as native array-level constraints.
predicate array_int_minimum(var int: m, array [int] of var int: x);
predicate array_int_maximum(var int: m, array [int] of var int: x);
