% Crusher: native fzn_regular — prevent decomposition into state variables.
% FlatZinc builtins require 1D arrays, so convert 2D transition table to 1D.
predicate fzn_regular(array [int] of var int: x, int: Q, int: S, array [int] of int: d, int: q0, set of int: F);

predicate fzn_regular(array [int] of var int: x, int: Q, int: S, array [int, int] of int: d, int: q0, set of int: F) =
    fzn_regular(x, Q, S, array1d(d), q0, F);
