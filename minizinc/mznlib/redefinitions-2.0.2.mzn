% Override standard 2.0.2 decompositions for Crusher.
% This file REPLACES the standard redefinitions-2.0.2.mzn, so we must
% include all decompositions we want to keep.

% Symmetry breaking is counterproductive for local search.
predicate symmetry_breaking_constraint(var bool: b) = true;

% Redundant constraints help guide local search — keep them.
predicate redundant_constraint(var bool: b) = b;

% Standard element decompositions (must be included since we override this file).
predicate array_var_bool_element_nonshifted(var int: idx, array [int] of var bool: x, var bool: c) =
  array_var_bool_element((idx - (min(index_set(x)) - 1)) :: domain, array1d(x), c);

predicate array_var_int_element_nonshifted(var int: idx, array [int] of var int: x, var int: c) =
  array_var_int_element((idx - (min(index_set(x)) - 1)) :: domain, array1d(x), c);

predicate array_var_float_element_nonshifted(
  var int: idx,
  array [int] of var float: x,
  var float: c,
) = array_var_float_element((idx - (min(index_set(x)) - 1)) :: domain, array1d(x), c);

predicate array_var_set_element_nonshifted(
  var int: idx,
  array [int] of var set of int: x,
  var set of int: c,
) = array_var_set_element((idx - (min(index_set(x)) - 1)) :: domain, array1d(x), c);
