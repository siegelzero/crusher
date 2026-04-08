% Crusher-specific global constraint: forbid any three selected cells on
% an n×n grid from forming an isosceles triangle (including the degenerate
% "midpoint of two collinear cells" case).
%
% The model passes the row-major flattening of the n×n grid as `x`, and
% the side length `n` as a parameter. Crusher's FlatZinc translator
% recognises `crusher_isosceles_free` and emits a single dedicated
% constraint, which enumerates the bad triples in Nim at constraint
% construction time. This avoids the O(n^6) MiniZinc flattening blow-up
% of the parametric `forall(a, b, c) where ...` formulation.
%
% Each x[i] must be a binary {0, 1} variable; value 1 means "cell i is
% selected". Cells are indexed in row-major order: cell `i*n + j` is at
% row `i`, column `j` (0-based). When the array uses 1-based MiniZinc
% indexing (`array[1..n*n]`), the same row-major interpretation applies
% — Crusher's translator handles the 1-based-to-0-based conversion.

predicate crusher_isosceles_free(array [int] of var int: x, int: n);

predicate isosceles_free(array [int] of var int: x, int: n) =
    crusher_isosceles_free(x, n);
