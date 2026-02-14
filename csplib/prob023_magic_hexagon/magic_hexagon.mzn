%
% Magic Hexagon in MiniZinc.
% CSPLib Problem 023
%
% A magic hexagon of order 3 consists of the numbers 1..19 arranged in a
% hexagonal pattern:
%
%        a  b  c
%       d  e  f  g
%      h  i  j  k  l
%       m  n  o  p
%        q  r  s
%
% such that all rows (in all three directions of the hexagonal grid)
% sum to the magic constant 38.
%
% There are 15 such row constraints (5 horizontal + 5 diagonal-left + 5 diagonal-right).
% It is known that the magic hexagon of order 3 is essentially unique
% (up to rotation and reflection).
%
% Model created by Hakan Kjellerstrand, hakank@bonetmail.com
% See also: http://www.hakank.org/minizinc
%

include "globals.mzn";

set of int: N = 1..19;
var N: a;
var N: b;
var N: c;
var N: d;
var N: e;
var N: f;
var N: g;
var N: h;
var N: i;
var N: j;
var N: k;
var N: l;
var N: m;
var N: n;
var N: o;
var N: p;
var N: q;
var N: r;
var N: s;

array[N] of var N: LD = [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s];

solve satisfy;

constraint
  all_different(LD) /\

  % Rows (horizontal, left to right)
  a + b + c           = 38 /\
  d + e + f + g       = 38 /\
  h + i + j + k + l   = 38 /\
  m + n + o + p       = 38 /\
  q + r + s           = 38 /\

  % Rows (diagonal, top-left to bottom-right)
  a + d + h           = 38 /\
  b + e + i + m       = 38 /\
  c + f + j + n + q   = 38 /\
  g + k + o + r       = 38 /\
  l + p + s           = 38 /\

  % Rows (diagonal, top-right to bottom-left)
  c + g + l           = 38 /\
  b + f + k + p       = 38 /\
  a + e + j + o + s   = 38 /\
  d + i + n + r       = 38 /\
  h + m + q           = 38 /\

  % Symmetry breaking (fixes one orientation)
  a < c  /\
  a < h  /\
  a < l  /\
  a < q  /\
  a < s  /\
  c < h
;

output [
  "     " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c) ++ "\n" ++
  "    " ++ show(d) ++ " " ++ show(e) ++ " " ++ show(f) ++ " " ++ show(g) ++ "\n" ++
  "   " ++ show(h) ++ " " ++ show(i) ++ " " ++ show(j) ++ " " ++ show(k) ++ " " ++ show(l) ++ "\n" ++
  "    " ++ show(m) ++ " " ++ show(n) ++ " " ++ show(o) ++ " " ++ show(p) ++ "\n" ++
  "     " ++ show(q) ++ " " ++ show(r) ++ " " ++ show(s) ++ "\n"
];
