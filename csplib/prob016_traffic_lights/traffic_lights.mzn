%
% Traffic lights problem in MiniZinc.
% CSPLib Problem 016
%
% http://www.csplib.org/Problems/prob016
% """
% Specification:
% Consider a four way traffic junction with eight traffic lights. Four of
% the traffic lights are for the vehicles and can be represented by the
% variables V1 to V4 with domains
% {r,ry,g,y} (for red, red-yellow, green and yellow).
%  The other four traffic lights are for the pedestrians and can be
%  represented by the variables P1 to P4 with domains {r,g}.
%
% The constraints on these variables can be modelled by quaternary
% constraints on
% (Vi, Pi, Vj, Pj) for 1<=i<=4, j=(1+i)mod 4 which allow just the tuples
% {(r,r,g,g), (ry,r,y,r), (g,g,r,r), (y,r,ry,r)}.
%
% Results
% Only 2^2 out of the 2^12 possible assignments are solutions.
%
% (V1,P1,V2,P2,V3,P3,V4,P4) =
%    {(r,r,g,g,r,r,g,g), (ry,r,y,r,ry,r,y,r),
%     (g,g,r,r,g,g,r,r), (y,r,ry,r,y,r,ry,r)}
% """
%
% The problem has relatively few constraints, but each is very tight.
% Local propagation appears to be rather ineffective on this problem.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% Licenced under CC-BY-4.0 : http://creativecommons.org/licenses/by/4.0/

include "globals.mzn";

int: n = 4;
int: r  = 1; % red
int: ry = 2; % red-yellow
int: g  = 3; % green
int: y  = 4; % yellow

set of int: Cars = {r, ry, g, y};
set of int: Pedestrians = {r, g};

% Allowed tuples: (Vi, Pi, Vj, Pj)
array[1..4, 1..4] of Cars: allowed;

array[1..n] of var Cars: V;
array[1..n] of var Pedestrians: P;

solve satisfy;

constraint
 forall(i in 1..n, j in 1..n where j = (1+i) mod 4) (
   table([V[i], P[i], V[j], P[j]], allowed)
 )
;

allowed = array2d(1..4, 1..4,
[
 r,  r,  g,  g,
 ry, r,  y,  r,
 g,  g,  r,  r,
 y,  r,  ry, r
]);

output [
 "V = " ++ show(V) ++ "\n" ++
 "P = " ++ show(P) ++ "\n"
];
