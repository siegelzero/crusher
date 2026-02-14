% Car sequencing in MiniZinc.
% CSPLib Problem 001: Car Sequencing
%
% "A number of cars are to be produced; they are not identical,
% because different options are available as variants on the basic model.
% The assembly line has different stations which install the various options
% (air-conditioning, sun-roof, etc.).
% These stations have been designed to handle at most a certain percentage of
% the cars passing along the assembly line.
% Furthermore, the cars requiring a certain option must not be bunched together,
% otherwise the station will not be able to cope. Consequently, the cars must be
% arranged in a sequence so that the capacity of each station is never exceeded."
%
% This is based on the OPL3 model car.mod.
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@bonetmail.com
% Model modified to match CSPLib data format by Chris Mears.
% Licenced under CC-BY-4.0 : http://creativecommons.org/licenses/by/4.0/

% include "globals.mzn";
int: numclasses;
int: numoptions;
int: numcars;
set of int: Classes = 1..numclasses;
set of int: Options = 1..numoptions;
set of int: Slots = 1..numcars;

array[Classes] of int: numberPerClass;
array[Classes,Options] of int: optionsRequired;
array[Options] of int: windowSize;
array[Options] of int: optMax;

array[Options] of int: optionNumberPerClass =
    [sum(j in Classes) (numberPerClass[j] * optionsRequired[j,i]) | i in Options];

% decision variables
array[Slots] of var Classes: slot;
array[Options, Slots] of var 0..1: setup;

var int: z = sum(s in Classes) (s*slot[s]);

solve :: int_search(slot, input_order, indomain_min, complete)
  satisfy;

constraint
  % Each class has exactly the required number of cars
  forall(c in Classes) (
    sum(s in Slots) (bool2int(slot[s] = c)) = numberPerClass[c]
  )
  /\
  % Sliding window capacity constraint: in any window of size windowSize[o],
  % at most optMax[o] cars can have option o
  forall(o in Options, s in 1..numcars - windowSize[o] + 1) (
    sum(j in s..s + windowSize[o] - 1) (setup[o,j]) <= optMax[o]
  )
  /\
  % Channeling: setup[o,s] = 1 iff car in slot s requires option o
  forall(o in Options, s in Slots) (
    setup[o,s] = optionsRequired[slot[s],o]
  )
  /\
  % Redundant lower-bound constraint
  forall(o in Options, i in 1..optionNumberPerClass[o]) (
    sum(s in 1..(numcars - i * windowSize[o])) (setup[o,s]) >=
           (optionNumberPerClass[o] - i * optMax[o])
  )
;

output [
 "z: " ++ show(z) ++ "\n" ++
 "slot: " ++ show(slot) ++ "\n"
] ++
[
  if j = 1 then "\n" else " " endif ++
    show(setup[i,j])
  | i in Options, j in Slots
];
