include "globals.mzn";

% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Variables
% TODO: check the correctness of these bounds 
int: l_low = min(col(CIRCUITS, 2));
int: l_up = sum(col(CIRCUITS, 2));
var l_low..l_up: l;

% Use 2 different arrays for the coordinates in order to give different bounds
array [1..N] of var 0..W-min(col(CIRCUITS, 1)): coord_x;
array [1..N] of var 0..l_up-min(col(CIRCUITS, 2)): coord_y;


%%%%%%%% CONSTRAINTS %%%%%%%%

% Avoid overlapping between the circuits
constraint diffn(coord_x, coord_y, col(CIRCUITS, 1), col(CIRCUITS, 2));
% Constrain the circuits within the available area
constraint forall(i in 1..N)(coord_x[i] + CIRCUITS[i, 1] <= W /\ coord_y[i] + CIRCUITS[i, 2] <= l);

% TODO: is there another way to run a search for 2 arrays?
solve :: seq_search([
             int_search(coord_x, first_fail, indomain_min),
             int_search(coord_y, input_order, indomain_min)])
      minimize l;

output ["- The max height is \(l).\n- The coordinates are:\n"];
output ["\t\(CIRCUITS[i,1]) \(CIRCUITS[i,2]), \(coord_x[i]) \(coord_y[i])\n" | i in 1..N];