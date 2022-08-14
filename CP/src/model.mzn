include "globals.mzn";

% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Extract widths and heights for usability 
array[1..N] of int: widths = [CIRCUITS[i, 1] | i in 1..N];
array[1..N] of int: heights = [CIRCUITS[i, 2] | i in 1..N];

% Variables
int: l_low = min(heights);
int: l_up = sum(heights);
var l_low..l_up: l;

% 2 arrays for the coordinates
array [1..N] of var 0..W-min(widths): coord_x;
array [1..N] of var 0..l_up-min(heights): coord_y;


%%%%%%%% CONSTRAINTS %%%%%%%%

% Avoid overlapping between the circuits
constraint diffn_nonstrict(coord_x, coord_y, widths, heights);

% Constrain the circuits within the available area
constraint forall(i in 1..N)(coord_x[i] + widths[i] <= W /\ coord_y[i] + heights[i] <= l);

% Find the x coordinates with 'cumulative' global constraints
constraint cumulative(coord_x, widths, heights, l);
constraint cumulative(coord_y, heights, widths, W);




solve :: seq_search([
             int_search(coord_x, first_fail, indomain_min),
             int_search(coord_y, input_order, indomain_min)])
      minimize l;

output ["- The max height is \(l).\n- The coordinates are:\n"];
output ["\t\(CIRCUITS[i,1]) \(CIRCUITS[i,2]), \(coord_x[i]) \(coord_y[i])\n" | i in 1..N];