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

% x and y coordinates of the circuits
array [1..N] of var 0..W-min(widths): coord_x;
array [1..N] of var 0..l_up-min(heights): coord_y;


%%%%%%%% CONSTRAINTS %%%%%%%%

% Put the largest circuit in the first position
%int: max_ind = reverse(arg_sort([widths[i]*heights[i] | i in 1..N]))[1];
%constraint coord_x[max_ind] = 0 /\ coord_y[max_ind] = 0;

% Avoid overlapping between the circuits
constraint diffn_nonstrict(coord_x, coord_y, widths, heights);

% Constrain the circuits within the available area
constraint forall(i in 1..N)(coord_x[i] + widths[i] <= W /\ coord_y[i] + heights[i] <= l);

% Implied constraints
% TODO: in each "line" if we sum all the circuits the sum is = W

% Find the x and y coordinates using 'cumulative' global constraints
constraint cumulative(coord_x, widths, heights, l);
constraint cumulative(coord_y, heights, widths, W);

%%%%%%%% Symmetry breaking %%%%%%%%
% TODO: with lex_greatereq the computation is speeded up (without sorting on the array), why?
% TODO: check if this constraint is correct, if I don't write i<j probably I consider 2 times
%       lex_greater(co[i]..co[j]) and lex_greater(co[j]..co[i])
% Symmetry breaking for circuits with the same widths and heights
predicate symm_breaking_same() = 
      forall(i,j in 1..N where i != j /\ widths[i]==widths[j] /\ heights[i]==heights[j])(
            lex_greater([coord_x[i], coord_y[i]], [coord_x[j], coord_y[j]])
      );

% I need to pass 'l' or 'W' and 'coord_y' or 'coord_x' respectively in order to compute the symmetry breaking
% w.r.t. a specific axis
predicate symm_breaking(var int: dim, array[1..N] of var int: coord, array[1..N] of var int: values) = 
      let {
            array[1..N] of var int: new_coord = [dim - coord[i] - values[i] | i in 1..N]
      } in lex_greater(coord, new_coord);


constraint symm_breaking_same() /\ symm_breaking(W, coord_x, widths) /\ symm_breaking(l, coord_y, heights);


solve :: seq_search([
            int_search([l], input_order, indomain_min),%::restart_luby(250),
            int_search(coord_x, input_order, indomain_min), % TODO: if I put input_order here it doesn't work well
            int_search(coord_y, input_order, indomain_min)])
      minimize l;

output ["- The max height is \(l).\n- The coordinates are:\n"];
output ["\t\(CIRCUITS[i,1]) \(CIRCUITS[i,2]), \(coord_x[i]) \(coord_y[i])\n" | i in 1..N];