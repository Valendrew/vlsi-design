include "globals.mzn";

% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Extract widths and heights for usability 
array[1..N] of int: widths = [CIRCUITS[i, 1] | i in 1..N];
array[1..N] of int: heights = [CIRCUITS[i, 2] | i in 1..N];

% Variables
% Lower bound is the minimum height among circuits' ones
int: l_low = ceil(sum([(widths[i]*heights[i]) | i in 1..N]) / W); % TODO: check correctness, otherwise use min(heights)
% Upper bound is the sum of all circuit heights, as staking one above the other
int: l_up = sum(heights);
var l_low..l_up: l;

% x and y coordinates of the circuits wrtt bottom left coordinate
array [1..N] of var 0..W-min(widths): coord_x;
array [1..N] of var 0..l_up-min(heights): coord_y;


%%%%%%%% CONSTRAINTS %%%%%%%%

% Put the largest circuit in the first position, the instance 40 fails
%int: max_ind = reverse(arg_sort([widths[i]*heights[i] | i in 1..N]))[1];
%constraint coord_x[max_ind] = 0 /\ coord_y[max_ind] = 0;

% Avoid overlapping between the circuits
% Constrains rectangles i, given by their origins (x[i], y[i]) and sizes (dx[i], dy[i]), to be non-overlapping.
constraint diffn(coord_x, coord_y, widths, heights);

% Constrains the circuits within the available area
constraint forall(i in 1..N)(coord_x[i] + widths[i] <= W /\ coord_y[i] + heights[i] <= l);

% Find the x and y coordinates using 'cumulative' global constraints
% Requires that a set of tasks given by start times s, durations d, and resource requirements r, 
% never require more than a global resource bound b at any one time.
constraint cumulative(coord_x, widths, heights, l);
constraint cumulative(coord_y, heights, widths, W);


%%%%%%%% Symmetry breaking %%%%%%%%
% Symmetry breaking for circuits with the same widths and heights
predicate symm_breaking_same() = 
      forall(i, j in 1..N where i < j /\ widths[i]==widths[j] /\ heights[i]==heights[j])(
            lex_lesseq([coord_x[i], coord_y[i]], [coord_x[j], coord_y[j]])
      );

% Compute the symmetry breaking w.r.t. the x or y axis
predicate symm_breaking_axes() = 
      let {
            array[1..N] of var int: new_x = [W - coord_x[i] - widths[i] | i in 1..N];
            array[1..N] of var int: new_y = [l - coord_y[i] - heights[i] | i in 1..N]
      } in lex_lesseq(coord_x, new_x) /\ lex_lesseq(coord_y, new_y);


constraint symm_breaking_same() /\ symm_breaking_axes();


solve :: seq_search([
            int_search([l], input_order, indomain_min),%::restart_luby(250),
            int_search(coord_x, input_order, indomain_min),
            int_search(coord_y, input_order, indomain_min)])
      minimize l;

output ["- The max height is \(l).\n- The coordinates are:\n"];
output ["\t\(CIRCUITS[i,1]) \(CIRCUITS[i,2]), \(coord_x[i]) \(coord_y[i])\n" | i in 1..N];