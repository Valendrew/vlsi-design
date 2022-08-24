include "globals.mzn";

% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Extract widths and heights for usability 
array[1..N] of int: widths = [CIRCUITS[i, 1] | i in 1..N];
array[1..N] of int: heights = [CIRCUITS[i, 2] | i in 1..N];

% Variables
% Lower bound is the maximum height among circuits' widths and heights
int: l_low = ceil(sum([(widths[i]*heights[i]) | i in 1..N]) / W);%max(max(heights), max(widths));
% Upper bound is the sum of all circuit heights, as staking one above the other + the sum of the widths
int: l_up = sum([max(heights[i], widths[i]) | i in 1..N]);%ceil(l_low + sum(heights) / 2);
var l_low..l_up: l;


% x and y coordinates of the circuits wrtt bottom left coordinate
array [1..N] of var 0..W-min(min(heights),min(widths)): coord_x;
array [1..N] of var 0..l_up-min(min(heights),min(widths)): coord_y;
array [1..N] of var bool: rot;

array [1..N] of var 1..max(max(widths), max(heights)): w_real = [if rot[i] then heights[i] else widths[i] endif | i in 1..N];
array [1..N] of var 1..max(max(widths), max(heights)): h_real = [if rot[i] then widths[i] else heights[i] endif | i in 1..N];


%%%%%%%% CONSTRAINTS %%%%%%%%
% Avoid overlapping between the circuits
% Constrains rectangles i, given by their origins (x[i], y[i]) and sizes (dx[i], dy[i]), to be non-overlapping.
constraint diffn(coord_x, coord_y, w_real, h_real);

% Find the x and y coordinates using 'cumulative' global constraints
% Requires that a set of tasks given by start times s, durations d, and resource requirements r, 
% never require more than a global resource bound b at any one time.
constraint cumulative(coord_x, w_real, h_real, l);
constraint cumulative(coord_y, h_real, w_real, W);

% Constrains the circuits within the available area
constraint forall(i in 1..N)(
      coord_x[i] + w_real[i] <= W /\ coord_y[i] + h_real[i] <=l
);


%%%%%%%% Symmetry breaking %%%%%%%%
% Break symmetries with circuits of the same size
predicate symm_breaking_same() = 
      forall(i,j in 1..N where i < j /\ w_real[i]==w_real[j] /\ h_real[i]==h_real[j])(
            lex_lesseq([coord_x[i], coord_y[i]], [coord_x[j], coord_y[j]])
      );

% Avoid symmetry wrt the x and y axes
predicate symm_breaking_axes() = 
      let {
            array[1..N] of var int: new_x = [W - coord_x[i] - w_real[i] | i in 1..N];
            array[1..N] of var int: new_y = [l - coord_y[i] - h_real[i] | i in 1..N]
      } in lex_lesseq(coord_x, new_x) /\ lex_lesseq(coord_y, new_y);

constraint symm_breaking_same() /\ symm_breaking_axes();

% Implied constraints, in each line the sum of the widths is equal to W (we compute only in the first and last row)
% TODO: it speeds up the computation for the instances but it worsen the solution for the last ones
%constraint (
%      let{
%            array[1..N] of var int: y_0 = [if coord_y[i] = 0 then w_real[i] else 0 endif | i in 1..N];
%            array[1..N] of var int: y_l = [if coord_y[i] = l-h_real[i] then w_real[i] else 0 endif | i in 1..N];
%      }in sum(y_0) == W /\ sum(y_l) == W
%);
 

% Set rotation to false for the squared circuits
constraint forall(i in 1..N)(
      if widths[i] == heights[i] then rot[i]=false endif
);

% Set rotation to false for the circuits that cannot be rotated
constraint forall(i in 1..N)(
      if heights[i] > W then rot[i]=false endif
);


solve :: seq_search([
            int_search([l], input_order, indomain_min),%::restart_luby(250),
            int_search(coord_x, input_order, indomain_min),
            int_search(coord_y, input_order, indomain_min)])
      minimize l;

output ["- The max height is \(l).\n- The coordinates are:\n"];
output ["\t\(CIRCUITS[i,1]) \(CIRCUITS[i,2]), \(coord_x[i]) \(coord_y[i])\n" | i in 1..N];