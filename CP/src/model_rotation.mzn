include "diffn_nonstrict.mzn";
include "cumulative.mzn";
include "lex_greater.mzn";

% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Extract widths and heights for usability 
array[1..N] of int: widths = [CIRCUITS[i, 1] | i in 1..N];
array[1..N] of int: heights = [CIRCUITS[i, 2] | i in 1..N];

% Variables
% Lower bound is the minimum height among circuits' ones
int: l_low = max(min(heights), min(widths));
% Upper bound is the sum of all circuit heights, as staking one above the other
int: l_up = sum(widths)+sum(heights);
var l_low..l_up: l;

int: xd = max(min(widths), min(heights));

% x and y coordinates of the circuits wrtt bottom left coordinate
array [1..N] of var 0..W-xd: coord_x;
array [1..N] of var 0..l_up-l_low: coord_y;
array [1..N] of var bool: rot;

%%%%%%%% CONSTRAINTS %%%%%%%%

% Avoid overlapping between the circuits, set the coordinates and constrain within the available area
constraint (
      let {
            array [1..N] of var 0..W-xd: x_real = [if rot[i] then coord_y[i] else coord_x[i] endif | i in 1..N];
            array [1..N] of var 0..l_up-l_low: y_real = [if rot[i] then coord_x[i] else coord_y[i] endif | i in 1..N];
            array [1..N] of var 0..max(max(widths), max(heights)): w_real = [if rot[i] then heights[i] else widths[i] endif | i in 1..N];
            array [1..N] of var 0..max(max(widths), max(heights)): h_real = [if rot[i] then widths[i] else heights[i] endif | i in 1..N];
      } in diffn_nonstrict(x_real, y_real, w_real, h_real) /\ cumulative(x_real, w_real, h_real, l) /\ cumulative(y_real, h_real, w_real, W) /\
      forall(i in 1..N)(x_real[i]+w_real[i] <= W /\ y_real[i]+h_real[i] <=l)
);

% TODO: vincolo sull'area totale che deve essere uguale a W*l
%constraint (let {
%      var int: area = sum([widths[i]*heights[i] | i in 1..N])
%} in area==(W*l));

%%%%%%%% Symmetry breaking %%%%%%%%
predicate symm_breaking_same() = 
      forall(i,j in 1..N where i != j)(
            if rot[i] /\ not(rot[j]) /\ heights[i]==widths[j] /\ widths[i]==heights[j] then lex_greater([coord_y[i], coord_x[i]], [coord_x[j], coord_y[j]]) 
            elseif not(rot[i]) /\ rot[j] /\ widths[i]==heights[j] /\ heights[i]==widths[j] then lex_greater([coord_x[i], coord_y[i]], [coord_y[j], coord_x[j]]) 
            elseif widths[i]==widths[j] /\ heights[i]==heights[j] then lex_greater([coord_x[i], coord_y[i]], [coord_x[j], coord_y[j]]) 
            else true endif
      );

% Avoid rotation of 180 degrees wrt the x and y axes
predicate symm_breaking() = 
      let {
            array [1..N] of var 0..W-xd: x_real = [if rot[i] then coord_y[i] else coord_x[i] endif | i in 1..N];
            array [1..N] of var 0..l_up-l_low: y_real = [if rot[i] then coord_x[i] else coord_y[i] endif | i in 1..N];
            array [1..N] of var 0..max(max(widths), max(heights)): w_real = [if rot[i] then heights[i] else widths[i] endif | i in 1..N];
            array [1..N] of var 0..max(max(widths), max(heights)): h_real = [if rot[i] then widths[i] else heights[i] endif | i in 1..N];

            array[1..N] of var int: new_x = [W - x_real[i] - w_real[i] | i in 1..N];
            array[1..N] of var int: new_y = [l - y_real[i] - h_real[i] | i in 1..N]
      } in lex_greater(x_real, new_x) /\ lex_greater(y_real, new_y);


constraint symm_breaking_same() /\ symm_breaking();


solve :: seq_search([
            int_search([l], input_order, indomain_min),%::restart_luby(250),
            int_search(coord_x, input_order, indomain_min),
            int_search(coord_y, input_order, indomain_min)])
      minimize l;

output ["- The max height is \(l).\n- The coordinates are:\n"];
output ["\t\(CIRCUITS[i,1]) \(CIRCUITS[i,2]), \(coord_x[i]) \(coord_y[i])\n" | i in 1..N];