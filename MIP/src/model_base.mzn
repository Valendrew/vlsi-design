% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Extract widths and heights for usability 
array[1..N] of int: widths = [CIRCUITS[i, 1] | i in 1..N];
array[1..N] of int: heights = [CIRCUITS[i, 2] | i in 1..N];

% Variables
% Lower bound is the maximum between the maximum height and the optimal one
int: l_low = max(max(heights), ceil(sum([(widths[i]*heights[i]) | i in 1..N]) / W));
% Upper bound is the sum of all circuit heights, as staking one above the other
int: l_up = sum(heights);
var l_low..l_up: l;

% x and y coordinates of the circuits wrtt bottom left coordinate
array [1..N] of var 0..W-min(widths): coord_x;
array [1..N] of var 0..l_up-min(heights): coord_y;
array[1..N, 1..N, 1..2] of var bool: delta;

constraint forall(i in 1..N)(coord_x[i] + widths[i] <= W);
constraint forall(i in 1..N) (coord_y[i] + heights[i] <= l);

constraint forall(i,j in 1..N where i < j) (sum(k in 1..2) (delta[i,j,k] + delta[j,i,k]) == 1);

constraint forall(i,j in 1..N where i < j) (coord_x[i] + widths[i] <= coord_x[j] + (delta[j,i,1] + delta[i,j,2] + delta[j,i,2]) * W);
constraint forall(i,j in 1..N where i < j) (coord_x[j] + widths[j] <= coord_x[i] + (delta[i,j,1] + delta[i,j,2] + delta[j,i,2]) * W);
constraint forall(i,j in 1..N where i < j) (coord_y[i] + heights[i] <= coord_y[j] + (delta[i,j,1] + delta[j,i,1] + delta[j,i,2]) * l_up);
constraint forall(i,j in 1..N where i < j) (coord_y[j] + heights[j] <= coord_y[i] + (delta[i,j,1] + delta[j,i,1] + delta[i,j,2]) * l_up);

solve :: seq_search([
            int_search([l], input_order, indomain_min),
            int_search(coord_x, input_order, indomain_min),
            int_search(coord_y, input_order, indomain_min)])
    minimize l;

output ["- The max height is \(l).\n"];