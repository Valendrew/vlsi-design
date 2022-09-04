% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Set of N
set of int: set_I = 1..N;
% Extract widths and heights for usability 
array[1..N] of int: widths = [CIRCUITS[i, 1] | i in set_I];
array[1..N] of int: heights = [CIRCUITS[i, 2] | i in set_I];

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

% Lower bound is the minimum height among circuits' ones
int: l_bound = ceil(sum([(widths[i]*heights[i]) | i in set_I]) / W);
% Height
int: l = l_bound;
var int: z = 0;

% Set of TILES
int: MAX_TILES = W * l;
set of int: set_P = 1..MAX_TILES;
% Positions
array[int] of set of int: POSITIONS = [array2set([-i, r + c*W]) | i in set_I, c in 0..l_bound - heights[i], r in 0..W - widths[i]];

% Set of VALID POSITIONS V(i)
set of int: set_J = 1..(length(POSITIONS));

% Array of V(i)
array[set_I] of set of int: valid_i = [array2set([j | j in 1..length(POSITIONS) where -i in POSITIONS[j]]) | i in set_I];
array[set_J] of int: coords::add_to_output = [POSITIONS[j][2] | j in set_J]; 

function int: check_pos(int: j, int: p) =
  let {
    int: start_x = coords[j] mod W;
    int: start_y = coords[j] div W;
    int: c = POSITIONS[j][1] * -1;
    int: coord_x = (p-1) mod W;
    int: coord_y = (p-1) div W;
  } in if coord_x in start_x..(start_x + widths[c]-1) /\ coord_y in start_y..(start_y + heights[c]-1)then 1 else 0 endif;
  
array[set_J, set_P] of 0..1: corr_matrix = array2d(set_J, set_P, [check_pos(j,p) | j in set_J, p in set_P]);

array[set_I, set_J] of var 0..1: place::add_to_output;

constraint forall (p in set_P) (sum (i in set_I, j in valid_i[i]) (corr_matrix[j,p] * place[i,j]) <= 1);
constraint forall (i in set_I) (sum (j in valid_i[i]) (place[i,j]) == 1);
constraint sum (i in set_I, j in valid_i[i], p in set_P) (corr_matrix[j,p] * place[i,j]) <= W * l;
solve minimize z = 0;

output ["- The max height is \(l)."];
