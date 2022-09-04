% Inputs 
int: W;
int: N;
array[1..N, 1..2] of int: CIRCUITS;

% Set of N
set of int: set_I = 1..N;
% Extract widths and heights for usability 
array[set_I] of int: widths = [CIRCUITS[i, 1] | i in set_I];
array[set_I] of int: heights = [CIRCUITS[i, 2] | i in set_I];

int: max_circuit = arg_max([widths[i] * heights[i] | i in set_I]);

% Variables
% Lower bound is the minimum height among circuits' ones
int: l_bound = max(max(heights), ceil(sum([(widths[i]*heights[i]) | i in set_I]) / W));
% Height
int: l = l_bound;

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

int: j_max_circuit = min(valid_i[max_circuit]);

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

constraint place[max_circuit, j_max_circuit] = 1;

constraint forall (p in set_P) (sum (i in set_I, j in valid_i[i]) (corr_matrix[j,p] * place[i,j]) <= 1);
constraint forall (i in set_I) (sum (j in valid_i[i]) (place[i,j]) == 1);

constraint forall (i in set_I) (sum (j in set_J diff valid_i[i]) (place[i,j]) == 0);

% constraint sum (i in set_I, j in valid_i[i], p in set_P) (corr_matrix[j,p] * place[i,j]) <= N;
solve minimize l;

output ["- The max height is \(l)."];