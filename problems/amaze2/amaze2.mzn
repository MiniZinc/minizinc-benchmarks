include "globals.mzn";

int: X;		% Number of cells in the x-direction.
int: Y;		% Number of cells in the y-direction.
int: N;		% Number of pairs.

   % These arrays all correspond.
   %
array[1..N] of 1..X: end_points_start_x;
array[1..N] of 1..Y: end_points_start_y;
array[1..N] of 1..X: end_points_end_x;
array[1..N] of 1..Y: end_points_end_y;

int : M = X * Y;

array[1..X, 1..Y] of 1..M : id = array2d(1..X, 1..Y, [i | i in 1..M]);
% array[1..M] of 1..X : pos_x = [i | i in 1..X, j in 1..Y];
% array[1..M] of 1..Y : pos_y = [j | i in 1..X, j in 1..Y];

array[1..M] of set of 1..M : neighbours = 
  [ (if i > 1 then {id[i-1, j]} else {} endif) union
    (if i < X then {id[i+1, j]} else {} endif) union
    (if j > 1 then {id[i, j-1]} else {} endif) union
    (if j < Y then {id[i, j+1]} else {} endif) | i in 1..X, j in 1..Y];

array[1..N] of 1..M : start = 
  [id[end_points_start_x[i], end_points_start_y[i]] | i in 1..N];

array[1..N] of 1..M : end = 
  [id[end_points_end_x[i], end_points_end_y[i]] | i in 1..N];

array[0..M] of var 0..N : path;
array[1..M] of var 0..M : next;

constraint path[0] = 0;

constraint forall(i in 1..N)(
    sum(j in neighbours[start[i]]) (bool2int(next[j] = start[i])) = 0 /\
    next[end[i]] = end[i] /\
    path[start[i]] = i /\
    path[end[i]] = i
);

constraint forall(i in 1..M where not(i in {j | j in end}))(
  path[i] = path[next[i]]
);

constraint forall(i in 1..M where not(i in {j | j in start})) (
  path[i] != 0 -> 
  (sum(j in neighbours[i]) (bool2int(next[j] = i)) = 1)
%  sum(j in neighbours[i]) (bool2int(next[j] = i)) = bool2int(path[i] != 0)
);

constraint forall(i in 1..M)(
  path[i] = 0 -> next[i] = 0
);

solve 
	:: int_search(next ++ path, first_fail, indomain_min, complete)
	satisfy;

output [show_int(floor(log10(int2float(N)) + 1.0), path[id[x, y]]) ++
       if x = X then "\n" else " " endif | y in 1..Y, x in 1..X
];
