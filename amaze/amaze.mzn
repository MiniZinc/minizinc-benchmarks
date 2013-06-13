% Given a grid containing pairs of numbers (ranging from 1 .. N), connect the
% pairs (e.g. 1 to 1; 2 to 2; etc) by drawing a line horizontally and
% vertically, but not diagonally.  The lines must never cross.

%----------------------------------------------------------------------------%

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

%----------------------------------------------------------------------------%

% We put a boundary around the board to make it simpler to deal with the edges.
%
array[0..X + 1, 0..Y + 1] of var 0..N: board;

% Constrain all the cells in the boundary to be empty.
%
constraint forall(y in 0..Y + 1) (
    board[0, y] = 0 /\ board[X + 1, y] = 0 
);

constraint forall(x in 0..X + 1) (
    board[x, 0] = 0 /\ board[x, Y + 1] = 0 
);

% Constrain the end points to appear in the board.
%
constraint forall(n in 1..N) (
    board[end_points_start_x[n], end_points_start_y[n]] = n /\
    board[end_points_end_x[n], end_points_end_y[n]] = n
);

% Constrain the end points to have exactly one horizontal or
% vertical neighbour of the same value.
%
constraint forall(n in 1..N) (
    let {
	int: x1 = end_points_start_x[n],
       	int: y1 = end_points_start_y[n],
	int: x2 = end_points_end_x[n],
        int: y2 = end_points_end_y[n],
        array[1..4] of var 0..N: neighbours_start = 
	    [board[x1, y1 + 1], board[x1 + 1, y1], board[x1, y1 - 1], board[x1 - 1, y1]],
  	array[1..4] of var 0..N: neighbours_end = 
	    [board[x2, y2 + 1], board[x2 + 1, y2], board[x2, y2 - 1], board[x2 - 1, y2]]
     } in (
	count(neighbours_start, board[x1, y1], 1) /\
        count(neighbours_end, board[x2, y2], 1) 
     )
);

% Return true if the given point is one of the end points of a path.
%
test is_end_point(int: x, int: y) =
    exists (n in 1..N) (
	end_points_start_x[n] = x /\ end_points_start_y[n] = y \/
        end_points_end_x[n] = x /\ end_points_end_y[n] = y
);

% Constrain any non-empty cell that is not an end-point to have exactly two
% horizontal or vertical neighbours of the same value.
%
constraint forall(x in 1..X, y in 1..Y) (
    if is_end_point(x, y) then	
	true
    else
    	board[x, y] != 0 -> count([board[x, y + 1], board[x + 1, y], board[x, y - 1], board[x - 1, y]], board[x, y], 2) 
    endif
);

solve 
    :: int_search(array1d(1..(X + 2) * (Y + 2), board), input_order, indomain_min, complete)
    minimize sum(board);

output [show_int(floor(log10(int2float(N)) + 1.0), board[x, y]) ++
       if x = X then "\n" else " " endif | y in 1..Y, x in 1..X
] ++ ["\nobj = ", show(sum(board))];
