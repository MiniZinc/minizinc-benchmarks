%------------------------------------------------------------------------------%

include "count.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: X;     % Number of cells in the x-direction
int: Y;     % NUmber of cells in the y-direction
int: N;     % Number of pairs

set of int: Pairs = 1..N;
set of int: Xs = 1..X;
set of int: Ys = 1..Y;

   % These arrays all correspond.
   %
array[Pairs] of Xs: end_points_start_x;
array[Pairs] of Ys: end_points_start_y;
array[Pairs] of Xs: end_points_end_x;
array[Pairs] of Ys: end_points_end_y;

set of int: Dom = 0..N;

%------------------------------------------------------------------------------%
% Variables

array [Xs, Ys] of var Dom: board;

%------------------------------------------------------------------------------%
% Tests

test is_end_point(int: x, int: y) = 
    exists(i in Pairs)(
        (end_points_start_x[i] = x /\ end_points_start_y[i] = y)
    \/  (end_points_end_x  [i] = x /\ end_points_end_y  [i] = y)
    );

test is_neighbour_from_xy(int: x, int: y, int: u, int: v) = (
    u in Xs /\ v in Ys /\ x in Xs /\ y in Ys
/\  (   (x == u /\ y in {v - 1, v + 1})
    \/  (y == v /\ x in {u - 1, u + 1})
    )
);

%------------------------------------------------------------------------------%
% Constraints

    % Endpoints must be match with input
    %
constraint
    forall(i in Pairs)(
        board[end_points_start_x[i], end_points_start_y[i]] = i
    /\  board[end_points_end_x  [i], end_points_end_y  [i]] = i
    );

    % Every endpoint has exactly one neighbour
    %
constraint
    forall(i in Pairs)(
        let {
            int: x1 = end_points_start_x[i],
            int: y1 = end_points_start_y[i],
            int: y2 = end_points_end_y  [i],
            int: x2 = end_points_end_x  [i]
        } in (
            count([board[u, v] | u in x1-1..x1+1, v in y1-1..y1+1 where 
                is_neighbour_from_xy(x1, y1, u, v)], i, 1
            )
        /\  count([board[u, v] | u in x2-1..x2+1, v in y2-1..y2+1 where 
                is_neighbour_from_xy(x2, y2, u, v)], i, 1
            )
        )
    );

    % Interior points has exactly two neighbours
    %
constraint
    forall(x in Xs, y in Ys)(
        if is_end_point(x, y) then 
            true 
        else
            board[x, y] != 0 ->
                count([board[u, v] | u in x-1..x+1, v in y-1..y+1 where
                    is_neighbour_from_xy(x, y, u, v)], board[x, y], 2)
        endif
    );

    % Some redudant constraints
    %
constraint redundant_constraint(
    forall(i in Pairs)(
        let {
            int: x1 = min(end_points_start_x[i], end_points_end_x[i]),
            int: y1 = min(end_points_start_y[i], end_points_end_y[i]),
            int: x2 = max(end_points_start_x[i], end_points_end_x[i]),
            int: y2 = max(end_points_start_y[i], end_points_end_y[i])
        } in (
            if x1 + 1 < x2 then
                forall(x in x1+1..x2-1)(
                    sum(z in Ys)(bool2int(board[x, z] == i)) > 0
                )
            else
                true
            endif
        /\  if y1 + 1 < y2 then
                forall(y in y1+1..y2-1)(
                    sum(z in Xs)(bool2int(board[z, y] == i)) > 0
                )
            else
                true
            endif
        )
    )
);

%------------------------------------------------------------------------------%
% Search

solve
    :: int_search(array1d(1..X*Y, board), input_order, indomain_split, complete)
    satisfy;

%------------------------------------------------------------------------------%
% Output

output [
 "% "
] ++ [
    show_int(floor(log10(int2float(N)) + 1.0), board[x, y]) ++
       if x = X then "\n% " else " " endif 
| y in Ys, x in Xs
] ++ [
    "\nboard = array2d(", show(Xs), ", ", show(Ys), ", ", show(board), ");\n"
];

