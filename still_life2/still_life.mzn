% File: still_life.mzn
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
% vim: ft=zinc ts=4 sw=4 et
%
% John Conway's Game of Life is a grid of cellular automata each obeying
% these rules:
% - a cell with < 2 live neighbours is dead in the next generation;
% - a cell with = 2 live neighbours is unchanged in the next generation;
% - a cell with = 3 live neighbours is live in the next generation;
% - a cell with > 3 live neighbours is dead in the next generation.
%
% The still life problem is to find an arrangement of cells that does not
% change from one generation to the next.  We want the solution with the
% largest number of live cells.  (N.B.: we assume the grid is surrounded
% by cells that must always be dead).
%
% I've tried several attempts to improve search; the best I have come
% up with is to label the edges first (since they are most tightly
% constrained).  Attempting to squeeze

% ===== Parameters =====

	% This model assumes an nxn grid of cells.
    %
int: n;

% ===== Model =====

    % a[r, c] = 1 iff cell (r, c) is live.
    % s[r, c] is the number of live neighbours for cell (r, c).
    %   A still life neighbourhood can't have more than 6 live cells.
    %   I suspect the lower bound on the size of a live neighbourhood
    %   is 1 on the edges and 2 in the interior, not 0, but I haven't
    %   proved this.
    %
array [1..n, 1..n] of var 0..1: a;
array [1..n, 1..n] of var 0..6: s;
var int: total = sum (r, c in 1..n) (a[r, c]);

    % Compute the sum of live neighbours for each cell.
    %
constraint
    forall (r, c in 1..n) (
        s[r, c] =
            sum (   rr in max(1, r - 1)..min(n, r + 1),
                    cc in max(1, c - 1)..min(n, c + 1)
                    where rr != r \/ cc != c) (
                a[rr, cc]
            )
    );

    % Impose the still life rules.
    %
constraint forall (r, c in 1..n) (a[r, c] = 0  ->  s[r, c] != 3);
constraint forall (r, c in 1..n) (a[r, c] = 1  ->  s[r, c] in 2..3);

    % Impose the boundary conditions.
    %
constraint
    forall (i in 2..(n - 1)) (
        sum (j in (i - 1)..(i + 1)) (a[1, j]) < 3
    /\  sum (j in (i - 1)..(i + 1)) (a[n, j]) < 3
    /\  sum (j in (i - 1)..(i + 1)) (a[j, 1]) < 3
    /\  sum (j in (i - 1)..(i + 1)) (a[j, n]) < 3
    );

    % Look for the maximum solution.
    %
solve
    % Label the edges first, since they are the most tightly constrained.
    %
    :: int_search(
        [ a[        r,         c] | c in 1..n, r in 1..min(4, n) ] ++
        [ a[        r,         c] | r in 1..n, c in 1..min(4, n) ] ++
        [ a[1 + n - r,         c] | c in 1..n, r in 1..min(4, n) ] ++
        [ a[        r, 1 + n - c] | r in 1..n, c in 1..min(4, n) ] ++
        [ a[r, c] | r, c in 1..n ],
        input_order, indomain_max, complete
    )
    maximize total;

% ===== Output =====

output [ show(a[r, c]) ++ if c = n then "\n" else " " endif
       | r, c in 1..n
       ] ++
       [ "total = ", show(total), "\n" ];
