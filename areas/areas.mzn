% areas.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Fri Nov 30 13:34:19 EST 2007
%
% The "areas puzzle" as described in Peter Szeredi's paper "Teaching
% Constraints through Logic Puzzles".
%
% In an areas puzzle, a grid is partially filled in with numbers.  The
% problem is to fill in the remainder of the grid.  Each maximally
% contiguous area containing the number N must have exactly N cells.
% Two cells are contiguous if they share a side.
%
%
% XXX This assumption is wrong: every occurrence of a given number N in the
% initial grid must occur in a distinct area.  Fix this problem.
%
% For example, a solution to
%
% _ _ _ _ _
% 2 1 _ 4 3
% _ _ _ 2 _
% _ 5 _ 3 _
% 3 _ _ _ 2
%
% is
%
% 2 4 4 3 3
% 2 1 4 4 3
% 3 5 5 2 2
% 3 5 3 3 3
% 3 5 5 2 2

include "globals.mzn";

int: w;                                 % The width of the grid.
int: h;                                 % The height of the grid.
int: n;                                 % The number of regions.
set of int: row = 1..h;
set of int: col = 1..w;
set of int: region = 1..n;
set of int: maybe_region = 0..n;        % 0 indicates 'undecided'.
array [row, col] of maybe_region: puzzle;
                                        % The initial state of the puzzle.
                                        % Each cell is either 0 or a region
                                        % number.
array [region] of int: region_size;     % The target size for each region.

int: max_size = max(region_size);
set of int: step = 1..max_size;

% This is where our solution goes.
array [row, col] of var region: grid;

array [row, col] of var step: when;     % The step when a grid cell is decided.
                                        %   We use this array to ensure that
                                        %   regions are contiguous.

    % If a cell in the puzzle is non-zero then the corresponding cell in the
    % grid is given.
    %
    % Zero puzzle cells are initially undecided.  At some step s + 1 a
    % puzzle cell is decided by extending the region of one of its neighbours
    % that was decided in the previous step.
    %
constraint
    forall (r in row, c in col) (
        if puzzle[r, c] != 0 then
            grid[r, c] = puzzle[r, c]
        /\  when[r, c] = 1
        else
            copies_neighbour(r, c, r + 1, c)
        \/  copies_neighbour(r, c, r - 1, c)
        \/  copies_neighbour(r, c, r, c + 1)
        \/  copies_neighbour(r, c, r, c - 1)
        endif
    );

predicate copies_neighbour(row: r, col: c, int: rn, int: cn)  =
        if on_grid(rn, cn)
        then grid[r, c] = grid[rn, cn] /\  when[r, c] = when[rn, cn] + 1
        else false
        endif;

test on_grid(int: r, int: c)  =  1 <= r /\ r <= h /\ 1 <= c /\ c <= w;

    % If cell [r, c] is too far from the "root" [Rr, Rc] of region R then we
    % can remove R from the domain of that grid cell.
    %
constraint
    forall (Rr in row, Rc in col where puzzle[Rr, Rc] != 0) (
        let
        {
            region: R = puzzle[Rr, Rc],
            int: Rs = region_size[R]
        }
        in
            forall (r in row, c in col) (
                if abs(r - Rr) + abs(c - Rc) >= Rs then
                    grid[r, c] != R
                else
                    true
                endif
            )
    );

    % If two regions have the same size, they cannot have neighbouring
    % cells.
    %
constraint
    forall (R1, R2 in region
            where R1 < R2 /\ region_size[R1] = region_size[R2]) (
        forall (r in row, c in col) (
            exclude_neighbours(r, c, r + 1, c, R1, R2)
        /\  exclude_neighbours(r, c, r, c + 1, R1, R2)
        )
    );

predicate exclude_neighbours(par row: r1, par col: c1,
        par int: r2, par int: c2, par region: R1, par region: R2)  =
    if on_grid(r2, c2) then
        ( grid[r1, c1] = R1  ->  grid[r2, c2] != R2 )
    /\  ( grid[r1, c1] = R2  ->  grid[r2, c2] != R1 )
    else
        true
    endif;

    % There must be the correct number of cells in each region.
    %
constraint
    forall (R in region) (
        sum (r in row, c in col) (bool2int(grid[r, c] = R))  =  region_size[R]
    );

    % Any solution will do.
    %
solve
    :: int_search(
        [grid[r, c] | r in row, c in col],
        first_fail,
        indomain_split,
        complete
    )
    satisfy;

output [
    ( if c = 1 then "\n" else "" endif ) ++ show(region_size[grid[r, c]])
     |   r in row, c in col
];

%----------------------------------------------------------------------------%
%----------------------------------------------------------------------------%
