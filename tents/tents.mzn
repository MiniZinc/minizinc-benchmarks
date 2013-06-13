% tents.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Fri Dec 12 10:43:04 EST 2008
%
% A tents problem involves completing a grid which has been partially filled
% out with trees.  Each remaining square contains either a tent or grass.
% There is exactly one tent orthogonally adjacent to each tree and no two
% tents may be adjacent, orthogonally or otherwise.  Furthermore, the number
% of tents in each row and column is specified as part of the problem.
%
% For example, the problem (where 'T' represents a tree, 'A' a tent, '_' grass,
% and '.' unknown):
%
%      2 2 1 1 1 2 1 2
%   
%   3  . T . T . . . .
%   1  . T . . . T . .
%   1  . . . . . . . T
%   0  . . . . T . . .
%   2  . . . . . . . .
%   1  T . . . . . T .
%   0  T . . T . . . T
%   4  . . . . T . . .
%
% Has this solution:
%
%      2 2 1 1 1 2 1 2
%   
%   3  A T A T _ A _ _
%   1  _ T _ _ _ T _ A
%   1  _ A _ _ _ _ _ T
%   0  _ _ _ _ T _ _ _
%   2  _ _ _ _ A _ A _
%   1  T A _ _ _ _ T _
%   0  T _ _ T _ _ _ T
%   4  A _ _ A T A _ A

% Parameters.

int: n;                                 % The length of side of the board.

set of int: row = 1..n;
set of int: col = 1..n;

array [row, col] of 0..1: a;            % The problem: 1 - tree, 0 - unknown.
array [row] of int: row_sums;           % The number of tents in each row.
array [col] of int: col_sums;           % The number of tents in each column.

% Model.

set of int: ROW = 0..(n + 1);
set of int: COL = 0..(n + 1);

% The tents (0 - non-tent, 1 - tent).
array [ROW, COL] of var 0..1: t;

% We can't place a tent on the surrounding border or on top of a tree.
%
constraint forall (r in {0, n + 1}, c in COL) (t[r, c] = 0);
constraint forall (r in ROW, c in {0, n + 1}) (t[r, c] = 0);
constraint
    forall (r in row, c in col) (
        if a[r, c] = 1 then t[r, c] = 0 else true endif
    );

% The row and column sum constraints.
%
constraint forall (r in row) (sum (c in col) (t[r, c]) = row_sums[r]);
constraint forall (c in col) (sum (r in row) (t[r, c]) = col_sums[c]);

% Each tree must have an orthogonally neighbouring tent.
%
constraint
    forall (r in row, c in col where a[r, c] = 1) (
        t[r - 1, c] + t[r + 1, c] + t[r, c - 1] + t[r, c + 1] >= 1
    );

% No 2x2 area can contain two tents (otherwise tents would be adjacent).
%
constraint
    forall (r in row, c in col where r < n /\ c < n) (
        t[r, c] + t[r + 1, c] + t[r, c + 1] + t[r + 1, c + 1] <= 1
    );

% A well posed problem should have a unique solution...
% 
solve
    :: int_search(
        [t[r, c] | r in row, c in col],
        input_order,
        indomain_max,
        complete
    )
    satisfy;

output ["t = ", show(t), "\n"];
