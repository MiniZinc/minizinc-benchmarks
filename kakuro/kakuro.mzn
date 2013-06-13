% kakuro.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Tue Dec  4 16:34:41 EST 2007
%
% Model for kakuro puzzles.  A kakuro is a kind of crossword where
% each "word" is a permutation of a subset of {1, 2, 3, ..., 9} summing
% to a given value.

include "globals.mzn";

int: h;                                 % The number of rows in the grid.
int: w;                                 % The number of columns in the grid.
set of int: row = 1..h;
set of int: col = 1..w;
set of int: digit = 0..9;               % 0 indicates "blacked out".

array [row, col] of 0..1: grid_data;    % "Blacked out" squares.  As above
                                        % 0 indicates blacked out.

array [row, col] of var digit: grid;
                                        % The puzzle grid.
int: n_h;                               % The number of horizontal clues in
                                        %   the puzzle.
array [1..n_h, 1..4] of int: h_clue;    % clue[i, 1], clue[i, 2] is the
                                        %   row, col of the clue cell
                                        %   (which is blacked out);
                                        %   clue[i, 3], clue[i, 4] are the
                                        %   length and sum of the word.
int: n_v;                               % The number of vertical clues in
                                        %   the puzzle.
array [1..n_v, 1..4] of int: v_clue;    % clue[i, 1], clue[i, 2] is the
                                        %   row, col of the clue cell
                                        %   (which is blacked out);
                                        %   clue[i, 3], clue[i, 4] are the
                                        %   length and sum of the word.
int: clue_row = 1;
int: clue_col = 2;
int: clue_len = 3;
int: clue_sum = 4;

% We use a separate grid_data parameter so that we can write out the value
% for grid as MiniZinc data in the solution.  We cannot feed that solution
% back into the original model if the data files refer to grid directly.
%
constraint forall (r in row) (
    forall (c in col) (
        if grid_data[r, c] = 0 then grid[r, c] = 0 else true endif)
    );

    % Each word must be composed of distinct digits greater than zero
    % and sum to its target value.
    %
constraint
    forall (i in 1..n_h) (
        let
        {
            int: r = h_clue[i, clue_row],
            int: c = h_clue[i, clue_col],
            int: l = h_clue[i, clue_len],
            int: s = h_clue[i, clue_sum],
            array [1..l] of var digit: word = [grid[r, c + j] | j in 1..l]
        }
        in

            % Word digits must be positive.
            forall (j in 1..l) (word[j] > 0)

            % Word digits must sum to the clue.
        /\  sum(word)  =  s

            % Word digits must all be different.
        /\  alldifferent(word)

            % Apply a "magic word" constraint if possible.
        /\  magic_constraint(l, s, word)

    );

constraint
    forall (i in 1..n_v) (
        let
        {
            int: r = v_clue[i, clue_row],
            int: c = v_clue[i, clue_col],
            int: l = v_clue[i, clue_len],
            int: s = v_clue[i, clue_sum],
            array [1..l] of var digit: word = [grid[r + j, c] | j in 1..l]
        }
        in

            % Word digits must be positive.
            forall (j in 1..l) (word[j] > 0)

            % Word digits must sum to the clue.
        /\  sum(word)  =  s

            % Word digits must all be different.
        /\  alldifferent(word)

            % Apply a "magic word" constraint if possible.
        /\  magic_constraint(l, s, word)

    );

    % There are various "magic" sums with unique combinations, such as
    % These are described by the following forms:
    % - sum 1..k                    E.g.,  6 = sum {1, 2, 3}
    % - sum 1..k union {k + 2}      E.g.,  7 = sum {1, 2, 4}
    % - sum k..9                    E.g., 24 = sum {7, 8, 9}
    % - sum {k} union k+2..9        E.g., 29 = sum {5, 7, 8, 9}
    %
    % TODO: add these pruning constraints where possible.

int: n_magic = 28;
int: magic_len = 1;
int: magic_sum = 2;
int: magic_lo  = 3;
int: magic_hi  = 4;
int: magic_ex  = 5;
array [1..n_magic, 1..5] of int: magic = [|
    % Each row describes a "magic" word:
    % - sum
    % - length
    % - lowest digit
    % - highest digit
    % - excluded digit (if any, otherwise 0)
    2, 3, 1, 2, 0|
    2, 4, 1, 3, 2|
    3, 6, 1, 3, 0|
    3, 7, 1, 4, 3|
    4, 10, 1, 4, 0|
    4, 11, 1, 5, 4|
    5, 15, 1, 5, 0|
    5, 16, 1, 6, 5|
    6, 21, 1, 6, 0|
    6, 22, 1, 7, 6|
    7, 28, 1, 7, 0|
    7, 29, 1, 8, 7|
    8, 36, 1, 8, 0|
    8, 37, 1, 9, 8|
    9, 45, 1, 9, 0|
    2, 17, 8, 9, 0|
    2, 16, 7, 9, 8|
    3, 24, 7, 9, 0|
    3, 23, 6, 9, 7|
    4, 30, 6, 9, 0|
    4, 29, 5, 9, 6|
    5, 35, 5, 9, 0|
    5, 34, 4, 9, 5|
    6, 39, 4, 9, 0|
    6, 38, 3, 9, 4|
    7, 42, 3, 9, 0|
    7, 41, 2, 9, 3|
    8, 44, 2, 9, 0
|];

predicate magic_constraint(int: l, int: s, array [int] of var digit: word)  =
    forall (i in 1..n_magic) (
        if l = magic[i, magic_len] /\ s = magic[i, magic_sum] then
            let
            {
                int: lo = magic[i, magic_lo],
                int: hi = magic[i, magic_hi],
                int: ex = magic[i, magic_ex]
            }
            in
                forall (j in index_set(word)) (
                    lo <= word[j]
                /\  word[j] <= hi
                /\  word[j] != ex
                )
        else
            true
        endif
    );

    % Any solution will do.
    %
solve satisfy;

output ["grid = ", show(grid), "\n"];

%----------------------------------------------------------------------------%
%----------------------------------------------------------------------------%
