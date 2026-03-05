% kakuro.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Tue Dec  4 16:34:41 EST 2007
%
% Model for kakuro puzzles.  A kakuro is a kind of crossword where
% each "word" is a permutation of a subset of {1, 2, 3, ..., 9} summing
% to a given value.

include "all_different.mzn";

% 0 indicates "blacked out" and it cannot be used, 1 means that is must be used.
array [int, int] of 0..1: grid_data;
set of int: Row = index_set_1of2(grid_data);
set of int: Col = index_set_2of2(grid_data);

% The puzzle grid, absent indicates blacked out.
array [Row, Col] of var opt 1..9: grid;
type Clue = record(int: row, int: col, int: len, int: sum);
% Horizontal clue cells (which are blacked out), with target word length and sum.
list of Clue: h_clue;
% Vertical clue cells (which are blacked out), with target word length and sum.
list of Clue: v_clue;

% We use a separate grid_data parameter so that we can write out the value
% for grid as MiniZinc data in the solution.  We cannot feed that solution
% back into the original model if the data files refer to grid directly.
%
constraint forall (r in Row, c in Col) (
	grid_data[r,c] = 0 <-> absent(grid[r, c])
);

% Each word must be composed of distinct digits and sum to its target value.
%
predicate kakuro(list of var int: x, int: s) =
	all_different(x) /\ sum(x) = s /\ magic_constraint(s, x);

constraint forall (clue in h_clue) (
	let {
		constraint forall(j in 1..clue.len)(
			assert(grid_data[clue.row, clue.col + j] = 1, "horizontal clue \(clue) uses a blacked-out cell")
		);
		any: word = deopt([grid[clue.row, clue.col + j] | j in 1..clue.len])
	} in kakuro(word, clue.sum)
);

constraint forall (clue in v_clue) (
	let {
		constraint forall(j in 1..clue.len)(
			assert(grid_data[clue.row + j, clue.col] = 1, "vertical clue \(clue) uses a blacked-out cell")
		);
		any: word = deopt([grid[clue.row + j, clue.col] | j in 1..clue.len])
	} in kakuro(word, clue.sum)
);

% There are various "magic" sums with unique combinations, such as
% These are described by the following forms:
% - sum 1..k                    E.g.,  6 = sum {1, 2, 3}
% - sum 1..k union {k + 2}      E.g.,  7 = sum {1, 2, 4}
% - sum k..9                    E.g., 24 = sum {7, 8, 9}
% - sum {k} union k+2..9        E.g., 29 = sum {5, 7, 8, 9}
%
% TODO: add these pruning constraints where possible.
type Magic = record(int: len, int: sum, int: lo, int: hi, int: ex);
list of Magic: magic = [
	(len: 2, sum: 3, lo: 1, hi: 2, ex: 0),
	(len: 2, sum: 4, lo: 1, hi: 3, ex: 2),
	(len: 3, sum: 6, lo: 1, hi: 3, ex: 0),
	(len: 3, sum: 7, lo: 1, hi: 4, ex: 3),
	(len: 4, sum: 10, lo: 1, hi: 4, ex: 0),
	(len: 4, sum: 11, lo: 1, hi: 5, ex: 4),
	(len: 5, sum: 15, lo: 1, hi: 5, ex: 0),
	(len: 5, sum: 16, lo: 1, hi: 6, ex: 5),
	(len: 6, sum: 21, lo: 1, hi: 6, ex: 0),
	(len: 6, sum: 22, lo: 1, hi: 7, ex: 6),
	(len: 7, sum: 28, lo: 1, hi: 7, ex: 0),
	(len: 7, sum: 29, lo: 1, hi: 8, ex: 7),
	(len: 8, sum: 36, lo: 1, hi: 8, ex: 0),
	(len: 8, sum: 37, lo: 1, hi: 9, ex: 8),
	(len: 9, sum: 45, lo: 1, hi: 9, ex: 0),
	(len: 2, sum: 17, lo: 8, hi: 9, ex: 0),
	(len: 2, sum: 16, lo: 7, hi: 9, ex: 8),
	(len: 3, sum: 24, lo: 7, hi: 9, ex: 0),
	(len: 3, sum: 23, lo: 6, hi: 9, ex: 7),
	(len: 4, sum: 30, lo: 6, hi: 9, ex: 0),
	(len: 4, sum: 29, lo: 5, hi: 9, ex: 6),
	(len: 5, sum: 35, lo: 5, hi: 9, ex: 0),
	(len: 5, sum: 34, lo: 4, hi: 9, ex: 5),
	(len: 6, sum: 39, lo: 4, hi: 9, ex: 0),
	(len: 6, sum: 38, lo: 3, hi: 9, ex: 4),
	(len: 7, sum: 42, lo: 3, hi: 9, ex: 0),
	(len: 7, sum: 41, lo: 2, hi: 9, ex: 3),
	(len: 8, sum: 44, lo: 2, hi: 9, ex: 0)
];

predicate magic_constraint(int: s, array [int] of var int: word) =
	let {
		int: l = length(word);
	} in forall (m in magic where l = m.len /\ s = m.sum, x in word) (
		m.lo <= x
		/\ x <= m.hi
		/\ x != m.ex
	);
